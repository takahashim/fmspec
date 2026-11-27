# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require_relative "../examples/crash/double_charge"
require_relative "../examples/crash/discarded_job"

# プロセスのクラッシュの、実装との適合性検査（docs/crash_design.md §5）。
class CrashMbtTest < Minitest::Test
  # 決済サービスの fake。idempotent なら、同じ注文の2回目の決済をしない。
  class Gateway
    attr_reader :charges

    def initialize(idempotent:)
      @idempotent = idempotent
      @charges = 0
      @keys = []
    end

    def charge(order)
      return if @idempotent && @keys.include?(order)

      @keys << order
      @charges += 1
    end
  end

  # 注文のDBとジョブの実装の記録。
  class Store
    attr_accessor :paid
    attr_reader :log

    def initialize(gateway)
      @gateway = gateway
      @paid = false
      @log = Queue.new
    end

    def charges = @gateway.charges
    def gateway = @gateway
  end

  # 決済してから注文を保存するジョブ。1回の実行（perform）が1つのインスタンスのコンテキストである。
  class CheckoutJob
    def initialize(store, id)
      @store = store
      @id = id
      @store.log << [:setup, id, Thread.current]
    end

    def charge = @store.gateway.charge(:order1)
    def save = @store.paid = true

    # ワーカーが落ちる。メモリ上の状態を捨てる。
    def abandon!
      @store.log << [:crash, @id, Thread.current]
    end

    def close = @store.log << [:teardown, @id, Thread.current]
  end

  def checkout_binding(model, idempotent:)
    model.bind do
      setup { Store.new(Gateway.new(idempotent: idempotent)) }
      process :job do
        setup { |store, id| CheckoutJob.new(store, id) }
        teardown(&:close)
        step(:charge, method: :charge)
        step(:save, method: :save)
        crash(method: :abandon!)
      end
      observe(:charges, &:charges)
      observe(:paid, &:paid)
    end
  end

  def log(result_store) = Array.new(result_store.log.size) { result_store.log.pop }

  def test_a_crash_counterexample_is_reproduced_on_the_implementation
    model = CrashExamples::DoubleCharge.define(:naive)
    trace = model.check.trace
    result = model.test(checkout_binding(model, idempotent: false), replay: trace)
    # 実装も、落ちたあとの再試行で二重に決済し、仕様の不変条件の違反に至る。
    assert_equal :model_violation, result.status
    assert_equal "charged_at_most_once", result.detail.dig("property", "name")
    assert_equal %i[job[0].charge job[0].crash job[0].charge], result.steps.map(&:action)
    assert_equal 2, result.steps.last.observation[:charges]
  end

  def test_the_implementation_is_checked_against_the_idempotent_model
    model = CrashExamples::DoubleCharge.define(:idempotent)
    assert_equal :passed, model.test(checkout_binding(model, idempotent: true), cases: 20, steps: 5, seed: 1).status
    # 冪等キーを渡さない実装は、落ちたあとの再試行で、仕様と違って二度目の決済をする。
    result = model.test(checkout_binding(model, idempotent: false), cases: 20, steps: 5, seed: 1)
    assert_equal :conformance_failure, result.status
    assert_equal ["charges"], result.detail["mismatch"]
  end

  def test_a_crash_ends_the_thread_without_teardown_and_restarts_with_setup
    model = CrashExamples::DoubleCharge.define(:naive)
    stores = []
    binding = model.bind do
      setup { Store.new(Gateway.new(idempotent: false)).tap { |s| stores << s } }
      process :job do
        setup { |store, id| CheckoutJob.new(store, id) }
        teardown(&:close)
        step(:charge, method: :charge)
        step(:save, method: :save)
        crash(method: :abandon!)
      end
      observe(:charges, &:charges)
    end
    inputs = [[:"job[0].charge", {}], [:"job[0].crash", {}], [:"job[0].charge", {}]]
    model.test(binding, replay: inputs)
    events = log(stores.last)
    assert_equal [%i[setup crash], %i[setup teardown]], events.map(&:first).each_slice(2).to_a
    # 落ちたインスタンスの crash はそのスレッドで実行し、再試行は新しいスレッドで setup から始める。
    first, crashed, second, closed = events.map(&:last)
    assert_equal first, crashed
    refute_equal first, second
    assert_equal second, closed
  end

  # retries: が尽きたあとのクラッシュでは、setup をもう一度呼ばない。
  def test_a_discarded_instance_is_not_restarted
    model = CrashExamples::DiscardedJob.define(:retries)
    setups = Queue.new
    binding = model.bind do
      setup { Object.new }
      process :job do
        setup { |_context, id| setups << id }
        step(:pay) { |_job| nil }
        step(:save) { |_job| nil }
        crash { |_job| nil }
      end
    end
    inputs = Array.new(3) { [:"job[0].crash", {}] }
    result = model.test(binding, replay: inputs)
    # 仕様では、3回目のクラッシュで注文が pending のまま捨てられる。
    assert_equal :model_violation, result.status
    assert_equal 3, setups.size
  end

  # crash: :abort のインスタンスは、落ちたあと setup をもう一度呼ばない。on_crash の環境の変化は、実装の crash が起こす。
  def test_an_aborted_instance_releases_the_lock_through_the_implementation
    model = Fmspec.define(:workers) do
      state :holder, int(-1..1), initial: -1
      state :count, int(0..2), initial: 0
      process :worker, count: 2, crash: :abort do |id|
        step(:lock) do |s|
          guard s.holder.eq(-1)
          update holder: id
        end
        step(:work) { |s| update count: s.count + 1 }
        step(:unlock) { |_s| update holder: -1 }
        on_crash { |s| update holder: ite(s.holder.eq(id), -1, s.holder) }
      end
    end
    db = Struct.new(:holder, :count, :setups)
    binding_for = lambda do |release:|
      model.bind do
        setup { db.new(-1, 0, Queue.new) }
        process :worker do
          setup do |d, id|
            d.setups << id
            [d, id]
          end
          step(:lock) { |(d, id)| d.holder = id }
          step(:work) { |(d, _)| d.count += 1 }
          step(:unlock) { |(d, _)| d.holder = -1 }
          # 接続を閉じると、DBはその接続のロックを解放する。release: false は、解放しない誤った実装。
          crash { |(d, id)| d.holder = -1 if release && d.holder == id }
        end
        observe(:holder, &:holder)
        observe(:count, &:count)
      end
    end
    assert_equal :passed, model.test(binding_for.call(release: true), cases: 30, steps: 6, seed: 3).status
    result = model.test(binding_for.call(release: false), cases: 30, steps: 6, seed: 3)
    assert_equal :conformance_failure, result.status
    assert_equal ["holder"], result.detail["mismatch"]
    assert_includes result.steps.map(&:action).last.to_s, "crash"
  end

  def test_crash_bindings_are_validated
    model = CrashExamples::DoubleCharge.define(:naive)
    error = assert_raises(Fmspec::BuildError) do
      model.bind do
        setup { nil }
        process(:job) do
          step(:charge) { |_j| nil }
          step(:save) { |_j| nil }
        end
      end
    end
    assert_match(/job\[0\]\.crash/, error.message)
    assert_raises(Fmspec::BuildError) do
      model.bind do
        setup { nil }
        process(:job) do
          step(:charge) { |_j| nil }
          step(:save) { |_j| nil }
          crash { |_j| nil }
          crash { |_j| nil }
        end
      end
    end

    plain = Fmspec.define(:plain) do
      state :n, int(0..1), initial: 0
      process(:p) { step(:a) { |_s| unchanged } }
    end
    error = assert_raises(Fmspec::BuildError) do
      plain.bind do
        setup { nil }
        process(:p) do
          step(:a) { |_j| nil }
          crash { |_j| nil }
        end
      end
    end
    assert_match(/crash: を持ちません/, error.message)
  end
end
