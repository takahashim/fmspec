# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 並行するプロセス（仕様書 §12.4）。プログラムカウンタとローカル状態への展開と、スケジュールを固定した実装の実行。
class ProcessTest < Minitest::Test
  # 2つのプロセスが、共有のカウンタを読んでから書く。読みと書きは別の atomic step である。
  def racy = @racy ||= define_racy(invariant: true)

  # 不変条件のない、実装のとおりの仕様。
  def plain = @plain ||= define_racy(invariant: false)

  def define_racy(invariant:)
    Fmspec.define(:racy) do
      state :count, int(0..2), initial: 0
      process :incr, count: 2 do
        local :seen, int(0..2), initial: 0
        step(:load) { |s| update seen: s.count }
        step(:store) { |s| update count: s.seen + 1 }
      end
      invariant(:no_lost_update) { |s| implies(s.incr[0].done & s.incr[1].done, s.count.eq(2)) } if invariant
    end
  end

  # ロックを取ってから読み書きする。
  def locked = @locked ||= define_locked

  def define_locked
    Fmspec.define(:locked) do
      state :count, int(0..2), initial: 0
      state :holder, int(-1..1), initial: -1
      process :incr, count: 2 do |id|
        local :seen, int(0..2), initial: 0
        step(:acquire) do |s|
          guard s.holder.eq(-1)
          update holder: id
        end
        step(:load) { |s| update seen: s.count }
        step(:store) { |s| update count: s.seen + 1 }
        step(:release) { |_s| update holder: -1 }
      end
      invariant(:no_lost_update) { |s| implies(s.incr[0].done & s.incr[1].done, s.count.eq(2)) }
      invariant(:mutual_exclusion) { |s| not_(s.incr[0].pc.eq(:store) & s.incr[1].pc.eq(:store)) }
    end
  end

  def test_processes_expand_into_program_counters_locals_and_steps
    ir = racy.to_ir
    assert_equal %w[count incr[0].pc incr[0].seen incr[1].pc incr[1].seen], ir["states"].map { |s| s["name"] }
    assert_equal({ "name" => "incr.pc", "variants" => %w[load store done] }, ir["enums"].last)
    assert_equal %w[incr[0].load incr[0].store incr[1].load incr[1].store], ir["actions"].map { |a| a["name"] }
    store = ir["actions"][1]
    # ステップは、プログラムカウンタがそのステップのときだけ有効で、実行すると次のステップに進む。
    assert_equal({ "eq" => [{ "var" => 1 }, { "enum" => { "type" => "incr.pc", "variant" => "store" } }] }, store["guard"])
    assert_includes store["updates"], { "target" => 1, "expr" => { "enum" => { "type" => "incr.pc", "variant" => "done" } } }
    # ローカル変数は、そのインスタンスの状態変数になる。
    assert_includes store["updates"], { "target" => 0, "expr" => { "add" => [{ "var" => 2 }, { "int" => 1 }] } }
    assert_equal({ incr: { count: 2, steps: %i[load store] } }, racy.processes)
  end

  def test_interleavings_are_enumerated
    result = racy.check(deadlock: true)
    assert_equal :violated, result.status
    assert_equal "no_lost_update", result.property["name"]
    assert_equal %i[incr[0].load incr[1].load incr[0].store incr[1].store], result.trace.steps.map(&:action)

    # すべてのプロセスが終われば終端なので、デッドロックではない。ロックがあれば、更新は失われない。
    assert locked.check(deadlock: true).verified?
  end

  def test_goto_changes_the_next_step
    retry_model = Fmspec.define(:retry) do
      state :version, int(0..3), initial: 0
      process :writer, count: 2 do
        local :read, int(0..3), initial: 0
        step(:load) { |s| update read: s.version }
        # 読んだ後に版が変わっていれば、読み直す（楽観的ロック）。
        step(:write) do |s|
          accept_if s.version.eq(s.read)
          on_accept { update version: s.version + 1 }
          goto :load, s.version.ne(s.read)
        end
      end
      invariant(:both_written) { |s| implies(s.writer[0].done & s.writer[1].done, s.version.eq(2)) }
    end
    assert retry_model.check(deadlock: true).verified?

    error = assert_raises(Fmspec::BuildError) do
      Fmspec.define(:bad) do
        process(:p) { step(:a) { |_s| goto :nowhere } }
      end
    end
    assert_match(/goto の行き先/, error.message)
  end

  def test_invalid_processes_are_rejected
    errors = {
      /ステップがありません/ => proc { process(:p) { nil } },
      /予約されています/ => proc { process(:p) { local :pc, int(0..1), initial: 0 } },
      /状態変数または定数と同じ名前/ => proc {
        state :x, int(0..1), initial: 0
        process(:p) { local :x, int(0..1), initial: 0 }
      },
      /インスタンスごとに同じ/ => proc { process(:p, count: 2) { |id| step(:"s#{id}") { |_s| unchanged } } },
      /update では変えられません/ => proc { process(:p) { step(:a) { |_s| update pc: :done } } },
      /インスタンスの番号は 0..0/ => proc {
        process(:p) { step(:a) { |_s| unchanged } }
        invariant(:x) { |s| s.p[1].done }
      }
    }
    errors.each do |message, block|
      error = assert_raises(Fmspec::BuildError) { Fmspec.define(:bad, &block) }
      assert_match message, error.message
    end
  end

  # 実装。カウンタを共有し、各クライアントが読んでから書く。
  class Counter
    attr_accessor :count

    def initialize(lock: false)
      @count = 0
      @lock = lock ? Mutex.new : nil
    end

    def client = Client.new(self, @lock)
  end

  class Client
    attr_reader :threads

    def initialize(counter, lock)
      @counter = counter
      @lock = lock
      @threads = []
    end

    def load
      @threads << Thread.current
      # ロックを取ると、store まで手放さない。
      @lock&.lock
      @seen = @counter.count
    end

    def store
      @threads << Thread.current
      @counter.count = @seen + 1
      @lock&.unlock
    end
  end

  def counter_binding(model, lock: false, timeout: 1, clients: [])
    model.bind do
      setup { Counter.new(lock: lock) }
      process :incr, timeout: timeout do
        setup { |counter, _id| counter.client.tap { |c| clients << c } }
        step(:load, method: :load)
        step(:store, method: :store)
      end
      observe(:count, &:count)
    end
  end

  def test_steps_run_on_a_thread_per_instance_in_the_chosen_order
    clients = []
    result = plain.test(counter_binding(plain, clients: clients), cases: 30, steps: 4, seed: 1)
    assert_equal :passed, result.status
    # 各インスタンスのステップは、そのインスタンスの1つのスレッドで実行する。テストのスレッドではない。
    clients.each do |c|
      assert_equal 1, c.threads.uniq.length
      refute_equal Thread.current, c.threads.first
    end
    assert_equal 60, clients.length
  end

  def test_a_counterexample_schedule_is_reproduced_on_the_implementation
    violation = racy.check.trace
    binding = counter_binding(racy)
    # 反例のスケジュールで実装を動かすと、実装も仕様のとおりに更新を1つ失い、不変条件の違反に至る。
    result = racy.test(binding, replay: violation)
    assert_equal :model_violation, result.status
    assert_equal "no_lost_update", result.detail.dig("property", "name")
    assert_equal 4, result.matched_steps
    assert_equal 1, result.steps.last.observation[:count]
  end

  def test_a_step_blocked_by_the_implementation_is_inconclusive
    # 実装は load から store までロックを持つので、仕様が許す「両方が読んでから書く」スケジュールを再現できない。
    binding = counter_binding(racy, lock: true, timeout: 0.1)
    result = racy.test(binding, replay: racy.check.trace)
    assert_equal :inconclusive, result.status
    assert_equal :step_timeout, result.reason
    assert_equal :"incr[1].load", result.steps.last.action
    assert_equal 1, result.matched_steps
  end

  def test_the_implementation_is_checked_against_a_locked_model
    model = locked
    lock = Mutex.new
    binding = model.bind do
      setup { Counter.new }
      process :incr do
        setup { |counter, _id| counter.client }
        step(:acquire) { |_c| lock.lock }
        step(:load, method: :load)
        step(:store) do |c|
          c.store
          # 誤り: 書いた値を1つ多くする。
          c.instance_variable_get(:@counter).count += 1 if c.instance_variable_get(:@counter).count == 1
        end
        step(:release) { |_c| lock.unlock }
      end
      observe(:count, &:count)
    end
    result = model.test(binding, cases: 10, steps: 8, seed: 2)
    assert_equal :conformance_failure, result.status
    assert_equal ["count"], result.detail["mismatch"]
  end

  def test_process_bindings_are_validated
    model = racy
    assert_raises(Fmspec::BuildError) { model.bind { setup { nil }; process(:other) { nil } } }
    error = assert_raises(Fmspec::BuildError) do
      model.bind do
        setup { nil }
        process(:incr) { step(:load) { |_c| nil } }
      end
    end
    assert_match(/command が登録されていない操作があります: incr\[0\].store, incr\[1\].store/, error.message)
    assert_raises(Fmspec::BuildError) { model.bind { setup { nil }; process(:incr) { step(:missing) { |_c| nil } } } }
  end

  def test_a_failing_process_setup_is_a_setup_error
    binding = racy.bind do
      setup { Counter.new }
      process :incr do
        setup { |_counter, id| raise "接続できません" if id == 1 }
        step(:load) { |_c| nil }
        step(:store) { |_c| nil }
      end
      observe(:count, &:count)
    end
    result = racy.test(binding, cases: 1, steps: 1, seed: 0)
    assert_equal :setup_error, result.status
    assert_equal "接続できません", result.exception.message
  end

  def test_processes_survive_composition
    model = Fmspec.compose(:both, a: racy)
    assert_equal({ "a.incr": { count: 2, steps: %i[load store] } }, model.processes)
    assert_includes model.to_ir["actions"].map { |a| a["name"] }, "a.incr[0].load"
  end
end
