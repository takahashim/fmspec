# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require "timeout"

# 実装との適合性検査（仕様書 §11、§17.2）。意図的にバグを入れた実装で、検出と縮小を確かめる。
class MbtTest < Minitest::Test
  # チケット売り場の実装。bug で、仕様から外れる振る舞いを選ぶ。
  class BoxOffice
    attr_reader :sold

    def initialize(capacity:, bug: nil)
      @capacity = capacity
      @sold = 0
      @bug = bug
    end

    def sell(quantity)
      raise "売り切れのはずがない" if @bug == :raises_at_three && @sold + quantity == 3

      @sold += quantity
    end

    def refund
      # 2枚売れているときの払い戻しで、2枚減らしてしまう。
      @sold -= @bug == :double_refund && @sold == 2 ? 2 : 1
    end
  end

  def tickets = @tickets ||= TestModels.tickets

  def binding_for(bug = nil, log: nil)
    tickets.bind do
      setup { BoxOffice.new(capacity: 3, bug: bug) }
      teardown { |office| log << office.sold if log }
      command(:purchase) { |office, quantity:| office.sell(quantity) }
      command(:cancel, method: :refund)
      observe(:sold) { |office| office.sold }
    end
  end

  def test_a_conforming_implementation_passes
    torn_down = []
    result = tickets.test(binding_for(log: torn_down), cases: 100, steps: 20, seed: 42)
    assert_equal :passed, result.status
    assert_same result, result.assert_passed!
    assert_equal [100, 2000, 42], [result.cases, result.matched_steps, result.seed]
    assert_equal 100, torn_down.length
    assert_equal "Passed: tickets（100 ケース、照合済み 2000 ステップ、seed 42）\n", result.to_s
  end

  def test_a_wrong_state_is_detected_and_shrunk
    binding = binding_for(:double_refund)
    result = tickets.test(binding, cases: 100, steps: 20, seed: 42)
    assert_equal :conformance_failure, result.status
    # 縮小後の操作列は、2枚にしてから払い戻す最小の形になる。
    assert_includes [[[:purchase, { quantity: 2 }], [:cancel, {}]],
                     [[:purchase, { quantity: 1 }], [:purchase, { quantity: 1 }], [:cancel, {}]]], result.inputs
    assert_operator result.original_steps, :>=, result.steps.length
    assert_equal ["sold"], result.detail["mismatch"]
    assert_equal [{ "state" => { "sold" => 1 } }], result.detail["expected"]
    assert_equal 0, result.steps.last.observation[:sold]

    report = result.to_s
    assert_match(/\AConformance failure: tickets \/ sold\n  seed: 42/, report)
    assert_match(/^  \d+\. cancel\(\)\n/, report)
    assert_match(/^  expected sold: 1\n  observed sold: 0\n/, report)
    assert_match(/^  specification: .*models\.rb:\d+\n/, report)
    assert_match(/^  binding: #{Regexp.escape(__FILE__)}:\d+\n/, report)
    error = assert_raises(Fmspec::TestFailed) { result.assert_passed! }
    assert_equal report, error.message

    # 同じ seed なら同じ結果になり、縮小後の操作列はそのまま再実行できる。
    assert_equal result.inputs, tickets.test(binding, cases: 100, steps: 20, seed: 42).inputs
    replayed = tickets.test(binding, replay: result.inputs)
    assert_equal [:conformance_failure, result.inputs], [replayed.status, replayed.inputs]
    assert_equal :passed, tickets.test(binding_for, replay: result.inputs).status
  end

  def test_shrinking_can_be_turned_off
    result = tickets.test(binding_for(:double_refund), cases: 100, steps: 20, seed: 42, shrink: false)
    assert_equal :conformance_failure, result.status
    assert_nil result.original_steps
    assert_equal :cancel, result.inputs.last[0]
  end

  def test_an_unexpected_exception_is_an_execution_error
    torn_down = []
    result = tickets.test(binding_for(:raises_at_three, log: torn_down), cases: 50, steps: 20, seed: 1)
    assert_equal :execution_error, result.status
    assert_instance_of RuntimeError, result.exception
    # 縮小しても、同じ操作で同じ例外が起きる。3枚目に達する最短の操作列は2ステップ。
    assert_equal 2, result.steps.length
    assert_equal 3, result.inputs.sum { |_, args| args[:quantity] }
    assert_match(/\AExecution error: tickets\n.*RuntimeError: 売り切れのはずがない/m, result.to_s)
    # teardown は、失敗したケースでも、縮小のための再実行でも呼ばれる。
    refute_empty torn_down
  end

  def test_setup_and_teardown_failures_are_not_successes
    model = tickets
    failing_setup = model.bind do
      setup { raise ArgumentError, "DB に接続できない" }
      command(:purchase) { |_c, quantity:| quantity }
      command(:cancel) { |_c| nil }
    end
    result = model.test(failing_setup, cases: 3, steps: 3, seed: 1)
    assert_equal [:setup_error, ArgumentError], [result.status, result.exception.class]
    assert_match(/\ASetup error: tickets\n.*DB に接続できない/m, result.to_s)

    failing_teardown = model.bind do
      setup { BoxOffice.new(capacity: 3) }
      teardown { |_office| raise "後始末に失敗" }
      command(:purchase) { |office, quantity:| office.sell(quantity) }
      command(:cancel, method: :refund)
      observe(:sold, method: :sold)
    end
    assert_equal :setup_error, model.test(failing_teardown, cases: 3, steps: 3, seed: 1).status
  end

  # 拒否を同じ操作の結果として書いた仕様（仕様書 §12.1）。
  def orders
    @orders ||= Fmspec.define(:orders) do
      status = enum(:status, :open, :cancelled)
      enum(:result, :success, :forbidden)
      state :order, status, initial: :open
      state :cancellations, int(0..3), initial: 0

      action :cancel, user: 0..1 do |s, user|
        accept_if user.eq(0) & s.order.eq(:open)
        on_accept do
          update order: :cancelled, cancellations: s.cancellations + 1
          returns :success
        end
        on_reject do
          unchanged
          returns :forbidden
        end
      end

      action :reopen do |s|
        guard s.order.eq(:cancelled) & (s.cancellations < 3)
        update order: :open
      end
    end
  end

  # 注文の実装。所有者は利用者0。
  class Orders
    attr_reader :status, :cancellations

    def initialize(bug)
      @status = :open
      @cancellations = 0
      @bug = bug
    end

    def cancel(user:)
      allowed = user.zero? && @status == :open
      # 拒否したのに、取消の回数だけ数えてしまう。
      @cancellations += 1 if allowed || (@bug == :counts_rejections && @status == :open)
      return @bug == :wrong_result ? :success : :forbidden unless allowed

      @status = :cancelled
      :success
    end

    def reopen = @status = :open
  end

  def orders_binding(bug = nil)
    orders.bind do
      setup { Orders.new(bug) }
      command(:cancel) { |o, user:| o.cancel(user: user) }
      command(:reopen, method: :reopen)
      observe(:order, method: :status)
      observe(:cancellations, method: :cancellations)
    end
  end

  def test_rejections_and_return_values_are_checked
    assert_equal :verified, orders.check.status
    orders.test(orders_binding, cases: 100, steps: 12, seed: 3).assert_passed!

    # 拒否の副作用。
    result = orders.test(orders_binding(:counts_rejections), cases: 100, steps: 12, seed: 3)
    assert_equal [:conformance_failure, ["cancellations"]], [result.status, result.detail["mismatch"]]
    assert_equal [[:cancel, { user: 1 }]], result.inputs
    assert_match(/expected cancellations: 0\n  observed cancellations: 1/, result.to_s)

    # 戻り値の不一致。状態は合っている。
    result = orders.test(orders_binding(:wrong_result), cases: 100, steps: 12, seed: 3)
    assert_equal [:conformance_failure, ["output"]], [result.status, result.detail["mismatch"]]
    assert_equal :cancel, result.inputs.last[0]
    assert_match(/\AConformance failure: orders \/ output\n/, result.to_s)
    assert_match(/expected return value: "forbidden"\n  observed return value: :success/, result.to_s)
  end

  # 外部の決済APIの応答を内部選択として書いた仕様。応答はテストが決めて、fake に指示する（仕様書 §12.3）。
  def payments
    @payments ||= Fmspec.define(:payments) do
      enum(:response, :ok, :declined, :timeout_charged)
      state :paid, bool, initial: false
      # 決済の回数。0、1、2以上の3値に飽和させて、二重決済を見つける。
      ghost :charges, int(0..2), initial: 0

      action :pay do |s|
        guard s.paid.not_
        response = choose(:response, enum(:response, :ok, :declined, :timeout_charged))
        charged = response.ne(:declined)
        # 同じ注文への2回目の請求は、冪等キーによって新しい決済にならない。
        update paid: response.eq(:ok), charges: ite(charged, max(s.charges, 1), s.charges)
      end

      invariant(:no_double_charge) { |s| s.charges <= 1 }
    end
  end

  # 決済APIの fake。次の応答を指示でき、決済の記録を持つ。
  class FakeGateway
    attr_accessor :next_response
    attr_reader :charges

    def initialize
      @charges = []
      @keys = {}
    end

    def charge(key)
      return :declined if next_response == :declined

      @charges << key unless key && @keys[key]
      @keys[key] = true if key
      next_response == :ok ? :ok : (raise Timeout::Error)
    end
  end

  class Shop
    attr_reader :gateway, :paid

    def initialize(idempotent:)
      @gateway = FakeGateway.new
      @paid = false
      @idempotent = idempotent
    end

    def pay
      @paid = gateway.charge(@idempotent ? "order-1" : nil) == :ok
    rescue Timeout::Error
      @paid = false
    end
  end

  def payments_binding(idempotent:, seen: nil)
    payments.bind do
      setup { Shop.new(idempotent: idempotent) }
      command(:pay, inject: [:response]) do |shop, response:|
        seen << response if seen
        shop.gateway.next_response = response
        shop.pay
      end
      observe(:paid, method: :paid)
      # Ghost State は、fake が記録した実際の決済から観測する。期待した回数を代入しない。
      observe(:charges) { |shop| [shop.gateway.charges.length, 2].min }
    end
  end

  def test_fault_injection_finds_a_double_charge
    assert_equal [:charges], payments.ghosts
    assert_equal :verified, payments.check.status
    seen = []
    payments.test(payments_binding(idempotent: true, seen: seen), cases: 100, steps: 6, seed: 9).assert_passed!
    # テストが、決済APIの応答をすべての種類で注入している。
    assert_equal %i[declined ok timeout_charged], seen.uniq.sort

    # 冪等キーを付けない実装は、応答を失った決済のあとの再試行で、二重に決済する。
    result = payments.test(payments_binding(idempotent: false), cases: 100, steps: 6, seed: 9)
    assert_equal [:conformance_failure, ["charges"]], [result.status, result.detail["mismatch"]]
    assert_equal [:pay, :pay], result.inputs.map(&:first)
    assert_equal :timeout_charged, result.inputs[0][1][:response]
    refute_equal :declined, result.inputs[1][1][:response]
    assert_match(/1\. pay\(response: :timeout_charged\)\n/, result.to_s)
    assert_match(/expected charges: 1\n  observed charges: 2/, result.to_s)
    # 注入した値ごと、操作列を再実行できる。
    replayed = payments.test(payments_binding(idempotent: false), replay: result.inputs)
    assert_equal [:conformance_failure, result.inputs], [replayed.status, replayed.inputs]
    assert_equal :passed, payments.test(payments_binding(idempotent: true), replay: result.inputs).status
    # JSON に保存した操作列（キーと列挙型の値が文字列）でも再実行できる。
    saved = JSON.parse(JSON.generate(result.inputs))
    assert_equal :conformance_failure, payments.test(payments_binding(idempotent: false), replay: saved).status
  end

  def test_injected_choices_are_checked_against_the_specification
    model = payments
    error = assert_raises(Fmspec::BuildError) do
      model.bind do
        setup { Object.new }
        command(:pay, inject: [:outcome]) { |_c, outcome:| outcome }
      end
    end
    assert_match(/command pay の inject に、操作にない内部選択があります: outcome/, error.message)
  end

  def test_values_outside_the_specification_do_not_match
    model = tickets
    weird = model.bind do
      setup { BoxOffice.new(capacity: 3) }
      command(:purchase) { |office, quantity:| office.sell(quantity) }
      command(:cancel, method: :refund)
      observe(:sold) { |office| office.sold.to_s }
    end
    result = model.test(weird, cases: 1, steps: 1, seed: 1)
    assert_equal [:conformance_failure, 0, ["sold"]], [result.status, result.steps.length, result.detail["mismatch"]]
    assert_match(/expected sold: 0\n  observed sold: "0"/, result.to_s)
  end

  def test_bindings_are_checked_against_the_specification
    model = tickets
    rejected = lambda do |pattern, &block|
      error = assert_raises(Fmspec::BuildError) { model.bind(&block) }
      assert_match pattern, error.message
    end
    rejected.call(/setup が必要/) { command(:purchase) { |_c, quantity:| quantity } }
    rejected.call(/command が登録されていない操作があります: cancel/) do
      setup { Object.new }
      command(:purchase) { |_c, quantity:| quantity }
    end
    rejected.call(/仕様にない操作の command があります: refund/) do
      setup { Object.new }
      command(:purchase) { |_c, quantity:| quantity }
      command(:cancel) { |_c| nil }
      command(:refund) { |_c| nil }
    end
    rejected.call(/仕様にない状態変数の observe があります: total/) do
      setup { Object.new }
      command(:purchase) { |_c, quantity:| quantity }
      command(:cancel) { |_c| nil }
      observe(:total) { |_c| 0 }
    end
    rejected.call(/command purchase のブロックのキーワード引数（count）が、操作の引数と注入する選択（quantity）と合いません/) do
      setup { Object.new }
      command(:purchase) { |_c, count:| count }
      command(:cancel) { |_c| nil }
    end
    rejected.call(/command cancel の登録が重複/) do
      setup { Object.new }
      command(:cancel) { |_c| nil }
      command(:cancel) { |_c| nil }
    end
    rejected.call(/ブロックか method: のどちらか一方/) do
      setup { Object.new }
      command(:cancel)
    end
    other = TestModels.tickets.bind do
      setup { Object.new }
      command(:purchase) { |_c, quantity:| quantity }
      command(:cancel) { |_c| nil }
    end
    assert_raises(ArgumentError) { model.test(other) }
    assert_raises(ArgumentError) { model.test(binding_for, actions: [:refund]) }
  end

  def test_actions_can_be_limited
    purchases = []
    model = tickets
    binding = model.bind do
      setup { BoxOffice.new(capacity: 3) }
      command(:purchase) { |office, quantity:| purchases << quantity && office.sell(quantity) }
      command(:cancel) { |_office| flunk "対象外の操作が呼ばれた" }
      observe(:sold, method: :sold)
    end
    result = model.test(binding, cases: 20, steps: 10, seed: 5, actions: [:purchase])
    assert_equal :passed, result.status
    # 購入だけでは3枚で行き止まりになり、ケースはそこで終わる。
    assert_equal result.matched_steps, purchases.length
    assert_operator result.matched_steps, :<, 20 * 10
  end
end
