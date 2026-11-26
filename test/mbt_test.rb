# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

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
    rejected.call(/command purchase のブロックのキーワード引数（count）が、操作の引数（quantity）と合いません/) do
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
