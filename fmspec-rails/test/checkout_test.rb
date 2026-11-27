# frozen_string_literal: true

require_relative "test_helper"

# DB、ジョブ、Webhook を含む代表例（仕様書 §16 段階6、§17.2）。
# 正しい実装が適合することと、代表的な変異を検出することを確かめる。
class CheckoutTest < Minitest::Test
  def setup
    CheckoutApp.bug = nil
  end

  def teardown
    CheckoutApp.bug = nil
    PaymentGateway.client = nil
  end

  def binding
    @binding ||= Fmspec::Rails.bind(Checkout, app: CheckoutApp, records: [Order, Fulfillment]) do
      setup do |c|
        c[:order] = Order.create!(owner_id: 0)
        c[:gateway] = PaymentGateway.client = FakeGateway.new
      end

      command(:checkout) { |c| c.post("/orders/#{c[:order].id}/checkout") }
      # 決済APIの応答を fake に指示してから、キューのジョブを実行する。
      command(:run_job, inject: [:response]) do |c, response:|
        c[:gateway].next_response = response
        c.perform_next_job
      end
      command(:webhook) do |c|
        c.post("/webhooks/payments", params: { type: "payment.succeeded", order_id: c[:order].id })
      end
      command(:cancel) do |c, user:|
        c.post("/orders/#{c[:order].id}/cancel", params: { user_id: user }).status == 200 ? :success : :forbidden
      end

      observe(:status) { |c| c[:order].reload.status.to_sym }
      observe(:queued) { |c| c.enqueued_jobs.any? }
      # Ghost State は、fake とDBに残った実際の記録から観測する。
      observe(:charges) { |c| [c[:gateway].charges.length, 2].min }
      observe(:fulfillments) { |c| [Fulfillment.where(order: c[:order]).count, 2].min }
    end
  end

  def run_test(**options)
    Checkout.test(binding, cases: 300, steps: 12, seed: 2026, **options)
  end

  def test_the_specification_is_safe
    result = Checkout.check(deadlock: false)
    assert_equal :verified, result.status, result.to_s
    assert_equal %i[charges fulfillments], Checkout.ghosts
  end

  def test_the_application_conforms
    result = run_test
    assert_equal :passed, result.status, result.to_s
    assert_equal 300, result.cases
    # ケースの中の変更は、どれも残っていない。
    assert_equal [0, 0], [Order.count, Fulfillment.count]
  end

  # 変異を検出し、一致しなかった項目と、縮小後の操作列を返す。
  def detect(bug)
    CheckoutApp.bug = bug
    result = run_test
    assert_equal :conformance_failure, result.status, "#{bug} を検出できなかった\n#{result}"
    assert_equal [0, 0], [Order.count, Fulfillment.count]
    # 縮小後の操作列は、そのまま再実行でき、正しい実装では通る。
    assert_equal :conformance_failure, Checkout.test(binding, replay: result.inputs).status
    CheckoutApp.bug = nil
    assert_equal :passed, Checkout.test(binding, replay: result.inputs).status
    [result.detail["mismatch"], result.inputs.map(&:first), result]
  end

  # 拒否操作の副作用。
  def test_a_rejected_cancel_with_a_side_effect_is_detected
    mismatch, actions, result = detect(:cancel_side_effect)
    assert_equal ["status"], mismatch
    assert_equal [[:cancel, { user: 1 }]], result.inputs
    assert_equal [:cancel], actions
    assert_match(/expected status: "pending"\n  observed status: :cancelled/, result.to_s)
  end

  # 二重決済。応答を失った決済のあとの再試行で起きる。
  def test_a_double_charge_is_detected
    mismatch, actions, result = detect(:no_idempotency_key)
    assert_equal ["charges"], mismatch
    assert_equal %i[checkout run_job run_job], actions
    assert_equal :timeout_charged, result.inputs[1][1][:response]
    assert_includes %i[ok timeout_charged], result.inputs[2][1][:response]
    assert_match(/expected charges: 1\n  observed charges: 2/, result.to_s)
  end

  # Webhook の重複。
  def test_a_duplicated_webhook_is_detected
    mismatch, actions, = detect(:webhook_not_idempotent)
    assert_equal ["fulfillments"], mismatch
    assert_equal :webhook, actions.last
    assert_operator actions.length, :<=, 4
  end

  # ジョブの再試行。
  def test_a_job_that_is_not_retried_is_detected
    mismatch, actions, result = detect(:job_not_retried)
    assert_equal ["queued"], mismatch
    assert_equal %i[checkout run_job], actions
    assert_includes %i[timeout_lost timeout_charged], result.inputs[1][1][:response]
  end

  def test_failures_report_the_binding_and_the_specification
    CheckoutApp.bug = :no_idempotency_key
    report = run_test.to_s
    assert_match(/\AConformance failure: checkout \/ charges\n  seed: 2026/, report)
    assert_match(/^  2\. run_job\(response: :timeout_charged\)$/, report)
    assert_match(%r{^  specification: .*test/support/checkout_spec\.rb:\d+$}, report)
    assert_match(/^  binding: #{Regexp.escape(__FILE__)}:\d+$/, report)
  end
end
