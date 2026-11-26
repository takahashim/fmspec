# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# DSL で書いた仕様を、エンジン（native extension）で検査する。
class CheckTest < Minitest::Test
  def test_the_example_from_the_specification_is_verified
    result = TestModels.tickets.check(max_states: 10_000, certificate: true)
    assert_equal :verified, result.status
    assert_predicate result, :verified?
    assert_equal 4, result.visited_states
    assert_equal [[0], [1], [2], [3]], result.certificate["states"]
    assert_nil result.trace
    assert_equal "Verified: tickets\n  証明書の状態数 4（判定ゲートが受理）\n  探索: 完走、訪問状態数 4、遷移数 8（探索器の報告）\n", result.to_s
  end

  def test_a_violation_comes_with_the_shortest_trace_and_the_source_location
    model = TestModels.tickets(guarded: false)
    result = model.check
    assert_equal :violated, result.status
    assert_equal({ "violation" => "invariant", "name" => "capacity_respected" }, result.property.except("source"))
    assert_equal File.expand_path("models.rb", __dir__), result.property["source"]["file"]
    trace = result.trace
    assert_equal 2, trace.length
    assert_equal({ "sold" => 0 }, trace.initial)
    assert_equal [:purchase, :purchase], trace.steps.map(&:action)
    assert_equal [{ "quantity" => 2 }, { "quantity" => 2 }], trace.steps.map(&:args)
    assert_equal [{ "sold" => 2 }, { "sold" => 4 }], trace.states
    assert_match(/\AViolated: tickets \/ 不変条件 capacity_respected の違反\n  定義: .*models\.rb:\d+\n/, result.to_s)
    # トレースは、そのまま再生できる。
    assert_equal :violated, model.replay(trace).status
    assert_equal :violated, model.replay(trace.to_json).status
  end

  def test_errors_and_initial_violations
    result = TestModels.tickets(constant_update: 5).check
    assert_equal :error, result.status
    assert_equal ["update", "sold", 5], result.property.values_at("site", "target").push(result.property["error"]["value"])
    assert_equal 0, result.trace.length

    result = TestModels.tickets(initial: 4).check
    assert_equal [:violated, 0], [result.status, result.trace.length]
  end

  def test_internal_choices_and_outputs_are_kept_in_the_trace
    result = TestModels.responder.check
    assert_equal :violated, result.status
    assert_equal({ "violation" => "contract", "name" => "succeeds" }, result.property.except("source"))
    step = result.trace.steps[0]
    assert_equal [:request, { "id" => 7 }, { "allowed" => false }, "forbidden"], [step.action, step.args, step.choices, step.output]
    # 契約を対象から外せば、同じモデルは安全である。
    assert_equal :verified, TestModels.responder.check(contracts: []).status
  end

  def test_conditions
    model = TestModels.tickets
    assert_equal :verified, model.check(deadlock: true).status
    # 購入を対象から外すと、初期状態から動けない。
    assert_equal :verified, model.check(actions: [:cancel]).status
    result = model.check(actions: [:cancel], deadlock: true)
    assert_equal [:violated, { "violation" => "deadlock", "source" => nil }], [result.status, result.property]
    error = assert_raises(ArgumentError) { model.check(actions: [:refund]) }
    assert_match(/未定義の操作 "refund"/, error.message)
    assert_raises(ArgumentError) { model.check(max_states: 0) }
    assert_raises(ArgumentError) { model.check(depth: 3) }
  end

  def test_terminal_states_are_not_deadlocks
    stuck = Fmspec.define(:stuck) { state :x, int(0..0), initial: 0 }
    assert_equal :violated, stuck.check(deadlock: true).status
    done = Fmspec.define(:done) do
      state :x, int(0..0), initial: 0
      terminal { |s| s.x.eq(0) }
    end
    assert_equal :verified, done.check(deadlock: true).status
  end

  def test_the_state_limit
    model = TestModels.counters(2, 9)
    result = model.check(max_states: 99)
    assert_equal [:inconclusive, :max_states, 99], [result.status, result.reason, result.visited_states]
    assert_predicate result, :inconclusive?
    assert_equal [:verified, 100], model.check(max_states: 100).then { |r| [r.status, r.visited_states] }
  end

  def test_expression_boundaries
    overflow = ->(big) { (big + 1) > 0 }
    status = ->(&invariant) { TestModels.big(&invariant).check.status }
    assert_equal :verified, status.call { |big| Fmspec.ite(false, overflow.(big), true) }
    assert_equal :error, status.call { |big| Fmspec.ite(true, overflow.(big), true) }
    assert_equal :violated, status.call { |big| Fmspec.all(false, overflow.(big)) }
    assert_equal :verified, status.call { |big| Fmspec.any(true, overflow.(big)) }
    assert_equal :verified, status.call { |big| Fmspec.implies(false, overflow.(big)) }
    assert_equal :error, status.call { |big| Fmspec.all(true, overflow.(big)) }
    assert_equal :error, status.call { |big| Fmspec.any(false, overflow.(big)) }
    assert_equal :error, status.call { |big| Fmspec.implies(true, overflow.(big)) }
    result = TestModels.big { |big| Fmspec.all(true, overflow.(big)) }.check
    assert_equal({ "kind" => "overflow" }, result.property["error"])
  end

  def test_certificates_are_verified_separately
    model = TestModels.tickets
    certificate = model.check(certificate: true).certificate
    assert_equal :verified, model.verify_certificate(certificate).status
    assert_equal :verified, model.verify_certificate(JSON.generate(certificate)).status
    # 状態を欠いた証明書、別の検査条件、別のモデル。
    short = certificate.merge("states" => [[0], [1], [2]])
    result = model.verify_certificate(short)
    assert_equal [:rejected, "missing_successor"], [result.status, result.rejected["reason"]]
    assert_equal "condition_mismatch", model.verify_certificate(certificate, deadlock: true).rejected["reason"]
    assert_equal "unreadable", TestModels.tickets(guarded: false).verify_certificate(certificate).rejected["reason"]
  end

  def test_forged_traces_are_rejected
    model = TestModels.tickets(guarded: false)
    trace = JSON.parse(model.check.trace.to_json)
    trace["steps"][0]["state"]["sold"] = 3
    result = model.replay(trace)
    assert_equal [:rejected, "step_mismatch"], [result.status, result.rejected["reason"]]
  end

  def test_simulation_is_reproducible_and_claims_no_coverage
    model = TestModels.tickets
    result = model.simulate(traces: 30, max_steps: 10, seed: 42)
    assert_equal [:sampled, 42, 30, 300], [result.status, result.seed, *result.simulation.values_at("completed_traces", "steps")]
    refute_predicate result, :verified?
    assert_match(/\ASampled: tickets（網羅性の主張なし）/, result.to_s)

    unsafe = TestModels.tickets(guarded: false)
    first = unsafe.simulate(seed: 7)
    assert_includes %i[violated error], first.status
    assert_equal first.trace.to_h, unsafe.simulate(seed: 7).trace.to_h
    assert_equal 7, first.trace.seed
    assert_equal first.status, unsafe.replay(first.trace).status
    # seed を省略すると無作為に選び、結果に記録する。その seed で再現できる。
    random = unsafe.simulate
    assert_kind_of Integer, random.seed
    assert_equal random.trace.to_h, unsafe.simulate(seed: random.seed).trace.to_h
    assert_raises(ArgumentError) { model.simulate(traces: 0) }
  end

  def test_digest_identifies_the_model
    assert_equal TestModels.tickets.digest, TestModels.tickets.digest
    refute_equal TestModels.tickets.digest, TestModels.tickets(guarded: false).digest
    assert_match(/\Asha256:\h{64}\z/, TestModels.tickets.digest)
  end

  # エンジンの結果が、参照実装の結果と一致する。
  def test_the_engine_agrees_with_the_reference_implementation
    require_relative "../reference/fmspec_reference"
    [TestModels.tickets, TestModels.tickets(guarded: false), TestModels.responder, TestModels.counters(2, 3)].each do |model|
      expected = FmspecReference::Model.new(JSON.parse(model.to_json)).check(deadlock: true)
      actual = model.check(deadlock: true)
      assert_equal expected["status"], actual.status.to_s
      assert_equal expected["visited_states"], actual.visited_states
      steps = actual.trace&.to_h&.fetch("steps")
      expected["steps"] ? assert_equal(expected["steps"], steps) : assert_nil(steps)
    end
  end
end
