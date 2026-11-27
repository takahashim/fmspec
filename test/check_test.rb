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

  # 2つのカウンタ（0..9）の最も深い状態 (9, 9) は、初期状態から18回の遷移で到達する。
  def test_the_depth_limit
    model = TestModels.counters(2, 9)
    assert_equal :verified, model.check(max_depth: 18).status
    result = model.check(max_depth: 17, certificate: true)
    assert_equal [:inconclusive, :max_depth], [result.status, result.reason]
    assert_nil result.certificate
    assert_raises(ArgumentError) { model.check(max_depth: -1) }
  end

  def test_the_time_limit
    model = TestModels.tickets
    assert_equal [:inconclusive, :max_time_ms], model.check(max_time_ms: 0).then { |r| [r.status, r.reason] }
    assert_equal [:inconclusive, :max_time_ms], model.simulate(max_time_ms: 0, seed: 1).then { |r| [r.status, r.reason] }
    assert_equal :verified, model.check(max_time_ms: 60_000).status
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

  def test_model_traces_can_be_shrunk
    model = TestModels.tickets(guarded: false)
    long = (0..200).lazy.map { |seed| model.simulate(seed: seed, invariants: [:capacity_respected]) }
                   .find { |r| r.violated? && r.trace.length > 2 }
    shrunk = model.shrink(long.trace)
    assert_equal :violated, shrunk.status
    assert_equal "capacity_respected", shrunk.property["name"]
    assert_equal [2, long.trace.length], [shrunk.trace.length, shrunk.to_h["original_steps"]]
    assert_equal long.trace.seed, shrunk.trace.seed
    assert_equal :violated, model.replay(shrunk.trace).status
    assert_equal true, shrunk.shrink["complete"]
    # 上限に達したら打ち切り、それまでに判定ゲートが受理したトレースを返す。
    late = model.shrink(long.trace, max_time_ms: 0)
    assert_equal [:violated, false, "max_time_ms"], [late.status, late.shrink["complete"], late.shrink["limit"]]
    assert_equal long.trace.to_h["steps"], late.trace.to_h["steps"]
    assert_equal "attempts", model.shrink(long.trace, attempts: 1).shrink["limit"]
    # 見積もりが上限を超えるトレースは検査しない。
    [model.replay(long.trace, max_check_cost: 1), model.shrink(long.trace, max_check_cost: 1)].each do |r|
      assert_equal [:inconclusive, :max_check_cost], [r.status, r.reason]
    end
    # BFS の反例は最短なので、それ以上は縮まない。
    shortest = model.check.trace
    assert_equal shortest.to_h["steps"], model.shrink(shortest).trace.to_h["steps"]
  end

  def test_evidence_for_another_model_is_checked_only_when_asked
    old = TestModels.tickets(guarded: false)
    trace = old.check.trace
    # 不変条件を1つ加えた、別のモデル。トレースの検査条件は加えた不変条件を含まない。
    new = Fmspec.define(:tickets) do
      state :sold, int(0..4), initial: 0
      action(:purchase, quantity: 1..2) { |s, quantity| update sold: s.sold + quantity }
      action :cancel do |s|
        guard s.sold > 0
        update sold: s.sold - 1
      end
      invariant(:capacity_respected) { |s| s.sold <= 3 }
      invariant(:nonnegative) { |s| s.sold >= 0 }
    end
    refute_equal old.digest, new.digest

    refused = new.replay(trace)
    assert_equal [:rejected, "unreadable"], [refused.status, refused.rejected["reason"]]
    assert_nil refused.evidence_model_digest
    assert_equal "unreadable", new.shrink(trace).rejected["reason"]

    replayed = new.replay(trace, allow_other_model: true)
    assert_equal :violated, replayed.status
    assert_equal old.digest, replayed.evidence_model_digest
    assert_equal new.digest, replayed.trace.to_h["model_digest"]
    assert_equal :violated, new.replay(replayed.trace).status
    assert_equal :violated, new.shrink(trace, allow_other_model: true).status

    # 判定は今のモデルに対して行う。guard のあるモデルでは、この反例はたどれない。
    guarded = TestModels.tickets.replay(trace, allow_other_model: true)
    assert_equal [:rejected, "step_mismatch"], [guarded.status, guarded.rejected["reason"]]

    certificate = TestModels.tickets.check(certificate: true).certificate
    assert_equal "unreadable", old.verify_certificate(certificate).rejected["reason"]
    checked = old.verify_certificate(certificate, allow_other_model: true)
    assert_equal :rejected, checked.status
    refute_equal "unreadable", checked.rejected["reason"]
    assert_equal TestModels.tickets.digest, checked.evidence_model_digest
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

  # 探索器の内部の不整合は、公開APIからは起こせない。エンジンが返す形の結果を読めることを確かめる。
  def test_an_inconsistency_of_the_search_is_an_internal_error_with_its_content
    inconsistency = { "kind" => "successors", "action" => "purchase", "state" => nil, "encoded_state" => [9],
                      "message" => "状態での操作の遷移を列挙できません。操作が未定義か、状態が状態型に従いません" }
    result = Fmspec::Result.new("status" => "internal_error", "model" => "tickets",
                                "inconsistency" => inconsistency,
                                "message" => "探索器の内部の不整合です。fmspec の不具合です")
    assert result.internal_error?
    assert_nil result.rejected
    assert_nil result.reason
    assert_equal "purchase", result.inconsistency["action"]
    assert_equal <<~TEXT, result.to_s
      InternalError: tickets
        不整合: 状態での操作の遷移を列挙できません。操作が未定義か、状態が状態型に従いません
          action: purchase
          encoded_state: [9]
        探索器の内部の不整合です。fmspec の不具合です
    TEXT
  end
end
