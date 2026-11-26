# frozen_string_literal: true

require_relative "test_helper"

# 仕様書 §17.1.1 の境界ケースを、参照実装で実行する（ロードマップ段階1の完了条件）。
class BoundaryTest < Minitest::Test
  T = { "bool" => true }.freeze
  F = { "bool" => false }.freeze
  E = Models.overflowing.freeze

  def states_of(result)
    result["steps"].map { |s| s["state"].values.first }
  end

  def test_tickets_is_verified
    r = reference(Models.tickets).check(max_states: 10_000)
    assert_equal "verified", r["status"]
    assert_equal [[0], [1], [2], [3]], r["certificate"]
  end

  def test_removing_the_purchase_guard_gives_the_shortest_counterexample
    r = reference(Models.tickets_without_guard).check
    assert_equal "violated", r["status"]
    assert_equal({ "violation" => "invariant", "name" => "capacity_respected" }, r["property"])
    assert_equal [{ "quantity" => 2 }, { "quantity" => 2 }], r["steps"].map { |s| s["args"] }
    assert_equal [2, 4], states_of(r)
  end

  def test_updating_to_a_constant_out_of_range_is_an_error
    ir = Models.tickets
    ir["actions"][0]["updates"][0]["expr"] = { "int" => 5 }
    r = reference(ir).check
    assert_equal "error", r["status"]
    assert_empty r["steps"]
    assert_equal "update", r["property"]["site"]
    assert_equal({ "kind" => "out_of_range", "value" => 5, "type" => { "int" => { "min" => 0, "max" => 4 } } },
                 r["property"]["error"])
  end

  def test_a_violating_initial_state_is_a_zero_step_counterexample
    ir = Models.tickets
    ir["states"][0]["initial"] = { "int" => 4 }
    r = reference(ir).check
    assert_equal "violated", r["status"]
    assert_empty r["steps"]
  end

  def test_a_contract_violation_keeps_the_internal_choice_and_output
    m = reference(Models.responder)
    r = m.check
    assert_equal "violated", r["status"]
    assert_equal({ "violation" => "contract", "name" => "succeeds" }, r["property"])
    assert_equal 1, r["steps"].length
    assert_equal({ "allowed" => false }, r["steps"][0]["choices"])
    assert_equal({ "value" => "forbidden" }, r["steps"][0]["output"])
    assert_equal "contract_not_held", m.reject_certificate([[0]])
  end

  def test_a_stuck_initial_state_is_a_deadlock_unless_terminal
    ir = Models.counter(0, [])
    r = reference(ir).check(deadlock: true)
    assert_equal "violated", r["status"]
    assert_equal({ "violation" => "deadlock" }, r["property"])
    assert_empty r["steps"]
    assert_equal "verified", reference(ir.merge("terminal" => T)).check(deadlock: true)["status"]
  end

  def test_max_states_one
    r = reference(Models.counter(1, [Models.stay])).check(max_states: 1)
    assert_equal ["verified", 1], [r["status"], r["visited_states"]]
    r = reference(Models.counter(1, [Models.stay, Models.go("go", 0, 1)])).check(max_states: 1)
    assert_equal ["inconclusive", "max_states", 1], [r["status"], r["reason"], r["visited_states"]]
  end

  def test_a_certificate_may_be_a_superset_of_the_reachable_states
    m = reference(Models.counter(1, [Models.stay]))
    assert_nil m.reject_certificate([[0], [1]])
    assert_equal 1, m.check["visited_states"]
  end

  def test_certificates_missing_states_are_rejected
    m = reference(Models.counter(1, [Models.go("go", 0, 1)]))
    assert_equal "missing_initial", m.reject_certificate([[1]])
    assert_equal "missing_successor", m.reject_certificate([[0]])
    assert_nil m.reject_certificate([[0], [1]])
  end

  def status(invariant)
    reference(Models.big(invariant)).check["status"]
  end

  def test_ite_evaluates_only_the_chosen_branch
    assert_equal "verified", status({ "ite" => [F, E, T] })
    assert_equal "error", status({ "ite" => [T, E, T] })
  end

  def test_all_any_implies_stop_at_the_deciding_operand
    assert_equal "violated", status({ "all" => [F, E] })
    assert_equal "verified", status({ "any" => [T, E] })
    assert_equal "verified", status({ "implies" => [F, E] })
  end

  def test_all_any_implies_evaluate_the_rest_otherwise
    assert_equal "error", status({ "all" => [T, E] })
    assert_equal "error", status({ "any" => [F, E] })
    assert_equal "error", status({ "implies" => [T, E] })
  end

  def test_updates_are_not_evaluated_when_the_guard_is_false
    bump = lambda do |guard|
      Models.big({ "ge" => [{ "var" => 0 }, { "int" => 0 }] }).merge(
        "actions" => [{ "name" => "bump", "guard" => { "bool" => guard },
                        "updates" => [{ "target" => 0, "expr" => { "add" => [{ "var" => 0 }, { "int" => 1 }] } }] }]
      )
    end
    assert_equal "verified", reference(bump.(false)).check["status"]
    r = reference(bump.(true)).check
    assert_equal "error", r["status"]
    assert_equal ["update", { "kind" => "overflow" }], [r["property"]["site"], r["property"]["error"]]
  end
end
