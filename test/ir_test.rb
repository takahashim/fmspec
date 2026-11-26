# frozen_string_literal: true

require_relative "test_helper"
require "fmspec/dsl"
require_relative "../reference/fmspec_reference"

# DSL からIRへの変換（仕様書 §14.3、§16 段階4）。
# native extension を使わない。生成したIRを期待するIRと比べ、さらに参照実装で実行して意味を確かめる。
class IrTest < Minitest::Test
  def reference(model)
    FmspecReference::Model.new(JSON.parse(model.to_json))
  end

  def test_the_tickets_example_becomes_the_documented_ir
    expected = JSON.parse(File.read(File.join(ROOT, "examples/models/tickets.json")))
    actual = without_sources(JSON.parse(TestModels.tickets.to_json))
    # 例のIRは省略できるキーを省いている。DSL は常に書く。
    expected["enums"] = []
    expected["contracts"] = []
    expected["actions"][1].merge!("params" => [], "choices" => [])
    assert_equal expected["states"], actual["states"]
    assert_equal expected["actions"].map { |a| a.except("guard", "updates") }, actual["actions"].map { |a| a.except("guard", "updates") }
    assert_equal expected["invariants"], actual["invariants"]
    assert_equal expected.keys.sort, actual.keys.sort
    purchase = actual["actions"][0]
    # 定数は、参照した位置でリテラルになる。
    assert_equal({ "le" => [{ "add" => [{ "var" => 0 }, { "param" => 0 }] }, { "int" => 3 }] }, purchase["guard"])
    assert_equal [{ "target" => 0, "expr" => { "add" => [{ "var" => 0 }, { "param" => 0 }] } }], purchase["updates"]
    assert_equal expected["actions"][1]["guard"], actual["actions"][1]["guard"]
  end

  def test_definitions_record_their_source_location
    ir = TestModels.tickets.to_ir
    models = File.expand_path("models.rb", __dir__)
    assert_equal models, ir["states"][0]["source"]["file"]
    assert_equal [models] * 3, (ir["actions"] + ir["invariants"]).map { |d| d["source"]["file"] }
    lines = (ir["actions"] + ir["invariants"]).map { |d| d["source"]["line"] }
    assert_equal lines.sort, lines
    assert_equal 3, lines.uniq.length
  end

  def test_choices_outputs_and_contracts
    ir = without_sources(TestModels.responder.to_ir)
    success = { "enum" => { "type" => "result", "variant" => "success" } }
    forbidden = { "enum" => { "type" => "result", "variant" => "forbidden" } }
    assert_equal [{ "name" => "result", "variants" => %w[success forbidden] }], ir["enums"]
    action = ir["actions"][0]
    assert_equal [{ "name" => "id", "type" => { "int" => { "min" => 7, "max" => 7 } } }], action["params"]
    assert_equal [{ "name" => "allowed", "type" => { "bool" => {} } }], action["choices"]
    assert_equal({ "bool" => true }, action["guard"])
    assert_equal({ "type" => { "enum" => "result" }, "expr" => { "ite" => [{ "choice" => 0 }, success, forbidden] } },
                 action["output"])
    assert_equal [{ "name" => "succeeds", "action" => "request", "expr" => { "eq" => [{ "output" => {} }, success] } }],
                 ir["contracts"]
  end

  def test_operators_build_the_matching_ir_nodes
    model = Fmspec.define(:ops) do
      color = enum(:color, :red, :green)
      state :n, int(-5..5), initial: 0
      state :on, bool, initial: false
      state :c, color, initial: :green
      invariant(:arith) { |s| (1 + s.n * 2 - -s.n) >= 0 }
      invariant(:logic) { |s| ((s.n < 1) & s.on) | s.on.not_ }
      invariant(:equal) { |s| s.c.eq(:red).implies(s.n.ne(3)) }
      invariant(:nary) { |s| all(s.on, any(s.on, s.n > 0), true) }
      invariant(:cond) { |s| ite(s.on, s.c, color[:red]).eq(s.c) }
    end
    n = { "var" => 0 }
    on = { "var" => 1 }
    c = { "var" => 2 }
    red = { "enum" => { "type" => "color", "variant" => "red" } }
    expected = [
      { "ge" => [{ "sub" => [{ "add" => [{ "int" => 1 }, { "mul" => [n, { "int" => 2 }] }] },
                             { "sub" => [{ "int" => 0 }, n] }] }, { "int" => 0 }] },
      { "any" => [{ "all" => [{ "lt" => [n, { "int" => 1 }] }, on] }, { "not" => [on] }] },
      { "implies" => [{ "eq" => [c, red] }, { "ne" => [n, { "int" => 3 }] }] },
      { "all" => [on, { "any" => [on, { "gt" => [n, { "int" => 0 }] }] }, { "bool" => true }] },
      { "eq" => [{ "ite" => [on, c, red] }, c] }
    ]
    assert_equal expected, model.to_ir["invariants"].map { |i| i["expr"] }
    assert_equal [{ "int" => 0 }, { "bool" => false }, { "enum" => { "type" => "color", "variant" => "green" } }],
                 model.to_ir["states"].map { |s| s["initial"] }
  end

  # 拒否を、同じ操作の条件分岐する更新と出力で表す（仕様書 §12.1）。
  def orders
    Fmspec.define(:orders) do
      status = enum(:status, :open, :cancelled)
      enum(:result, :success, :forbidden)
      state :owner, int(0..1), initial: 0
      state :order, status, initial: :open
      state :attempts, int(0..2), initial: 0

      action :cancel, user: 0..1 do |s, user|
        guard s.attempts < 2
        update attempts: s.attempts + 1
        accept_if s.owner.eq(user) & s.order.eq(:open)
        on_accept do
          update order: :cancelled
          returns :success
        end
        on_reject do
          unchanged
          returns :forbidden
        end
        preserves :owner
        ensures(:forbidden_changes_nothing) { |after, result| result.eq(:forbidden).implies(after.order.eq(s.order)) }
      end
    end
  end

  def test_accept_and_reject_become_conditional_updates_and_outputs
    ir = without_sources(orders.to_ir)
    action = ir["actions"][0]
    accepted = { "all" => [{ "eq" => [{ "var" => 0 }, { "param" => 0 }] },
                           { "eq" => [{ "var" => 1 }, { "enum" => { "type" => "status", "variant" => "open" } }] }] }
    label = ->(type, v) { { "enum" => { "type" => type, "variant" => v } } }
    assert_equal({ "lt" => [{ "var" => 2 }, { "int" => 2 }] }, action["guard"])
    assert_equal [
      { "target" => 2, "expr" => { "add" => [{ "var" => 2 }, { "int" => 1 }] } },
      { "target" => 1, "expr" => { "ite" => [accepted, label.("status", "cancelled"), { "var" => 1 }] } }
    ], action["updates"]
    assert_equal({ "type" => { "enum" => "result" },
                   "expr" => { "ite" => [accepted, label.("result", "success"), label.("result", "forbidden")] } },
                 action["output"])
    assert_equal %w[cancel_preserves_owner forbidden_changes_nothing], ir["contracts"].map { |c| c["name"] }
    assert_equal({ "eq" => [{ "next" => 0 }, { "var" => 0 }] }, ir["contracts"][0]["expr"])
  end

  def test_the_generated_ir_means_what_the_specification_says
    assert_equal "verified", reference(TestModels.tickets).check["status"]
    r = reference(TestModels.tickets(guarded: false)).check
    assert_equal ["violated", [2, 4]], [r["status"], r["steps"].map { |s| s["state"]["sold"] }]
    r = reference(TestModels.tickets(constant_update: 5)).check
    assert_equal ["error", 5], [r["status"], r["property"]["error"]["value"]]
    r = reference(TestModels.responder).check
    assert_equal ["violated", { "allowed" => false }, { "value" => "forbidden" }],
                 [r["status"], r["steps"][0]["choices"], r["steps"][0]["output"]]

    # 拒否は有効な遷移で、出力は forbidden、注文は変わらない。受理すると注文は cancelled になる。
    m = reference(orders)
    r = m.check
    assert_equal "verified", r["status"]
    open = FmspecReference::EnumValue.new("status", "open")
    cancel = orders.to_ir["actions"][0]
    outcomes = m.transitions(JSON.parse(JSON.generate(cancel)), [0, open, 0]).map do |t|
      [t["params"], t["state"][1].label, t["output"].label]
    end
    assert_equal [[[0], "cancelled", "success"], [[1], "open", "forbidden"]], outcomes
  end

  def test_models_are_immutable
    model = TestModels.tickets
    assert_predicate model.to_ir, :frozen?
    assert_raises(FrozenError) { model.to_ir["actions"][0]["guard"]["le"] = [] }
  end
end
