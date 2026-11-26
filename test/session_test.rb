# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require_relative "../reference/fmspec_reference"
require_relative "../reference/test/model_generator"

# 非決定性と部分観測のもとでの適合性判定（仕様書 §12.2、§17.2.1）。
class SessionTest < Minitest::Test
  # start を1回実行すると、同じ戻り値と観測値を持つ候補 A・B に分岐する。
  # A では approve だけ、B では cancel だけが有効。phase は観測できない。
  def workflow(ping: false, reveal: false)
    Fmspec.define(:workflow) do
      enum(:phase, :init, :a, :b)
      state :phase, enum(:phase, :init, :a, :b), initial: :init
      state :started, bool, initial: false
      state :shown, bool, initial: false

      action :start do |s|
        guard s.phase.eq(:init)
        to_a = choose(:to_a, bool)
        update phase: ite(to_a, :a, :b), started: true
      end

      action :approve do |s|
        guard s.phase.eq(:a)
        unchanged
      end

      action :cancel do |s|
        guard s.phase.eq(:b)
        unchanged
      end

      # 両候補に共通の自己ループ。
      (action(:ping) { |s| guard s.phase.ne(:init) }) if ping

      # phase を観測できる値に写す。
      (action(:reveal) { |s| guard s.phase.ne(:init); update shown: s.phase.eq(:a) }) if reveal
    end
  end

  # 実装。start で A に入る。calls に、呼ばれた command を記録する。
  class Workflow
    attr_reader :started, :shown

    def initialize(calls, start_sets_flag: true)
      @calls = calls
      @started = false
      @shown = false
      @start_sets_flag = start_sets_flag
    end

    def call(name)
      @calls << name
      @started = @start_sets_flag if name == :start
      @shown = true if name == :reveal
      nil
    end
  end

  def binding_for(model, calls, **options)
    names = model.to_ir["actions"].map { |a| a["name"].to_sym }
    model.bind do
      setup { Workflow.new(calls, **options) }
      names.each { |name| command(name) { |w| w.call(name) } }
      observe(:started, method: :started)
      observe(:shown, method: :shown)
    end
  end

  def test_no_common_input_ends_the_case_as_inconclusive
    calls = []
    model = workflow
    result = model.test(binding_for(model, calls), cases: 1, steps: 2, seed: 1)
    assert_equal [:inconclusive, :no_common_input], [result.status, result.reason]
    # 照合済み1ステップ。2回目の command は呼ばれない。
    assert_equal 1, result.matched_steps
    assert_equal [:start], calls
    # 未完了のケースを含む実行は、成功として扱わない。
    refute_predicate result, :passed?
    assert_raises(Fmspec::TestFailed) { result.assert_passed! }
    assert_match(/\AInconclusive: workflow（no_common_input）/, result.to_s)
  end

  def test_an_observation_matching_no_candidate_is_a_conformance_failure
    calls = []
    model = workflow
    result = model.test(binding_for(model, calls, start_sets_flag: false), cases: 1, steps: 2, seed: 1)
    assert_equal :conformance_failure, result.status
    assert_equal [[:start, {}]], result.inputs
    assert_equal ["started"], result.detail["mismatch"]
    assert_equal 1, result.detail["step"]
  end

  def test_a_common_input_keeps_both_candidates
    calls = []
    model = workflow(ping: true)
    result = model.test(binding_for(model, calls), cases: 1, steps: 2, seed: 1)
    assert_equal [:passed, 2], [result.status, result.matched_steps]
    assert_equal %i[start ping], calls
  end

  # ---- セッションを直接使う ----

  def session(model, **options)
    native = Fmspec::Native::Model.load(model.to_json)
    Fmspec::Native::Session.start(native, JSON.generate({ "observe" => %w[started shown] }.merge(options)))
  end

  def ask(json) = JSON.parse(json)

  def observe(session, action, started:, shown: false)
    ask(session.observe(JSON.generate("action" => action, "args" => {}, "observation" => { "started" => started, "shown" => shown })))
  end

  def phases(session) = ask(session.candidates).map { |s| s["phase"] }

  def test_candidates_are_kept_until_an_observation_tells_them_apart
    s = session(workflow(ping: true, reveal: true))
    assert_equal({ "status" => "continue", "candidates" => 1, "matched" => 0 },
                 ask(s.initial('{"started": false, "shown": false}')))
    assert_equal({ "status" => "input", "action" => "start", "args" => {} }, ask(s.next_input))
    assert_equal 2, observe(s, "start", started: true)["candidates"]
    assert_equal %w[a b], phases(s)
    # 候補を任意に1つへ絞らない。共通の操作のあとも、両方が残る。
    assert_equal 2, observe(s, "ping", started: true)["candidates"]
    assert_equal %w[a b], phases(s)
    # 片方の候補でしか有効でない入力は、全候補で有効な入力ではない。
    assert_equal "invalid", ask(s.check_input('{"action": "approve", "args": {}}'))["status"]
    assert_equal "valid", ask(s.check_input('{"action": "reveal", "args": {}}'))["status"]
    assert_equal "invalid_input", observe(s, "approve", started: true)["status"]
    # 観測が候補を区別すれば、一致する候補だけが残る。
    assert_equal({ "status" => "continue", "candidates" => 1, "matched" => 3 }, observe(s, "reveal", started: true, shown: true))
    assert_equal %w[a], phases(s)
    assert_equal "valid", ask(s.check_input('{"action": "approve", "args": {}}'))["status"]
  end

  def test_an_empty_candidate_set_reports_what_the_model_allows
    s = session(workflow(reveal: true))
    s.initial('{"started": false, "shown": false}')
    observe(s, "start", started: true)
    # reveal のあと started が偽になることは、どの候補でも起きない。
    answer = observe(s, "reveal", started: false, shown: true)
    assert_equal ["conformance_failure", 2, 2, ["started"]], answer.values_at("status", "step", "candidates", "mismatch")
    assert_equal [{ "state" => { "started" => true, "shown" => true } }, { "state" => { "started" => true, "shown" => false } }].sort_by(&:to_s),
                 answer["expected"].sort_by(&:to_s)
  end

  def test_the_initial_observation_is_compared_too
    s = session(workflow)
    answer = ask(s.initial('{"started": true, "shown": false}'))
    assert_equal ["conformance_failure", 0, ["started"]], answer.values_at("status", "step", "mismatch")
  end

  def test_too_many_candidates_is_inconclusive
    s = session(workflow, "max_candidates" => 1)
    s.initial('{"started": false, "shown": false}')
    assert_equal %w[inconclusive max_candidates], observe(s, "start", started: true).values_at("status", "reason")
  end

  def test_session_arguments_are_checked
    native = Fmspec::Native::Model.load(workflow.to_json)
    assert_match(/未定義の状態変数/, ask(Fmspec::Native::Session.start(native, '{"observe": ["missing"]}'))["message"])
    assert_raises(TypeError) { Fmspec::Native::Session.start(Object.new, "{}") }
    assert_raises(NoMethodError, TypeError) { Fmspec::Native::Session.new }
    s = session(workflow)
    assert_equal "usage_error", ask(s.next_input)["status"]
    assert_equal "usage_error", ask(s.initial('{"started": false}'))["status"]
    s.initial('{"started": false, "shown": false}')
    assert_equal "usage_error", ask(s.observe('{"action": "launch", "args": {}, "observation": {}}'))["status"]
  end

  def test_a_model_error_is_not_a_conformance_failure
    model = Fmspec.define(:overflowing) do
      state :n, int(0..3), initial: 3
      action(:bump) { |s| update n: s.n + 1 }
    end
    binding = model.bind do
      setup { Object.new }
      command(:bump) { |_c| flunk "モデルの評価エラーのある入力は、実装に適用しない" }
      observe(:n) { |_c| 3 }
    end
    result = model.test(binding, cases: 1, steps: 1, seed: 1)
    assert_equal :model_error, result.status
    assert_equal ["update", "n", 4], result.detail["property"].values_at("site", "target").push(result.detail.dig("property", "error", "value"))
  end

  def test_a_model_violation_is_not_a_conformance_failure
    model = Fmspec.define(:unsafe) do
      state :n, int(0..3), initial: 0
      action(:bump) { |s| update n: s.n + 1 }
      invariant(:small) { |s| s.n < 2 }
    end
    count = 0
    binding = model.bind do
      setup { count = 0 }
      command(:bump) { |_c| count += 1 }
      observe(:n) { |_c| count }
    end
    result = model.test(binding, cases: 1, steps: 5, seed: 1)
    # 実装は仕様どおりに動いているが、仕様のほうが自分の不変条件を破る。
    assert_equal :model_violation, result.status
    assert_equal({ "violation" => "invariant", "name" => "small" }, result.detail["property"])
    assert_equal 2, result.steps.length
    assert_match(/\AModel violation: unsafe \/ small\n/, result.to_s)
  end

  # ---- 参照実装との比較 ----

  # 内部選択で進むかどうかが決まるカウンタのモデル。観測しない変数があると、候補が複数残る。
  def nondeterministic_ir(rng)
    vars = Array.new(2 + rng.rand(2)) { |i| { "id" => i, "name" => "v#{i}", "type" => { "int" => { "min" => 0, "max" => 3 } }, "initial" => { "int" => 0 } } }
    actions = vars.each_index.map do |i|
      moved = { "add" => [{ "var" => i }, { "int" => 1 }] }
      action = { "name" => "nudge#{i}", "params" => [], "choices" => [{ "name" => "go", "type" => { "bool" => {} } }],
                 "guard" => { "lt" => [{ "var" => i }, { "int" => 3 }] },
                 "updates" => [{ "target" => i, "expr" => { "ite" => [{ "choice" => 0 }, moved, { "var" => i }] } }] }
      # ときどき、進んだかどうかを戻り値で知らせる。
      action["output"] = { "type" => { "bool" => {} }, "expr" => { "choice" => 0 } } if rng.rand < 0.3
      action
    end
    actions << { "name" => "reset", "params" => [{ "name" => "which", "type" => { "int" => { "min" => 0, "max" => vars.length - 1 } } }],
                 "choices" => [], "guard" => { "gt" => [{ "var" => 0 }, { "int" => 1 }] },
                 "updates" => [{ "target" => 0, "expr" => { "param" => 0 } }] }
    { "ir_version" => 1, "name" => "nudges", "states" => vars, "actions" => actions }
  end

  # ランダムなモデルで、隠れた真の状態を参照実装で進めながら、候補集合を突き合わせる。
  def test_candidate_sets_agree_with_the_reference_implementation
    compared = 0
    kept_several = 0
    200.times do |n|
      seed = 9_000_000 + n
      rng = Random.new(seed)
      ir = n.even? ? ModelGenerator.new(seed).model : nondeterministic_ir(rng)
      ir["contracts"] = []
      ir["invariants"] = []
      reference = FmspecReference::Model.new(ir)
      cond = reference.conditions
      names = ir["states"].map { |s| s["name"] }
      observed = (0...names.length).select { rng.rand < 0.5 }
      project = ->(state) { observed.to_h { |i| [names[i], reference.json_value(state[i])] } }
      native = Fmspec::Native::Model.load(JSON.generate(ir))
      session = Fmspec::Native::Session.start(native, JSON.generate("seed" => seed, "observe" => observed.map { |i| names[i] }))
      truth = reference.initial
      candidates = [truth]
      assert_equal "continue", ask(session.initial(JSON.generate(project.(truth))))["status"]

      6.times do
        context = -> { "seed #{seed}\n#{JSON.generate(ir)}\ncandidates: #{candidates.inspect}" }
        expected_inputs = begin
          reference.common_inputs(candidates, cond)
        rescue FmspecReference::StepError
          assert_equal "model_error", ask(session.next_input)["status"], context
          break
        end
        answer = ask(session.next_input)
        if expected_inputs.empty?
          any = candidates.any? { |s| !reference.enabled_inputs(s, cond).empty? }
          assert_equal (any ? "inconclusive" : "end"), answer["status"], context
          break
        end
        assert_equal "input", answer["status"], context
        action = reference.action_named(answer["action"])
        params = (action["params"] || []).map do |p|
          v = answer["args"].fetch(p["name"])
          p["type"].key?("enum") ? FmspecReference::EnumValue.new(p["type"]["enum"], v) : v
        end
        assert_includes expected_inputs, [action["name"], params], context

        # 真の状態から、モデルが許す遷移を1つ選んで、実装の応答とする。
        chosen = reference.transitions(action, truth).select { |t| t["params"] == params }.sample(random: rng)
        truth = chosen["state"]
        candidates = reference.next_candidates(candidates, action["name"], params, chosen["output"], observed,
                                               observed.map { |i| truth[i] })
        report = { "action" => action["name"], "args" => answer["args"], "output" => reference.json_value(chosen["output"]),
                   "observation" => project.(truth) }
        observed_answer = ask(session.observe(JSON.generate(report)))
        assert_equal ["continue", candidates.length], observed_answer.values_at("status", "candidates"), context
        assert_equal reference.sort_states(candidates).map { |s| reference.json_state(s) }, ask(session.candidates), context
        compared += 1
        kept_several += 1 if candidates.length > 1
      end
    end
    assert_operator compared, :>, 400
    assert_operator kept_several, :>, 100, "複数の候補が残る場合を、ほとんど試していない"
  end
end
