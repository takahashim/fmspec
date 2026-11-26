# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require_relative "../reference/fmspec_reference"
require_relative "../reference/test/model_generator"

# 有界応答性（仕様書 §12.5）。有限モニタへの変換と、その意味。
class ResponseTest < Minitest::Test
  # ジョブを待ち行列に入れると、ワーカーが処理する。処理は2回まで失敗し、3回目は必ず成功する。
  def jobs(within, counting: [:work], on_terminal: :violation, terminal: true)
    Fmspec.define(:jobs) do
      state :queued, bool, initial: false
      state :tries, int(0..2), initial: 0
      state :done, bool, initial: false
      action :enqueue do |s|
        guard s.queued.not_ & s.done.not_
        update queued: true
      end
      action :work do |s|
        ok = choose(:ok, bool)
        guard s.queued & (ok | (s.tries < 2))
        update queued: ok.not_, done: ok, tries: ite(ok, s.tries, s.tries + 1)
      end
      # 時間だけが進む。
      action :tick do |s|
        guard s.done.not_
        unchanged
      end
      terminal { |s| s.done } if terminal
      responds(:processed, within: within, counting: counting, on_terminal: on_terminal) do
        trigger :enqueue
        response { |s| s.done }
      end
    end
  end

  def test_the_deadline_counts_only_the_counted_steps
    # 3回目の work で必ず処理するので、work で数えれば期限3で成り立ち、期限2では破れる。
    assert jobs(3).check.verified?
    late = jobs(2).check
    assert_equal :violated, late.status
    assert_equal "processed", late.property["name"]
    # 3回目の work で処理しても、期限2には遅い。
    assert_equal %i[enqueue work work work], late.trace.steps.map(&:action)
    assert_equal [3, true], late.trace.states.last.values_at("processed.elapsed", "done")

    # tick も数えると、tick が続くだけで期限を過ぎる。
    all = jobs(3, counting: nil).check
    assert_equal :violated, all.status
    assert_equal 5, all.trace.length
  end

  def test_the_monitor_is_a_state_variable_and_an_invariant
    ir = jobs(3).to_ir
    monitor = ir["states"].last
    assert_equal "processed.elapsed", monitor["name"]
    assert_equal({ "int" => { "min" => -1, "max" => 4 } }, monitor["type"])
    assert_equal "processed", ir["invariants"].last["name"]
    # どの操作も、最後にモニタを更新する。元の guard は変えない。
    assert(ir["actions"].all? { |a| a["updates"].last["target"] == 3 })
    assert_equal jobs(3).to_ir["actions"].map { |a| a["guard"] }, ir["actions"].map { |a| a["guard"] }
  end

  # 要求に応えずに止まることがある。
  def stop(on_terminal)
    Fmspec.define(:stop) do
      state :requested, bool, initial: false
      state :stopped, bool, initial: false
      action :request do |s|
        guard s.requested.not_ & s.stopped.not_
        update requested: true
      end
      action :answer do |s|
        guard s.requested & s.stopped.not_
        update requested: false
      end
      action :halt do |s|
        guard s.stopped.not_
        update stopped: true
      end
      terminal { |s| s.stopped }
      responds(:answered, within: 5, on_terminal: on_terminal) do
        trigger { |s| s.requested }
        response { |s| s.requested.not_ }
      end
    end
  end

  def test_obligations_left_at_a_terminal_state
    left = stop(:violation).check
    assert_equal :violated, left.status
    assert_equal %i[request halt], left.trace.steps.map(&:action)
    # :allowed なら、終端状態に残った義務は違反にしない。期限は、終端状態の前に来ない。
    assert stop(:allowed).check.verified?
  end

  def test_within_zero_needs_the_response_at_the_trigger
    model = Fmspec.define(:zero) do
      state :x, int(0..2), initial: 0
      action(:inc) do |s|
        guard s.x < 2
        update x: s.x + 1
      end
      responds(:immediate, within: 0) do
        trigger { |s| s.x.eq(1) }
        response { |s| s.x >= 1 }
      end
      responds(:next_step, within: 0) do
        trigger { |s| s.x.eq(1) }
        response { |s| s.x.eq(2) }
      end
    end
    assert model.check(invariants: [:immediate]).verified?
    late = model.check(invariants: [:next_step])
    assert_equal :violated, late.status
    assert_equal 2, late.trace.length
  end

  def test_invalid_definitions_are_rejected
    errors = {
      /trigger が必要/ => proc { responds(:r, within: 1) { response { |s| s.x.eq(0) } } },
      /response が必要/ => proc { responds(:r, within: 1) { trigger { |s| s.x.eq(0) } } },
      /within: は0以上の整数/ => proc { responds(:r, within: -1) { nil } },
      /on_terminal:/ => proc { responds(:r, within: 1, on_terminal: :ignore) { nil } },
      /未定義の操作です: missing/ => proc {
        responds(:r, within: 1) do
          trigger :missing
          response { |s| s.x.eq(0) }
        end
      },
      /trigger は1つだけ/ => proc {
        responds(:r, within: 1) do
          trigger { |s| s.x.eq(0) }
          trigger { |s| s.x.eq(1) }
        end
      },
      /不変条件 r は/ => proc {
        invariant(:r) { |s| s.x.eq(0) }
        responds(:r, within: 1) { nil }
      }
    }
    errors.each do |message, block|
      error = assert_raises(Fmspec::BuildError) do
        Fmspec.define(:bad) do
          state :x, int(0..1), initial: 0
          action(:a) { |_s| unchanged }
          instance_eval(&block)
        end
      end
      assert_match message, error.message
    end
  end

  # ---- 変換の意味の検査 ----
  #
  # 参照実装（reference/fmspec_reference.rb）の上で、有界応答性を定義どおりに検査する。
  # モニタと違い、果たされていない義務をすべて、それぞれの経過とともに持つ。
  # 元のモデルの状態と義務の経過の集合を幅優先でたどり、違反に至る最短の長さを返す。違反がなければ nil。
  def literal_violation(ir, spec)
    model = FmspecReference::Model.new(ir)
    env = ->(state) { FmspecReference::Env.new(state, nil, nil, nil, nil) }
    happens = lambda do |part, state, action|
      (action && part[:actions].include?(action["name"])) || (part[:expr] && model.prop(part[:expr], env.call(state)))
    end
    late = ->(state, pending) { spec.on_terminal == :violation && !pending.empty? && model.terminal?(state) }
    frontier = model.initials.map do |s|
      [s, happens.call(spec.trigger, s, nil) && !happens.call(spec.response, s, nil) ? [0] : []]
    end
    return 0 if frontier.any? { |s, pending| late.call(s, pending) }

    seen = frontier.to_set
    depth = 0
    until frontier.empty?
      depth += 1
      frontier = frontier.flat_map do |state, pending|
        ir["actions"].flat_map do |action|
          counted = spec.counting.nil? || spec.counting.include?(action["name"]) ? 1 : 0
          model.transitions(action, state).map do |t|
            after = t["state"]
            responded = happens.call(spec.response, after, action)
            aged = pending.map { |age| age + counted }
            return depth if aged.any? { |age| age > spec.within }

            left = responded ? [] : aged
            left |= [0] if happens.call(spec.trigger, after, action) && !responded
            return depth if late.call(after, left)

            [after, left.sort]
          end
        end
      end.uniq.reject { |node| seen.include?(node) }
      seen.merge(frontier)
    end
    nil
  end

  # 生成したモデルの状態変数についての、ランダムな状態述語。
  def predicate(rng, ir)
    candidates = ir["states"].each_index.filter_map do |i|
      type = ir["states"][i]["type"]
      if type.key?("int")
        range = type["int"]
        { %w[le ge eq ne].sample(random: rng) => [{ "var" => i }, { "int" => rng.rand(range["min"]..range["max"]) }] }
      elsif type.key?("bool")
        rng.rand < 0.5 ? { "var" => i } : { "not" => [{ "var" => i }] }
      end
    end
    candidates.empty? ? { "bool" => rng.rand < 0.5 } : candidates.sample(random: rng)
  end

  def part(rng, ir, names)
    actions = names.select { rng.rand < 0.3 }
    { actions: actions, expr: actions.empty? || rng.rand < 0.5 ? predicate(rng, ir) : nil }
  end

  def test_the_monitor_agrees_with_the_literal_definition
    compared = 0
    violated = 0
    300.times do |seed|
      ir = ModelGenerator.new(seed).model
      reference = FmspecReference::Model.new(ir)
      original = reference.check
      # 元のモデルに評価エラーのあるものは、比べる対象にしない。
      original = reference.check(invariants: []) if original["status"] == "violated"
      next unless original["status"] == "verified"

      rng = Random.new(seed)
      names = ir["actions"].map { |a| a["name"] }
      spec = Fmspec::Response::Spec.new(
        name: "bounded", trigger: part(rng, ir, names), response: part(rng, ir, names), within: rng.rand(0..2),
        counting: rng.rand < 0.5 ? nil : names.select { rng.rand < 0.6 }, on_terminal: %i[violation allowed].sample(random: rng)
      )
      expanded = Fmspec::Response.expand(ir, [spec])
      result = Fmspec::Model.new(:expanded, expanded).check(invariants: ["bounded"])
      expected = literal_violation(ir, spec)
      message = "seed #{seed}: #{spec.to_h}"
      if expected
        assert_equal :violated, result.status, message
        assert_equal expected, result.trace.length, message
        violated += 1
      else
        assert_equal :verified, result.status, message
      end

      # モニタは元の遷移を制限しない。元の状態変数の到達可能な値は、変換の前後で同じである。
      projected = FmspecReference::Model.new(expanded).check(invariants: [])["certificate"].map { |row| row[0...ir["states"].length] }
      assert_equal original["certificate"].sort_by(&:to_s), projected.uniq.sort_by(&:to_s), message
      compared += 1
    end
    assert_operator compared, :>=, 100
    assert_operator violated, :>=, 20
    assert_operator compared - violated, :>=, 20
  end
end
