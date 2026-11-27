# frozen_string_literal: true

$LOAD_PATH.unshift(File.expand_path("../lib", __dir__))
require "minitest/autorun"
require "json"
require "fmspec/dsl"
require_relative "../reference/fmspec_reference"
require_relative "support/concrete_dsl"
require_relative "support/dsl_generator"
require "tmpdir"

# DSL が生成した IR が、仕様のブロックを Ruby の値で実行したときの意味と一致することを確かめる。
#
# 同じブロックを、Fmspec.define（記号式で IR を組み立てる）と ConcreteDsl（具体的な値で実行し直す。
# test/support/concrete_dsl.rb）の両方に渡す。IR は参照実装（reference/fmspec_reference.rb）で評価する。
# どちらも Fmspec の Expr と Builder を使わない。
#
# 初期状態と、ランダムな状態と引数のそれぞれで、次を比べる。
#
# - 状態変数の名前と型、操作の名前と引数、不変条件と遷移契約の名前
# - 初期状態の集合
# - 不変条件と終端条件の結果（真、偽、評価エラーの種類）
# - 操作の結果（無効、有効なら遷移先と出力と遷移契約の結果、評価エラー）
#
# 評価エラーは、IR が報告した最初の失敗（箇所、状態変数、種類）が、具体的な実行で失敗した箇所の1つであることを確かめる。
# どの更新から先に評価するかは IR の組み立て方の選択で、利用者の書いた仕様の意味ではないからである。
#
#   FMSPEC_DSL_SAMPLES  モデルごとに調べる状態の数（既定は60）
#   FMSPEC_DSL_FUZZ     ランダムに生成する仕様の数（既定は300）
#   FMSPEC_SEED         乱数の種（既定は1）
class DslConcreteTest < Minitest::Test
  SAMPLES = Integer(ENV.fetch("FMSPEC_DSL_SAMPLES", "60"))
  SEED = Integer(ENV.fetch("FMSPEC_SEED", "1"))
  FUZZ = Integer(ENV.fetch("FMSPEC_DSL_FUZZ", "300"))
  ARGS_PER_STATE = 6
  # 生成した仕様のブロック。生成したソースのファイルが、ここに登録する。
  GENERATED = {}
  T = ConcreteDsl::T

  # ---- 比較 ----

  def random_value(type, rng)
    case type
    when T::Int
      pick = [type.min, type.max, type.min + 1, type.max - 1].select { |v| v.between?(type.min, type.max) }
      rng.rand < 0.3 ? pick.sample(random: rng) : rng.rand(type.min..type.max)
    when T::Bool then rng.rand < 0.5
    when T::Enum then type.labels.sample(random: rng)
    when T::Tuple then type.items.map { |t| random_value(t, rng) }
    when T::Record then type.fields.transform_values { |t| random_value(t, rng) }
    when T::Option then rng.rand < 0.3 ? nil : ConcreteDsl::Some.new(random_value(type.inner, rng))
    when T::SetOf then type.elem.values.select { rng.rand < 0.4 }.to_set
    when T::MapOf then type.key.values.select { rng.rand < 0.4 }.to_h { |k| [k, random_value(type.value, rng)] }
    when T::ListOf then Array.new(rng.rand(0..type.max)) { random_value(type.elem, rng) }
    end
  end

  def invariant_result(ref, state, name)
    found = ref.failing_invariant(state, { invariants: [name] })
    return "true" unless found

    found[1] == false ? "false" : found[1].detail["kind"]
  end

  def contract_result(ref, action, state, transition, name)
    found = ref.failing_contract(action, state, transition, { contracts: [name] })
    return "true" unless found

    found[1] == false ? "false" : found[1].detail["kind"]
  end

  def compare(label, block, seed: SEED)
    ir = Fmspec.define(label, &block).to_ir
    ref = FmspecReference::Model.new(ir)
    cm = ConcreteDsl.define(&block)
    rng = Random.new(seed)
    enums = cm.enums
    types = ir["states"].map { |s| T.from_ir(s["type"], enums) }
    context = ->(extra = "") { "#{label}\n#{JSON.generate(ir)}\n#{extra}" }

    # 宣言
    assert_equal ir["states"].map { |s| s["name"] }, cm.states.map { |s| s[:name].to_s }, context.()
    assert_equal ir["states"].map { |s| s["type"] }, cm.states.map { |s| s[:type].to_ir }, context.()
    assert_equal ir["actions"].map { |a| a["name"] }, cm.actions.map(&:name), context.()
    ir["actions"].zip(cm.actions).each do |a, ca|
      assert_equal a["params"].map { |p| p["name"] }, ca.params.keys.map(&:to_s), context.()
      a["params"].zip(ca.params.values).each do |p, spec|
        assert_equal p["type"], T.coerce(spec).to_ir, context.() unless spec.is_a?(Proc)
      end
    end
    assert_equal((ir["invariants"] || []).map { |i| i["name"] }, cm.invariants.map(&:first), context.())
    assert_equal ir.key?("terminal"), !cm.terminal_block.nil?, context.()

    # 初期状態
    json_row = ->(row) { types.zip(row).map { |t, v| t.to_json(v) } }
    ref_initial = ref.initials.map { |st| ir["states"].each_with_index.map { |s, i| ref.json_value(s["type"], st[i]) } }
    cm_initial = cm.initial_states.map(&json_row)
    assert_equal ref_initial.sort_by(&:to_s), cm_initial.sort_by(&:to_s), context.("初期状態")

    rows = cm.initial_states + Array.new(SAMPLES) { types.map { |t| random_value(t, rng) } }
    checked = Hash.new(0)
    rows.each do |row|
      json = json_row.(row)
      state = ref.state_from_json(json)
      at = ->(extra) { context.("状態 #{JSON.generate(json)}\n#{extra}") }

      cm.invariants.each do |name, inv|
        assert_equal invariant_result(ref, state, name), cm.evaluate(inv, row), at.("不変条件 #{name}")
      end
      if cm.terminal_block
        expected = begin
          ref.terminal?(state) ? "true" : "false"
        rescue FmspecReference::EvalError => e
          e.detail["kind"]
        end
        assert_equal expected, cm.evaluate(cm.terminal_block, row), at.("終端条件")
      end

      ir["actions"].zip(cm.actions).each do |action, ca|
        bindings = (action["params"] || []) + (action["choices"] || [])
        btypes = bindings.map { |b| T.from_ir(b["type"], enums) }
        n_params = (action["params"] || []).length
        ARGS_PER_STATE.times do
          values = btypes.map { |t| random_value(t, rng) }
          bjson = btypes.zip(values).map { |t, v| t.to_json(v) }
          refs = bindings.zip(bjson).map { |b, j| ref.from_json(b["type"], j) }
          params = refs.take(n_params)
          choices = refs.drop(n_params)
          where = at.("操作 #{action['name']} 引数 #{JSON.generate(bjson)}")

          expected = begin
            step = ref.step(action, params, choices, state)
            step.nil? ? [:invalid] : [:ok, step]
          rescue FmspecReference::StepError => e
            [:error, [e.property["site"], e.property["target"] || "", e.property["error"]["kind"]]]
          end
          actual = ca.run(row, values.take(n_params), values.drop(n_params))
          assert_equal expected[0], actual[0], -> { "#{where}\nIR: #{expected.inspect}\n具体的な実行: #{actual.inspect}" }
          checked[expected[0]] += 1
          case expected[0]
          when :error
            assert_includes actual[1], expected[1], where
          when :ok
            nxt, out = expected[1]
            next_json = ir["states"].each_with_index.map { |s, i| ref.json_value(s["type"], nxt[i]) }
            assert_equal next_json, json_row.(actual[1]), where
            if action["output"]
              out_type = T.from_ir(action["output"]["type"], enums)
              assert_equal ref.json_value(action["output"]["type"], out), out_type.to_json(actual[2]), where
            end
            transition = { "params" => params, "choices" => choices, "state" => nxt, "output" => out }
            (ir["contracts"] || []).select { |c| c["action"] == action["name"] }.each do |c|
              assert_equal contract_result(ref, action, state, transition, c["name"]), actual[3].fetch(c["name"]),
                           "#{where}\n遷移契約 #{c['name']}"
            end
          end
        end
      end
    end
    checked
  end

  # ---- 仕様 ----

  SPECS = {
    tickets: proc do
      state :sold, int(0..4), initial: 0
      constant :capacity, 3

      action :purchase, quantity: 1..2 do |s, quantity|
        guard s.sold + quantity <= s.capacity
        update sold: s.sold + quantity
      end

      action :cancel do |s|
        guard s.sold > 0
        update sold: s.sold - 1
      end

      invariant(:capacity_respected) { |s| s.sold <= s.capacity }
    end,

    responder: proc do
      result = enum(:result, :success, :forbidden)
      state :x, int(0..0), initial: 0

      action :request, id: 7..7 do |_s, _id|
        allowed = choose(:allowed, bool)
        returns ite(allowed, :success, :forbidden), result
        ensures(:succeeds) { |_after, out| out.eq(:success) }
      end
    end,

    cancel: proc do
      order = enum(:order, :open, :cancelled)
      outcome = enum(:outcome, :success, :forbidden)
      state :owner, int(0..1), initial_in: 0..1
      state :order, order, initial: :open

      action :cancel, user: 0..1 do |s, user|
        accept_if s.owner.eq(user) & s.order.eq(:open)
        on_accept do
          update order: :cancelled
          returns :success
        end
        on_reject do
          unchanged
          returns :forbidden
        end
        ensures(:only_owner) { |after, out| out.eq(outcome[:success]).implies(after.order.eq(:cancelled)) }
      end
    end,

    basket: proc do
      item = enum(:item, :apple, :bread, :milk)
      state :items, set_of(item), initial: Set[]
      state :other, set_of(item), initial_in: [Set[], Set[:milk]]

      action :add, x: item do |s, x|
        guard s.items.include?(x).not_
        update items: s.items.add(x)
      end

      action :drop, x: ->(s) { s.items } do |s, x|
        update items: s.items.delete(x)
      end

      action :merge do |s|
        guard s.items.size < 3
        guard (s.items & s.other).empty?
        update items: s.items | s.other, other: s.items - s.other
      end

      invariant(:small) { |s| s.items.size <= 2 }
      invariant(:no_milk_alone) { |s| s.items.include?(:milk).implies(s.items.any? { |y| y.ne(:milk) }) }
      invariant(:other_within) { |s| s.other <= s.items }
      invariant(:items_within) { |s| s.items.subset?(s.other) }
      invariant(:sum) { |s| (s.items + s.other).size.eq(s.items.union(s.other).size) }
    end,

    seats: proc do
      user = enum(:user, :ann, :bob, :cat)
      seats = list_of(user, max: 2)
      state :waiting, set_of(user), initial: Set[:ann, :bob, :cat]
      state :seated, seats, initial: []

      action :seat, u: ->(s) { s.waiting } do |s, u|
        update waiting: s.waiting.delete(u), seated: s.seated.push(u)
      end

      action :swap, out: ->(s) { s.seated }, inn: ->(s, out) { s.waiting.delete(out) } do |s, out, inn|
        guard s.seated.size.eq(2)
        update seated: ite(s.seated[0].eq(out), seats.value([inn, s.seated[1]]), [s.seated[0], inn]),
               waiting: s.waiting.delete(inn).add(out)
      end

      action :leave do |s|
        update seated: s.seated.shift, waiting: s.waiting.add(s.seated.first)
      end

      action :pop do |s|
        guard s.seated.empty?.not_
        update seated: s.seated.pop, waiting: s.waiting.add(s.seated.last)
      end

      invariant(:disjoint) { |s| s.seated.all? { |u| s.waiting.include?(u).not_ } }
      invariant(:second) { |s| s.seated[1].ne(:cat) }
    end,

    shapes: proc do
      user = enum(:user, :ann, :bob)
      state :pos, record(x: int(0..2), y: int(0..2)), initial: { x: 0, y: 0 }
      state :holder, option(user), initial: nil
      state :pair, tuple(int(0..1), bool), initial: [0, false]
      state :credit, map_of(user, int(0..3)), initial: { ann: 1 }

      action :right do |s|
        update pos: { x: s.pos[:x] + 1, y: s.pos[:y] }
      end

      action :take, u: user do |s, u|
        guard s.holder.eq(nil)
        update holder: some(u), credit: s.credit.put(u, s.credit[u] + 1)
      end

      action :give do |s|
        guard s.holder.some?
        update holder: none(user), credit: s.credit.delete(s.holder.unwrap)
      end

      action :flip do |s|
        update pair: [1 - s.pair[0], s.pair[1].not_]
        returns s.pair[0] * 2, int(0..1)
      end

      action :grab, u: user do |s, u|
        update holder: some(u)
        returns s.credit.key?(u)
        ensures(:held) { |after, had| after.holder.eq(some(u)) & had.eq(s.credit.keys.include?(u)) }
      end

      invariant(:diag) { |s| s.pos[:x] >= s.pos[:y] }
      invariant(:holder_has_credit) { |s| s.holder.none? | s.credit.key?(s.holder.unwrap) }
      invariant(:credit_small) { |s| forall(s.credit) { |u| s.credit[u] < 3 } }
    end,

    arithmetic: proc do
      color = enum(:color, :red, :green)
      state :a, color, initial_in: color
      state :b, color, initial_in: color
      state :n, int(-3..3), initial_in: 0..1
      ghost :count, int(0..2), initial: 0
      constant :menu, set_of(color), Set[:red]
      initially { |s| s.a.ne(s.b) }

      action :step, d: -2..2 do |s, d|
        guard (s.n.ne(0)) & ((10 / s.n) > d)
        update n: (s.n * d) % 4 - 1, count: min(s.count + 1, 2)
      end

      action :neg do |s|
        update n: -s.n
        preserves :a, :b
      end

      action :div, d: -2..2 do |s, d|
        update n: let(s.n / d) { |q| max(q, -3) }
      end

      action :paint, c: color do |s, c|
        guard exists(color) { |k| k.eq(c) & s.menu.include?(k) }
        update a: c
      end

      invariant(:bounded) { |s| (s.n >= -3) & (s.n <= 3) }
      invariant(:let_eager) { |s| let(10 / s.n) { |_| true } }
      invariant(:forall_ints) { |s| forall(int(-1..1)) { |k| (s.n + k).ne(4) } }
      invariant(:any_all) { |s| any(s.a.eq(:red), 1 / s.n > 0) & all(s.count >= 0, implies(s.n > 0, s.n < 4)) }
      terminal { |s| s.count.eq(2) & (s.n % 2).eq(1) }
    end,

    failures: proc do
      bit = int(0..1)
      state :l, list_of(bit, max: 1), initial: [1]
      state :m, map_of(bit, bit), initial: { 0 => 1 }
      state :o, option(bit), initial: nil
      state :t, tuple(bit, bit), initial: [0, 0]

      action :at, i: -1..2 do |s, i|
        update t: [s.l[i], s.m[i]]
      end

      action :push, x: -1..2 do |s, x|
        update l: s.l.push(x), m: s.m.put(x, x + 1)
      end

      action :unwrap do |s|
        update t: [s.o.unwrap, 0], o: some(2)
      end

      action :empty do |s|
        update l: s.l.pop.pop
        returns s.l.first
      end

      action :set_out, x: -1..2 do |s, x|
        update m: s.m.put(0, x), t: [x, s.t[1] + 2]
      end

      invariant(:first) { |s| s.l.first.eq(1) }
      invariant(:missing) { |s| s.m[1].eq(0) }
    end
  }.freeze

  # DSL のソースをランダムに生成した仕様。記号ブロックは Lint がソースを読むので、ファイルに書いてから読み込む。
  def test_random_specs
    rejected = Hash.new(0)
    checked = Hash.new(0)
    Dir.mktmpdir("fmspec-dsl") do |dir|
      FUZZ.times do |n|
        seed = (SEED * 5_000_011) + n
        lines = DslGenerator.new(seed).model
        path = File.join(dir, "spec_#{seed}.rb")
        File.write(path, "DslConcreteTest::GENERATED[#{seed}] = proc do\n#{lines.map { |l| "  #{l}" }.join("\n")}\nend\n")
        load path
        begin
          Fmspec.define(:"g#{seed}", &GENERATED.fetch(seed))
        rescue Fmspec::BuildError => e
          rejected[e.message[0, 30]] += 1
          next
        end
        result = compare(:"g#{seed}", GENERATED.fetch(seed), seed: seed) rescue raise($!.class, "#{$!.message}\n#{File.read(path)}")
        result.each { |k, v| checked[k] += v }
      end
    end
    warn "DSL が拒否した仕様: #{rejected}\n結果の分布: #{checked}" if ENV["FMSPEC_DSL_VERBOSE"]
    # DSL が拒否した仕様を除いても、比べる仕様が十分に残り、どの結果も試していること。
    assert_operator rejected.values.sum, :<, FUZZ / 2, "DSL が拒否した仕様: #{rejected}"
    %i[ok invalid error].each { |k| assert_operator checked[k], :>, FUZZ, "結果の分布: #{checked}" }
  end

  SPECS.each do |name, block|
    define_method("test_#{name}") do
      checked = compare(name, block)
      assert_operator checked.values.sum, :>, 0
    end
  end
end
