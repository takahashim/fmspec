# frozen_string_literal: true

# 比較テスト用の、小さな整形式モデルのランダム生成器。
# 型に従って式を組み立てるので、生成したIRは必ずIR検証を通る。
class ModelGenerator
  INT = :int
  BOOL = :bool

  def initialize(seed)
    @rng = Random.new(seed)
  end

  def pick(items)
    items[@rng.rand(items.length)]
  end

  def chance(probability)
    @rng.rand < probability
  end

  def model
    ir = chance(0.5) ? counters : free_form
    initial_constraint(ir)
    ir
  end

  # 初期状態を複数にするなら、ときどき初期条件で絞る。
  # 評価が失敗する初期条件や、どの候補も満たさない初期条件は、IRの読み込みで拒否されるので付けない。
  def initial_constraint(ir)
    return unless ir["states"].any? { |s| s.key?("initial_in") } && chance(0.5)

    ir["initial_constraint"] = chance(0.5) ? comparison({ vars: @state_types }) : expr(BOOL, { vars: @state_types }, 2)
    ir.delete("initial_constraint") if FmspecReference::Model.new(ir).initials.empty?
  rescue FmspecReference::EvalError
    ir.delete("initial_constraint")
  end

  # 初期値か、ときどき初期値の候補の配列。
  def initial_of(state, value)
    return state.merge("initial" => value) unless chance(0.3)

    candidates = [value] + Array.new(@rng.rand(1..3)) { yield }
    state.merge("initial_in" => candidates.shuffle(random: @rng))
  end

  # 整数のカウンタを少しずつ動かすモデル。状態空間が広く、違反があっても深い位置にある。
  def counters
    @enums = []
    @state_types = Array.new(1 + @rng.rand(3)) { { "int" => { "min" => 0, "max" => 2 + @rng.rand(4) } } }
    states = @state_types.each_with_index.map do |t, i|
      initial_of({ "id" => i, "name" => "s#{i}", "type" => t }, { "int" => 0 }) { { "int" => @rng.rand(0..2) } }
    end
    actions = Array.new(1 + @rng.rand(3)) do |n|
      params = chance(0.4) ? [{ "name" => "p0", "type" => { "int" => { "min" => 1, "max" => 2 } } }] : []
      scope = { vars: @state_types, params: params.map { |p| p["type"] } }
      target = @rng.rand(@state_types.length)
      delta = params.empty? || chance(0.3) ? { "int" => pick([1, 1, 1, -1, 2]) } : { "param" => 0 }
      moved = { "add" => [{ "var" => target }, delta] }
      range = @state_types[target]["int"]
      in_range = { "all" => [{ "ge" => [moved, { "int" => 0 }] }, { "le" => [moved, { "int" => range["max"] }] }] }
      act = { "name" => "a#{n}", "params" => params, "choices" => [] }
      # guard で範囲を守る形と、更新式の条件式で守る形を混ぜる。守らない形は範囲外更新のエラーになる。
      case @rng.rand(5)
      when 0, 1
        act["guard"] = in_range
        act["updates"] = [{ "target" => target, "expr" => moved }]
      when 2, 3
        act["guard"] = comparison(scope) if chance(0.4)
        act["updates"] = [{ "target" => target, "expr" => { "ite" => [in_range, moved, { "var" => target }] } }]
      else
        act["updates"] = [{ "target" => target, "expr" => moved }]
      end
      act
    end
    ir = { "ir_version" => 1, "name" => "counters", "enums" => [], "states" => states, "actions" => actions }
    ir["invariants"] = Array.new(@rng.rand(3)) { |i| { "name" => "inv#{i}", "expr" => deep_property } }
    ir["contracts"] = Array.new(@rng.rand(2)) do |i|
      act = pick(actions)
      target = act["updates"][0]["target"]
      { "name" => "con#{i}", "action" => act["name"],
        "expr" => { pick(%w[ge gt ne le]) => [{ "next" => target }, { "var" => target }] } }
    end
    ir["terminal"] = deep_property if chance(0.3)
    ir
  end

  # 上限に近い値の組み合わせでだけ破れる性質。
  def deep_property
    i = @rng.rand(@state_types.length)
    j = @rng.rand(@state_types.length)
    max_i = @state_types[i]["int"]["max"]
    max_j = @state_types[j]["int"]["max"]
    case @rng.rand(3)
    when 0 then { "lt" => [{ "add" => [{ "var" => i }, { "var" => j }] }, { "int" => max_i + max_j - @rng.rand(2) }] }
    when 1 then { "not" => [{ "all" => [{ "eq" => [{ "var" => i }, { "int" => max_i }] },
                                         { "ge" => [{ "var" => j }, { "int" => max_j - 1 }] }] }] }
    else { "le" => [{ "var" => i }, { "int" => max_i }] }
    end
  end

  def free_form
    @enums = chance(0.4) ? [{ "name" => "color", "variants" => %w[red green blue].take(2 + @rng.rand(2)) }] : []
    @state_types = Array.new(1 + @rng.rand(3)) { type }
    states = @state_types.each_with_index.map do |t, i|
      initial_of({ "id" => i, "name" => "s#{i}", "type" => t }, literal_of(t, initial: true)) { literal_of(t) }
    end
    actions = Array.new(@rng.rand(4)) { |i| action("a#{i}") }
    ir = { "ir_version" => 1, "name" => "random", "enums" => @enums, "states" => states, "actions" => actions }
    scope = { vars: @state_types }
    ir["invariants"] = Array.new(@rng.rand(3)) { |i| { "name" => "inv#{i}", "expr" => property(scope) } }
    ir["contracts"] = Array.new(actions.empty? ? 0 : @rng.rand(3)) { |i| contract("con#{i}", pick(actions)) }
    ir["terminal"] = expr(BOOL, scope, 2) if chance(0.3)
    ir
  end

  def type
    roll = @rng.rand
    if roll < 0.6
      min = @rng.rand(-2..1)
      { "int" => { "min" => min, "max" => min + @rng.rand(7) } }
    elsif roll < 0.85 || @enums.empty?
      { "bool" => {} }
    else
      { "enum" => @enums[0]["name"] }
    end
  end

  def kind(type)
    return INT if type.key?("int")
    return BOOL if type.key?("bool")

    [:enum, type["enum"]]
  end

  def literal_of(type, initial: false)
    case kind(type)
    when INT then { "int" => @rng.rand(type["int"]["min"]..type["int"]["max"]) }
    when BOOL then { "bool" => chance(0.5) }
    else { "enum" => { "type" => type["enum"], "variant" => pick(@enums[0]["variants"]) } }
    end
  end

  def action(name)
    params = Array.new(@rng.rand(3)) { |i| { "name" => "p#{i}", "type" => type } }
    choices = Array.new(chance(0.3) ? 1 : 0) { |i| { "name" => "c#{i}", "type" => type } }
    scope = { vars: @state_types, params: params.map { |p| p["type"] }, choices: choices.map { |c| c["type"] } }
    act = { "name" => name, "params" => params, "choices" => choices }
    act["guard"] = chance(0.5) ? comparison(scope) : expr(BOOL, scope, 3) if chance(0.6)
    targets = (0...@state_types.length).to_a.shuffle(random: @rng).take(@rng.rand(@state_types.length + 1))
    act["updates"] = targets.map { |t| { "target" => t, "expr" => update(@state_types[t], t, scope) } }
    if chance(0.4)
      out = type
      act["output"] = { "type" => out, "expr" => update(out, nil, scope) }
    end
    act
  end

  # 型 `type` に格納する式。整数の多くは、範囲内に収まるように条件式で包む。
  # 状態空間が広がるように、対象の変数に小さな値を足す形を多めに作る。
  def update(type, target, scope)
    e = expr(kind(type), scope, 3)
    return e unless type.key?("int")

    e = { "add" => [{ "var" => target }, leaf(INT, scope.merge(vars: []))] } if target && chance(0.6)
    return e unless chance(0.7)

    range = type["int"]
    fallback = target ? { "var" => target } : { "int" => range["min"] }
    in_range = { "all" => [{ "ge" => [e, { "int" => range["min"] }] }, { "le" => [e, { "int" => range["max"] }] }] }
    { "ite" => [in_range, e, fallback] }
  end

  def contract(name, action)
    scope = {
      vars: @state_types, next: true,
      params: action["params"].map { |p| p["type"] }, choices: action["choices"].map { |c| c["type"] },
      output: action["output"] && action["output"]["type"]
    }
    { "name" => name, "action" => action["name"], "expr" => property(scope) }
  end

  # 整数どうしの単純な比較。
  def comparison(scope)
    { pick(%w[lt le gt ge ne]) => [leaf(INT, scope), leaf(INT, scope)] }
  end

  # 不変条件と遷移契約。すぐには破れない、状態変数の上限や禁止値の形を多めに作る。
  def property(scope)
    ints = scope[:vars].each_index.select { |i| kind(scope[:vars][i]) == INT }
    return expr(BOOL, scope, 3) if ints.empty? || chance(0.35)

    i = pick(ints)
    range = scope[:vars][i]["int"]
    ref = scope[:next] && chance(0.5) ? { "next" => i } : { "var" => i }
    case @rng.rand(3)
    when 0 then { "le" => [ref, { "int" => range["max"] - @rng.rand(2) }] }
    when 1 then { "ne" => [ref, { "int" => @rng.rand(range["min"]..range["max"]) }] }
    else { "implies" => [comparison(scope), { "ge" => [ref, { "int" => range["min"] + @rng.rand(2) }] }] }
    end
  end

  # 種類 `want` を持つ参照（状態変数、引数、遷移後の状態、出力）。
  def refs(want, scope)
    found = []
    scope[:vars].each_with_index { |t, i| found << { "var" => i } if kind(t) == want }
    (scope[:params] || []).each_with_index { |t, i| found << { "param" => i } if kind(t) == want }
    (scope[:choices] || []).each_with_index { |t, i| found << { "choice" => i } if kind(t) == want }
    scope[:vars].each_with_index { |t, i| found << { "next" => i } if kind(t) == want } if scope[:next]
    found << { "output" => {} } if scope[:output] && kind(scope[:output]) == want
    found
  end

  def leaf(want, scope)
    found = refs(want, scope)
    return pick(found) if !found.empty? && chance(0.7)

    case want
    when INT
      chance(0.06) ? { "int" => pick([2**62, 2**63 - 1, -(2**63), -(2**62)]) } : { "int" => @rng.rand(-3..5) }
    when BOOL then { "bool" => chance(0.5) }
    else { "enum" => { "type" => want[1], "variant" => pick(@enums[0]["variants"]) } }
    end
  end

  def expr(want, scope, depth)
    return leaf(want, scope) if depth.zero? || chance(0.3)

    sub = ->(k) { expr(k, scope, depth - 1) }
    case want
    when INT
      if chance(0.2)
        { "ite" => [sub.(BOOL), sub.(INT), sub.(INT)] }
      else
        { pick(%w[add add sub mul]) => [sub.(INT), sub.(INT)] }
      end
    when BOOL
      case @rng.rand(10)
      when 0..3 then { pick(%w[lt le gt ge]) => [sub.(INT), sub.(INT)] }
      when 4
        k = pick([INT, BOOL] + @enums.map { |e| [:enum, e["name"]] })
        { pick(%w[eq ne]) => [sub.(k), sub.(k)] }
      when 5 then { "not" => [sub.(BOOL)] }
      when 6 then { "all" => Array.new(@rng.rand(4)) { sub.(BOOL) } }
      when 7 then { "any" => Array.new(@rng.rand(4)) { sub.(BOOL) } }
      when 8 then { "implies" => [sub.(BOOL), sub.(BOOL)] }
      else { "ite" => [sub.(BOOL), sub.(BOOL), sub.(BOOL)] }
      end
    else
      chance(0.5) ? { "ite" => [sub.(BOOL), sub.(want), sub.(want)] } : leaf(want, scope)
    end
  end
end
