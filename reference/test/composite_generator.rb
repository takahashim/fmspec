# frozen_string_literal: true

# 比較テスト用の、複合型を使う小さな整形式モデルのランダム生成器。
# 型に従って式を組み立てるので、生成したIRは必ずIR検証を通る。
#
# 式の型は、IRの型の JSON で表す。整数は、Set、Map、List の中を除いて範囲を区別しない
# （IRの型検査と同じ）ので、型の比較には `xt` で範囲を落とした形を使う。
class CompositeGenerator
  COLOR = "color"

  def initialize(seed)
    @rng = Random.new(seed)
    @names = 0
  end

  def pick(items)
    items[@rng.rand(items.length)]
  end

  def chance(probability)
    @rng.rand < probability
  end

  def fresh(prefix)
    @names += 1
    "#{prefix}#{@names}"
  end

  # ---- 型 ----

  def int_type(min = 0, max = 2)
    { "int" => { "min" => min, "max" => max } }
  end

  def scalar_type
    case @rng.rand(4)
    when 0 then { "bool" => {} }
    when 1 then { "enum" => COLOR }
    else int_type(pick([0, 0, -1]), pick([1, 2, 2]))
    end
  end

  # Set の要素と Map のキーに使う、値の少ない型。
  def key_type
    case @rng.rand(6)
    when 0 then { "bool" => {} }
    when 1, 2 then { "enum" => COLOR }
    when 3 then int_type(0, pick([1, 2]))
    when 4 then { "option" => pick([{ "bool" => {} }, { "enum" => COLOR }]) }
    else { "tuple" => [{ "bool" => {} }, int_type(0, 1)] }
    end
  end

  def state_type
    case @rng.rand(9)
    when 0 then scalar_type
    when 1, 2 then { "set" => key_type }
    when 3 then { "map" => { "key" => pick([{ "bool" => {} }, { "enum" => COLOR }]), "value" => small_value_type } }
    when 4 then { "list" => { "of" => small_value_type, "max" => 1 + @rng.rand(2) } }
    when 5 then { "option" => scalar_type }
    when 6 then { "tuple" => Array.new(1 + @rng.rand(2)) { scalar_type } }
    when 7
      { "record" => [{ "name" => "a", "type" => scalar_type }, { "name" => "b", "type" => scalar_type }].take(1 + @rng.rand(2)) }
    else { "list" => { "of" => int_type(0, 2), "max" => 2 } }
    end
  end

  def small_value_type
    pick([{ "bool" => {} }, int_type(0, pick([1, 2])), { "enum" => COLOR }, { "option" => { "bool" => {} } }])
  end

  # 状態の部分の型（要素、キー、値、フィールド）。引数をこの型にすると、遷移が状態を動かしやすい。
  def parts(type)
    kind, body = type.first
    case kind
    when "set", "option" then [body]
    when "map" then [body["key"], body["value"]]
    when "list" then [body["of"]]
    when "tuple" then body
    when "record" then body.map { |f| f["type"] }
    else [type]
    end
  end

  def param_type
    return pick(@state_types.flat_map { |t| parts(t) }) if chance(0.6)

    case @rng.rand(10)
    when 0 then { "option" => pick([{ "bool" => {} }, { "enum" => COLOR }]) }
    when 1 then { "tuple" => [{ "bool" => {} }, int_type(0, 1)] }
    when 2 then { "set" => { "bool" => {} } }
    else scalar_type
    end
  end

  # 式の型を比べるための形。Set、Map、List の外では、整数の範囲を落とす。
  def xt(type)
    kind, body = type.first
    case kind
    when "int" then "int"
    when "bool" then "bool"
    when "enum" then [kind, body]
    when "tuple" then [kind, body.map { |t| xt(t) }]
    when "record" then [kind, body.map { |f| [f["name"], xt(f["type"])] }]
    when "option" then [kind, xt(body)]
    else type
    end
  end

  def kind(type) = type.keys.first

  def collection?(type) = %w[set map list].include?(kind(type))

  # ---- 値 ----

  def variants = @enums[0]["variants"]

  def values_of(type)
    kind, body = type.first
    case kind
    when "bool" then [false, true]
    when "int" then (body["min"]..body["max"]).to_a
    when "enum" then variants
    when "tuple" then body.map { |t| values_of(t) }.reduce([[]]) { |acc, vs| acc.flat_map { |p| vs.map { |v| p + [v] } } }
    when "option" then [nil] + values_of(body).map { |v| { "some" => v } }
    end
  end

  # 型 `type` の値を書いた式。整数は範囲の中に収める。
  def literal_of(type)
    kind, body = type.first
    case kind
    when "bool" then { "bool" => chance(0.5) }
    when "int" then { "int" => @rng.rand(body["min"]..body["max"]) }
    when "enum" then { "enum" => { "type" => body, "variant" => pick(variants) } }
    when "tuple" then { "tuple" => body.map { |t| literal_of(t) } }
    when "record" then { "record" => body.map { |f| { "name" => f["name"], "expr" => literal_of(f["type"]) } } }
    when "option" then chance(0.4) ? { "none" => body } : { "some" => [literal_of(body)] }
    when "set"
      { "set" => { "of" => body, "items" => Array.new(@rng.rand(3)) { literal_of(body) } } }
    when "map"
      { "map" => { "key" => body["key"], "value" => body["value"],
                   "items" => Array.new(@rng.rand(3)) { [literal_of(body["key"]), literal_of(body["value"])] } } }
    when "list"
      { "list" => { "of" => body["of"], "max" => body["max"],
                    "items" => Array.new(@rng.rand(body["max"] + 1)) { literal_of(body["of"]) } } }
    end
  end

  # 証明書を崩すための、型に従うJSONの値。`bad` なら、ときどき整数を範囲の外にする。
  def json_of(type, bad: false)
    kind, body = type.first
    case kind
    when "bool" then chance(0.5)
    when "int"
      bad && chance(0.1) ? body["max"] + 1 : @rng.rand(body["min"]..body["max"])
    when "enum" then pick(variants)
    when "tuple" then body.map { |t| json_of(t, bad: bad) }
    when "record" then body.to_h { |f| [f["name"], json_of(f["type"], bad: bad)] }
    when "option" then chance(0.4) ? nil : { "some" => json_of(body, bad: bad) }
    when "set" then values_of(body).select { chance(0.5) }
    when "map"
      values_of(body["key"]).select { chance(0.5) }.map { |k| [k, json_of(body["value"], bad: bad)] }
    when "list" then Array.new(@rng.rand(body["max"] + 1)) { json_of(body["of"], bad: bad) }
    end
  end

  # ---- モデル ----

  def model
    @enums = [{ "name" => COLOR, "variants" => %w[red green blue].take(2 + @rng.rand(2)) }]
    @state_types = Array.new(1 + @rng.rand(2)) { state_type }
    @initials = @state_types.map { |t| literal_of(t) }
    states = @state_types.each_with_index.map do |t, i|
      { "id" => i, "name" => "s#{i}", "type" => t, "initial" => @initials[i] }
    end
    @constants = []
    if chance(0.3)
      t = pick(@state_types)
      @constants << { "name" => "k0", "type" => t, "value" => literal_of(t) }
      states.each_with_index { |s, i| s["initial"] = { "const" => "k0" } if @state_types[i] == t && chance(0.5) }
    end
    actions = Array.new(2 + @rng.rand(3)) { |i| action("a#{i}") }
    ir = { "ir_version" => 1, "name" => "composite", "enums" => @enums, "constants" => @constants,
           "states" => states, "actions" => actions }
    scope = { vars: @state_types }
    ir["invariants"] = Array.new(@rng.rand(3)) { |i| { "name" => "inv#{i}", "expr" => property(scope) } }
    ir["contracts"] = Array.new(@rng.rand(2)) do |i|
      act = pick(actions)
      { "name" => "con#{i}", "action" => act["name"], "expr" => property(contract_scope(act)) }
    end
    ir["terminal"] = expr(bool, scope, 2) if chance(0.2)
    ir
  end

  def bool = { "bool" => {} }

  # 不変条件と遷移契約。すぐには破れない、大きさの上限や禁止値の形を多めに作る。
  def property(scope)
    return expr(bool, scope, 3) if chance(0.15)

    i = @rng.rand(@state_types.length)
    type = @state_types[i]
    x = scope[:next] && chance(0.5) ? { "next" => i } : { "var" => i }
    kind, body = type.first
    case kind
    when "set", "map", "list"
      case @rng.rand(3)
      when 0 then { "le" => [{ "size" => [x] }, { "int" => max_size(type) - @rng.rand(2) }] }
      when 1
        name = fresh("x")
        elem = { "set" => -> { body }, "map" => -> { body["key"] }, "list" => -> { body["of"] } }.fetch(kind).call
        y = { "local" => name }
        check = { "ne" => [y, literal_of(elem)] }
        # ある要素では失敗し、別の要素では偽になる本体。どちらが先に起きるかは、たどる順で決まる。
        if chance(0.5)
          failing = { "eq" => [{ "div" => [{ "int" => 1 }, { "int" => 0 }] }, { "int" => 0 }] }
          check = { "ite" => [{ "eq" => [y, literal_of(elem)] }, failing, check] }
        end
        { pick(%w[forall forall exists]) => { "name" => name, "in" => x, "body" => check } }
      else { "implies" => [expr(bool, scope, 1), { "le" => [{ "size" => [x] }, { "int" => max_size(type) - 1 }] }] }
      end
    else
      # 初期値と同じ値は、なるべく避ける。
      value = Array.new(3) { literal_of(type) }.find { |v| v != @initials[i] } || literal_of(type)
      { "ne" => [x, value] }
    end
  end

  def max_size(type)
    kind, body = type.first
    case kind
    when "set" then values_of(body).length
    when "map" then values_of(body["key"]).length
    else body["max"]
    end
  end

  def contract_scope(action)
    { vars: @state_types, next: true,
      params: action["params"].map { |p| p["type"] }, choices: action["choices"].map { |c| c["type"] },
      output: action["output"] && action["output"]["type"] }
  end

  def action(name)
    params = Array.new(@rng.rand(3)) { |i| { "name" => "p#{i}", "type" => param_type } }
    choices = Array.new(chance(0.2) ? 1 : 0) { |i| { "name" => "c#{i}", "type" => scalar_type } }
    scope = { vars: @state_types, params: params.map { |p| p["type"] }, choices: choices.map { |c| c["type"] } }
    act = { "name" => name, "params" => params, "choices" => choices }
    act["guard"] = expr(bool, scope, 2) if chance(0.25)
    targets = (0...@state_types.length).to_a.shuffle(random: @rng).take(1 + @rng.rand(@state_types.length))
    act["updates"] = targets.map { |t| { "target" => t, "expr" => update(t, scope) } }
    if chance(0.3)
      out = scalar_type
      act["output"] = { "type" => out, "expr" => guarded(out, expr(out, scope, 2)) }
    end
    act
  end

  # 状態変数 `target` の更新式。多くは、いまの値を少し変える形にし、失敗しうる演算は条件式で守る。
  def update(target, scope)
    type = @state_types[target]
    var = { "var" => target }
    case @rng.rand(12)
    when 0 then literal_of(type)
    when 1 then expr(type, scope, 2)
    else
      changed = change(type, var, scope)
      safe = safe_condition(type, var, changed)
      safe && chance(0.75) ? { "ite" => [safe, changed, var] } : changed
    end
  end

  # 値 `x`（型 `type`）を少し変える式。
  def change(type, x, scope)
    kind, body = type.first
    case kind
    when "bool" then { "not" => [x] }
    when "int" then { pick(%w[add add sub]) => [x, { "int" => pick([1, 1, 2]) }] }
    when "enum" then { "ite" => [expr(bool, scope, 1), literal_of(type), x] }
    when "tuple"
      i = @rng.rand(body.length)
      { "tuple" => body.each_with_index.map do |t, j|
        part = { "nth" => { "of" => x, "index" => j } }
        i == j ? change(t, part, scope) : part
      end }
    when "record"
      i = @rng.rand(body.length)
      { "record" => body.each_with_index.map do |f, j|
        part = { "field" => { "of" => x, "name" => f["name"] } }
        { "name" => f["name"], "expr" => i == j ? change(f["type"], part, scope) : part }
      end }
    when "option"
      case @rng.rand(5)
      when 0 then { "none" => body }
      when 1 then { "some" => [stretch(literal_of(body))] }
      else { "some" => [element(body, scope)] }
      end
    when "set"
      { pick(%w[insert insert remove]) => [x, element(body, scope)] }
    when "map"
      if chance(0.7)
        { "put" => [x, element(body["key"], scope), element(body["value"], scope)] }
      else
        { "delete" => [x, element(body["key"], scope)] }
      end
    when "list"
      case @rng.rand(10)
      when 0..4 then { "push" => [x, element(body["of"], scope)] }
      # 2つ続けて入れると、満杯の列に、要素の型に属さない値を入れることがある。
      when 5 then { "push" => [{ "push" => [x, element(body["of"], scope)] }, stretch(literal_of(body["of"]))] }
      else { pick(%w[pop shift]) => [x] }
      end
    end
  end

  # 変えた値が型に収まり、変える演算が失敗しない条件。作れなければ nil。
  def safe_condition(type, x, changed)
    kind, body = type.first
    case kind
    when "int" then in_range(changed, body)
    when "tuple", "record"
      ranges = []
      parts = kind == "tuple" ? body.each_with_index.map { |t, j| [t, { "nth" => { "of" => changed, "index" => j } }] }
                              : body.map { |f| [f["type"], { "field" => { "of" => changed, "name" => f["name"] } }] }
      parts.each { |t, e| ranges << in_range(e, t["int"]) if t.key?("int") }
      ranges.empty? ? nil : { "all" => ranges }
    when "list"
      op = changed.keys.first
      op == "push" ? { "lt" => [{ "size" => [x] }, { "int" => body["max"] }] } : { "not" => [{ "is_empty" => [x] }] }
    end
  end

  def in_range(e, range)
    { "all" => [{ "ge" => [e, { "int" => range["min"] }] }, { "le" => [e, { "int" => range["max"] }] }] }
  end

  # 出力式。整数は、多くの場合、範囲の中に収める。
  def guarded(type, e)
    return e unless type.key?("int") && chance(0.7)

    { "ite" => [in_range(e, type["int"]), e, { "int" => type["int"]["min"] }] }
  end

  # 要素として置く式。多くは型に属する値で、ときどき範囲の外になりうる式にする。
  def element(type, scope)
    found = refs(type, scope).select { |r, t| t == type || !t.key?("int") }.map(&:first)
    return pick(found) if !found.empty? && chance(0.6)
    return stretch(literal_of(type)) if chance(0.2)
    # 取り出し（unwrap、get など）は失敗しうる。
    if chance(0.15) && (p = projection(type, scope))
      return p
    end

    literal_of(type)
  end

  # 式の中の最初の整数に1を足す。範囲の上限の値なら、要素の型に属さなくなる。
  def stretch(e)
    return { "add" => [e, { "int" => 1 }] } if e.is_a?(Hash) && e["int"].is_a?(Integer)

    case e
    when Hash
      e.each do |k, v|
        changed = stretch(v)
        return e.merge(k => changed) unless changed.equal?(v)
      end
    when Array
      e.each_with_index do |v, i|
        changed = stretch(v)
        return e.dup.tap { |a| a[i] = changed } unless changed.equal?(v)
      end
    end
    e
  end

  # ---- 式 ----

  # 型が `type` に合う参照を、[式, 宣言された型] で返す。
  def refs(type, scope)
    want = xt(type)
    found = []
    add = ->(e, t) { found << [e, t] if xt(t) == want }
    scope[:vars].each_with_index { |t, i| add.({ "var" => i }, t) }
    (scope[:params] || []).each_with_index { |t, i| add.({ "param" => i }, t) }
    (scope[:choices] || []).each_with_index { |t, i| add.({ "choice" => i }, t) }
    scope[:vars].each_with_index { |t, i| add.({ "next" => i }, t) } if scope[:next]
    add.({ "output" => {} }, scope[:output]) if scope[:output]
    (scope[:locals] || []).each { |name, t| add.({ "local" => name }, t) }
    @constants.each { |c| add.({ "const" => c["name"] }, c["type"]) }
    found
  end

  # 参照できる値すべてを、[式, 型] で返す。
  def all_refs(scope)
    found = []
    scope[:vars].each_with_index { |t, i| found << [{ "var" => i }, t] }
    (scope[:params] || []).each_with_index { |t, i| found << [{ "param" => i }, t] }
    (scope[:choices] || []).each_with_index { |t, i| found << [{ "choice" => i }, t] }
    scope[:vars].each_with_index { |t, i| found << [{ "next" => i }, t] } if scope[:next]
    found << [{ "output" => {} }, scope[:output]] if scope[:output]
    (scope[:locals] || []).each { |name, t| found << [{ "local" => name }, t] }
    found
  end

  def leaf(type, scope)
    found = refs(type, scope).map(&:first)
    return pick(found) if !found.empty? && chance(0.7)
    return { "int" => pick([2**62, 2**63 - 1, -(2**63)]) } if type.key?("int") && chance(0.03)

    literal_of(type)
  end

  # 参照から、型 `type` の部分を取り出す式。取り出しは、失敗しうる（none、キーがない、空、範囲外）。
  def projection(type, scope)
    want = xt(type)
    options = []
    all_refs(scope).each do |e, t|
      kind, body = t.first
      case kind
      when "tuple"
        body.each_with_index { |u, i| options << { "nth" => { "of" => e, "index" => i } } if xt(u) == want }
      when "record"
        body.each { |f| options << { "field" => { "of" => e, "name" => f["name"] } } if xt(f["type"]) == want }
      when "option"
        options << { "unwrap" => [e] } if xt(body) == want
      when "map"
        options << { "get" => [e, element(body["key"], scope)] } if xt(body["value"]) == want
      when "list"
        if xt(body["of"]) == want
          options << { pick(%w[first last]) => [e] }
          options << { "at" => [e, { "int" => @rng.rand(-1..2) }] }
        end
      end
    end
    options.empty? ? nil : pick(options)
  end

  def collections(scope)
    all_refs(scope).select { |_, t| collection?(t) }
  end

  def expr(type, scope, depth)
    return leaf(type, scope) if depth.zero? || chance(0.25)

    sub = ->(t) { expr(t, scope, depth - 1) }
    if chance(0.15) && (p = projection(type, scope))
      return p
    end
    if chance(0.08)
      t = pick(all_refs(scope))&.last || scalar_type
      name = fresh("l")
      inner = scope.merge(locals: (scope[:locals] || []) + [[name, t]])
      return { "let" => { "name" => name, "value" => sub.(t), "body" => expr(type, inner, depth - 1) } }
    end
    kind, body = type.first
    case kind
    when "int" then int_expr(scope, depth, sub)
    when "bool" then bool_expr(scope, depth, sub)
    when "set" then set_expr(type, scope, sub)
    when "map" then map_expr(type, scope, sub)
    when "list" then list_expr(type, scope, sub)
    when "tuple"
      chance(0.5) ? { "tuple" => body.map { |t| sub.(t) } } : { "ite" => [sub.(bool), sub.(type), sub.(type)] }
    when "record"
      if chance(0.5)
        { "record" => body.map { |f| { "name" => f["name"], "expr" => sub.(f["type"]) } } }
      else
        { "ite" => [sub.(bool), sub.(type), sub.(type)] }
      end
    when "option"
      case @rng.rand(3)
      when 0 then { "none" => body }
      when 1 then { "some" => [sub.(body)] }
      else { "ite" => [sub.(bool), sub.(type), sub.(type)] }
      end
    else { "ite" => [sub.(bool), sub.(type), sub.(type)] }
    end
  end

  def int_expr(scope, _depth, sub)
    case @rng.rand(10)
    when 0..3 then { pick(%w[add add sub mul]) => [sub.(int_type), sub.(int_type)] }
    when 4
      divisor = chance(0.7) ? { "int" => pick([-2, -1, 1, 2, 3]) } : sub.(int_type)
      { pick(%w[div mod]) => [sub.(int_type), divisor] }
    when 5, 6
      c = collections(scope)
      c.empty? ? sub.(int_type) : { "size" => [pick(c).first] }
    else { "ite" => [sub.(bool), sub.(int_type), sub.(int_type)] }
    end
  end

  def bool_expr(scope, depth, sub)
    case @rng.rand(16)
    when 0..2 then { pick(%w[lt le gt ge]) => [sub.(int_type), sub.(int_type)] }
    when 3, 4
      t = pick(all_refs(scope)).last
      { pick(%w[eq eq ne]) => [sub.(t), sub.(t)] }
    when 5 then { "not" => [sub.(bool)] }
    when 6 then { "all" => Array.new(@rng.rand(4)) { sub.(bool) } }
    when 7 then { "any" => Array.new(@rng.rand(4)) { sub.(bool) } }
    when 8 then { "implies" => [sub.(bool), sub.(bool)] }
    when 9 then { "ite" => [sub.(bool), sub.(bool), sub.(bool)] }
    when 10, 11 then quantifier(scope, depth)
    else query(scope, sub)
    end
  end

  # 集合、写像、列、Option についての述語。
  def query(scope, sub)
    candidates = all_refs(scope).select { |_, t| collection?(t) || t.key?("option") }
    return sub.(bool) if candidates.empty?

    e, t = pick(candidates)
    kind, body = t.first
    case kind
    when "option" then { pick(%w[is_some is_none]) => [e] }
    when "set"
      case @rng.rand(4)
      when 0 then { "is_empty" => [e] }
      when 1 then { "subset" => [e, sub.(t)] }
      else { "contains" => [e, element(body, scope)] }
      end
    when "map" then chance(0.7) ? { "has_key" => [e, element(body["key"], scope)] } : { "is_empty" => [e] }
    else chance(0.7) ? { "contains" => [e, element(body["of"], scope)] } : { "is_empty" => [e] }
    end
  end

  def quantifier(scope, depth)
    name = fresh("x")
    c = collections(scope)
    if !c.empty? && chance(0.75)
      e, t = pick(c)
      kind, body = t.first
      over = { "in" => e }
      elem_type = { "set" => -> { body }, "map" => -> { body["key"] }, "list" => -> { body["of"] } }.fetch(kind).call
    else
      elem_type = key_type
      over = { "type" => elem_type }
    end
    inner = scope.merge(locals: (scope[:locals] || []) + [[name, elem_type]])
    { pick(%w[forall exists]) => { "name" => name, **over, "body" => expr(bool, inner, depth - 1) } }
  end

  def set_expr(type, scope, sub)
    body = type["set"]
    case @rng.rand(6)
    when 0 then literal_of(type)
    when 1, 2 then { pick(%w[insert remove]) => [sub.(type), element(body, scope)] }
    when 3 then { pick(%w[union intersection difference]) => [sub.(type), sub.(type)] }
    when 4
      maps = all_refs(scope).select { |_, t| t.key?("map") && t["map"]["key"] == body }
      maps.empty? ? leaf(type, scope) : { "keys" => [pick(maps).first] }
    else { "ite" => [sub.(bool), sub.(type), sub.(type)] }
    end
  end

  def map_expr(type, scope, sub)
    body = type["map"]
    case @rng.rand(5)
    when 0 then literal_of(type)
    when 1, 2 then { "put" => [sub.(type), element(body["key"], scope), element(body["value"], scope)] }
    when 3 then { "delete" => [sub.(type), element(body["key"], scope)] }
    else { "ite" => [sub.(bool), sub.(type), sub.(type)] }
    end
  end

  def list_expr(type, scope, sub)
    body = type["list"]
    case @rng.rand(5)
    when 0 then literal_of(type)
    when 1 then { "push" => [sub.(type), element(body["of"], scope)] }
    when 2 then { pick(%w[pop shift]) => [sub.(type)] }
    else { "ite" => [sub.(bool), sub.(type), sub.(type)] }
    end
  end
end
