# frozen_string_literal: true

# fmspec の参照実装（仕様書 §3、§14.3）。
#
# IR のJSONを直接解釈する、小さな Evaluator、幅優先探索、証明書検査器である。
# Rust の実装とは独立に書いてあり、比較テストで両者の結果を突き合わせる。
# 速度や診断は考えない。入力は整形式のIRとし、IR検証は行わない。
#
# 複合型の値は、スロットの列に下ろさず、そのまま持つ。
# Tuple は Array、Record はフィールド名から値への Hash、Option は nil か Some で表す。
# Set、Map、List は、要素の型を持つ構造体で表す（要素の検査と、正規順の整列に使う）。
#
# 結果は `fmspec check --json` と同じ形のHashで返す（比較に使う項目だけ）。
require "json"
require "set"

module FmspecReference
  I64 = (-(2**63))..(2**63 - 1)

  # 列挙型の値。型名とラベルで持つ。
  EnumValue = Struct.new(:type, :label)

  # Option の値のうち、空でないもの。空は nil。
  Some = Struct.new(:value)

  # 有限集合。`elem` は要素の型、`items` は Set。
  SetValue = Struct.new(:elem, :items)

  # 有限写像。`key`、`value` は型、`entries` はキーから値への Hash。
  MapValue = Struct.new(:key, :value, :entries)

  # 長さに上限のある列。`elem` は要素の型、`items` は Array。
  ListValue = Struct.new(:elem, :max, :items)

  ABSENT = Object.new.freeze

  # 式の評価、または状態・出力の更新の失敗。
  # `slot` は、範囲外更新が起きた、状態変数の中のスロットの位置。
  class EvalError < StandardError
    attr_reader :detail, :slot

    def initialize(detail, slot = nil)
      @detail = detail
      @slot = slot
      super(detail.inspect)
    end
  end

  # 操作の適用の失敗。失敗した箇所（guard、update、output）を持つ。
  class StepError < StandardError
    attr_reader :property

    def initialize(property)
      @property = property
      super(property.inspect)
    end
  end

  Env = Struct.new(:pre, :params, :choices, :post, :output, :locals) do
    def with_local(name, value)
      Env.new(pre, params, choices, post, output, (locals || {}).merge(name => value))
    end
  end

  class Model
    attr_reader :ir

    def initialize(ir)
      @ir = ir
      @enums = (ir["enums"] || []).to_h { |e| [e["name"], e["variants"]] }
      @states = ir["states"]
      @actions = ir["actions"] || []
      @invariants = ir["invariants"] || []
      @contracts = ir["contracts"] || []
      @terminal = ir["terminal"]
      @domains = {}
      @constants = {}
      (ir["constants"] || []).each { |c| @constants[c["name"]] = ev(c["value"], Env.new) }
    end

    # ---- 値 ----

    def literal(node)
      kind, body = node.first
      kind == "enum" ? EnumValue.new(body["type"], body["variant"]) : body
    end

    # 初期状態の集合。状態変数ごとの候補（`initial` か `initial_in`）の直積から、
    # `initial_constraint` を満たすものを残し、正規順に整列して重複を除く。
    def initials
      @initials ||= begin
        candidates = @states.map do |s|
          s.key?("initial_in") ? s["initial_in"].map { |e| ev(e, Env.new) } : [ev(s["initial"], Env.new)]
        end
        states = product(candidates)
        if (constraint = @ir["initial_constraint"])
          states = states.select { |state| prop(constraint, Env.new(state, nil, nil, nil, nil)) }
        end
        sort_states(states.uniq)
      end
    end

    def product(lists)
      lists.reduce([[]]) { |acc, values| acc.flat_map { |prefix| values.map { |v| prefix + [v] } } }
    end

    # 型に属する値を、正規順に並べる。
    # 正規順は、Bool は偽が先、Int は小さい順、Enum はラベルの順で、Tuple と Record は辞書式、
    # Option は空が先、Set は要素ごとの有無（要素の正規順に並べた、偽が先の真偽値の列）の辞書式、
    # Map はキーごとの「なし、または値」（なしが先）の辞書式、List は長さの順で、同じ長さなら辞書式。
    def domain(type)
      @domains[type] ||= begin
        kind, body = type.first
        case kind
        when "bool" then [false, true]
        when "int" then (body["min"]..body["max"]).to_a
        when "enum" then @enums.fetch(body).map { |label| EnumValue.new(body, label) }
        when "tuple" then product(body.map { |t| domain(t) })
        when "record"
          product(body.map { |f| domain(f["type"]) }).map { |vs| body.map { |f| f["name"] }.zip(vs).to_h }
        when "option" then [nil] + domain(body).map { |v| Some.new(v) }
        when "set"
          elems = domain(body)
          product(elems.map { [false, true] }).map do |bits|
            SetValue.new(body, elems.zip(bits).select(&:last).map(&:first).to_set)
          end
        when "map"
          keys = domain(body["key"])
          product(keys.map { [ABSENT] + domain(body["value"]) }).map do |row|
            MapValue.new(body["key"], body["value"], keys.zip(row).reject { |_, v| v.equal?(ABSENT) }.to_h)
          end
        when "list"
          (0..body["max"]).flat_map do |n|
            product([domain(body["of"])] * n).map { |items| ListValue.new(body["of"], body["max"], items) }
          end
        end
      end
    end

    def member?(type, value)
      kind, body = type.first
      case kind
      when "bool" then [true, false].include?(value)
      when "int" then value.is_a?(Integer) && value.between?(body["min"], body["max"])
      when "enum" then value.is_a?(EnumValue) && value.type == body && @enums.fetch(body).include?(value.label)
      when "tuple"
        value.is_a?(Array) && value.length == body.length && body.zip(value).all? { |t, v| member?(t, v) }
      when "record"
        value.is_a?(Hash) && value.keys == body.map { |f| f["name"] } &&
          body.all? { |f| member?(f["type"], value[f["name"]]) }
      when "option" then value.nil? || (value.is_a?(Some) && member?(body, value.value))
      when "set" then value.is_a?(SetValue) && value.items.all? { |v| member?(body, v) }
      when "map"
        value.is_a?(MapValue) &&
          value.entries.all? { |k, v| member?(body["key"], k) && member?(body["value"], v) }
      when "list"
        value.is_a?(ListValue) && value.items.length <= body["max"] && value.items.all? { |v| member?(body["of"], v) }
      end
    end

    # 正規順の整列に使うキー。
    def order_key(type, value)
      kind, body = type.first
      case kind
      when "bool" then value ? 1 : 0
      when "int" then value
      when "enum" then @enums.fetch(body).index(value.label)
      when "tuple" then body.each_with_index.map { |t, i| order_key(t, value[i]) }
      when "record" then body.map { |f| order_key(f["type"], value[f["name"]]) }
      when "option" then value.nil? ? [0] : [1, order_key(body, value.value)]
      when "set" then domain(body).map { |e| value.items.include?(e) ? 1 : 0 }
      when "map"
        domain(body["key"]).map do |k|
          value.entries.key?(k) ? [1, order_key(body["value"], value.entries[k])] : [0]
        end
      when "list" then [value.items.length] + value.items.map { |v| order_key(body["of"], v) }
      end
    end

    def sorted(type, values)
      values.sort_by { |v| order_key(type, v) }
    end

    # 値が占めるスロットの数。範囲外更新の位置を、エンジンと同じ形で示すのに使う。
    def width(type)
      kind, body = type.first
      case kind
      when "tuple" then body.sum { |t| width(t) }
      when "record" then body.sum { |f| width(f["type"]) }
      when "option" then 1 + width(body)
      when "set" then domain(body).length
      when "map" then domain(body["key"]).length * (1 + width(body["value"]))
      when "list" then 1 + body["max"] * width(body["of"])
      else 1
      end
    end

    def sort_states(states)
      states.sort_by { |s| s.each_with_index.map { |v, i| order_key(@states[i]["type"], v) } }
    end

    def json_value(type, value)
      kind, body = type.first
      case kind
      when "enum" then value.label
      when "tuple" then body.each_with_index.map { |t, i| json_value(t, value[i]) }
      when "record" then body.to_h { |f| [f["name"], json_value(f["type"], value[f["name"]])] }
      when "option" then value.nil? ? nil : { "some" => json_value(body, value.value) }
      when "set" then sorted(body, value.items.to_a).map { |v| json_value(body, v) }
      when "map"
        sorted(body["key"], value.entries.keys).map do |k|
          [json_value(body["key"], k), json_value(body["value"], value.entries[k])]
        end
      when "list" then value.items.map { |v| json_value(body["of"], v) }
      else value
      end
    end

    def from_json(type, json)
      kind, body = type.first
      case kind
      when "enum" then EnumValue.new(body, json)
      when "tuple" then body.each_with_index.map { |t, i| from_json(t, json[i]) }
      when "record" then body.to_h { |f| [f["name"], from_json(f["type"], json[f["name"]])] }
      when "option" then json.nil? ? nil : Some.new(from_json(body, json["some"]))
      when "set" then SetValue.new(body, json.map { |v| from_json(body, v) }.to_set)
      when "map"
        MapValue.new(body["key"], body["value"],
                     json.to_h { |k, v| [from_json(body["key"], k), from_json(body["value"], v)] })
      when "list" then ListValue.new(body["of"], body["max"], json.map { |v| from_json(body["of"], v) })
      else json
      end
    end

    def json_state(state)
      @states.each_with_index.to_h { |s, i| [s["name"], json_value(s["type"], state[i])] }
    end

    def json_bindings(bindings, values)
      (bindings || []).each_with_index.to_h { |b, i| [b["name"], json_value(b["type"], values[i])] }
    end

    def json_output(action, output)
      action["output"] ? { "value" => json_value(action["output"]["type"], output) } : { "unit" => true }
    end

    # ---- 式の評価（仕様書 §4.2）----

    def int(value)
      raise EvalError, { "kind" => "type_mismatch" } unless value.is_a?(Integer)

      value
    end

    def bool(value)
      raise EvalError, { "kind" => "type_mismatch" } unless [true, false].include?(value)

      value
    end

    def bound(values, index)
      raise EvalError, { "kind" => "unbound" } if values.nil? || index >= values.length

      values[index]
    end

    def arith(result)
      raise EvalError, { "kind" => "overflow" } unless I64.cover?(result)

      result
    end

    def scalar?(value)
      value.is_a?(Integer) || value.is_a?(EnumValue) || value == true || value == false
    end

    def same_kind(left, right)
      return unless scalar?(left) || scalar?(right)

      same = if left.is_a?(EnumValue) || right.is_a?(EnumValue)
               left.is_a?(EnumValue) && right.is_a?(EnumValue) && left.type == right.type
             else
               left.is_a?(Integer) == right.is_a?(Integer)
             end
      raise EvalError, { "kind" => "type_mismatch" } unless same
    end

    def fail!(kind)
      raise EvalError, { "kind" => kind }
    end

    # 要素の型に属さなければ失敗する。
    def element(type, value)
      fail!("not_in_domain") unless member?(type, value)
      value
    end

    def ev(node, env)
      op, body = node.first
      case op
      when "int", "bool", "enum" then literal(node)
      when "var" then bound(env.pre, body)
      when "param" then bound(env.params, body)
      when "choice" then bound(env.choices, body)
      when "next" then bound(env.post, body)
      when "output"
        raise EvalError, { "kind" => "unbound" } if env.output.nil?

        env.output
      when "add", "sub", "mul"
        left = ev(body[0], env)
        right = ev(body[1], env)
        int(left)
        int(right)
        arith({ "add" => left + right, "sub" => left - right, "mul" => left * right }.fetch(op))
      when "div", "mod"
        left = ev(body[0], env)
        right = ev(body[1], env)
        int(left)
        int(right)
        fail!("division_by_zero") if right.zero?
        # Ruby の整数の除算と剰余は、負の無限大の方向に丸める。
        arith(op == "div" ? left / right : left % right)
      when "lt", "le", "gt", "ge"
        left = ev(body[0], env)
        right = ev(body[1], env)
        int(left).public_send({ "lt" => :<, "le" => :<=, "gt" => :>, "ge" => :>= }.fetch(op), int(right))
      when "eq", "ne"
        left = ev(body[0], env)
        right = ev(body[1], env)
        same_kind(left, right)
        (left == right) == (op == "eq")
      when "not" then !bool(ev(body[0], env))
      when "all"
        body.each { |operand| return false unless bool(ev(operand, env)) }
        true
      when "any"
        body.each { |operand| return true if bool(ev(operand, env)) }
        false
      when "implies" then bool(ev(body[0], env)) ? bool(ev(body[1], env)) : true
      when "ite" then bool(ev(body[0], env)) ? ev(body[1], env) : ev(body[2], env)
      when "local" then env.locals.fetch(body)
      when "const" then @constants.fetch(body)
      when "let" then ev(body["body"], env.with_local(body["name"], ev(body["value"], env)))
      when "forall", "exists" then quantify(op == "forall", body, env)
      else composite(op, body, env)
      end
    end

    def quantify(all, body, env)
      values = if body.key?("in")
                 c = ev(body["in"], env)
                 case c
                 when SetValue then sorted(c.elem, c.items.to_a)
                 when MapValue then sorted(c.key, c.entries.keys)
                 else c.items
                 end
               else
                 domain(body["type"])
               end
      # 値を決める要素（forall では偽、exists では真）があればその値を返す。
      # 本体の評価の失敗は最初のものを保留して残りをたどり、値を決める要素がなければその失敗を伝える。
      pending = nil
      values.each do |x|
        begin
          holds = bool(ev(body["body"], env.with_local(body["name"], x)))
        rescue EvalError => e
          pending ||= e
          next
        end
        return holds if holds != all
      end
      raise pending if pending

      all
    end

    # 複合型の値を作る演算と、取り出す演算。部分式は左から順に評価する。
    def composite(op, body, env)
      case op
      when "tuple" then body.map { |e| ev(e, env) }
      when "record" then body.to_h { |f| [f["name"], ev(f["expr"], env)] }
      when "nth" then ev(body["of"], env)[body["index"]]
      when "field" then ev(body["of"], env)[body["name"]]
      when "none" then nil
      when "some" then Some.new(ev(body[0], env))
      when "is_some" then !ev(body[0], env).nil?
      when "is_none" then ev(body[0], env).nil?
      when "unwrap"
        x = ev(body[0], env)
        fail!("none") if x.nil?
        x.value
      when "set"
        items = body["items"].map { |e| element(body["of"], ev(e, env)) }
        SetValue.new(body["of"], items.to_set)
      when "map"
        body["items"].reduce(MapValue.new(body["key"], body["value"], {})) do |m, (k, v)|
          put(m, k, v, env)
        end
      when "list"
        ListValue.new(body["of"], body["max"], body["items"].map { |e| element(body["of"], ev(e, env)) })
      when "contains"
        c = ev(body[0], env)
        x = ev(body[1], env)
        c.items.include?(x)
      when "insert", "remove"
        s = ev(body[0], env)
        x = ev(body[1], env)
        op == "insert" ? SetValue.new(s.elem, s.items | [element(s.elem, x)]) : SetValue.new(s.elem, s.items - [x])
      when "union", "intersection", "difference", "subset"
        a = ev(body[0], env)
        b = ev(body[1], env)
        case op
        when "union" then SetValue.new(a.elem, a.items | b.items)
        when "intersection" then SetValue.new(a.elem, a.items & b.items)
        when "difference" then SetValue.new(a.elem, a.items - b.items)
        else a.items.subset?(b.items)
        end
      when "size", "is_empty"
        c = ev(body[0], env)
        n = c.is_a?(MapValue) ? c.entries.size : c.items.size
        op == "size" ? n : n.zero?
      when "has_key", "get"
        m = ev(body[0], env)
        k = ev(body[1], env)
        return m.entries.key?(k) if op == "has_key"

        fail!("missing_key") unless m.entries.key?(k)
        m.entries[k]
      when "put" then put(ev(body[0], env), body[1], body[2], env)
      when "delete"
        m = ev(body[0], env)
        k = ev(body[1], env)
        MapValue.new(m.key, m.value, m.entries.except(k))
      when "keys"
        m = ev(body[0], env)
        SetValue.new(m.key, m.entries.keys.to_set)
      when "at"
        l = ev(body[0], env)
        i = int(ev(body[1], env))
        fail!("index_out_of_range") unless i >= 0 && i < l.items.length
        l.items[i]
      when "first", "last"
        l = ev(body[0], env)
        fail!("empty") if l.items.empty?
        op == "first" ? l.items.first : l.items.last
      when "push"
        l = ev(body[0], env)
        x = element(l.elem, ev(body[1], env))
        fail!("full") if l.items.length >= l.max
        ListValue.new(l.elem, l.max, l.items + [x])
      when "pop", "shift"
        l = ev(body[0], env)
        fail!("empty") if l.items.empty?
        ListValue.new(l.elem, l.max, op == "pop" ? l.items[0...-1] : l.items[1..])
      else raise ArgumentError, "未知の演算子 #{op}"
      end
    end

    # キーを評価して検査し、値を評価して検査してから置く。
    def put(map, key_node, value_node, env)
      k = element(map.key, ev(key_node, env))
      v = element(map.value, ev(value_node, env))
      MapValue.new(map.key, map.value, map.entries.merge(k => v))
    end

    # ---- 遷移（仕様書 §5.1）----

    # 型の範囲を検査して値を格納する。複合型では、整数の部分の範囲を、スロットの順に検査する。
    def store(type, value)
      return value if member?(type, value)
      if %w[bool int enum].include?(type.keys.first)
        raise EvalError, { "kind" => "type_mismatch" } unless type.key?("int") && value.is_a?(Integer)

        raise EvalError, { "kind" => "out_of_range", "value" => value, "type" => type }
      end
      x, int_type, slot = out_of_range(type, value, 0)
      raise EvalError.new({ "kind" => "out_of_range", "value" => x, "type" => int_type }, slot)
    end

    # 型の範囲の外にある最初の整数を、[値, 整数の型, スロットの位置] で返す。
    def out_of_range(type, value, at)
      kind, body = type.first
      found = lambda do |parts|
        parts.each do |t, v, offset|
          bad = out_of_range(t, v, offset)
          return bad if bad
        end
        nil
      end
      case kind
      when "int" then value.between?(body["min"], body["max"]) ? nil : [value, type, at]
      when "tuple"
        offsets = body.each_with_index.map { |_, i| at + body.take(i).sum { |t| width(t) } }
        found.call(body.each_with_index.map { |t, i| [t, value[i], offsets[i]] })
      when "record"
        types = body.map { |f| f["type"] }
        found.call(body.each_with_index.map do |f, i|
          [f["type"], value[f["name"]], at + types.take(i).sum { |t| width(t) }]
        end)
      when "option" then value.nil? ? nil : out_of_range(body, value.value, at + 1)
      when "map"
        w = width(body["value"])
        parts = domain(body["key"]).each_with_index.filter_map do |k, i|
          [body["value"], value.entries[k], at + i * (1 + w) + 1] if value.entries.key?(k)
        end
        found.call(parts)
      when "list"
        w = width(body["of"])
        found.call(value.items.each_with_index.map { |v, p| [body["of"], v, at + 1 + p * w] })
      end
    end

    def failing(action, params, choices, site, target = nil)
      yield
    rescue EvalError => e
      property = {
        "action" => action["name"],
        "args" => json_bindings(action["params"], params),
        "choices" => json_bindings(action["choices"], choices),
        "site" => site,
        "error" => e.detail
      }
      if target
        property["target"] = @states[target]["name"]
        property["slot"] = e.slot if e.slot && width(@states[target]["type"]) > 1
      end
      raise StepError, property
    end

    # 操作を適用する。guard が偽なら nil、有効なら [次状態, 出力]。
    def step(action, params, choices, state)
      env = Env.new(state, params, choices, nil, nil)
      enabled = failing(action, params, choices, "guard") do
        in_domain?(action, params, choices, env) && (action["guard"] ? bool(ev(action["guard"], env)) : true)
      end
      return nil unless enabled

      nxt = state.dup
      (action["updates"] || []).each do |update|
        target = update["target"]
        failing(action, params, choices, "update", target) do
          nxt[target] = store(@states[target]["type"], ev(update["expr"], env))
        end
      end
      output = nil
      if action["output"]
        failing(action, params, choices, "output") do
          output = store(action["output"]["type"], ev(action["output"]["expr"], env))
        end
      end
      [nxt, output]
    end

    # 動的ドメイン（`in`）。引数を宣言順に調べ、ドメインの式の値に含まれなければ偽。
    def in_domain?(action, params, choices, env)
      bindings = (action["params"] || []).zip(params) + (action["choices"] || []).zip(choices)
      bindings.all? do |b, value|
        next true unless b["in"]

        domain = ev(b["in"], env)
        domain.items.include?(value)
      end
    end

    def tuples(bindings)
      (bindings || []).map { |b| domain(b["type"]) }.reduce([[]]) do |acc, values|
        acc.flat_map { |prefix| values.map { |v| prefix + [v] } }
      end
    end

    # 状態での操作の有効な遷移を、引数の辞書順に並べる。評価エラーがあれば StepError。
    def transitions(action, state)
      n_params = (action["params"] || []).length
      tuples((action["params"] || []) + (action["choices"] || [])).filter_map do |args|
        params = args.take(n_params)
        choices = args.drop(n_params)
        result = step(action, params, choices, state)
        result && { "params" => params, "choices" => choices, "state" => result[0], "output" => result[1] }
      end
    end

    # ---- 性質 ----

    def prop(node, env)
      bool(ev(node, env))
    end

    # 真でない最初の不変条件を [名前, false または EvalError] で返す。
    def failing_invariant(state, cond)
      @invariants.each do |inv|
        next unless cond[:invariants].include?(inv["name"])

        begin
          return [inv["name"], false] unless prop(inv["expr"], Env.new(state, nil, nil, nil, nil))
        rescue EvalError => e
          return [inv["name"], e]
        end
      end
      nil
    end

    def failing_contract(action, state, transition, cond)
      @contracts.each do |con|
        next unless con["action"] == action["name"] && cond[:contracts].include?(con["name"])

        env = Env.new(state, transition["params"], transition["choices"], transition["state"], transition["output"])
        begin
          return [con["name"], false] unless prop(con["expr"], env)
        rescue EvalError => e
          return [con["name"], e]
        end
      end
      nil
    end

    def terminal?(state)
      @terminal ? prop(@terminal, Env.new(state, nil, nil, nil, nil)) : false
    end

    def property(kind, name, value)
      if value == false
        { "violation" => kind, "name" => name }
      else
        { "error" => value.detail, "site" => kind, "name" => name }
      end
    end

    def conditions(actions: nil, invariants: nil, contracts: nil, deadlock: false)
      {
        actions: actions || @actions.map { |a| a["name"] },
        invariants: invariants || @invariants.map { |i| i["name"] },
        contracts: contracts || @contracts.map { |c| c["name"] },
        deadlock: deadlock
      }
    end

    def json_step(action, transition)
      {
        "action" => action["name"],
        "args" => json_bindings(action["params"], transition["params"]),
        "choices" => json_bindings(action["choices"], transition["choices"]),
        "output" => json_output(action, transition["output"]),
        "state" => json_state(transition["state"])
      }
    end

    # ---- 幅優先探索（仕様書 §8.1）----

    # `max_depth` は深さ（初期状態からの遷移数）の上限。上限の深さの状態からの遷移が、未訪問の状態に至るか、
    # 遷移契約を満たさない（トレースが上限を超える）ときは、報告せずに探索を続け、最後に未完了とする。
    def check(max_states: nil, max_depth: nil, **options)
      cond = conditions(**options)
      parents = {}
      depth = {}
      truncated = false
      # 開始状態と、そこからのステップ。
      path = lambda do |state|
        steps = []
        while (edge = parents[state])
          steps.unshift(edge[1])
          state = edge[0]
        end
        [state, steps]
      end
      found = lambda do |prop, (start, steps)|
        { "status" => prop.key?("violation") ? "violated" : "error", "property" => prop,
          "initial" => json_state(start), "steps" => steps, "visited_states" => parents.size }
      end

      queue = []
      initials.each do |init|
        next if parents.key?(init)
        if max_states && parents.size >= max_states
          return { "status" => "inconclusive", "reason" => "max_states", "visited_states" => parents.size }
        end

        parents[init] = nil
        depth[init] = 0
        if (bad = failing_invariant(init, cond))
          return found.call(property("invariant", *bad), [init, []])
        end

        queue << init
      end
      until queue.empty?
        current = queue.shift
        enabled = false
        at_limit = max_depth && depth[current] >= max_depth
        @actions.each do |action|
          next unless cond[:actions].include?(action["name"])

          begin
            successors = transitions(action, current)
          rescue StepError => e
            return found.call(e.property, path.call(current))
          end
          successors.each do |transition|
            enabled = true
            edge = json_step(action, transition)
            if (bad = failing_contract(action, current, transition, cond))
              if at_limit
                truncated = true
                next
              end
              start, steps = path.call(current)
              return found.call(property("contract", *bad), [start, steps + [edge]])
            end
            nxt = transition["state"]
            next if parents.key?(nxt)
            if at_limit
              truncated = true
              next
            end
            if max_states && parents.size >= max_states
              return { "status" => "inconclusive", "reason" => "max_states", "visited_states" => parents.size }
            end

            parents[nxt] = [current, edge]
            depth[nxt] = depth[current] + 1
            if (bad = failing_invariant(nxt, cond))
              return found.call(property("invariant", *bad), path.call(nxt))
            end
            queue << nxt
          end
        end
        next unless cond[:deadlock] && !enabled

        begin
          return found.call({ "violation" => "deadlock" }, path.call(current)) unless terminal?(current)
        rescue EvalError => e
          return found.call({ "error" => e.detail, "site" => "terminal" }, path.call(current))
        end
      end

      return { "status" => "inconclusive", "reason" => "max_depth", "visited_states" => parents.size } if truncated

      states = sort_states(parents.keys)
      { "status" => "verified", "visited_states" => states.length,
        "certificate" => states.map { |s| s.each_with_index.map { |v, i| json_value(@states[i]["type"], v) } } }
    end

    # ---- ランダムシミュレーション（仕様書 §9）----

    # SplitMix64。エンジンと同じ乱数列を作る。
    class SplitMix64
      MASK = 2**64 - 1

      def initialize(seed)
        @state = seed
      end

      def next
        @state = (@state + 0x9E3779B97F4A7C15) & MASK
        z = @state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        z ^ (z >> 31)
      end

      # 0...n の一様な整数。剰余の偏りは、棄却して取り除く。
      def below(n)
        threshold = (2**64) % n
        loop do
          x = self.next
          return x % n if x >= threshold
        end
      end
    end

    def simulate(seed: 0, traces: 100, max_steps: 100, **options)
      cond = conditions(**options)
      rng = SplitMix64.new(seed)
      completed = 0
      total = 0
      start = nil
      found = lambda do |prop, steps|
        { "status" => prop.key?("violation") ? "violated" : "error", "property" => prop,
          "initial" => json_state(start), "steps" => steps, "completed_traces" => completed, "total_steps" => total }
      end
      traces.times do
        # 初期状態が1つなら乱数を消費しない。
        start = initials.length > 1 ? initials[rng.below(initials.length)] : initials[0]
        state = start
        steps = []
        if (bad = failing_invariant(state, cond))
          return found.call(property("invariant", *bad), steps)
        end
        max_steps.times do
          enabled = []
          @actions.each do |action|
            next unless cond[:actions].include?(action["name"])

            begin
              transitions(action, state).each { |t| enabled << [action, t] }
            rescue StepError => e
              return found.call(e.property, steps)
            end
          end
          if enabled.empty?
            if cond[:deadlock]
              begin
                return found.call({ "violation" => "deadlock" }, steps) unless terminal?(state)
              rescue EvalError => e
                return found.call({ "error" => e.detail, "site" => "terminal" }, steps)
              end
            end
            break
          end
          action, transition = enabled[rng.below(enabled.length)]
          total += 1
          steps += [json_step(action, transition)]
          if (bad = failing_contract(action, state, transition, cond))
            return found.call(property("contract", *bad), steps)
          end
          state = transition["state"]
          if (bad = failing_invariant(state, cond))
            return found.call(property("invariant", *bad), steps)
          end
        end
        completed += 1
      end
      { "status" => "sampled", "completed_traces" => completed, "total_steps" => total }
    end

    # ---- 適合性検査の候補集合（仕様書 §12.2）----

    def action_named(name) = @actions.find { |a| a["name"] == name }

    # 遷移の入力。[操作名, 公開引数, 注入する選択の値]。
    # `injected` は、操作名から、注入する内部選択の添字の配列への Hash。
    def input_of(action, transition, injected)
      [action["name"], transition["params"], (injected[action["name"]] || []).map { |i| transition["choices"][i] }]
    end

    # 状態で有効な入力。
    def enabled_inputs(state, cond, injected = {})
      @actions.flat_map do |action|
        next [] unless cond[:actions].include?(action["name"])

        transitions(action, state).map { |t| input_of(action, t, injected) }.uniq
      end
    end

    # 全候補で有効な入力。
    def common_inputs(candidates, cond, injected = {})
      candidates.map { |state| enabled_inputs(state, cond, injected) }.reduce { |kept, inputs| kept & inputs } || []
    end

    # 実装の応答で候補集合を更新する。
    # Cnext = { t | exists s in C, k, r: T(s, (a, k, r), t) and output_matches(r, y) and obs(t) = x }
    # `input` は input_of の形で、注入した選択の値と一致する遷移だけを考える。
    # `observed` は観測する状態変数の添字、`seen` はその値。出力を宣言しない操作では、戻り値を比べない。
    def next_candidates(candidates, input, output, observed, seen, injected = {})
      action = action_named(input[0])
      candidates.flat_map do |state|
        transitions(action, state).filter_map do |t|
          next unless input_of(action, t, injected) == input
          next unless action["output"].nil? || t["output"] == output
          next unless observed.map { |i| t["state"][i] } == seen

          t["state"]
        end
      end.uniq
    end

    # ---- 証明書の検査（仕様書 §14.2）----

    # 証明書（状態の配列）を検査する。受理なら nil、拒否なら理由の名前を返す。
    def reject_certificate(states, **options)
      cond = conditions(**options)
      members = states.to_set
      return "missing_initial" unless initials.all? { |init| members.include?(init) }

      sort_states(members.to_a).each do |state|
        typed = state.length == @states.length && state.each_with_index.all? { |v, i| member?(@states[i]["type"], v) }
        return "ill_typed_state" unless typed
        return "invariant_not_held" if failing_invariant(state, cond)

        enabled = false
        @actions.each do |action|
          next unless cond[:actions].include?(action["name"])

          begin
            successors = transitions(action, state)
          rescue StepError
            return "step_failed"
          end
          successors.each do |transition|
            enabled = true
            return "missing_successor" unless members.include?(transition["state"])
            return "contract_not_held" if failing_contract(action, state, transition, cond)
          end
        end
        next unless cond[:deadlock] && !enabled

        begin
          return "deadlock" unless terminal?(state)
        rescue EvalError
          return "deadlock"
        end
      end
      nil
    end

    # JSONの値の配列で書かれた状態を、参照実装の値に戻す。
    def state_from_json(row)
      row.each_with_index.map { |v, i| from_json(@states[i]["type"], v) }
    end
  end

  def self.load(path)
    Model.new(JSON.parse(File.read(path, encoding: Encoding::UTF_8)))
  end
end
