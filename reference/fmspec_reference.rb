# frozen_string_literal: true

# fmspec の参照実装（仕様書 §3、§14.3）。
#
# IR のJSONを直接解釈する、小さな Evaluator、幅優先探索、証明書検査器である。
# Rust の実装とは独立に書いてあり、比較テストで両者の結果を突き合わせる。
# 速度や診断は考えない。入力は整形式のIRとし、IR検証は行わない。
#
# 結果は `fmspec check --json` と同じ形のHashで返す（比較に使う項目だけ）。
require "json"
require "set"

module FmspecReference
  I64 = (-(2**63))..(2**63 - 1)

  # 列挙型の値。型名とラベルで持つ。
  EnumValue = Struct.new(:type, :label)

  # 式の評価、または状態・出力の更新の失敗。
  class EvalError < StandardError
    attr_reader :detail

    def initialize(detail)
      @detail = detail
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

  Env = Struct.new(:pre, :params, :choices, :post, :output)

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
    end

    # ---- 値 ----

    def literal(node)
      kind, body = node.first
      kind == "enum" ? EnumValue.new(body["type"], body["variant"]) : body
    end

    def initial
      @states.map { |s| literal(s["initial"]) }
    end

    # 型に属する値を、列挙の順に並べる。
    def domain(type)
      kind, body = type.first
      case kind
      when "bool" then [false, true]
      when "int" then (body["min"]..body["max"]).to_a
      when "enum" then @enums.fetch(body).map { |label| EnumValue.new(body, label) }
      end
    end

    def member?(type, value)
      kind, body = type.first
      case kind
      when "bool" then [true, false].include?(value)
      when "int" then value.is_a?(Integer) && value.between?(body["min"], body["max"])
      when "enum" then value.is_a?(EnumValue) && value.type == body && @enums.fetch(body).include?(value.label)
      end
    end

    # 状態の整列に使う符号。Bool は 0/1、Enum はラベルの添字。
    def code(value)
      case value
      when true then 1
      when false then 0
      when EnumValue then @enums.fetch(value.type).index(value.label)
      else value
      end
    end

    def sort_states(states)
      states.sort_by { |s| s.map { |v| code(v) } }
    end

    def json_value(value)
      value.is_a?(EnumValue) ? value.label : value
    end

    def json_state(state)
      @states.each_with_index.to_h { |s, i| [s["name"], json_value(state[i])] }
    end

    def json_bindings(bindings, values)
      (bindings || []).each_with_index.to_h { |b, i| [b["name"], json_value(values[i])] }
    end

    def json_output(action, output)
      action["output"] ? { "value" => json_value(output) } : { "unit" => true }
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

    def same_kind(left, right)
      same = if left.is_a?(EnumValue) || right.is_a?(EnumValue)
               left.is_a?(EnumValue) && right.is_a?(EnumValue) && left.type == right.type
             else
               left.is_a?(Integer) == right.is_a?(Integer)
             end
      raise EvalError, { "kind" => "type_mismatch" } unless same
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
      else raise ArgumentError, "未知の演算子 #{op}"
      end
    end

    # ---- 遷移（仕様書 §5.1）----

    # 型の範囲を検査して値を格納する。
    def store(type, value)
      return value if member?(type, value)
      raise EvalError, { "kind" => "type_mismatch" } unless type.key?("int") && value.is_a?(Integer)

      raise EvalError, { "kind" => "out_of_range", "value" => value, "type" => type }
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
      property["target"] = target if target
      raise StepError, property
    end

    # 操作を適用する。guard が偽なら nil、有効なら [次状態, 出力]。
    def step(action, params, choices, state)
      env = Env.new(state, params, choices, nil, nil)
      enabled = failing(action, params, choices, "guard") do
        action["guard"] ? bool(ev(action["guard"], env)) : true
      end
      return nil unless enabled

      nxt = state.dup
      (action["updates"] || []).each do |update|
        target = update["target"]
        failing(action, params, choices, "update", @states[target]["name"]) do
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

    def check(max_states: nil, **options)
      cond = conditions(**options)
      init = initial
      parents = { init => nil }
      path = lambda do |state|
        steps = []
        while (edge = parents[state])
          steps.unshift(edge[1])
          state = edge[0]
        end
        steps
      end
      found = lambda do |prop, steps|
        { "status" => prop.key?("violation") ? "violated" : "error", "property" => prop, "steps" => steps,
          "visited_states" => parents.size }
      end

      if (bad = failing_invariant(init, cond))
        return found.call(property("invariant", *bad), [])
      end

      queue = [init]
      until queue.empty?
        current = queue.shift
        enabled = false
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
              return found.call(property("contract", *bad), path.call(current) + [edge])
            end
            nxt = transition["state"]
            next if parents.key?(nxt)
            if max_states && parents.size >= max_states
              return { "status" => "inconclusive", "reason" => "max_states", "visited_states" => parents.size }
            end

            parents[nxt] = [current, edge]
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

      states = sort_states(parents.keys)
      { "status" => "verified", "visited_states" => states.length,
        "certificate" => states.map { |s| s.map { |v| json_value(v) } } }
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
      found = lambda do |prop, steps|
        { "status" => prop.key?("violation") ? "violated" : "error", "property" => prop, "steps" => steps,
          "completed_traces" => completed, "total_steps" => total }
      end
      traces.times do
        state = initial
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

    # ---- 証明書の検査（仕様書 §14.2）----

    # 証明書（状態の配列）を検査する。受理なら nil、拒否なら理由の名前を返す。
    def reject_certificate(states, **options)
      cond = conditions(**options)
      members = states.to_set
      return "missing_initial" unless members.include?(initial)

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
      row.each_with_index.map do |v, i|
        type = @states[i]["type"]
        type.key?("enum") ? EnumValue.new(type["enum"], v) : v
      end
    end
  end

  def self.load(path)
    Model.new(JSON.parse(File.read(path)))
  end
end
