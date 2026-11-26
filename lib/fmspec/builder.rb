# frozen_string_literal: true

module Fmspec
  # 記号的な状態。状態変数と定数を名前で参照すると、記号式になる。実際の Ruby オブジェクトではない。
  class StateRef < BasicObject
    def initialize(builder, ref)
      @builder = builder
      @ref = ref
    end

    def method_missing(name, *args, &block)
      unless args.empty? && block.nil?
        ::Kernel.raise ::Fmspec::BuildError, "状態の参照 #{name} に引数は渡せません"
      end

      @builder.reference(name, @ref)
    end

    def respond_to_missing?(*) = true
    def inspect = "#<Fmspec::StateRef>"
  end

  # `Fmspec.define` のブロックの中の語彙。
  class Builder
    include Functions

    attr_reader :enums, :states

    def initialize(name)
      @name = name
      @enums = {}
      @states = []
      @constants = {}
      @actions = []
      @invariants = []
      @contracts = []
      @terminal = nil
      @names = {}
    end

    # ---- 型 ----

    # 列挙型を宣言する。`color = enum(:color, :red, :green)`。同じ宣言を繰り返すと、同じ型を返す。
    def enum(name, *labels)
      type = Types::Enum.new(name.to_sym, labels.flatten)
      known = @enums[type.name]
      raise BuildError, "列挙型 #{name} は、別のラベルで宣言済みです" if known && known != type

      @enums[type.name] = type
    end

    # ---- 宣言 ----

    # 状態変数。`state :sold, int(0..4), initial: 0`。
    def state(name, type, initial:)
      claim(name, "状態変数")
      type = Types.coerce(type, "状態変数 #{name}")
      value = type.literal(initial)
      if type.is_a?(Types::Int) && !value.between?(type.min, type.max)
        raise BuildError, "状態変数 #{name} の初期値 #{value} が #{type} の範囲外です"
      end

      @states << { name: name.to_sym, type: type, initial: value, source: source_of(caller_locations(1, 1)) }
      nil
    end

    # Ghost State（仕様書 §12.3）。履歴を記録する有限の補助状態で、モデルの上では普通の状態変数である。
    # 実装との照合では、実際の外部イベント（fake が記録した呼び出しなど）から観測する。
    def ghost(name, type, initial:)
      state(name, type, initial: initial)
      @states.last[:ghost] = true
      nil
    end

    # 定数。記号的な状態から、状態変数と同じように名前で参照できる。
    def constant(name, value)
      claim(name, "定数")
      @constants[name.to_sym] = Expr.lift(value, enums: declared_enums)
      nil
    end

    # 操作。キーワードは公開引数で、値はそのドメイン（型、または整数の範囲）。
    # ブロックは、記号的な状態と各引数を受け取る。
    def action(name, **params, &block)
      raise BuildError, "操作 #{name} にはブロックが必要です" unless block

      claim(name, "操作", :action)
      Lint.check!(block, "操作 #{name}")
      builder = ActionBuilder.new(self, name.to_sym, params, source_of(caller_locations(1, 1)))
      action, contracts = builder.build(&block)
      @actions << action
      @contracts.concat(contracts)
      nil
    end

    # 状態不変条件。ブロックは記号的な状態を受け取り、Bool の式を返す。
    def invariant(name, &block)
      raise BuildError, "不変条件 #{name} にはブロックが必要です" unless block

      claim(name, "不変条件", :invariant)
      Lint.check!(block, "不変条件 #{name}")
      expr = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "不変条件 #{name}")
      @invariants << { "name" => name.to_s, "expr" => expr.node, "source" => source_of(caller_locations(1, 1)) }
      nil
    end

    # 終端条件。真になる状態は、有効な遷移がなくてもデッドロックとみなさない。
    def terminal(&block)
      raise BuildError, "terminal にはブロックが必要です" unless block
      raise BuildError, "terminal は1つだけ書けます" if @terminal

      Lint.check!(block, "terminal")
      @terminal = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "terminal").node
      nil
    end

    # ---- 組み立て ----

    # 名前を、状態変数（`ref` は "var" か "next"）または定数の式にする。
    def reference(name, ref)
      index = @states.index { |s| s[:name] == name }
      return Expr.new({ ref => index }, @states[index][:type].kind) if index
      return @constants[name] if @constants.key?(name)

      raise BuildError, "未定義の状態変数または定数です: #{name}"
    end

    def state_index(name)
      @states.index { |s| s[:name] == name.to_sym } or raise BuildError, "未定義の状態変数です: #{name}"
    end

    def claim_contract(name)
      claim(name, "遷移契約", :contract)
    end

    def build
      Model.new(@name.to_sym, to_ir, ghosts: @states.select { |s| s[:ghost] }.map { |s| s[:name] })
    end

    def declared_enums = @enums.values

    private

    def to_ir
      ir = {
        "ir_version" => 1,
        "name" => @name.to_s,
        "enums" => @enums.values.map { |e| { "name" => e.name.to_s, "variants" => e.labels.map(&:to_s) } },
        "states" => @states.each_with_index.map do |s, i|
          { "id" => i, "name" => s[:name].to_s, "type" => s[:type].to_ir,
            "initial" => Expr.lift(s[:initial], s[:type].kind).node, "source" => s[:source] }
        end,
        "actions" => @actions,
        "invariants" => @invariants,
        "contracts" => @contracts
      }
      ir["terminal"] = @terminal if @terminal
      ir
    end

    # 名前の重複を拒否する。状態変数と定数は同じ名前空間で、操作、不変条件、遷移契約はそれぞれ別。
    def claim(name, what, space = :value)
      raise BuildError, "#{what}の名前は Symbol か String で書きます: #{name.inspect}" unless name.is_a?(Symbol) || name.is_a?(String)

      key = [space, name.to_sym]
      raise BuildError, "#{what} #{name} は、#{@names[key]}として定義済みです" if @names.key?(key)

      @names[key] = what
    end

    def source_of(locations)
      location = locations&.first
      location && { "file" => location.path, "line" => location.lineno }
    end
  end

  # 操作のブロックの中の語彙。
  class ActionBuilder
    include Functions

    Branch = Struct.new(:updates, :output)

    def initialize(model, name, params, source)
      @model = model
      @name = name
      @source = source
      @params = params.map { |param, domain| [param.to_sym, Types.coerce(domain, "操作 #{name} の引数 #{param}")] }
      @choices = []
      @guards = []
      @always = Branch.new({}, nil)
      @accept = nil
      @reject = nil
      @condition = nil
      @branch = @always
      @ensures = []
    end

    # 操作のブロックを実行し、IRの操作と遷移契約を返す。
    def build(&block)
      unless block.arity.negative? || block.arity == @params.length + 1
        names = ["s", *@params.map(&:first)].join(", ")
        raise BuildError, "操作 #{@name} のブロックは |#{names}| を受け取ります"
      end

      state = StateRef.new(@model, "var")
      args = @params.each_with_index.map { |(_, type), i| Expr.new({ "param" => i }, type.kind) }
      instance_exec(state, *args, &block)
      updates, output = merge
      action = {
        "name" => @name.to_s,
        "params" => bindings(@params),
        "choices" => bindings(@choices),
        "guard" => guard_node,
        "updates" => updates.map { |target, expr| { "target" => target, "expr" => expr.node } },
        "source" => @source
      }
      action["output"] = { "type" => output[1].to_ir, "expr" => output[0].node } if output
      [action, contracts(output)]
    end

    # 列挙型。仕様の定義の `enum` と同じで、宣言済みの型を返す。
    def enum(name, *labels) = @model.enum(name, *labels)

    # 遷移の有効性。複数書くと、すべてが真のときに有効になる。
    def guard(condition)
      top_level!("guard")
      @guards << lift(condition).expect(:bool, "操作 #{@name} の guard")
      nil
    end

    # 状態更新。同時代入で、書かれていない変数は維持する。式は遷移前の状態で評価する。
    def update(**assignments)
      assignments.each do |name, value|
        target = @model.state_index(name)
        type = @model.states[target][:type]
        raise BuildError, "操作 #{@name}: #{name} への代入が重複しています" if @branch.updates.key?(target)

        @branch.updates[target] = lift(value, type.kind).expect(type.kind, "操作 #{@name} の #{name} の更新")
      end
      nil
    end

    # 状態を変えないことを明示する。
    def unchanged
      nil
    end

    # 内部選択を宣言し、その値を表す式を返す。`allowed = choose(:allowed, bool)`。
    def choose(name, domain)
      top_level!("choose")
      taken = (@params + @choices).any? { |n, _| n == name.to_sym }
      raise BuildError, "操作 #{@name}: 引数 #{name} は定義済みです" if taken

      type = Types.coerce(domain, "操作 #{@name} の内部選択 #{name}")
      @choices << [name.to_sym, type]
      Expr.new({ "choice" => @choices.length - 1 }, type.kind)
    end

    # 出力。型を省略すると、式から決める（整数は範囲なし）。
    def returns(value, type = nil)
      raise BuildError, "操作 #{@name}: returns が重複しています" if @branch.output

      type &&= Types.coerce(type, "操作 #{@name} の出力")
      expr = lift(value, type&.kind)
      type ||= output_type(expr)
      @branch.output = [expr.expect(type.kind, "操作 #{@name} の出力"), type]
      nil
    end

    # 業務上の受理条件。on_accept と on_reject で、受理と拒否それぞれの更新と出力を書く。
    # 拒否も有効な遷移であり、guard のように遷移を無効にはしない（仕様書 §5.2、§12.1）。
    def accept_if(condition)
      top_level!("accept_if")
      raise BuildError, "操作 #{@name}: accept_if は1つだけ書けます" if @condition

      @condition = lift(condition).expect(:bool, "操作 #{@name} の accept_if")
      nil
    end

    def on_accept(&block)
      @accept = branch("on_accept", @accept, &block)
      nil
    end

    def on_reject(&block)
      @reject = branch("on_reject", @reject, &block)
      nil
    end

    # 遷移契約。この操作のすべての有効な遷移で成り立つべき事後条件。
    # ブロックは、遷移後の記号的な状態と、出力（宣言していれば）を受け取る。
    # 遷移前の状態と引数は、操作のブロックの変数をそのまま使う。
    def ensures(name, &block)
      top_level!("ensures")
      raise BuildError, "操作 #{@name} の ensures #{name} にはブロックが必要です" unless block

      @model.claim_contract(name)
      Lint.check!(block, "遷移契約 #{name}")
      location = caller_locations(1, 1)&.first
      @ensures << [name, block, location && { "file" => location.path, "line" => location.lineno }]
      nil
    end

    # 指定した状態変数が、この操作で変わらないことを遷移契約にする。
    def preserves(*names)
      top_level!("preserves")
      location = caller_locations(1, 1)&.first
      source = location && { "file" => location.path, "line" => location.lineno }
      names.each do |name|
        index = @model.state_index(name)
        kind = @model.states[index][:type].kind
        contract = :"#{@name}_preserves_#{name}"
        @model.claim_contract(contract)
        unchanged = Expr.new({ "next" => index }, kind).eq(Expr.new({ "var" => index }, kind))
        @ensures << [contract, nil, source, unchanged]
      end
      nil
    end

    private

    def declared_enums = @model.declared_enums

    def top_level!(what)
      return if @branch.equal?(@always)

      raise BuildError, "操作 #{@name}: #{what} は on_accept と on_reject の外に書きます"
    end

    def branch(what, existing, &block)
      top_level!(what)
      raise BuildError, "操作 #{@name}: #{what} にはブロックが必要です" unless block
      raise BuildError, "操作 #{@name}: #{what} は1つだけ書けます" if existing
      raise BuildError, "操作 #{@name}: #{what} の前に accept_if を書きます" unless @condition

      Lint.check!(block, "操作 #{@name} の #{what}")
      @branch = Branch.new({}, nil)
      block.call
      @branch
    ensure
      @branch = @always
    end

    def output_type(expr)
      case expr.kind
      when :int then Types::ANY_INT
      when :bool then Types::BOOL
      else expr.kind
      end
    end

    def bindings(list)
      list.map { |name, type| { "name" => name.to_s, "type" => type.to_ir } }
    end

    def guard_node
      case @guards.length
      when 0 then { "bool" => true }
      when 1 then @guards[0].node
      else { "all" => @guards.map(&:node) }
      end
    end

    # 受理と拒否の更新と出力を、受理条件による条件式にまとめる。
    def merge
      updates = @always.updates.dup
      output = @always.output
      return [updates, output] unless @condition

      accept = @accept || Branch.new({}, nil)
      reject = @reject || Branch.new({}, nil)
      (accept.updates.keys | reject.updates.keys).each do |target|
        name = @model.states[target][:name]
        raise BuildError, "操作 #{@name}: #{name} への代入が重複しています" if updates.key?(target)

        current = Expr.new({ "var" => target }, @model.states[target][:type].kind)
        updates[target] = ite(@condition, accept.updates[target] || current, reject.updates[target] || current)
      end
      if accept.output || reject.output
        raise BuildError, "操作 #{@name}: returns は on_accept と on_reject の両方に書きます" unless accept.output && reject.output
        raise BuildError, "操作 #{@name}: returns が重複しています" if output
        unless accept.output[1].kind == reject.output[1].kind
          raise BuildError, "操作 #{@name}: on_accept と on_reject の出力の型が合いません"
        end

        type = [accept.output[1], reject.output[1]].find { |t| t != Types::ANY_INT } || Types::ANY_INT
        output = [ite(@condition, accept.output[0], reject.output[0]), type]
      end
      [updates, output]
    end

    def contracts(output)
      after = StateRef.new(@model, "next")
      result = output && Expr.new({ "output" => {} }, output[1].kind)
      @ensures.map do |name, block, source, fixed|
        expr = fixed || lift(block.call(after, result)).expect(:bool, "遷移契約 #{name}")
        { "name" => name.to_s, "action" => @name.to_s, "expr" => expr.node, "source" => source }
      end
    end
  end
end
