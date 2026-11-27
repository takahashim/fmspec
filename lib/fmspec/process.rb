# frozen_string_literal: true

module Fmspec
  # 並行するプロセス（仕様書 §12.4）。`Builder#process` が使う。
  #
  # プロセスのインスタンスごとに、プログラムカウンタとローカル変数を状態変数として加え、
  # 各ステップを1つの操作に展開する（仕様書 §12.6）。ステップは atomic で、ステップのインターリーブを列挙する。
  #
  # - プログラムカウンタ `プロセス[i].pc` は、ステップの名前と `:done` をラベルに持つ列挙型 `プロセス.pc` の値である。
  #   最初のステップから始まる。
  # - ローカル変数 `プロセス[i].名前` は、そのインスタンスのステップからだけ名前で参照、更新できる。
  # - ステップ `プロセス[i].名前` は、プログラムカウンタがそのステップのときだけ有効になる。
  #   実行すると、プログラムカウンタは次のステップ（最後のステップなら `:done`）に進む。`goto` で行き先を変えられる。
  module Process
    # 仕様の定義の `process` のブロックの中の語彙。インスタンスごとに、インスタンスの番号を渡して実行する。
    class Body
      include Functions

      attr_reader :locals, :steps

      def initialize(model, name)
        @model = model
        @name = name
        @locals = []
        @steps = []
      end

      # ローカル変数。`state` と同じく、initial か initial_in のどちらか一方を書く。
      def local(name, type, **initial)
        name = name.to_sym
        raise BuildError, "プロセス #{@name}: ローカル変数の名前 #{name} は予約されています" if %i[pc done].include?(name)
        raise BuildError, "プロセス #{@name}: ローカル変数 #{name} は定義済みです" if @locals.any? { |l| l[0] == name }
        if @model.defined?(name)
          raise BuildError, "プロセス #{@name}: ローカル変数 #{name} は、状態変数または定数と同じ名前です"
        end

        @locals << [name, type, initial, caller_locations(1, 1)]
        nil
      end

      # atomic なステップ。ブロックは記号的な状態を受け取り、`action` のブロックと同じ語彙（guard、update、choose、
      # returns、accept_if、ensures など）に加えて、`goto` を使える。公開引数は持たない。
      def step(name, &block)
        raise BuildError, "プロセス #{@name} のステップ #{name} にはブロックが必要です" unless block

        name = name.to_sym
        raise BuildError, "プロセス #{@name}: ステップの名前 done は予約されています" if name == :done
        raise BuildError, "プロセス #{@name}: ステップ #{name} は定義済みです" if @steps.any? { |s| s[0] == name }

        Lint.check!(block, "プロセス #{@name} のステップ #{name}", statements: :effect)
        @steps << [name, block, caller_locations(1, 1)&.first]
        nil
      end

      def enum(name, *labels) = @model.enum(name, *labels)

      private

      def declared_enums = @model.declared_enums
    end

    # ステップのブロックから見た名前の解決。ローカル変数とプログラムカウンタを、インスタンスの状態変数にする。
    class Scope
      attr_reader :prefix

      def initialize(model, prefix, locals)
        @model = model
        @prefix = prefix
        @locals = locals
      end

      def states = @model.states
      def declared_enums = @model.declared_enums
      def enum(name, *labels) = @model.enum(name, *labels)

      def reference(name, ref)
        return @model.reference(:"#{@prefix}.#{name}", ref) if local?(name)

        @model.reference(name, ref)
      end

      def state_index(name)
        raise BuildError, "プログラムカウンタは update では変えられません。goto を使います" if name.to_sym == :pc

        @model.state_index(local?(name) ? :"#{@prefix}.#{name}" : name)
      end

      def claim_contract(name) = @model.claim_contract(qualify(name))

      # 遷移契約の名前に、インスタンスの接頭辞を付ける。
      def qualify(name)
        name = name.to_s
        name.start_with?("#{@prefix}.") ? name : "#{@prefix}.#{name}"
      end

      private

      def local?(name) = name.to_sym == :pc || @locals.include?(name.to_sym)
    end

    # ステップのブロックの中の語彙。`action` の語彙に `goto` を加える。
    class StepBuilder < ActionBuilder
      def initialize(scope, name, source, pc, following)
        super(scope, name, {}, source)
        @pc = pc
        @following = following
        # [行き先, 条件（なければ nil）] の列。書いた順に並べる。
        @gotos = []
      end

      # 次に実行するステップを変える。条件を渡すと、条件が真のときだけ変える。
      # 複数書くと、書いた順に条件を調べ、最初に真になった goto の行き先に進む。どれも偽なら次のステップに進む。
      # 条件のない goto は「それ以外」で、そのあとには goto を書けない。条件は遷移前の状態で評価する。
      # `goto :done` で、プロセスを終える。
      def goto(step, condition = nil)
        top_level!("goto")
        if @gotos.any? { |_, c| c.nil? }
          raise BuildError, "操作 #{@name}: 条件のない goto のあとに goto は書けません（その goto には進みません）"
        end

        target = label(step)
        @gotos << [target, condition.nil? ? nil : lift(condition).expect(:bool, "操作 #{@name} の goto の条件")]
        nil
      end

      def build(&block)
        action, contracts = super
        at = Expr.new({ "var" => @pc[:index] }, @pc[:type]).eq(@pc[:type][@pc[:label]])
        guard = action["guard"]
        action["guard"] = guard == { "bool" => true } ? at.node : { "all" => [at.node, guard] }
        action["updates"] << { "target" => @pc[:index], "expr" => next_step.node }
        [action, contracts.map { |c| c.merge("name" => @model.qualify(c["name"])) }]
      end

      private

      # 次のプログラムカウンタの式。goto を書いた順に条件式で重ね、最後は次のステップにする。
      def next_step
        @gotos.reverse.reduce(@following) do |rest, (target, condition)|
          condition.nil? ? target : ite(condition, target, rest)
        end
      end

      def label(step)
        unless step.is_a?(Symbol) && @pc[:type].labels.include?(step)
          raise BuildError, "操作 #{@name}: goto の行き先 #{step.inspect} は、ステップの名前か :done です"
        end

        @pc[:type][step]
      end
    end

    # 記号的な状態の `s.プロセス`。`s.プロセス[i]` でインスタンスの状態を参照する。
    class Ref
      def initialize(model, name, count, ref)
        @model = model
        @name = name
        @count = count
        @ref = ref
      end

      def [](id)
        unless id.is_a?(Integer) && id.between?(0, @count - 1)
          raise BuildError, "プロセス #{@name} のインスタンスの番号は 0..#{@count - 1} です: #{id.inspect}"
        end

        StateRef.new(Instance.new(@model, "#{@name}[#{id}]"), @ref)
      end

      def inspect = "#<Fmspec::Process::Ref #{@name}>"
    end

    # 1つのインスタンスの、プログラムカウンタとローカル変数。`done` は、プロセスを終えたこと。
    class Instance
      def initialize(model, prefix)
        @model = model
        @prefix = prefix
      end

      def reference(name, ref)
        return @model.reference(:"#{@prefix}.pc", ref).eq(:done) if name == :done

        @model.reference(:"#{@prefix}.#{name}", ref)
      end
    end
  end
end
