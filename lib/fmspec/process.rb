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
    # ステップとローカル変数に使えない名前。
    RESERVED_STEPS = %i[done crash crashed crashes].freeze
    RESERVED_LOCALS = %i[pc done crash crashed crashes].freeze

    # 仕様の定義の `process` のブロックの中の語彙。インスタンスごとに、インスタンスの番号を渡して実行する。
    class Body
      include Functions

      attr_reader :locals, :steps, :crash, :durable

      def initialize(model, name)
        @model = model
        @name = name
        @locals = []
        @steps = []
        @crash = nil
        @durable = []
      end

      # ローカル変数。`state` と同じく、initial か initial_in のどちらか一方を書く。
      # `durable: true` のローカル変数は、`crash: :restart` のクラッシュで初期値に戻らない。
      def local(name, type, durable: false, **initial)
        name = name.to_sym
        raise BuildError, "プロセス #{@name}: ローカル変数の名前 #{name} は予約されています" if RESERVED_LOCALS.include?(name)
        raise BuildError, "プロセス #{@name}: ローカル変数 #{name} の durable: は true か false です" unless [true, false].include?(durable)
        raise BuildError, "プロセス #{@name}: ローカル変数 #{name} は定義済みです" if @locals.any? { |l| l[0] == name }
        if @model.defined?(name)
          raise BuildError, "プロセス #{@name}: ローカル変数 #{name} は、状態変数または定数と同じ名前です"
        end

        @locals << [name, type, initial, caller_locations(1, 1)]
        @durable << name if durable
        nil
      end

      # クラッシュの遷移の中身。`process` に `crash:` を書いたときだけ使える。ブロックは記号的な状態を受け取り、
      # `update`、`unchanged`、`choose`、`guard`、`ensures`、`preserves` で、クラッシュで環境に起きることを書く。
      def on_crash(&block)
        raise BuildError, "プロセス #{@name} の on_crash にはブロックが必要です" unless block
        raise BuildError, "プロセス #{@name}: on_crash は1つだけ書けます" if @crash

        Lint.check!(block, "プロセス #{@name} の on_crash")
        @crash = [block, caller_locations(1, 1)&.first]
        nil
      end

      # atomic なステップ。ブロックは記号的な状態を受け取り、`action` のブロックと同じ語彙（guard、update、choose、
      # returns、accept_if、ensures など）に加えて、`goto` を使える。公開引数は持たない。
      def step(name, &block)
        raise BuildError, "プロセス #{@name} のステップ #{name} にはブロックが必要です" unless block

        name = name.to_sym
        raise BuildError, "プロセス #{@name}: ステップの名前 #{name} は予約されています" if RESERVED_STEPS.include?(name)
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

    # クラッシュの遷移の語彙。`on_crash` のブロックを、`action` の語彙のうち update、unchanged、choose、guard、
    # ensures、preserves で書く。プログラムカウンタとローカル変数は、クラッシュの方式に従って展開が更新する。
    #
    # - `:abort` なら、プログラムカウンタを `:crashed` にする。
    # - `:restart` なら、プログラムカウンタを最初のステップに、`durable: true` でないローカル変数を初期値に戻し、
    #   クラッシュの回数を1増やす。初期値の候補が複数あるローカル変数は、同じ名前の内部選択で選ぶ。
    # - `retries:` なら、回数が上限未満のときは `:restart` と同じで、上限に達したあとはプログラムカウンタを `:crashed` にする。
    #
    # guard は、プログラムカウンタが `crash_at:` のどれかであること（`max_crashes:` なら、回数が上限未満であること）と、
    # on_crash の guard の連言である。
    class CrashBuilder < ActionBuilder
      # plan は、:mode、:pc（index と type）、:at（ラベルの配列）、:first、:locals（[名前, index, durable] の配列）、
      # :crashes（回数の状態変数の index）、:max_crashes、:discard（retries: のとき真）。
      def initialize(scope, name, source, plan)
        super(scope, name, {}, source)
        @plan = plan
      end

      %i[returns accept_if on_accept on_reject goto].each do |word|
        define_method(word) { |*| raise BuildError, "操作 #{@name}: on_crash では #{word} を使えません" }
      end

      def build(&block)
        block ||= proc { |_s| nil }
        unless block.arity.negative? || block.arity == 1
          raise BuildError, "操作 #{@name}: on_crash のブロックは |s| を受け取ります"
        end

        plan = @plan
        action, contracts = super() do |s|
          instance_exec(s, &block)
          reset(plan)
        end
        guards = [crash_point.node]
        guards << (counter < plan[:max_crashes]).node if plan[:mode] == :restart && !plan[:discard]
        guards << action["guard"] unless action["guard"] == { "bool" => true }
        action["guard"] = guards.length == 1 ? guards[0] : { "all" => guards }
        [action, contracts.map { |c| c.merge("name" => @model.qualify(c["name"])) }]
      end

      private

      def pc = Expr.new({ "var" => @plan[:pc][:index] }, @plan[:pc][:type])
      def counter = Expr.new({ "var" => @plan[:crashes] }, :int)

      def crash_point
        points = @plan[:at].map { |label| pc.eq(@plan[:pc][:type][label]) }
        points.length == 1 ? points[0] : Expr.new({ "any" => points.map(&:node) }, :bool)
      end

      # プログラムカウンタ、ローカル変数、回数の更新を加える。on_crash がそれらを更新していれば拒否する。
      def reset(plan)
        updates = @always.updates
        plan[:locals].each do |name, index, _|
          raise BuildError, "操作 #{@name}: ローカル変数 #{name} は on_crash で更新できません" if updates.key?(index)
        end
        if plan[:mode] == :abort
          updates[plan[:pc][:index]] = plan[:pc][:type][:crashed]
          return
        end

        # retries: なら、再試行が残っているときだけやり直し、尽きていれば :crashed で終える。
        retry_left = plan[:discard] ? counter < plan[:max_crashes] : nil
        pick = ->(restart, &discard) { retry_left ? ite(retry_left, restart, discard.call) : restart }
        updates[plan[:pc][:index]] = pick.call(plan[:pc][:type][plan[:first]]) { plan[:pc][:type][:crashed] }
        plan[:locals].each do |name, index, durable|
          next if durable

          updates[index] = pick.call(initial_value(name, index)) { Expr.new({ "var" => index }, @model.states[index][:type].kind) }
        end
        updates[plan[:crashes]] = pick.call(counter + 1) { counter }
      end

      def initial_value(name, index)
        entry = @model.states[index]
        kind = entry[:type].kind
        return Expr.new(entry[:initial], kind) if entry.key?(:initial)

        candidates = entry[:initial_in].map { |node| Expr.new(node, kind) }
        return candidates[0] if candidates.length == 1

        value = choose(name, entry[:type])
        guard Expr.new({ "any" => candidates.map { |c| value.eq(c).node } }, :bool)
        value
      end
    end

    # 記号的な状態の `s.プロセス`。`s.プロセス[i]` でインスタンスの状態を参照する。
    class Ref
      # info は、Builder が記録したプロセスの情報（:count、:crash、:retries）。
      def initialize(model, name, info, ref)
        @model = model
        @name = name
        @count = info[:count]
        @ref = ref
        @crash = info[:crash] == :abort || info.key?(:retries) ? :abort : info[:crash]
        @counted = info[:crash] == :restart
      end

      def [](id)
        unless id.is_a?(Integer) && id.between?(0, @count - 1)
          raise BuildError, "プロセス #{@name} のインスタンスの番号は 0..#{@count - 1} です: #{id.inspect}"
        end

        StateRef.new(Instance.new(@model, "#{@name}[#{id}]", crashed: @crash == :abort, counted: @counted), @ref)
      end

      def inspect = "#<Fmspec::Process::Ref #{@name}>"
    end

    # 1つのインスタンスの、プログラムカウンタとローカル変数。`done` は、最後のステップまで実行してプロセスを終えたこと。
    # `crashed` は `crash: :abort` か `retries:` でクラッシュして終えたこと、`crashes` は `crash: :restart` でクラッシュした回数。
    class Instance
      def initialize(model, prefix, crashed: false, counted: false)
        @model = model
        @prefix = prefix
        @crashed = crashed
        @counted = counted
      end

      def reference(name, ref)
        return @model.reference(:"#{@prefix}.pc", ref).eq(:done) if name == :done
        if name == :crashed
          raise BuildError, "#{@prefix}.crashed は crash: :abort か retries: のプロセスで使えます" unless @crashed

          return @model.reference(:"#{@prefix}.pc", ref).eq(:crashed)
        end
        if name == :crashes && !@counted
          raise BuildError, "#{@prefix}.crashes は crash: :restart のプロセスで使えます"
        end

        @model.reference(:"#{@prefix}.#{name}", ref)
      end
    end
  end
end
