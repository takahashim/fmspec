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
      @initially = nil
      @names = {}
      @processes = {}
      @responses = []
      @migrations = {}
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
    # 複合型の初期値は Ruby の値で書く（`initial: Set[]`、`initial: { x: 0, y: 0 }`、`initial: nil`）。
    # 初期値の候補を `initial_in:` に並べると（`initial_in: 0..2`、`initial_in: [Set[], Set[:apple]]`）、
    # 状態変数ごとの候補の組み合わせがすべて初期状態になる。bool、int、enum の型を書くと、その型の値すべてが候補になる。
    def state(name, type, initial: NONE, initial_in: NONE)
      claim(name, "状態変数")
      type = Types.coerce(type, "状態変数 #{name}")
      entry = { name: name.to_sym, type: type, source: source_of(caller_locations(1, 1)) }
      if initial_in.equal?(NONE) == initial.equal?(NONE)
        raise BuildError, "状態変数 #{name} には initial と initial_in のどちらか一方を書きます"
      end

      if initial_in.equal?(NONE)
        entry[:initial] = initial_node(name, type, initial)
      else
        candidates = initial_candidates(name, type, initial_in)
        raise BuildError, "状態変数 #{name} の initial_in が空です" if candidates.empty?

        entry[:initial_in] = candidates.map { |v| initial_node(name, type, v) }
      end
      @states << entry
      nil
    end

    # Ghost State（仕様書 §12.3）。履歴を記録する有限の補助状態で、モデルの上では普通の状態変数である。
    # 実装との照合では、実際の外部イベント（fake が記録した呼び出しなど）から観測する。
    def ghost(name, type, initial:)
      state(name, type, initial: initial)
      @states.last[:ghost] = true
      nil
    end

    # 初期条件。ブロックは記号的な状態を受け取り、Bool の式を返す。
    # 初期値の候補の組み合わせのうち、真になるものだけが初期状態になる。
    def initially(&block)
      raise BuildError, "initially にはブロックが必要です" unless block
      raise BuildError, "initially は1つだけ書けます" if @initially

      Lint.check!(block, "initially")
      @initially = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "initially").node
      nil
    end

    # 定数。記号的な状態から、状態変数と同じように名前で参照できる。
    # 複合型の値は、型を添えて書く（`constant :menu, set_of(item), Set[:apple, :bread]`）。
    def constant(name, *args)
      claim(name, "定数")
      case args.length
      when 1 then @constants[name.to_sym] = Expr.lift(args[0], enums: declared_enums)
      when 2
        type = Types.coerce(args[0], "定数 #{name}")
        type.check!(args[1], "定数 #{name} の値")
        @constants[name.to_sym] = Expr.lift(args[1], type.kind, enums: declared_enums)
      else raise BuildError, "constant は constant(名前, 値) か constant(名前, 型, 値) と書きます"
      end
      nil
    end

    # 操作。キーワードは公開引数で、値はそのドメイン（型、または整数の範囲）。
    # ブロックは、記号的な状態と各引数を受け取る。
    def action(name, **params, &block)
      raise BuildError, "操作 #{name} にはブロックが必要です" unless block

      claim(name, "操作", :action)
      Lint.check!(block, "操作 #{name}", statements: :effect)
      builder = ActionBuilder.new(self, name.to_sym, params, source_of(caller_locations(1, 1)))
      action, contracts = builder.build(&block)
      @actions << action
      @contracts.concat(contracts)
      nil
    end

    # 並行するプロセス（仕様書 §12.4）。`count` 個のインスタンスを持つ。
    # ブロックはインスタンスごとに、インスタンスの番号（0から）を受け取って実行する普通の Ruby で、
    # 中の語彙（local、step、on_crash）は Fmspec::Process::Body にある。
    #
    #   process :incr, count: 2 do
    #     local :seen, int(0..2), initial: 0
    #     step(:load) { |s| update seen: s.count }
    #     step(:store) { |s| update count: s.seen + 1 }
    #   end
    #
    # 記号的な状態からは、`s.incr[0].seen`、`s.incr[0].pc`、`s.incr[0].done` で各インスタンスの状態を参照する。
    #
    # `crash:` を書くと、ステップの境界でインスタンスがクラッシュする操作 `incr[0].crash` を加える。
    #
    #   crash        :abort（クラッシュしたインスタンスは終わる）か :restart（最初のステップからやり直す）
    #   crash_at     クラッシュしうる位置（そのステップを実行する前）。既定は最初のステップを除くすべてのステップ
    #   max_crashes  :restart のとき、インスタンスごとのクラッシュの回数の上限。既定は1
    #   retries      :restart のとき、実装が再試行する回数。尽きたあとのクラッシュでは、インスタンスは :crashed で終わる。
    #                max_crashes: とは一緒に書けない
    def process(name, count: 1, crash: nil, crash_at: nil, max_crashes: nil, retries: nil, &body)
      raise BuildError, "プロセス #{name} にはブロックが必要です" unless body

      claim(name, "プロセス")
      raise BuildError, "プロセス #{name} の count: は1以上の整数です: #{count.inspect}" unless count.is_a?(Integer) && count >= 1

      name = name.to_sym
      bodies = Array.new(count) { |id| Process::Body.new(self, name).tap { |b| b.instance_exec(id, &body) } }
      labels = bodies.first.steps.map(&:first)
      raise BuildError, "プロセス #{name} にステップがありません" if labels.empty?
      unless bodies.all? { |b| b.steps.map(&:first) == labels }
        raise BuildError, "プロセス #{name} のステップの名前と順序は、インスタンスごとに同じにします"
      end

      crash = crash_options(name, labels, bodies, crash, crash_at, max_crashes, retries)
      pc = enum(:"#{name}.pc", *labels, :done, *(crash && crash[:crashed] ? [:crashed] : []))
      bodies.each_with_index do |b, id|
        state(:"#{name}[#{id}].pc", pc, initial: labels.first)
        b.locals.each { |local, type, initial, _| state(:"#{name}[#{id}].#{local}", type, **initial) }
        state(:"#{name}[#{id}].crashes", int(0..crash[:max_crashes]), initial: 0) if crash && crash[:mode] == :restart
      end
      @processes[name] = { count: count, steps: labels }
      @processes[name][:crash] = crash[:mode] if crash
      @processes[name][:retries] = crash[:max_crashes] if crash&.dig(:discard)
      location = caller_locations(1, 1)&.first
      bodies.each_with_index do |b, id|
        process_steps(name, id, b, pc)
        process_crash(name, id, b, pc, labels, crash, location) if crash
      end
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

    # 移行（仕様書 §12.5）。段階 `phases` を順に進む。ブロックの中の語彙（advance、holds）は
    # Fmspec::Migration::Body にある。意味は Fmspec::Migration を参照。
    #
    #   migration :rename, phases: %i[initial dual_write backfilled contracted] do
    #     advance(:backfilled) { |s| guard s.unmigrated.eq(0) }
    #     holds(:copied, during: %i[backfilled contracted]) { |s| s.new_name.eq(s.old_name) }
    #   end
    #
    # 記号的な状態からは、`s.rename.phase`、`s.rename.reached(:backfilled)`、`s.rename.during(:a, :b)` で段階を参照する。
    def migration(name, phases:, &block)
      claim(name, "移行")
      name = name.to_sym
      phases = Array(phases).map(&:to_sym)
      raise BuildError, "移行 #{name} の phases: には2つ以上の段階を書きます" if phases.length < 2
      raise BuildError, "移行 #{name} の段階の名前が重複しています" unless phases.uniq.length == phases.length

      body = Migration::Body.new(name, phases)
      # ブロックは普通の Ruby で、中の advance と holds のブロックが記号ブロックである。
      body.instance_eval(&block) if block
      state(:"#{name}.phase", enum(:"#{name}.phase", *phases), initial: phases.first)
      @migrations[name] = phases
      phase = reference(:"#{name}.phase", "var")
      phases.each_cons(2) do |from, to|
        action = :"#{name}.#{to}"
        claim(action, "操作", :action)
        steps, location = body.advances[to] || [proc { |_s| nil }, caller_locations(1, 1)&.first]
        built, contracts = Migration::StepBuilder.new(self, action, source_of([location]), phase, from, to).build(&steps)
        @actions << built
        @contracts.concat(contracts)
      end
      body.invariants.each do |invariant, during, condition, location|
        qualified = :"#{name}.#{invariant}"
        claim(qualified, "不変条件", :invariant)
        expr = lift(instance_exec(StateRef.new(self, "var"), &condition)).expect(:bool, "不変条件 #{qualified}")
        node = Migration::Ref.new(self, name, phases, "var").during(*during).implies(expr).node
        @invariants << { "name" => qualified.to_s, "expr" => node, "source" => source_of([location]) }
      end
      nil
    end

    # 有界応答性（仕様書 §12.5）。トリガーが起きたら、数えるステップで `within` 以内に応答が起きる。
    # ブロックの中の語彙（trigger、response）は Fmspec::Response::Body にある。意味は Fmspec::Response を参照。
    #
    #   counting     数えるステップの操作の名前の配列。省略時はすべての操作
    #   on_terminal  :violation（既定。果たされていない義務を残して終端状態に至れば違反）か :allowed
    #
    #   responds(:settled, within: 3, counting: [:run_job]) do
    #     trigger { |s| s.queued }
    #     response { |s| s.status.ne(:pending) }
    #   end
    #
    # 経過を状態変数 `名前.elapsed` に持ち、不変条件 `名前` として検査する。
    def responds(name, within:, counting: nil, on_terminal: :violation, &block)
      raise BuildError, "有界応答性 #{name} にはブロックが必要です" unless block
      raise BuildError, "有界応答性 #{name} の within: は0以上の整数です: #{within.inspect}" unless within.is_a?(Integer) && within >= 0
      unless %i[violation allowed].include?(on_terminal)
        raise BuildError, "有界応答性 #{name} の on_terminal: は :violation か :allowed です: #{on_terminal.inspect}"
      end

      claim(name, "不変条件", :invariant)
      claim(:"#{name}.elapsed", "状態変数")
      # ブロックは普通の Ruby で、中の trigger と response のブロックが記号ブロックである。
      body = Response::Body.new(self, name)
      body.instance_eval(&block)
      raise BuildError, "有界応答性 #{name} には trigger が必要です" unless body.triggers[:defined]
      raise BuildError, "有界応答性 #{name} には response が必要です" unless body.responses[:defined]

      @responses << Response::Spec.new(name: name.to_s, trigger: body.triggers, response: body.responses, within: within,
                                       counting: counting && Array(counting).map(&:to_s), on_terminal: on_terminal)
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
      return Process::Ref.new(self, name, @processes[name], ref) if @processes.key?(name)
      return Migration::Ref.new(self, name, @migrations[name], ref) if @migrations.key?(name)

      raise BuildError, "未定義の状態変数または定数です: #{name}"
    end

    # 状態変数か定数の名前か。
    def defined?(name) = @states.any? { |s| s[:name] == name.to_sym } || @constants.key?(name.to_sym)

    def state_index(name)
      @states.index { |s| s[:name] == name.to_sym } or raise BuildError, "未定義の状態変数です: #{name}"
    end

    def claim_contract(name)
      claim(name, "遷移契約", :contract)
    end

    def build
      Model.new(@name.to_sym, to_ir, ghosts: @states.select { |s| s[:ghost] }.map { |s| s[:name] },
                                     processes: @processes)
    end

    def declared_enums = @enums.values

    private

    # 省略されたキーワード引数の印。
    NONE = Object.new.freeze

    def initial_node(name, type, initial)
      if Types.scalar?(type.kind)
        value = type.literal(initial)
        if type.is_a?(Types::Int) && !value.between?(type.min, type.max)
          raise BuildError, "状態変数 #{name} の初期値 #{value} が #{type} の範囲外です"
        end

        Expr.lift(value, type.kind).node
      else
        type.check!(initial, "状態変数 #{name} の初期値")
        Expr.lift(initial, type.kind, enums: declared_enums).node
      end
    end

    def initial_candidates(name, type, initial_in)
      case initial_in
      when Types::Int then initial_in.min.upto(initial_in.max).to_a
      when Types::Bool, :bool then [false, true]
      when Types::Enum then initial_in.labels
      when Types::Common
        raise BuildError, "状態変数 #{name} の initial_in に型を書けるのは bool、int、enum だけです"
      when Enumerable then initial_in.to_a
      else raise BuildError, "状態変数 #{name} の initial_in は、値の配列、範囲、または型です"
      end
    end

    def to_ir
      ir = {
        "ir_version" => 1,
        "name" => @name.to_s,
        "enums" => @enums.values.map { |e| { "name" => e.name.to_s, "variants" => e.labels.map(&:to_s) } },
        "states" => @states.each_with_index.map do |s, i|
          initial = s.key?(:initial_in) ? { "initial_in" => s[:initial_in] } : { "initial" => s[:initial] }
          { "id" => i, "name" => s[:name].to_s, "type" => s[:type].to_ir, **initial, "source" => s[:source] }
        end,
        "actions" => @actions,
        "invariants" => @invariants,
        "contracts" => @contracts
      }
      terminal = @terminal || processes_done
      ir["terminal"] = terminal if terminal
      ir["initial_constraint"] = @initially if @initially
      @responses.empty? ? ir : Response.expand(ir, @responses)
    end

    # プロセスのインスタンス `id` のステップを、操作に展開する。
    def process_steps(name, id, body, pc)
      prefix = "#{name}[#{id}]"
      scope = Process::Scope.new(self, prefix, body.locals.map(&:first))
      index = state_index(:"#{prefix}.pc")
      labels = pc.labels
      body.steps.each_with_index do |(label, block, location), k|
        action = :"#{prefix}.#{label}"
        claim(action, "操作", :action)
        builder = Process::StepBuilder.new(scope, action, source_of([location]),
                                           { index: index, type: pc, label: label }, pc[labels[k + 1]])
        built, contracts = builder.build(&block)
        @actions << built
        @contracts.concat(contracts)
      end
    end

    # `crash:` の指定を検査し、展開に使う形にする。`crash:` がなければ nil。
    def crash_options(name, labels, bodies, mode, at, max_crashes, retries)
      if mode.nil?
        unless at.nil? && max_crashes.nil? && retries.nil?
          raise BuildError, "プロセス #{name}: crash_at:、max_crashes:、retries: は crash: と一緒に書きます"
        end
        raise BuildError, "プロセス #{name}: on_crash は crash: と一緒に書きます" if bodies.any?(&:crash)

        return nil
      end
      raise BuildError, "プロセス #{name} の crash: は :abort か :restart です: #{mode.inspect}" unless %i[abort restart].include?(mode)
      if mode == :abort
        raise BuildError, "プロセス #{name}: max_crashes: と retries: は crash: :restart で書きます" unless max_crashes.nil? && retries.nil?
        if bodies.any? { |b| !b.durable.empty? }
          raise BuildError, "プロセス #{name}: durable: のローカル変数は crash: :restart で使います"
        end
      end
      raise BuildError, "プロセス #{name}: max_crashes: と retries: は一緒に書けません" unless max_crashes.nil? || retries.nil?
      if retries && !(retries.is_a?(Integer) && retries >= 1)
        raise BuildError, "プロセス #{name} の retries: は1以上の整数です（再試行しないなら crash: :abort）: #{retries.inspect}"
      end

      max_crashes = retries || max_crashes || 1 if mode == :restart
      if mode == :restart && !(max_crashes.is_a?(Integer) && max_crashes >= 1)
        raise BuildError, "プロセス #{name} の max_crashes: は1以上の整数です: #{max_crashes.inspect}"
      end

      at = at.nil? ? labels.drop(1) : Array(at)
      unknown = at.reject { |label| label.is_a?(Symbol) && labels.include?(label) }
      raise BuildError, "プロセス #{name} の crash_at: にないステップがあります: #{unknown.map(&:inspect).join(', ')}" unless unknown.empty?
      raise BuildError, "プロセス #{name}: クラッシュしうる位置がありません。crash_at: で指定します" if at.empty?

      { mode: mode, at: labels & at, max_crashes: max_crashes, discard: !retries.nil?, crashed: mode == :abort || !retries.nil? }
    end

    # プロセスのインスタンス `id` の、クラッシュの操作を加える。
    # on_crash がなければ、ソースの位置は process の宣言である。
    def process_crash(name, id, body, pc, labels, crash, declared)
      prefix = "#{name}[#{id}]"
      action = :"#{prefix}.crash"
      claim(action, "操作", :action)
      block, location = body.crash || [nil, declared]
      locals = body.locals.map do |local, *|
        [local, state_index(:"#{prefix}.#{local}"), body.durable.include?(local)]
      end
      plan = { mode: crash[:mode], pc: { index: state_index(:"#{prefix}.pc"), type: pc }, at: crash[:at],
               first: labels.first, locals: locals, max_crashes: crash[:max_crashes], discard: crash[:discard] }
      plan[:crashes] = state_index(:"#{prefix}.crashes") if crash[:mode] == :restart
      scope = Process::Scope.new(self, prefix, body.locals.map(&:first))
      built, contracts = Process::CrashBuilder.new(scope, action, source_of([location]), plan).build(&block)
      @actions << built
      @contracts.concat(contracts)
    end

    # 終端条件の既定。プロセスがあれば、すべてのインスタンスがプロセスを終えたこと。
    # `crash: :abort` と `retries:` のプロセスでは、クラッシュして終えたことも含む。
    def processes_done
      return nil if @processes.empty?

      done = @processes.flat_map do |name, p|
        Array.new(p[:count]) do |id|
          pc = reference(:"#{name}[#{id}].pc", "var")
          crashed = p[:crash] == :abort || p.key?(:retries)
          crashed ? { "any" => [pc.eq(:done).node, pc.eq(:crashed).node] } : pc.eq(:done).node
        end
      end
      done.length == 1 ? done[0] : { "all" => done }
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
      # 型、または動的ドメイン（記号的な状態と前の引数を受け取って Set か List の式を返す Proc）。
      @params = params.map do |param, domain|
        [param.to_sym, domain.is_a?(Proc) ? domain : Types.coerce(domain, "操作 #{name} の引数 #{param}")]
      end
      @choices = []
      # 引数と内部選択の、動的ドメインの式。
      @domains = {}
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
      args = []
      @params = @params.each_with_index.map do |(param, spec), i|
        type = spec.is_a?(Proc) ? dynamic_domain([:param, i], "引数 #{param}", spec, [state, *args]) : spec
        args << Expr.new({ "param" => i }, type.kind)
        [param, type]
      end
      instance_exec(state, *args, &block)
      updates, output = merge
      action = {
        "name" => @name.to_s,
        "params" => bindings(@params, :param),
        "choices" => bindings(@choices, :choice),
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
    # ドメインに Set か List の式を渡すと、その要素から選ぶ（`victim = choose(:victim, s.users)`）。
    def choose(name, domain)
      top_level!("choose")
      taken = (@params + @choices).any? { |n, _| n == name.to_sym }
      raise BuildError, "操作 #{@name}: 引数 #{name} は定義済みです" if taken

      type = if domain.is_a?(Expr)
               domain_type(domain, "内部選択 #{name}").tap { @domains[[:choice, @choices.length]] = domain.node }
             else
               Types.coerce(domain, "操作 #{@name} の内部選択 #{name}")
             end
      @choices << [name.to_sym, type]
      Expr.new({ "choice" => @choices.length - 1 }, type.kind)
    end

    # 出力。型を省略すると、式から決める（整数は範囲なし）。
    def returns(value, type = nil)
      raise BuildError, "操作 #{@name}: returns が重複しています" if @branch.output

      type &&= Types.coerce(type, "操作 #{@name} の出力")
      expr = lift(value, type&.kind)
      unless Types.scalar?(type ? type.kind : expr.kind)
        raise BuildError, "操作 #{@name}: 出力の型は bool、int、enum に限ります（#{Types.kind_name(type ? type.kind : expr.kind)}）"
      end

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

      Lint.check!(block, "操作 #{@name} の #{what}", statements: :effect)
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

    def bindings(list, kind)
      list.each_with_index.map do |(name, type), i|
        binding = { "name" => name.to_s, "type" => type.to_ir }
        binding["in"] = @domains[[kind, i]] if @domains.key?([kind, i])
        binding
      end
    end

    # 動的ドメインの Proc を、記号的な状態と前の引数で呼び、ドメインの式から引数の型を決める。
    def dynamic_domain(key, what, spec, inputs)
      Lint.check!(spec, "操作 #{@name} の#{what}のドメイン")
      inputs = inputs.first(spec.arity) unless spec.arity.negative?
      domain = lift(instance_exec(*inputs, &spec))
      domain_type(domain, what).tap { @domains[key] = domain.node }
    end

    def domain_type(domain, what)
      case domain.kind
      when Types::SetOf, Types::ListOf then domain.kind.elem
      else
        raise BuildError, "操作 #{@name} の#{what}: ドメインは set_of か list_of の式です（#{Types.kind_name(domain.kind)} の式です）"
      end
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
