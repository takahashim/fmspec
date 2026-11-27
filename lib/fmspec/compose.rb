# frozen_string_literal: true

module Fmspec
  # モデル合成（仕様書 §12.5）。`Fmspec.compose` が使う。
  #
  # 複数のモデルを、名前空間を付けて1つのIRへ展開する。
  #
  # - 名前空間：各モデルの状態変数、定数、操作、不変条件、遷移契約の名前に `接頭辞.` を付ける。
  # - 所有状態：状態変数は、それを宣言したモデルの操作だけが更新する。
  # - 共有操作：`sync` で、各モデルの操作を1つの操作に同期させる。guard は連言、更新は連結である。
  #   公開引数は名前で揃え、同じ名前の引数は同じ値をとる。同期した操作は、単独では実行できない。
  #   同期しない操作は、他のモデルの状態を変えずに単独で実行する（インターリーブ）。
  # - 初期化：各状態変数の初期値の候補はそのまま使い、初期条件は各モデルの初期条件と `initially` の連言である。
  # - 終端条件：既定では、すべてのモデルが終端であること。終端条件のないモデルがあれば、合成も終端条件を持たない。
  #   `terminal` で書き換えられる。
  #
  # 各モデルの検査が成功しても、合成全体の安全性は推論しない。合成したモデルを改めて検査する。
  # モデルをまたぐ性質は、ブロックの `invariant` に書く。
  class Composer
    include Functions

    # 1つのモデルの状態を、名前空間の中の名前で参照する。
    class Scope
      def initialize(composer, prefix)
        @composer = composer
        @prefix = prefix
      end

      def reference(name, ref) = @composer.state_reference("#{@prefix}.#{name}", ref)
    end

    # 合成に加えるモデル。`offset` は、合成したモデルでの最初の状態変数の添字。
    Part = Struct.new(:prefix, :ir, :offset, :ghosts, :processes)

    def initialize(name, components)
      raise BuildError, "Fmspec.compose には1つ以上のモデルが必要です" if components.empty?

      @name = name
      @enums = {}
      @parts = []
      offset = 0
      components.each do |prefix, model|
        unless model.is_a?(Model)
          raise BuildError, "Fmspec.compose の #{prefix} は Fmspec::Model ではありません: #{model.inspect}"
        end

        prefix = prefix.to_s
        raise BuildError, "合成の接頭辞 #{prefix.inspect} に . は使えません" if prefix.include?(".")

        ir = model.to_ir
        merge_enums(prefix, ir)
        @parts << Part.new(prefix, ir, offset, model.ghosts, model.processes)
        offset += ir["states"].length
      end
      @state_types = composed_states.to_h { |s| [s["name"], Types.from_ir(s["type"], @enums)] }
      @syncs = []
      @plans = {}
      @synced = {}
      @invariants = []
      @terminal = nil
      @initially = nil
    end

    # 各モデルの操作を、名前 `name` の1つの操作に同期させる。`sync :checkout, cart: :pay, stock: :ship`。
    def sync(name, **actions)
      raise BuildError, "sync #{name} には、同期させる操作を1つ以上書きます" if actions.empty?

      name = unqualified!(name, "操作")
      raise BuildError, "操作 #{name} は定義済みです" if @syncs.any? { |s| s[:name] == name }

      members = actions.map do |prefix, action|
        part = part!(prefix)
        found = Array(part.ir["actions"]).find { |a| a["name"] == action.to_s }
        raise BuildError, "sync #{name}: #{prefix} に操作 #{action} がありません" unless found
        if crash_action?(part, found["name"])
          raise BuildError, "sync #{name}: #{prefix}.#{action} はプロセスのクラッシュなので、同期できません"
        end

        key = [part.prefix, found["name"]]
        raise BuildError, "sync #{name}: #{key.join('.')} は sync #{@synced[key]} で同期済みです" if @synced.key?(key)

        @synced[key] = name
        [part, found]
      end
      @syncs << { name: name, members: members, source: source_of(caller_locations(1, 1)) }
      nil
    end

    # モデルをまたぐ状態不変条件。ブロックは記号的な状態を受け取る。`s.cart.items` のように、接頭辞で各モデルの状態を参照する。
    def invariant(name, &block)
      raise BuildError, "不変条件 #{name} にはブロックが必要です" unless block

      name = unqualified!(name, "不変条件")
      raise BuildError, "不変条件 #{name} は定義済みです" if @invariants.any? { |i| i["name"] == name }

      Lint.check!(block, "不変条件 #{name}")
      expr = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "不変条件 #{name}")
      @invariants << { "name" => name, "expr" => expr.node, "source" => source_of(caller_locations(1, 1)) }
      nil
    end

    # 合成したモデルの終端条件。各モデルの終端条件の連言の代わりに使う。
    def terminal(&block)
      raise BuildError, "terminal にはブロックが必要です" unless block
      raise BuildError, "terminal は1つだけ書けます" if @terminal

      Lint.check!(block, "terminal")
      @terminal = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "terminal").node
      nil
    end

    # モデルをまたぐ初期条件。各モデルの初期条件に加えて、真になる組み合わせだけを初期状態にする。
    def initially(&block)
      raise BuildError, "initially にはブロックが必要です" unless block
      raise BuildError, "initially は1つだけ書けます" if @initially

      Lint.check!(block, "initially")
      @initially = lift(instance_exec(StateRef.new(self, "var"), &block)).expect(:bool, "initially").node
      nil
    end

    # 記号的な状態の、接頭辞の参照。
    def reference(name, ref)
      StateRef.new(Scope.new(self, part!(name).prefix), ref)
    end

    # 合成したモデルの状態変数の式。
    def state_reference(name, ref)
      index = composed_states.index { |s| s["name"] == name }
      raise BuildError, "未定義の状態変数です: #{name}" unless index

      Expr.new({ ref => index }, @state_types.fetch(name).kind)
    end

    def build
      ghosts = @parts.flat_map { |p| p.ghosts.map { |g| :"#{p.prefix}.#{g}" } }
      processes = @parts.flat_map { |p| p.processes.map { |name, v| [:"#{p.prefix}.#{name}", v] } }.to_h
      Model.new(@name.to_sym, to_ir, ghosts: ghosts, processes: processes)
    end

    private

    def declared_enums = @enums.values

    # 合成のブロックで定義する名前。`.` を含む名前は、各モデルの名前と重なりうるので使えない。
    def unqualified!(name, what)
      name = name.to_s
      raise BuildError, "#{what} #{name}: 合成のブロックで定義する名前に . は使えません" if name.include?(".")

      name
    end

    # 操作が、モデルのプロセスのクラッシュの操作か。
    def crash_action?(part, action)
      part.processes.any? do |name, p|
        p[:crash] && Array.new(p[:count]) { |id| "#{name}[#{id}].crash" }.include?(action)
      end
    end

    def part!(prefix)
      @parts.find { |p| p.prefix == prefix.to_s } or raise BuildError, "合成にないモデルです: #{prefix}"
    end

    # 名前と値が同じ列挙型は、1つにまとめる。
    def merge_enums(prefix, ir)
      Array(ir["enums"]).each do |e|
        type = Types::Enum.new(e["name"].to_sym, e["variants"].map(&:to_sym))
        known = @enums[e["name"]]
        if known && known != type
          raise BuildError, "列挙型 #{e['name']} が、#{prefix} と別のモデルで異なる値を持ちます。どちらかの名前を変えてください"
        end

        @enums[e["name"]] = type
      end
    end

    def composed_states
      @composed_states ||= @parts.flat_map do |part|
        part.ir["states"].map do |s|
          state = s.except("id").merge("name" => "#{part.prefix}.#{s['name']}")
          state["initial"] = rename(part, s["initial"]) if s.key?("initial")
          state["initial_in"] = s["initial_in"].map { |x| rename(part, x) } if s.key?("initial_in")
          state
        end
      end
    end

    def to_ir
      ir = {
        "ir_version" => 1,
        "name" => @name.to_s,
        "enums" => @enums.values.map { |e| { "name" => e.name.to_s, "variants" => e.labels.map(&:to_s) } },
        "states" => composed_states.each_with_index.map { |s, i| { "id" => i, **s } },
        "actions" => @parts.flat_map { |p| standalone_actions(p) } + @syncs.map { |s| synced_action(s) },
        "invariants" => @parts.flat_map { |p| invariants(p) } + @invariants,
        "contracts" => @parts.flat_map { |p| contracts(p) } + @syncs.flat_map { |s| synced_contracts(s) }
      }
      constants = @parts.flat_map { |p| constants(p) }
      ir["constants"] = constants unless constants.empty?
      terminal = @terminal || composed_terminal
      ir["terminal"] = terminal if terminal
      initially = @parts.filter_map { |p| p.ir["initial_constraint"] && rename(p, p.ir["initial_constraint"]) }
      initially << @initially if @initially
      ir["initial_constraint"] = initially.length == 1 ? initially[0] : { "all" => initially } unless initially.empty?
      ir
    end

    def constants(part)
      Array(part.ir["constants"]).map do |c|
        c.merge("name" => "#{part.prefix}.#{c['name']}", "value" => rename(part, c["value"]))
      end
    end

    def standalone_actions(part)
      Array(part.ir["actions"]).reject { |a| @synced.key?([part.prefix, a["name"]]) }.map do |a|
        action = a.merge(
          "name" => "#{part.prefix}.#{a['name']}",
          "params" => Array(a["params"]).map { |b| binding_of(b, part, nil) },
          "choices" => Array(a["choices"]).map { |b| binding_of(b, part, nil) },
          "guard" => rename(part, a.fetch("guard", { "bool" => true })),
          "updates" => updates(part, a, nil)
        )
        action["output"] = a["output"].merge("expr" => rename(part, a["output"]["expr"])) if a["output"]
        action
      end
    end

    def invariants(part)
      Array(part.ir["invariants"]).map do |i|
        i.merge("name" => "#{part.prefix}.#{i['name']}", "expr" => rename(part, i["expr"]))
      end
    end

    def contracts(part)
      Array(part.ir["contracts"]).reject { |c| @synced.key?([part.prefix, c["action"]]) }.map do |c|
        c.merge("name" => "#{part.prefix}.#{c['name']}", "action" => "#{part.prefix}.#{c['action']}",
                "expr" => rename(part, c["expr"]))
      end
    end

    # 終端条件の既定。すべてのモデルが終端であること。
    def composed_terminal
      return nil unless @parts.all? { |p| p.ir["terminal"] }

      terminals = @parts.map { |p| rename(p, p.ir["terminal"]) }
      terminals.length == 1 ? terminals[0] : { "all" => terminals }
    end

    # 同期した操作の引数の対応。公開引数は名前で揃え、内部選択はモデルの順に並べる。
    # 各モデルの操作について、添字の対応 [公開引数, 内部選択] を `:map` に入れ、
    # 合成した公開引数と内部選択を `:params`、`:choices` に入れる。
    def plan(sync)
      @plans[sync[:name]] ||= begin
        params = []
        choices = []
        members = sync[:members].map do |part, action|
          param_map = Array(action["params"]).map { |b| unify(sync, params, part, b) }
          choice_map = Array(action["choices"]).map do |b|
            choices << { binding: b, part: part }
            choices.length - 1
          end
          { part: part, action: action, map: [param_map, choice_map] }
        end
        names = (params + choices).map { |p| p[:binding]["name"] }
        duplicate = names.find { |n| names.count(n) > 1 }
        raise BuildError, "sync #{sync[:name]}: 引数 #{duplicate} が、複数のモデルの公開引数と内部選択にあります" if duplicate

        { members: members, params: params, choices: choices }
      end
    end

    # 公開引数 `b` を、同じ名前の公開引数に揃える。なければ加える。合成した操作での添字を返す。
    def unify(sync, params, part, binding)
      known = params.index { |p| p[:binding]["name"] == binding["name"] }
      unless known
        params << { binding: binding, part: part, also: [] }
        return params.length - 1
      end
      unless params[known][:binding]["type"] == binding["type"]
        raise BuildError, "sync #{sync[:name]}: 公開引数 #{binding['name']} の型が、#{part.prefix} と別のモデルで異なります"
      end

      params[known][:also] << [part, binding]
      known
    end

    def member_map(plan, part) = plan[:members].find { |m| m[:part].equal?(part) }[:map]

    def synced_action(sync)
      plan = plan(sync)
      guards = []
      plan[:members].each do |m|
        # 揃えた公開引数の、2つ目以降のモデルのドメインは guard で調べる。
        plan[:params].each_with_index do |p, i|
          p[:also].each do |other, b|
            guards << { "contains" => [rename(other, b["in"], m[:map]), { "param" => i }] } if other.equal?(m[:part]) && b["in"]
          end
        end
        guards << rename(m[:part], m[:action].fetch("guard", { "bool" => true }), m[:map])
      end
      outputs = plan[:members].select { |m| m[:action]["output"] }
      raise BuildError, "sync #{sync[:name]}: 出力を持つ操作は1つまでです" if outputs.length > 1

      action = {
        "name" => sync[:name],
        "params" => plan[:params].map { |p| binding_of(p[:binding], p[:part], member_map(plan, p[:part])) },
        "choices" => plan[:choices].map { |c| binding_of(c[:binding], c[:part], member_map(plan, c[:part])) },
        "guard" => guards.length == 1 ? guards[0] : { "all" => guards },
        "updates" => plan[:members].flat_map { |m| updates(m[:part], m[:action], m[:map]) },
        "source" => sync[:source]
      }
      outputs.each do |m|
        action["output"] = m[:action]["output"].merge("expr" => rename(m[:part], m[:action]["output"]["expr"], m[:map]))
      end
      action
    end

    # 同期した操作の、各モデルの遷移契約。
    def synced_contracts(sync)
      plan(sync)[:members].flat_map do |m|
        Array(m[:part].ir["contracts"]).select { |c| c["action"] == m[:action]["name"] }.map do |c|
          c.merge("name" => "#{m[:part].prefix}.#{c['name']}", "action" => sync[:name],
                  "expr" => rename(m[:part], c["expr"], m[:map]))
        end
      end
    end

    def updates(part, action, map)
      Array(action["updates"]).map do |u|
        { "target" => u["target"] + part.offset, "expr" => rename(part, u["expr"], map) }
      end
    end

    def binding_of(binding, part, map)
      binding = binding.dup
      binding["in"] = rename(part, binding["in"], map) if binding["in"]
      binding
    end

    # モデルの式を、合成したモデルの式にする。状態変数の添字をずらし、定数の名前に接頭辞を付け、
    # `map`（[公開引数, 内部選択] の添字の対応）があれば引数の添字を付け替える。
    def rename(part, node, map = nil)
      case node
      when Array then node.map { |x| rename(part, x, map) }
      when Hash
        if node.length == 1
          key, value = node.first
          case key
          when "var", "next" then return { key => value + part.offset }
          when "const" then return { key => "#{part.prefix}.#{value}" }
          when "param" then return { key => map ? map[0].fetch(value) : value }
          when "choice" then return { key => map ? map[1].fetch(value) : value }
          end
        end
        node.transform_values { |x| rename(part, x, map) }
      else node
      end
    end

    def source_of(locations)
      location = locations&.first
      location && { "file" => location.path, "line" => location.lineno }
    end
  end
end
