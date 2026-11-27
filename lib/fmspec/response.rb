# frozen_string_literal: true

module Fmspec
  # 有界応答性（仕様書 §12.5）。「トリガーが起きたら、数えるステップで `within` 以内に応答が起きる」。
  # `Builder#responds` が使う。
  #
  # 実行を、状態の列 s0, s1, ... と、s(j-1) から s(j) への操作 a(j) の列とする。位置 j で
  #
  # - **トリガー**は、トリガーの状態述語が s(j) で真か、a(j) がトリガーの操作であること。
  # - **応答**は、応答の状態述語が s(j) で真か、a(j) が応答の操作であること。
  #
  # 位置 i のトリガーは**義務**を作る。c(i, j) を、(i, j] の数えるステップ（`counting` の操作の遷移）の数とする。
  # 義務は、c(i, j) <= within である位置 j >= i（i 自身を含む）で応答が起きれば果たされる。
  # 果たされないまま c(i, j) が within を超える位置 j に至れば、違反である（その位置で応答が起きても遅い）。
  # `on_terminal: :violation`（既定）なら、果たされていない義務を残して終端状態に至ることも違反である。
  #
  # 同時に存在する義務は、1つの応答ですべて果たされるので、最も古い義務だけを数えれば足りる。
  # 変換は、その義務の経過（数えるステップの数、義務がなければ -1）を状態変数 `名前.elapsed` に持ち、
  # 各操作の更新に経過の更新を加え、不変条件 `名前` で違反を検出する（仕様書 §12.6）。
  # 元の操作の guard と更新は変えないので、元の状態変数の到達可能な値も変わらない。
  #
  # 数えるステップが起きなければ、期限は来ない。数えるステップが起き続けることや、環境が応答することは
  # モデルの仮定で、`counting` とモデルの guard で明示する。一般的な非有界活性や公平性は保証しない。
  module Response
    # `responds` のブロックの中の語彙。
    class Body
      include Functions

      # 定義した trigger と response。`{actions:, expr:, defined:}`。
      attr_reader :triggers, :responses

      def initialize(model, name)
        @model = model
        @name = name
        @triggers = { actions: [], expr: nil }
        @responses = { actions: [], expr: nil }
      end

      # トリガー。操作の名前を並べるか、記号的な状態を受け取って Bool の式を返すブロックを渡す。両方を書くと、どちらか。
      def trigger(*actions, &block) = define(@triggers, "trigger", actions, block)

      # 応答。書き方は trigger と同じ。
      def response(*actions, &block) = define(@responses, "response", actions, block)

      private

      def declared_enums = @model.declared_enums

      def define(part, what, actions, block)
        raise BuildError, "有界応答性 #{@name}: #{what} は1つだけ書けます" if part[:defined]
        raise BuildError, "有界応答性 #{@name}: #{what} には、操作の名前かブロックを渡します" if actions.empty? && !block

        part[:defined] = true
        part[:actions] = actions.map(&:to_s)
        return unless block

        Lint.check!(block, "有界応答性 #{@name} の #{what}")
        part[:expr] = lift(instance_exec(StateRef.new(@model, "var"), &block)).expect(:bool, "有界応答性 #{@name} の #{what}").node
      end
    end

    # 有界応答性の定義。IRの式と操作の名前で持つ。
    Spec = Struct.new(:name, :trigger, :response, :within, :counting, :on_terminal, keyword_init: true)

    module_function

    # IR に、有界応答性のモニタを加えた IR を返す。`specs` は Spec の配列。
    def expand(ir, specs)
      ir = JSON.parse(JSON.generate(ir))
      specs.each { |spec| add(ir, spec) }
      ir
    end

    def add(ir, spec)
      names = ir["actions"].map { |a| a["name"] }
      [*spec.trigger[:actions], *spec.response[:actions], *Array(spec.counting)].uniq.each do |action|
        raise BuildError, "有界応答性 #{spec.name}: 未定義の操作です: #{action}" unless names.include?(action)
      end

      index = ir["states"].length
      elapsed = { "var" => index }
      limit = spec.within + 1
      ir["states"] << { "id" => index, "name" => "#{spec.name}.elapsed",
                        "type" => { "int" => { "min" => -1, "max" => limit } },
                        "initial_in" => [{ "int" => -1 }, { "int" => 0 }] }
      initial = ite(holds(spec.response, nil, nil), { "int" => -1 }, ite(holds(spec.trigger, nil, nil), { "int" => 0 }, { "int" => -1 }))
      constrain(ir, { "eq" => [elapsed, initial] })
      ir["actions"].each do |action|
        counted = spec.counting.nil? || spec.counting.include?(action["name"])
        advanced = counted ? { "add" => [elapsed, { "int" => 1 }] } : elapsed
        responded = holds(spec.response, action, ir)
        # 義務がなければ、応答のないトリガーで義務を作る。義務があれば、期限を過ぎたか（過ぎたまま留まる）を
        # 応答より先に調べる。
        expr = ite({ "eq" => [elapsed, { "int" => -1 }] },
                   ite(responded, { "int" => -1 }, ite(holds(spec.trigger, action, ir), { "int" => 0 }, { "int" => -1 })),
                   ite({ "gt" => [advanced, { "int" => spec.within }] },
                       { "int" => limit },
                       ite(responded, { "int" => -1 }, advanced)))
        action["updates"] = Array(action["updates"]) + [{ "target" => index, "expr" => expr }]
      end
      within = { "le" => [elapsed, { "int" => spec.within }] }
      if spec.on_terminal == :violation && ir["terminal"]
        within = { "all" => [within, { "not" => [{ "all" => [ir["terminal"], { "ge" => [elapsed, { "int" => 0 }] }] }] }] }
      end
      (ir["invariants"] ||= []) << { "name" => spec.name.to_s, "expr" => within }
    end

    # トリガーか応答が、操作 `action` の遷移後の状態で起きる式。`action` が nil なら、初期状態で起きる式。
    def holds(part, action, ir)
      parts = []
      parts << { "bool" => true } if action && part[:actions].include?(action["name"])
      parts << (action ? after(part[:expr], action, ir) : part[:expr]) if part[:expr]
      case parts.length
      when 0 then { "bool" => false }
      when 1 then parts[0]
      else { "any" => parts }
      end
    end

    # 状態の式を、操作の遷移後の状態の式にする。状態変数を、その操作の更新式（なければそのまま）に置き換える。
    # 更新式は遷移前の状態と引数で評価するので、置き換えた式は同じ値になる。
    def after(node, action, ir)
      updates = Array(action["updates"]).to_h { |u| [u["target"], u["expr"]] }
      substitute(node, updates, ir)
    end

    def substitute(node, updates, ir)
      case node
      when Array then node.map { |x| substitute(x, updates, ir) }
      when Hash
        return updates.fetch(node["var"], node) if node.length == 1 && node.key?("var")

        node.transform_values { |x| substitute(x, updates, ir) }
      else node
      end
    end

    def constrain(ir, condition)
      existing = ir["initial_constraint"]
      ir["initial_constraint"] = existing ? { "all" => [existing, condition] } : condition
    end

    def ite(condition, on_true, on_false) = { "ite" => [condition, on_true, on_false] }
  end
end
