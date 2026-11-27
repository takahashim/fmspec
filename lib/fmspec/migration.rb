# frozen_string_literal: true

module Fmspec
  # 移行（仕様書 §12.5）。スキーマや機能フラグの段階的な切り替えを、段階の列として書く。`Builder#migration` が使う。
  #
  # - 段階 `移行.phase` は、段階の名前をラベルに持つ列挙型 `移行.phase` の状態変数で、最初の段階から始まる。
  # - 2番目以降の段階ごとに、その段階へ進む操作 `移行.段階` を作る。直前の段階にいるときだけ有効で、実行すると段階が進む。
  #   `advance` で、進む条件（guard）と、進むときの更新（列の追加など）を書ける。
  # - `holds` は、指定した段階で成り立つべき不変条件である（不変条件 `移行.名前`）。
  #
  # 混在するバージョン、バックフィル、再試行は、普通の状態変数と操作で書き、段階を guard で参照する。
  # これは移行の手順のモデルであり、実DBの移行全体の正しさを証明するものではない。
  module Migration
    # `migration` のブロックの中の語彙。
    class Body
      # 定義した advance（段階から [ブロック, 位置]）と holds（[名前, 段階, ブロック, 位置] の配列）。
      attr_reader :advances, :invariants

      def initialize(name, phases)
        @name = name
        @phases = phases
        @advances = {}
        @invariants = []
      end

      # 段階 `phase` へ進む操作の中身。ブロックは `action` のブロックと同じ語彙で書く。公開引数は持たない。
      def advance(phase, &block)
        phase = phase.to_sym
        raise BuildError, "移行 #{@name}: advance にはブロックが必要です" unless block
        raise BuildError, "移行 #{@name}: 段階 #{phase} はありません" unless @phases.include?(phase)
        raise BuildError, "移行 #{@name}: 最初の段階 #{phase} へは進めません" if phase == @phases.first
        raise BuildError, "移行 #{@name}: advance #{phase} は定義済みです" if @advances.key?(phase)

        Lint.check!(block, "移行 #{@name} の advance #{phase}")
        @advances[phase] = [block, caller_locations(1, 1)&.first]
        nil
      end

      # 段階 `during` で成り立つべき不変条件。ブロックは記号的な状態を受け取り、Bool の式を返す。
      def holds(name, during:, &block)
        raise BuildError, "移行 #{@name}: holds #{name} にはブロックが必要です" unless block

        during = Array(during).map(&:to_sym)
        unknown = during - @phases
        raise BuildError, "移行 #{@name}: holds #{name} の段階 #{unknown.join(', ')} はありません" unless unknown.empty?
        raise BuildError, "移行 #{@name}: holds #{name} の during: が空です" if during.empty?

        Lint.check!(block, "移行 #{@name} の holds #{name}")
        @invariants << [name, during, block, caller_locations(1, 1)&.first]
        nil
      end
    end

    # 段階へ進む操作の語彙。`action` の語彙と同じで、guard と更新に段階の条件と更新を加える。
    class StepBuilder < ActionBuilder
      def initialize(model, name, source, phase, from, to)
        super(model, name, {}, source)
        @phase = phase
        @from = from
        @to = to
      end

      def build(&block)
        action, contracts = super
        at = @phase.eq(@from)
        guard = action["guard"]
        action["guard"] = guard == { "bool" => true } ? at.node : { "all" => [at.node, guard] }
        action["updates"] << { "target" => @phase.node["var"], "expr" => @phase.kind[@to].node }
        [action, contracts]
      end
    end

    # 記号的な状態の `s.移行`。
    class Ref
      def initialize(model, name, phases, ref)
        @model = model
        @name = name
        @phases = phases
        @ref = ref
      end

      # 段階の式。
      def phase = @model.reference(:"#{@name}.phase", @ref)

      # 段階が、`phases` のどれかである。
      def during(*phases)
        phases.flatten.map(&:to_sym).each { |p| check!(p) }
        Expr.new({ "any" => phases.flatten.map { |p| phase.eq(p).node } }, :bool)
      end

      # 段階 `p` に達した（`p` か、それより後の段階にいる）。
      def reached(p)
        check!(p.to_sym)
        during(*@phases.drop(@phases.index(p.to_sym)))
      end

      def inspect = "#<Fmspec::Migration::Ref #{@name}>"

      private

      def check!(p)
        raise BuildError, "移行 #{@name} に段階 #{p} はありません" unless @phases.include?(p)
      end
    end
  end
end
