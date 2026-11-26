# frozen_string_literal: true

module Fmspec
  # 記号式。演算子は値を計算せず、IRの式ノードを組み立てる（仕様書 §4.1）。
  #
  # 等価性は `eq` / `ne`、論理積と論理和は `&` / `|`、否定は `not_`、条件式は `ite` で書く。
  # Ruby の `==`、`!=`、`!`、`&&`、`||`、`if` は記号式に使えない。
  class Expr
    # IRの式ノード。
    attr_reader :node
    # 式の型の種類。:int、:bool、または列挙型（Types::Enum）。
    attr_reader :kind

    def initialize(node, kind)
      @node = node
      @kind = kind
      freeze
    end

    # Ruby の値を式にする。
    # Symbol は列挙型のラベルとして読む。型は `kind` で決まり、なければ宣言済みの列挙型 `enums` から探す。
    def self.lift(value, kind = nil, enums: nil)
      case value
      when Expr then value
      when Integer
        unless value.between?(I64_MIN, I64_MAX)
          raise BuildError, "整数リテラルが符号付き64ビット整数に収まりません: #{value}"
        end

        new({ "int" => value }, :int)
      when true, false then new({ "bool" => value }, :bool)
      when Symbol then lift_label(value, kind, enums)
      else raise BuildError, "記号式にできない値です: #{value.inspect}"
      end
    end

    def self.lift_label(label, kind, enums)
      return kind[label] if kind.is_a?(Types::Enum)

      found = (enums || []).select { |e| e.labels.include?(label) }
      return found.first[label] if found.length == 1

      hint = found.empty? ? "" : "（#{found.map(&:name).join('、')} にあります）"
      raise BuildError, "#{label.inspect} がどの列挙型のラベルか決まりません#{hint}。型[#{label.inspect}] と書いてください"
    end

    # 種類 `want` の式であることを確かめる。
    def expect(want, what)
      return self if kind == want

      raise BuildError, "#{what}: #{Types.kind_name(want)} の式が必要ですが、#{Types.kind_name(kind)} の式です"
    end

    def self.binary(op, left, right, operand, result)
      a = lift(left).expect(operand, op)
      b = lift(right).expect(operand, op)
      new({ op => [a.node, b.node] }, result)
    end
    private_class_method :lift_label

    { :+ => "add", :- => "sub", :* => "mul" }.each do |method, op|
      define_method(method) { |other| Expr.binary(op, self, other, :int, :int) }
    end

    { :< => "lt", :<= => "le", :> => "gt", :>= => "ge" }.each do |method, op|
      define_method(method) { |other| Expr.binary(op, self, other, :int, :bool) }
    end

    def -@ = Expr.binary("sub", 0, self, :int, :int)

    # 記述順に評価し、左が偽なら右を評価しない。
    def &(other) = Expr.binary("all", self, other, :bool, :bool)

    # 記述順に評価し、左が真なら右を評価しない。
    def |(other) = Expr.binary("any", self, other, :bool, :bool)

    # 前件が偽なら後件を評価しない。
    def implies(other) = Expr.binary("implies", self, other, :bool, :bool)

    def not_ = Expr.new({ "not" => [expect(:bool, "not_").node] }, :bool)

    def eq(other) = compare("eq", other)
    def ne(other) = compare("ne", other)

    # `1 + s.sold` のように、整数を左に書けるようにする。
    def coerce(other) = [Expr.lift(other), self]

    def ==(_other) = raise(BuildError, "記号式に == は使えません。eq を使ってください")
    def !=(_other) = raise(BuildError, "記号式に != は使えません。ne を使ってください")
    def ! = raise(BuildError, "記号式に ! は使えません。not_ を使ってください")

    def inspect = "#<Fmspec::Expr #{Types.kind_name(kind)} #{node}>"
    alias to_s inspect

    private

    def compare(op, other)
      # Symbol は、左辺の列挙型のラベルとして読む。
      right = Expr.lift(other, kind)
      unless right.kind == kind
        raise BuildError, "#{op}: 同じ型の式どうしを比べます（#{Types.kind_name(kind)} と #{Types.kind_name(right.kind)}）"
      end

      Expr.new({ op => [node, right.node] }, :bool)
    end
  end

  # 型と式を組み立てる関数。仕様の定義の中でも、外（`Fmspec.ite` など）でも使える。
  module Functions
    # 整数型。`int(0..4)`。
    def int(range) = Types.coerce(range, "int")

    def bool = Types::BOOL

    # 条件に続いて、選ばれた枝だけを評価する条件式。
    def ite(condition, on_true, on_false)
      c = lift(condition).expect(:bool, "ite の条件")
      # 片方が Symbol なら、もう片方の列挙型のラベルとして読む。
      a = lift(on_true, on_false.is_a?(Expr) ? on_false.kind : nil)
      b = lift(on_false, a.kind)
      unless a.kind == b.kind
        raise BuildError, "ite: 2つの枝は同じ型にします（#{Types.kind_name(a.kind)} と #{Types.kind_name(b.kind)}）"
      end

      Expr.new({ "ite" => [c.node, a.node, b.node] }, a.kind)
    end

    # 記述順に評価し、最初の偽で打ち切る。
    def all(*operands)
      Expr.new({ "all" => operands.map { |o| lift(o).expect(:bool, "all").node } }, :bool)
    end

    # 記述順に評価し、最初の真で打ち切る。
    def any(*operands)
      Expr.new({ "any" => operands.map { |o| lift(o).expect(:bool, "any").node } }, :bool)
    end

    # 小さいほう。`min(s.charges + 1, 2)` は、2で飽和するカウンタの増分になる。
    def min(left, right)
      a = lift(left).expect(:int, "min")
      b = lift(right).expect(:int, "min")
      ite(a <= b, a, b)
    end

    # 大きいほう。
    def max(left, right)
      a = lift(left).expect(:int, "max")
      b = lift(right).expect(:int, "max")
      ite(a >= b, a, b)
    end

    def implies(premise, conclusion)
      lift(premise).expect(:bool, "implies").implies(conclusion)
    end

    def not_(operand)
      lift(operand).not_
    end

    private

    def lift(value, kind = nil)
      Expr.lift(value, kind, enums: declared_enums)
    end

    # Symbol をラベルとして読むときに探す列挙型。仕様の定義の中では、宣言済みの列挙型になる。
    def declared_enums = nil
  end

  extend Functions
end
