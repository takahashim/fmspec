# frozen_string_literal: true

module Fmspec
  I64_MIN = -(2**63)
  I64_MAX = (2**63) - 1

  # 状態変数、引数、出力の型（仕様書 §4.2）。
  module Types
    # 閉区間の整数。
    class Int
      attr_reader :min, :max

      def initialize(min, max)
        unless min.is_a?(Integer) && max.is_a?(Integer) && min <= max
          raise BuildError, "整数型の範囲が不正です: #{min.inspect}..#{max.inspect}"
        end
        unless min >= I64_MIN && max <= I64_MAX
          raise BuildError, "整数型の範囲は符号付き64ビット整数に収めます: #{min}..#{max}"
        end

        @min = min
        @max = max
        freeze
      end

      # 式の型としての種類。整数の範囲は格納する型にだけあり、式の型は範囲を持たない。
      def kind = :int
      def to_ir = { "int" => { "min" => min, "max" => max } }
      def to_s = "int(#{min}..#{max})"

      def literal(value)
        raise BuildError, "#{self} の値として整数が必要です: #{value.inspect}" unless value.is_a?(Integer)

        value
      end

      def ==(other) = other.is_a?(Int) && min == other.min && max == other.max
      alias eql? ==
      def hash = [Int, min, max].hash
    end

    class Bool
      def kind = :bool
      def to_ir = { "bool" => {} }
      def to_s = "bool"

      def literal(value)
        raise BuildError, "bool の値として true か false が必要です: #{value.inspect}" unless [true, false].include?(value)

        value
      end

      def ==(other) = other.is_a?(Bool)
      alias eql? ==
      def hash = Bool.hash
    end

    # 列挙型。ラベルは Symbol で書く。
    class Enum
      attr_reader :name, :labels

      def initialize(name, labels)
        raise BuildError, "列挙型 #{name} にはラベルが1つ以上必要です" if labels.empty?
        raise BuildError, "列挙型 #{name} のラベルは Symbol で書きます" unless labels.all?(Symbol)
        raise BuildError, "列挙型 #{name} のラベルが重複しています" unless labels.uniq.length == labels.length

        @name = name
        @labels = labels.dup.freeze
        freeze
      end

      # 列挙型の式の種類は、型そのものである。
      def kind = self
      def to_ir = { "enum" => name.to_s }
      def to_s = "enum(#{name})"

      def literal(value)
        return value if labels.include?(value)

        raise BuildError, "列挙型 #{name} に #{value.inspect} はありません（#{labels.map(&:inspect).join(', ')}）"
      end

      # ラベルのリテラル式。`color[:red]`。
      def [](label)
        Expr.new({ "enum" => { "type" => name.to_s, "variant" => literal(label).to_s } }, kind)
      end

      def ==(other) = other.is_a?(Enum) && name == other.name && labels == other.labels
      alias eql? ==
      def hash = [Enum, name, labels].hash
    end

    BOOL = Bool.new
    # 範囲を限らない整数。出力の型を書かなかったときに使う。
    ANY_INT = Int.new(I64_MIN, I64_MAX)

    module_function

    # 型の指定を型にする。整数の Range は整数型として読む。
    def coerce(spec, what)
      case spec
      when Int, Bool, Enum then spec
      when Range
        unless spec.begin.is_a?(Integer) && spec.end.is_a?(Integer)
          raise BuildError, "#{what}: 範囲は両端が整数でなければなりません: #{spec.inspect}"
        end

        Int.new(spec.begin, spec.exclude_end? ? spec.end - 1 : spec.end)
      else
        raise BuildError, "#{what}: 型が必要です（int(0..3)、bool、enum、または整数の範囲）: #{spec.inspect}"
      end
    end

    def kind_name(kind)
      kind.to_s
    end
  end
end
