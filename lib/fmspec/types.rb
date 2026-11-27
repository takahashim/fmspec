# frozen_string_literal: true

require "set"

module Fmspec
  I64_MIN = -(2**63)
  I64_MAX = (2**63) - 1

  # 状態変数、引数、出力の型（仕様書 §4.2）。
  #
  # 型は、IRの型（`to_ir`）と、式の型としての種類（`kind`）を持つ。
  # 整数の範囲は格納する型にだけあり、式の種類は範囲を持たない（:int）。
  # Tuple、Record、Option の種類は、部分の種類から作る（TupleKind など）。
  # Set、Map、List の種類は型そのもので、要素の型の範囲まで区別する。
  #
  # Ruby の値との対応は、Tuple が Array、Record が Hash（キーは Symbol）、Option が nil か値、
  # Set が Set（Array も受け付ける）、Map が Hash、List が Array である。
  module Types
    # 実装の値が、仕様の値として表せないことを示すJSON。エンジンは、どの値とも一致しないものとして扱う。
    # 報告に使うため、元の値の inspect を持つ。
    def self.unrepresentable(value) = { "unrepresentable" => value.inspect }

    def self.unrepresentable?(json) = json.is_a?(Hash) && json.keys == ["unrepresentable"]

    # 型に共通の振る舞い。
    module Common
      def ==(other) = other.class == self.class && other.to_ir == to_ir
      alias eql? ==
      def hash = [self.class, to_ir].hash
      def inspect = to_s

      # 初期値や定数の値として、Ruby の値を検査する。`what` は誤りの報告に使う。
      def check!(value, what)
        problem = problem(value)
        raise BuildError, "#{what} #{value.inspect} は #{self} の値ではありません#{problem && "（#{problem}）"}" if problem
      end

      # Set の要素と Map のキーに使える（値の数が有限で少なく、Set、Map、List を含まない）。
      def keyable? = false

      # Ruby の値を、この型の値の式にする。型の決まらない位置に複合型のリテラルを書くときに使う。
      # `seats.value([a, b])`。
      def value(value) = Expr.lift(value, kind)
    end

    # 閉区間の整数。
    class Int
      include Common
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

      def kind = :int
      def to_ir = { "int" => { "min" => min, "max" => max } }
      def to_s = "int(#{min}..#{max})"
      def keyable? = max - min < 4096

      def literal(value)
        raise BuildError, "#{self} の値として整数が必要です: #{value.inspect}" unless value.is_a?(Integer)

        value
      end

      def problem(value)
        return "整数ではありません" unless value.is_a?(Integer)

        "範囲外です" unless value.between?(min, max)
      end

      def to_wire(value) = value.is_a?(Integer) && value.between?(I64_MIN, I64_MAX) ? value : Types.unrepresentable(value)
      def from_wire(json) = json
    end

    class Bool
      include Common

      def kind = :bool
      def to_ir = { "bool" => {} }
      def to_s = "bool"
      def keyable? = true

      def literal(value)
        raise BuildError, "bool の値として true か false が必要です: #{value.inspect}" unless [true, false].include?(value)

        value
      end

      def problem(value) = [true, false].include?(value) ? nil : "true か false ではありません"
      def to_wire(value) = [true, false].include?(value) ? value : Types.unrepresentable(value)
      def from_wire(json) = json
    end

    # 列挙型。ラベルは Symbol で書く。
    class Enum
      include Common
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
      def keyable? = true

      def literal(value)
        return value if labels.include?(value)

        raise BuildError, "列挙型 #{name} に #{value.inspect} はありません（#{labels.map(&:inspect).join(', ')}）"
      end

      def problem(value) = labels.include?(value) ? nil : "ラベルは #{labels.map(&:inspect).join(', ')} です"

      # ラベルのリテラル式。`color[:red]`。
      def [](label)
        Expr.new({ "enum" => { "type" => name.to_s, "variant" => literal(label).to_s } }, kind)
      end

      def to_wire(value) = value.is_a?(Symbol) || value.is_a?(String) ? value.to_s : Types.unrepresentable(value)
      def from_wire(json) = json.to_sym

      def ==(other) = other.is_a?(Enum) && name == other.name && labels == other.labels
      alias eql? ==
      def hash = [Enum, name, labels].hash
    end

    # 組。要素は1つ以上。
    class Tuple
      include Common
      attr_reader :items

      def initialize(items)
        raise BuildError, "tuple には要素の型が1つ以上必要です" if items.empty?

        @items = items.each_with_index.map { |t, i| Types.coerce(t, "tuple の #{i} 番目の要素") }.freeze
        freeze
      end

      def kind = TupleKind.new(items.map(&:kind))
      def to_ir = { "tuple" => items.map(&:to_ir) }
      def to_s = "tuple(#{items.join(', ')})"
      def keyable? = items.all?(&:keyable?)

      def problem(value)
        return "要素が #{items.length} 個の Array ではありません" unless value.is_a?(Array) && value.length == items.length

        items.zip(value).each_with_index do |(t, v), i|
          inner = t.problem(v)
          return "#{i} 番目の要素: #{inner}" if inner
        end
        nil
      end

      def to_wire(value)
        return Types.unrepresentable(value) unless value.respond_to?(:to_a) && value.to_a.length == items.length

        items.zip(value.to_a).map { |t, v| t.to_wire(v) }
      end

      def from_wire(json) = items.zip(json).map { |t, v| t.from_wire(v) }
    end

    # フィールド名の付いた組。フィールドの順は、書いた順である。
    class Record
      include Common
      attr_reader :fields

      def initialize(fields)
        raise BuildError, "record にはフィールドが1つ以上必要です" if fields.empty?

        @fields = fields.to_h { |name, t| [name.to_sym, Types.coerce(t, "record のフィールド #{name}")] }.freeze
        freeze
      end

      def kind = RecordKind.new(fields.map { |n, t| [n, t.kind] })
      def to_ir = { "record" => fields.map { |n, t| { "name" => n.to_s, "type" => t.to_ir } } }
      def to_s = "record(#{fields.map { |n, t| "#{n}: #{t}" }.join(', ')})"
      def keyable? = fields.values.all?(&:keyable?)

      def problem(value)
        return "Hash ではありません" unless value.is_a?(Hash)
        return "フィールドは #{fields.keys.join(', ')} です" unless value.keys.map(&:to_sym).sort == fields.keys.sort

        fields.each do |n, t|
          inner = t.problem(Record.field(value, n))
          return "フィールド #{n}: #{inner}" if inner
        end
        nil
      end

      def self.field(value, name) = value.key?(name) ? value[name] : value[name.to_s]

      def to_wire(value)
        value = value.to_h if !value.is_a?(Hash) && value.respond_to?(:to_h)
        return Types.unrepresentable(value) unless value.is_a?(Hash) && value.keys.map(&:to_sym).sort == fields.keys.sort

        fields.to_h { |n, t| [n.to_s, t.to_wire(Record.field(value, n))] }
      end

      def from_wire(json) = fields.to_h { |n, t| [n, t.from_wire(json[n.to_s])] }
    end

    # 値がないこと（nil）を含む型。
    class Option
      include Common
      attr_reader :inner

      def initialize(inner)
        @inner = Types.coerce(inner, "option の中身")
        freeze
      end

      def kind = OptionKind.new(inner.kind)
      def to_ir = { "option" => inner.to_ir }
      def to_s = "option(#{inner})"
      def keyable? = inner.keyable?
      def problem(value) = value.nil? ? nil : inner.problem(value)
      def to_wire(value) = value.nil? ? nil : { "some" => inner.to_wire(value) }
      def from_wire(json) = json.nil? ? nil : inner.from_wire(json["some"])
    end

    # 有限集合。要素の型は、値の少ない型（`keyable?`）に限る。
    class SetOf
      include Common
      attr_reader :elem

      def initialize(elem)
        @elem = Types.coerce(elem, "set_of の要素")
        raise BuildError, "set_of の要素の型 #{@elem} は、値が少なく、set、map、list を含まない型に限ります" unless @elem.keyable?

        freeze
      end

      def kind = self
      def to_ir = { "set" => elem.to_ir }
      def to_s = "set_of(#{elem})"

      def problem(value)
        return "Set ではありません" unless value.is_a?(::Set) || value.is_a?(Array)

        value.each do |v|
          inner = elem.problem(v)
          return "要素 #{v.inspect}: #{inner}" if inner
        end
        nil
      end

      # Array も集合として扱う。境界の形式は重複を含まない要素の配列なので、
      # 要素を wire の値にしてから重複を除く（`[:a, :a]` は `Set[:a]` と同じ値になる）。
      def to_wire(value)
        return Types.unrepresentable(value) unless value.is_a?(::Set) || value.is_a?(Array)

        value.map { |v| elem.to_wire(v) }.uniq
      end

      def from_wire(json) = json.map { |v| elem.from_wire(v) }.to_set
    end

    # 有限写像。キーの型は、値の少ない型（`keyable?`）に限る。
    class MapOf
      include Common
      attr_reader :key, :value

      def initialize(key, value)
        @key = Types.coerce(key, "map_of のキー")
        @value = Types.coerce(value, "map_of の値")
        raise BuildError, "map_of のキーの型 #{@key} は、値が少なく、set、map、list を含まない型に限ります" unless @key.keyable?

        freeze
      end

      def kind = self
      def to_ir = { "map" => { "key" => key.to_ir, "value" => value.to_ir } }
      def to_s = "map_of(#{key}, #{value})"

      def problem(map)
        return "Hash ではありません" unless map.is_a?(Hash)

        map.each do |k, v|
          inner = key.problem(k)
          return "キー #{k.inspect}: #{inner}" if inner

          inner = value.problem(v)
          return "キー #{k.inspect} の値: #{inner}" if inner
        end
        nil
      end

      def to_wire(map)
        return Types.unrepresentable(map) unless map.is_a?(Hash)

        map.map { |k, v| [key.to_wire(k), value.to_wire(v)] }
      end

      def from_wire(json) = json.to_h { |k, v| [key.from_wire(k), value.from_wire(v)] }
    end

    # 長さに上限のある列。
    class ListOf
      include Common
      attr_reader :elem, :max

      def initialize(elem, max)
        @elem = Types.coerce(elem, "list_of の要素")
        raise BuildError, "list_of の max: は0以上の整数で書きます: #{max.inspect}" unless max.is_a?(Integer) && max >= 0

        @max = max
        freeze
      end

      def kind = self
      def to_ir = { "list" => { "of" => elem.to_ir, "max" => max } }
      def to_s = "list_of(#{elem}, max: #{max})"

      def problem(value)
        return "Array ではありません" unless value.is_a?(Array)
        return "要素が #{value.length} 個あり、上限 #{max} を超えます" if value.length > max

        value.each_with_index do |v, i|
          inner = elem.problem(v)
          return "#{i} 番目の要素: #{inner}" if inner
        end
        nil
      end

      def to_wire(value)
        return Types.unrepresentable(value) unless value.is_a?(Array)

        value.map { |v| elem.to_wire(v) }
      end

      def from_wire(json) = json.map { |v| elem.from_wire(v) }
    end

    # 式の種類。Tuple、Record、Option の値の式は、整数の範囲を区別しない。
    TupleKind = Struct.new(:items) do
      def to_s = "tuple(#{items.map { |k| Types.kind_name(k) }.join(', ')})"
    end

    RecordKind = Struct.new(:fields) do
      def to_s = "record(#{fields.map { |n, k| "#{n}: #{Types.kind_name(k)}" }.join(', ')})"
      def [](name) = fields.find { |n, _| n == name }&.last
    end

    OptionKind = Struct.new(:inner) do
      def to_s = "option(#{Types.kind_name(inner)})"
    end

    BOOL = Bool.new
    # 範囲を限らない整数。出力の型を書かなかったときに使う。
    ANY_INT = Int.new(I64_MIN, I64_MAX)

    module_function

    # 型の指定を型にする。整数の Range は整数型として読む。
    def coerce(spec, what)
      case spec
      when Int, Bool, Enum, Tuple, Record, Option, SetOf, MapOf, ListOf then spec
      when Range
        unless spec.begin.is_a?(Integer) && spec.end.is_a?(Integer)
          raise BuildError, "#{what}: 範囲は両端が整数でなければなりません: #{spec.inspect}"
        end

        Int.new(spec.begin, spec.exclude_end? ? spec.end - 1 : spec.end)
      else
        raise BuildError, "#{what}: 型が必要です（int(0..3)、bool、enum、tuple、record、option、set_of、map_of、list_of、" \
                          "または整数の範囲）: #{spec.inspect}"
      end
    end

    def kind_name(kind)
      kind.to_s
    end

    # 種類に属する値の式を書くための型。整数は範囲を限らない。`none` の型に使う。
    def kind_type(kind)
      case kind
      when :int then ANY_INT
      when :bool then BOOL
      when TupleKind then Tuple.new(kind.items.map { |k| kind_type(k) })
      when RecordKind then Record.new(kind.fields.to_h { |n, k| [n, kind_type(k)] })
      when OptionKind then Option.new(kind_type(kind.inner))
      else kind
      end
    end

    def scalar?(kind) = kind == :int || kind == :bool || kind.is_a?(Enum)

    # IRの型（JSON）を型にする。`enums` は、名前から列挙型への Hash。
    def from_ir(json, enums)
      kind, body = json.first
      case kind
      when "int" then Int.new(body["min"], body["max"])
      when "bool" then BOOL
      when "enum" then enums.fetch(body)
      when "tuple" then Tuple.new(body.map { |t| from_ir(t, enums) })
      when "record" then Record.new(body.to_h { |f| [f["name"], from_ir(f["type"], enums)] })
      when "option" then Option.new(from_ir(body, enums))
      when "set" then SetOf.new(from_ir(body, enums))
      when "map" then MapOf.new(from_ir(body["key"], enums), from_ir(body["value"], enums))
      when "list" then ListOf.new(from_ir(body["of"], enums), body["max"])
      end
    end
  end
end
