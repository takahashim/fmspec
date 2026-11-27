# frozen_string_literal: true

module Fmspec
  # 記号式。演算子は値を計算せず、IRの式ノードを組み立てる（仕様書 §4.1）。
  #
  # 等価性は `eq` / `ne`、論理積と論理和は `&` / `|`、否定は `not_`、条件式は `ite` で書く。
  # Ruby の `==`、`!=`、`!`、`&&`、`||`、`if` は記号式に使えない。
  #
  # 複合型の値の式は、Ruby の Array、Hash、Set に似たメソッドを持つ。どれも新しい値の式を返し、
  # 元の値は変えない（`s.queue.push(x)` は、x を末尾に加えた列の式である）。
  class Expr
    # IRの式ノード。
    attr_reader :node
    # 式の型の種類。:int、:bool、列挙型（Types::Enum）、または複合型の種類（Types の説明を参照）。
    attr_reader :kind

    def initialize(node, kind)
      @node = node
      @kind = kind
      freeze
    end

    @locals = 0

    # 量化と let で束縛する局所変数の名前。式の中で一意にする。
    def self.fresh_local
      @locals += 1
      "_#{@locals}"
    end

    # Ruby の値を式にする。複合型の値は、種類 `kind` が決まっているときに限って式にできる。
    # Symbol は列挙型のラベルとして読む。型は `kind` で決まり、なければ宣言済みの列挙型 `enums` から探す。
    def self.lift(value, kind = nil, enums: nil)
      return value if value.is_a?(Expr)

      case kind
      when Types::TupleKind, Types::RecordKind, Types::OptionKind, Types::SetOf, Types::MapOf, Types::ListOf
        return lift_composite(value, kind, enums)
      end

      case value
      when Integer
        unless value.between?(I64_MIN, I64_MAX)
          raise BuildError, "整数リテラルが符号付き64ビット整数に収まりません: #{value}"
        end

        new({ "int" => value }, :int)
      when true, false then new({ "bool" => value }, :bool)
      when Symbol then lift_label(value, kind, enums)
      when nil, Array, Hash, ::Set
        raise BuildError, "#{value.inspect} の型が決まりません。型の決まる位置に書くか、型.value(値)、some(値)、none(型) で書いてください"
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

    def self.lift_part(value, kind, enums, what)
      lift(value, kind, enums: enums).expect(kind, what).node
    end

    # 複合型の値を、種類に従って式にする。
    def self.lift_composite(value, kind, enums)
      node = case kind
             when Types::TupleKind
               unless value.is_a?(Array) && value.length == kind.items.length
                 raise BuildError, "#{Types.kind_name(kind)} の値として、要素が #{kind.items.length} 個の Array が必要です: #{value.inspect}"
               end

               { "tuple" => kind.items.zip(value).map { |k, v| lift_part(v, k, enums, "tuple の要素") } }
             when Types::RecordKind
               names = kind.fields.map(&:first)
               unless value.is_a?(Hash) && value.keys.map(&:to_sym).sort == names.sort
                 raise BuildError, "#{Types.kind_name(kind)} の値として、フィールド #{names.join(', ')} の Hash が必要です: #{value.inspect}"
               end

               { "record" => kind.fields.map do |n, k|
                 { "name" => n.to_s, "expr" => lift_part(Types::Record.field(value, n), k, enums, "フィールド #{n}") }
               end }
             when Types::OptionKind
               return none(Types.kind_type(kind.inner)) if value.nil?

               { "some" => [lift_part(value, kind.inner, enums, "option の中身")] }
             when Types::SetOf
               unless value.is_a?(::Set) || value.is_a?(Array)
                 raise BuildError, "#{kind} の値として Set か Array が必要です: #{value.inspect}"
               end

               { "set" => { "of" => kind.elem.to_ir,
                            "items" => value.map { |v| lift_part(v, kind.elem.kind, enums, "#{kind} の要素") } } }
             when Types::MapOf
               raise BuildError, "#{kind} の値として Hash が必要です: #{value.inspect}" unless value.is_a?(Hash)

               { "map" => { "key" => kind.key.to_ir, "value" => kind.value.to_ir,
                            "items" => value.map do |k, v|
                              [lift_part(k, kind.key.kind, enums, "#{kind} のキー"),
                               lift_part(v, kind.value.kind, enums, "#{kind} の値")]
                            end } }
             else
               unless value.is_a?(Array) && value.length <= kind.max
                 raise BuildError, "#{kind} の値として、要素が #{kind.max} 個以下の Array が必要です: #{value.inspect}"
               end

               { "list" => { "of" => kind.elem.to_ir, "max" => kind.max,
                             "items" => value.map { |v| lift_part(v, kind.elem.kind, enums, "#{kind} の要素") } } }
             end
      new(node, kind)
    end

    def self.none(type) = new({ "none" => type.to_ir }, Types::OptionKind.new(type.kind))

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
    private_class_method :lift_label, :lift_part, :lift_composite

    { :* => "mul", :/ => "div", :% => "mod" }.each do |method, op|
      define_method(method) { |other| Expr.binary(op, self, other, :int, :int) }
    end

    # 整数の和。Set では和集合。
    def +(other) = kind.is_a?(Types::SetOf) ? union(other) : Expr.binary("add", self, other, :int, :int)

    # 整数の差。Set では差集合。
    def -(other) = kind.is_a?(Types::SetOf) ? difference(other) : Expr.binary("sub", self, other, :int, :int)

    { :< => "lt", :> => "gt", :>= => "ge" }.each do |method, op|
      define_method(method) { |other| Expr.binary(op, self, other, :int, :bool) }
    end

    # 整数の比較。Set では部分集合。
    def <=(other) = kind.is_a?(Types::SetOf) ? subset?(other) : Expr.binary("le", self, other, :int, :bool)

    def -@ = Expr.binary("sub", 0, self, :int, :int)

    # 記述順に評価し、左が偽なら右を評価しない。Set では共通部分。
    def &(other) = kind.is_a?(Types::SetOf) ? intersection(other) : Expr.binary("all", self, other, :bool, :bool)

    # 記述順に評価し、左が真なら右を評価しない。Set では和集合。
    def |(other) = kind.is_a?(Types::SetOf) ? union(other) : Expr.binary("any", self, other, :bool, :bool)

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

    # ---- 複合型 ----

    # 要素の取り出し。Tuple は位置（整数）、Record はフィールド名、List は位置の式、Map はキーで引く。
    # List の位置が範囲の外なら index_out_of_range、Map にキーがなければ missing_key の評価エラーになる。
    def [](key)
      case kind
      when Types::TupleKind
        unless key.is_a?(Integer) && key >= 0 && key < kind.items.length
          raise BuildError, "#{Types.kind_name(kind)} の要素の位置は 0 から #{kind.items.length - 1} の整数です: #{key.inspect}"
        end

        Expr.new({ "nth" => { "of" => node, "index" => key } }, kind.items[key])
      when Types::RecordKind
        field = kind[key.to_sym] or raise BuildError, "#{Types.kind_name(kind)} にフィールド #{key} はありません"
        Expr.new({ "field" => { "of" => node, "name" => key.to_s } }, field)
      when Types::ListOf
        Expr.new({ "at" => [node, Expr.lift(key).expect(:int, "list の位置").node] }, kind.elem.kind)
      when Types::MapOf
        Expr.new({ "get" => [node, item(key, kind.key, "map のキー")] }, kind.value.kind)
      else raise BuildError, "[] は tuple、record、list_of、map_of の式に使います（#{Types.kind_name(kind)} の式です）"
      end
    end

    # Option に値がある。
    def some? = Expr.new({ "is_some" => [option!("some?")] }, :bool)

    # Option に値がない。
    def none? = Expr.new({ "is_none" => [option!("none?")] }, :bool)

    # Option の値。値がなければ none の評価エラーになる。
    def unwrap
      option!("unwrap")
      Expr.new({ "unwrap" => [node] }, kind.inner)
    end

    # Set の要素か、List に含まれる。Set では、要素の型に属さない値は含まれない（偽）。
    def include?(value)
      case kind
      when Types::SetOf then Expr.new({ "contains" => [node, item(value, kind.elem, "set の要素")] }, :bool)
      when Types::ListOf then Expr.new({ "contains" => [node, item(value, kind.elem, "list の要素")] }, :bool)
      else raise BuildError, "include? は set_of と list_of の式に使います（#{Types.kind_name(kind)} の式です）"
      end
    end

    # 要素を加えた Set。要素の型に属さない値なら not_in_domain の評価エラーになる。
    def add(value)
      collection!(Types::SetOf, "add")
      Expr.new({ "insert" => [node, item(value, kind.elem, "set の要素")] }, kind)
    end

    # 要素を除いた Set、またはキーを除いた Map。
    def delete(value)
      case kind
      when Types::SetOf then Expr.new({ "remove" => [node, item(value, kind.elem, "set の要素")] }, kind)
      when Types::MapOf then Expr.new({ "delete" => [node, item(value, kind.key, "map のキー")] }, kind)
      else raise BuildError, "delete は set_of と map_of の式に使います（#{Types.kind_name(kind)} の式です）"
      end
    end

    def union(other) = set_operation("union", other, kind)
    def intersection(other) = set_operation("intersection", other, kind)
    def difference(other) = set_operation("difference", other, kind)
    def subset?(other) = set_operation("subset", other, :bool)

    # 要素の数（Set、List）か、キーの数（Map）。
    def size
      collection!([Types::SetOf, Types::MapOf, Types::ListOf], "size")
      Expr.new({ "size" => [node] }, :int)
    end

    def empty?
      collection!([Types::SetOf, Types::MapOf, Types::ListOf], "empty?")
      Expr.new({ "is_empty" => [node] }, :bool)
    end

    # Map がキーを持つ。キーの型に属さない値なら偽。
    def key?(key)
      collection!(Types::MapOf, "key?")
      Expr.new({ "has_key" => [node, item(key, kind.key, "map のキー")] }, :bool)
    end

    # キーに値を置いた Map。キーか値が型に属さなければ not_in_domain の評価エラーになる。
    def put(key, value)
      collection!(Types::MapOf, "put")
      Expr.new({ "put" => [node, item(key, kind.key, "map のキー"), item(value, kind.value, "map の値")] }, kind)
    end

    # Map のキーの Set。
    def keys
      collection!(Types::MapOf, "keys")
      Expr.new({ "keys" => [node] }, Types::SetOf.new(kind.key))
    end

    # List の最初と最後の要素。空なら empty の評価エラーになる。
    def first = list_end("first")
    def last = list_end("last")

    # 末尾に要素を加えた List。要素の型に属さなければ not_in_domain、満杯なら full の評価エラーになる。
    def push(value)
      collection!(Types::ListOf, "push")
      Expr.new({ "push" => [node, item(value, kind.elem, "list の要素")] }, kind)
    end

    # 末尾（pop）または先頭（shift）の要素を除いた List。空なら empty の評価エラーになる。
    def pop = list_drop("pop")
    def shift = list_drop("shift")

    # 要素（Set）、キー（Map）、要素（List）のすべてで、ブロックの式が真。正規順にたどり、最初の偽で打ち切る。
    def all?(&block) = Expr.quantify("forall", over_node, element_type, block)

    # どれかの要素で、ブロックの式が真。正規順にたどり、最初の真で打ち切る。
    def any?(&block) = Expr.quantify("exists", over_node, element_type, block)

    # 量化の式。`over` は `{"in" => 式}` か `{"type" => 型}`。
    def self.quantify(op, over, type, block)
      raise BuildError, "#{op} にはブロックが必要です" unless block

      name = fresh_local
      body = lift(block.call(new({ "local" => name }, type.kind))).expect(:bool, "#{op} の本体")
      new({ op => { "name" => name, **over, "body" => body.node } }, :bool)
    end

    private

    def compare(op, other)
      # Symbol は、左辺の列挙型のラベルとして読む。複合型のリテラルも、左辺の種類で読む。
      right = Expr.lift(other, kind)
      unless right.kind == kind
        raise BuildError, "#{op}: 同じ型の式どうしを比べます（#{Types.kind_name(kind)} と #{Types.kind_name(right.kind)}）"
      end

      Expr.new({ op => [node, right.node] }, :bool)
    end

    def item(value, type, what) = Expr.lift(value, type.kind).expect(type.kind, what).node

    def option!(what)
      return node if kind.is_a?(Types::OptionKind)

      raise BuildError, "#{what} は option の式に使います（#{Types.kind_name(kind)} の式です）"
    end

    def collection!(classes, what)
      return if Array(classes).any? { |c| kind.is_a?(c) }

      names = { Types::SetOf => "set_of", Types::MapOf => "map_of", Types::ListOf => "list_of" }
      raise BuildError, "#{what} は #{Array(classes).map { |c| names[c] }.join('、')} の式に使います（#{Types.kind_name(kind)} の式です）"
    end

    def set_operation(op, other, result)
      collection!(Types::SetOf, op)
      right = Expr.lift(other, kind)
      unless right.kind == kind
        raise BuildError, "#{op}: 同じ型の set_of どうしに使います（#{Types.kind_name(kind)} と #{Types.kind_name(right.kind)}）"
      end

      Expr.new({ op => [node, right.node] }, result)
    end

    def list_end(op)
      collection!(Types::ListOf, op)
      Expr.new({ op => [node] }, kind.elem.kind)
    end

    def list_drop(op)
      collection!(Types::ListOf, op)
      Expr.new({ op => [node] }, kind)
    end

    def over_node
      collection!([Types::SetOf, Types::MapOf, Types::ListOf], "all? と any?")
      { "in" => node }
    end

    def element_type
      case kind
      when Types::MapOf then kind.key
      else kind.elem
      end
    end
  end

  # 型と式を組み立てる関数。仕様の定義の中でも、外（`Fmspec.ite` など）でも使える。
  module Functions
    # 整数型。`int(0..4)`。
    def int(range) = Types.coerce(range, "int")

    def bool = Types::BOOL

    # 組の型。`tuple(int(0..2), bool)`。値は Array で書く。
    def tuple(*items) = Types::Tuple.new(items)

    # フィールド名の付いた組の型。`record(x: int(0..2), y: int(0..2))`。値は Hash で書く。
    def record(**fields) = Types::Record.new(fields)

    # 値がないこと（nil）を含む型。`option(user)`。
    def option(type) = Types::Option.new(type)

    # 有限集合の型。`set_of(item)`。値は Set か Array で書く。
    def set_of(type) = Types::SetOf.new(type)

    # 有限写像の型。`map_of(item, int(0..3))`。値は Hash で書く。
    def map_of(key, value) = Types::MapOf.new(key, value)

    # 長さに上限のある列の型。`list_of(int(0..3), max: 4)`。値は Array で書く。
    def list_of(type, max:) = Types::ListOf.new(type, max)

    # 値のある Option の式。
    def some(value)
      x = lift(value)
      Expr.new({ "some" => [x.node] }, Types::OptionKind.new(x.kind))
    end

    # 値のない Option の式。`none(user)`。
    def none(type) = Expr.none(Types.coerce(type, "none"))

    # 条件に続いて、選ばれた枝だけを評価する条件式。
    def ite(condition, on_true, on_false)
      c = lift(condition).expect(:bool, "ite の条件")
      # 片方が Symbol や複合型のリテラルなら、もう片方の式の型で読む。
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

    # 集合の要素（Set、Map のキー、List の要素）か、型の値のすべてで、ブロックの式が真。
    # 正規順にたどり、最初の偽で打ち切る。`forall(color) { |c| ... }`、`forall(s.items) { |x| ... }`。
    def forall(over, &block) = quantify("forall", over, block)

    # どれかの値で、ブロックの式が真。正規順にたどり、最初の真で打ち切る。
    def exists(over, &block) = quantify("exists", over, block)

    # 値を一度だけ評価して、ブロックに渡す。`let(s.queue.first) { |x| ... }`。
    def let(value, &block)
      raise BuildError, "let にはブロックが必要です" unless block

      x = lift(value)
      name = Expr.fresh_local
      body = lift(block.call(Expr.new({ "local" => name }, x.kind)))
      Expr.new({ "let" => { "name" => name, "value" => x.node, "body" => body.node } }, body.kind)
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

    def quantify(op, over, block)
      if over.is_a?(Expr)
        over.public_send(op == "forall" ? :all? : :any?, &block)
      else
        type = Types.coerce(over, op)
        raise BuildError, "#{op}: 型 #{type} は値が多いか、set、map、list を含むので、量化できません" unless type.keyable?

        Expr.quantify(op, { "type" => type.to_ir }, type, block)
      end
    end

    # Symbol をラベルとして読むときに探す列挙型。仕様の定義の中では、宣言済みの列挙型になる。
    def declared_enums = nil
  end

  extend Functions
end

module Fmspec
  # Ruby の真偽値と nil の論理演算（`true & x`、`false | x`、`nil ^ x` など）に記号式を渡すと、
  # Ruby は記号式を値として「真」と読み、結果は Ruby の真偽値になる。書いたつもりの条件は式に残らない。
  # 記号ブロックの外のヘルパー（lambda やメソッド）でも起きるので、構文検査ではなく、実行時に拒否する。
  # 記号式どうし、または記号式が左にある演算（`記号式 & true`）は Expr の演算子になるので、影響しない。
  module RubyBooleanGuard
    %i[& | ^].each do |op|
      define_method(op) do |other|
        if other.is_a?(Expr)
          location = caller_locations(1, 1)&.first
          where = location ? "#{location.path}:#{location.lineno}: " : ""
          raise BuildError, "#{where}#{inspect} #{op} 記号式 は Ruby の真偽値の演算になり、記号式が式に残りません。" \
                            "記号式を左に書くか、all(...) や any(...) を使います"
        end
        super(other)
      end
    end
  end

  [TrueClass, FalseClass, NilClass].each { |klass| klass.prepend(RubyBooleanGuard) }
end
