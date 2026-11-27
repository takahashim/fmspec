# frozen_string_literal: true

require "set"

# DSL の仕様のブロックを、記号式ではなく具体的な値で実行する解釈器。
# test/dsl_concrete_test.rb が、DSL の生成した IR を参照実装で評価した結果と比べる。
#
# Fmspec の Builder、Expr、Types は使わない。型と値の意味は docs/dsl.md と docs/ir.md から独立に書いた。
# 同じブロックを、状態と引数の具体的な値ごとに実行し直す。
#
# Ruby は引数を先に評価するので、`a & b` の `b` の評価エラーを例外にすると、IR の打ち切りと合わない。
# そこで評価エラーは、型を持ったまま失敗を表す値（CVal#err）にする。演算は、オペランドの失敗を
# 記述順に伝え、打ち切る演算（`&`、`|`、`implies`、`ite`、`all`、`any`、量化）は、使ったオペランドの失敗だけを伝える。
module ConcreteDsl
  # この解釈器が扱わない語彙（process、migration、responds など）。
  class Unsupported < StandardError; end

  # DSL が構築時に拒否するはずの書き方。
  class BuildError < StandardError; end

  # 値のある Option。値のない Option は nil。
  Some = Struct.new(:value)

  I64 = (-(2**63))..((2**63) - 1)

  # ---- 型 ----

  module T
    # 型に共通の操作。
    module Common
      def ==(other) = other.class == self.class && other.to_ir == to_ir
      alias eql? ==
      def hash = to_ir.hash

      # 正規順の値の列（キー型）。
      def values = raise(Unsupported, "#{to_ir} の値は列挙しない")

      def rank(value)
        @ranks ||= values.each_with_index.to_h
        @ranks.fetch(value)
      end

      # 値を置くときに、スロットの順で最初に範囲外になる整数。なければ nil。
      def first_out_of_range(_value) = nil

      # 型.value(値)
      def value(raw) = ConcreteDsl.lift(raw, self)
    end

    class Int
      include Common
      attr_reader :min, :max

      def initialize(min, max)
        @min = min
        @max = max
      end

      def any? = min.nil?
      def to_ir = { "int" => { "min" => min, "max" => max } }
      def member?(v) = v.is_a?(Integer) && (any? || v.between?(min, max))
      def values = (min..max).to_a
      def first_out_of_range(v) = member?(v) ? nil : v
      def to_json(v) = v
      def from_json(j) = j
    end

    ANY_INT = Int.new(nil, nil)

    class Bool
      include Common

      def to_ir = { "bool" => {} }
      def member?(v) = [true, false].include?(v)
      def values = [false, true]
      def to_json(v) = v
      def from_json(j) = j
    end

    BOOL = Bool.new

    class Enum
      include Common
      attr_reader :name, :labels

      def initialize(name, labels)
        @name = name
        @labels = labels
      end

      def to_ir = { "enum" => name.to_s }
      def ==(other) = other.is_a?(Enum) && other.name == name && other.labels == labels
      alias eql? ==
      def hash = [name, labels].hash
      def member?(v) = labels.include?(v)
      def values = labels
      def [](label)
        raise BuildError, "#{name} にラベル #{label} はない" unless labels.include?(label)

        CVal.ok(self, label)
      end

      def to_json(v) = v.to_s
      def from_json(j) = j.to_sym
    end

    class Tuple
      include Common
      attr_reader :items

      def initialize(items)
        @items = items
      end

      def to_ir = { "tuple" => items.map(&:to_ir) }
      def member?(v) = v.is_a?(Array) && v.length == items.length && items.zip(v).all? { |t, x| t.member?(x) }
      def values = items.map(&:values).reduce([[]]) { |acc, vs| acc.flat_map { |p| vs.map { |x| p + [x] } } }
      def first_out_of_range(v) = items.zip(v).each { |t, x| (bad = t.first_out_of_range(x)) && (return bad) } && nil
      def to_json(v) = items.zip(v).map { |t, x| t.to_json(x) }
      def from_json(j) = items.zip(j).map { |t, x| t.from_json(x) }
    end

    class Record
      include Common
      attr_reader :fields

      def initialize(fields)
        @fields = fields
      end

      def to_ir = { "record" => fields.map { |n, t| { "name" => n.to_s, "type" => t.to_ir } } }
      def member?(v) = v.is_a?(Hash) && v.keys.sort == fields.keys.sort && fields.all? { |n, t| t.member?(v[n]) }

      def values
        names = fields.keys
        Tuple.new(fields.values).values.map { |vs| names.zip(vs).to_h }
      end

      def first_out_of_range(v) = fields.each { |n, t| (bad = t.first_out_of_range(v[n])) && (return bad) } && nil
      def to_json(v) = fields.to_h { |n, t| [n.to_s, t.to_json(v[n])] }
      def from_json(j) = fields.to_h { |n, t| [n, t.from_json(j.fetch(n.to_s))] }
    end

    class Option
      include Common
      attr_reader :inner

      def initialize(inner)
        @inner = inner
      end

      def to_ir = { "option" => inner.to_ir }
      def member?(v) = v.nil? || (v.is_a?(Some) && inner.member?(v.value))
      def values = [nil] + inner.values.map { |x| Some.new(x) }
      def first_out_of_range(v) = v.nil? ? nil : inner.first_out_of_range(v.value)
      def to_json(v) = v.nil? ? nil : { "some" => inner.to_json(v.value) }
      def from_json(j) = j.nil? ? nil : Some.new(inner.from_json(j.fetch("some")))
    end

    class SetOf
      include Common
      attr_reader :elem

      def initialize(elem)
        @elem = elem
      end

      def to_ir = { "set" => elem.to_ir }
      def member?(v) = v.is_a?(::Set) && v.all? { |x| elem.member?(x) }
      def to_json(v) = v.sort_by { |x| elem.rank(x) }.map { |x| elem.to_json(x) }
      def from_json(j) = j.map { |x| elem.from_json(x) }.to_set
    end

    class MapOf
      include Common
      attr_reader :key, :value

      def initialize(key, value)
        @key = key
        @value = value
      end

      def to_ir = { "map" => { "key" => key.to_ir, "value" => value.to_ir } }
      def member?(v) = v.is_a?(Hash) && v.all? { |k, x| key.member?(k) && value.member?(x) }
      def to_json(v) = v.sort_by { |k, _| key.rank(k) }.map { |k, x| [key.to_json(k), value.to_json(x)] }
      def from_json(j) = j.to_h { |k, x| [key.from_json(k), value.from_json(x)] }
    end

    class ListOf
      include Common
      attr_reader :elem, :max

      def initialize(elem, max)
        @elem = elem
        @max = max
      end

      def to_ir = { "list" => { "of" => elem.to_ir, "max" => max } }
      def member?(v) = v.is_a?(Array) && v.length <= max && v.all? { |x| elem.member?(x) }
      def to_json(v) = v.map { |x| elem.to_json(x) }
      def from_json(j) = j.map { |x| elem.from_json(x) }
    end

    module_function

    # IR の型の JSON から型を作る。
    def from_ir(json, enums)
      kind, body = json.first
      case kind
      when "int" then Int.new(body["min"], body["max"])
      when "bool" then BOOL
      when "enum" then enums.fetch(body)
      when "tuple" then Tuple.new(body.map { |t| from_ir(t, enums) })
      when "record" then Record.new(body.to_h { |f| [f["name"].to_sym, from_ir(f["type"], enums)] })
      when "option" then Option.new(from_ir(body, enums))
      when "set" then SetOf.new(from_ir(body, enums))
      when "map" then MapOf.new(from_ir(body["key"], enums), from_ir(body["value"], enums))
      when "list" then ListOf.new(from_ir(body["of"], enums), body["max"])
      end
    end

    # 型の書き方（型か整数の範囲）を型にする。
    def coerce(spec)
      case spec
      when Common then spec
      when Range then Int.new(spec.begin, spec.exclude_end? ? spec.end - 1 : spec.end)
      else raise BuildError, "型ではない: #{spec.inspect}"
      end
    end
  end

  # ---- 値 ----

  # 具体的な値か、評価の失敗。どちらも型を持つ。
  class CVal
    attr_reader :type, :value, :err

    def self.ok(type, value) = new(type, value, nil)
    def self.bad(type, kind) = new(type, nil, kind)

    def initialize(type, value, err)
      @type = type
      @value = value
      @err = err
      freeze
    end

    def err? = !err.nil?
    def inspect = err? ? "#<CVal err #{err}>" : "#<CVal #{value.inspect}>"

    # オペランドを記述順に調べ、最初の失敗を返す。失敗がなければブロックに値を渡す。
    def self.strict(type, *operands)
      bad = operands.find(&:err?)
      return bad(type, bad.err) if bad

      yield(*operands.map(&:value))
    end

    def int(v) = I64.cover?(v) ? CVal.ok(T::ANY_INT, v) : CVal.bad(T::ANY_INT, "overflow")
    def bool(v) = CVal.ok(T::BOOL, v)
    def free(x) = ConcreteDsl.lift(x)
    def typed(x, type) = ConcreteDsl.lift(x, type)
    def set? = type.is_a?(T::SetOf)

    def arith(other, &op)
      CVal.strict(T::ANY_INT, self, free(other)) { |a, b| int(op.call(a, b)) }
    end

    def +(other) = set? ? union(other) : arith(other) { |a, b| a + b }
    def -(other) = set? ? difference(other) : arith(other) { |a, b| a - b }
    def *(other) = arith(other) { |a, b| a * b }

    def /(other)
      CVal.strict(T::ANY_INT, self, free(other)) do |a, b|
        b.zero? ? CVal.bad(T::ANY_INT, "division_by_zero") : int(a / b)
      end
    end

    def %(other)
      CVal.strict(T::ANY_INT, self, free(other)) do |a, b|
        b.zero? ? CVal.bad(T::ANY_INT, "division_by_zero") : int(a % b)
      end
    end

    def -@ = free(0) - self

    def <(other) = CVal.strict(T::BOOL, self, free(other)) { |a, b| bool(a < b) }
    def >(other) = CVal.strict(T::BOOL, self, free(other)) { |a, b| bool(a > b) }
    def >=(other) = CVal.strict(T::BOOL, self, free(other)) { |a, b| bool(a >= b) }
    def <=(other) = set? ? subset?(other) : CVal.strict(T::BOOL, self, free(other)) { |a, b| bool(a <= b) }

    def &(other)
      return intersection(other) if set?
      return self if err? || value == false

      free(other)
    end

    def |(other)
      return union(other) if set?
      return self if err? || value == true

      free(other)
    end

    def implies(other)
      return self if err?
      return bool(true) if value == false

      free(other)
    end

    def not_ = CVal.strict(T::BOOL, self) { |a| bool(!a) }
    def eq(other) = CVal.strict(T::BOOL, self, typed(other, type)) { |a, b| bool(a == b) }
    def ne(other) = CVal.strict(T::BOOL, self, typed(other, type)) { |a, b| bool(a != b) }
    def coerce(other) = [free(other), self]

    def ==(_other) = raise(BuildError, "== は使えない")
    def !=(_other) = raise(BuildError, "!= は使えない")
    def ! = raise(BuildError, "! は使えない")

    # ---- 複合型 ----

    def [](key)
      case type
      when T::Tuple
        raise BuildError, "tuple の位置" unless key.is_a?(Integer) && key >= 0 && key < type.items.length

        CVal.strict(type.items[key], self) { |v| CVal.ok(type.items[key], v[key]) }
      when T::Record
        field = type.fields.fetch(key.to_sym) { raise BuildError, "フィールド #{key}" }
        CVal.strict(field, self) { |v| CVal.ok(field, v[key.to_sym]) }
      when T::ListOf
        CVal.strict(type.elem, self, free(key)) do |l, i|
          i >= 0 && i < l.length ? CVal.ok(type.elem, l[i]) : CVal.bad(type.elem, "index_out_of_range")
        end
      when T::MapOf
        CVal.strict(type.value, self, typed(key, type.key)) do |m, k|
          m.key?(k) ? CVal.ok(type.value, m[k]) : CVal.bad(type.value, "missing_key")
        end
      else raise BuildError, "[] は使えない"
      end
    end

    def some? = CVal.strict(T::BOOL, self) { |v| bool(!v.nil?) }
    def none? = CVal.strict(T::BOOL, self) { |v| bool(v.nil?) }

    def unwrap
      CVal.strict(type.inner, self) { |v| v.nil? ? CVal.bad(type.inner, "none") : CVal.ok(type.inner, v.value) }
    end

    def include?(x)
      CVal.strict(T::BOOL, self, typed(x, type.elem)) { |c, v| bool(c.include?(v)) }
    end

    def add(x)
      CVal.strict(type, self, typed(x, type.elem)) do |s, v|
        type.elem.member?(v) ? CVal.ok(type, s | [v]) : CVal.bad(type, "not_in_domain")
      end
    end

    def delete(x)
      if set?
        CVal.strict(type, self, typed(x, type.elem)) { |s, v| CVal.ok(type, s - [v]) }
      else
        CVal.strict(type, self, typed(x, type.key)) { |m, k| CVal.ok(type, m.except(k)) }
      end
    end

    def union(other) = CVal.strict(type, self, typed(other, type)) { |a, b| CVal.ok(type, a | b) }
    def intersection(other) = CVal.strict(type, self, typed(other, type)) { |a, b| CVal.ok(type, a & b) }
    def difference(other) = CVal.strict(type, self, typed(other, type)) { |a, b| CVal.ok(type, a - b) }
    def subset?(other) = CVal.strict(T::BOOL, self, typed(other, type)) { |a, b| bool(a.subset?(b)) }

    def size = CVal.strict(T::ANY_INT, self) { |c| int(c.size) }
    def empty? = CVal.strict(T::BOOL, self) { |c| bool(c.empty?) }
    def key?(k) = CVal.strict(T::BOOL, self, typed(k, type.key)) { |m, x| bool(m.key?(x)) }

    # キーを評価して検査し、値を評価して検査する。
    def put(k, v)
      key = typed(k, type.key)
      val = typed(v, type.value)
      CVal.strict(type, self, key) do |m, kk|
        next CVal.bad(type, "not_in_domain") unless type.key.member?(kk)

        CVal.strict(type, val) do |vv|
          type.value.member?(vv) ? CVal.ok(type, m.merge(kk => vv)) : CVal.bad(type, "not_in_domain")
        end
      end
    end

    def keys = CVal.strict(T::SetOf.new(type.key), self) { |m| CVal.ok(T::SetOf.new(type.key), m.keys.to_set) }

    def first = CVal.strict(type.elem, self) { |l| l.empty? ? CVal.bad(type.elem, "empty") : CVal.ok(type.elem, l.first) }
    def last = CVal.strict(type.elem, self) { |l| l.empty? ? CVal.bad(type.elem, "empty") : CVal.ok(type.elem, l.last) }

    # 要素を検査してから、満杯かを調べる。
    def push(x)
      CVal.strict(type, self, typed(x, type.elem)) do |l, v|
        next CVal.bad(type, "not_in_domain") unless type.elem.member?(v)

        l.length >= type.max ? CVal.bad(type, "full") : CVal.ok(type, l + [v])
      end
    end

    def pop = CVal.strict(type, self) { |l| l.empty? ? CVal.bad(type, "empty") : CVal.ok(type, l[0...-1]) }
    def shift = CVal.strict(type, self) { |l| l.empty? ? CVal.bad(type, "empty") : CVal.ok(type, l[1..]) }

    def all?(&block) = quantify(true, &block)
    def any?(&block) = quantify(false, &block)

    # 要素（Set）、キー（Map）は正規順に、List は位置の順にたどる。
    def quantify(all, &block)
      CVal.strict(T::BOOL, self) do |c|
        elem, items = case type
                      when T::SetOf then [type.elem, c.sort_by { |x| type.elem.rank(x) }]
                      when T::MapOf then [type.key, c.keys.sort_by { |x| type.key.rank(x) }]
                      else [type.elem, c]
                      end
        ConcreteDsl.quantify(all, items.map { |x| CVal.ok(elem, x) }, &block)
      end
    end
  end

  module_function

  def enums_in_scope = Thread.current[:concrete_dsl_enums] || []

  # Ruby の値を、型に従って値にする。型がなければ、整数、真偽値、宣言済みの列挙型のラベルに限る。
  # 複合型のリテラルでは、要素を記述順に評価し、Set、Map、List の要素の型を検査する。
  def lift(raw, type = nil)
    return raw if raw.is_a?(CVal)

    case type
    when T::Tuple
      raise BuildError, "tuple の値" unless raw.is_a?(Array) && raw.length == type.items.length

      parts = type.items.zip(raw).map { |t, x| lift(x, t) }
      CVal.strict(type, *parts) { |*vs| CVal.ok(type, vs) }
    when T::Record
      raise BuildError, "record の値" unless raw.is_a?(Hash) && raw.keys.map(&:to_sym).sort == type.fields.keys.sort

      parts = type.fields.map { |n, t| lift(raw.key?(n) ? raw[n] : raw[n.to_s], t) }
      CVal.strict(type, *parts) { |*vs| CVal.ok(type, type.fields.keys.zip(vs).to_h) }
    when T::Option
      return CVal.ok(type, nil) if raw.nil?

      CVal.strict(type, lift(raw, type.inner)) { |v| CVal.ok(type, Some.new(v)) }
    when T::SetOf
      raise BuildError, "set の値" unless raw.is_a?(::Set) || raw.is_a?(Array)

      items(type, raw.to_a, type.elem) { |vs| CVal.ok(type, vs.to_set) }
    when T::ListOf
      raise BuildError, "list の値" unless raw.is_a?(Array) && raw.length <= type.max

      items(type, raw, type.elem) { |vs| CVal.ok(type, vs) }
    when T::MapOf
      raise BuildError, "map の値" unless raw.is_a?(Hash)

      raw.reduce(CVal.ok(type, {})) { |m, (k, v)| m.put(k, v) }
    else
      case raw
      when Integer
        raise BuildError, "64ビットに収まらない" unless I64.cover?(raw)

        CVal.ok(T::ANY_INT, raw)
      when true, false then CVal.ok(T::BOOL, raw)
      when Symbol
        return CVal.ok(type, raw) if type.is_a?(T::Enum) && type.labels.include?(raw)
        raise BuildError, "ラベル #{raw}" if type.is_a?(T::Enum)

        found = enums_in_scope.select { |e| e.labels.include?(raw) }
        raise BuildError, "ラベル #{raw} の型が決まらない" unless found.length == 1

        CVal.ok(found[0], raw)
      else raise BuildError, "型が決まらない値: #{raw.inspect}"
      end
    end
  end

  # 要素を記述順に評価し、評価するたびに要素の型を検査する。
  def items(type, raw, elem)
    values = []
    raw.each do |x|
      v = lift(x, elem)
      return CVal.bad(type, v.err) if v.err?
      return CVal.bad(type, "not_in_domain") unless elem.member?(v.value)

      values << v.value
    end
    yield values
  end

  # forall は最初の偽で、exists は最初の真で打ち切る。本体の失敗はそのまま伝える。
  def quantify(all, values)
    values.each do |x|
      r = lift(yield(x))
      return r if r.err? || r.value != all
    end
    CVal.ok(T::BOOL, all)
  end

  # ---- 関数（仕様の定義と操作のブロックで使う） ----

  module Functions
    def int(range) = T.coerce(range)
    def bool = T::BOOL
    def tuple(*items) = T::Tuple.new(items.map { |t| T.coerce(t) })
    def record(**fields) = T::Record.new(fields.transform_values { |t| T.coerce(t) })
    def option(type) = T::Option.new(T.coerce(type))
    def set_of(type) = T::SetOf.new(T.coerce(type))
    def map_of(key, value) = T::MapOf.new(T.coerce(key), T.coerce(value))
    def list_of(type, max:) = T::ListOf.new(T.coerce(type), max)

    def some(value)
      x = ConcreteDsl.lift(value)
      type = T::Option.new(x.type)
      CVal.strict(type, x) { |v| CVal.ok(type, Some.new(v)) }
    end

    def none(type) = CVal.ok(T::Option.new(T.coerce(type)), nil)

    # 片方が Ruby の値なら、もう片方の型で読む。
    def ite(condition, on_true, on_false)
      c = ConcreteDsl.lift(condition)
      a = ConcreteDsl.lift(on_true, on_false.is_a?(CVal) ? on_false.type : nil)
      b = ConcreteDsl.lift(on_false, a.type)
      return CVal.bad(a.type, c.err) if c.err?

      c.value ? a : b
    end

    def all(*operands) = operands.reduce(CVal.ok(T::BOOL, true)) { |acc, o| acc & o }

    def any(*operands)
      operands.each do |o|
        x = ConcreteDsl.lift(o)
        return x if x.err? || x.value
      end
      CVal.ok(T::BOOL, false)
    end

    def forall(over, &block) = quantify_over(true, over, &block)
    def exists(over, &block) = quantify_over(false, over, &block)

    # 値は、本体で使わなくても評価する（失敗すれば let 全体が失敗する）。
    def let(value)
      x = ConcreteDsl.lift(value)
      return x if x.err?

      ConcreteDsl.lift(yield(x))
    end

    def min(left, right)
      a = ConcreteDsl.lift(left)
      b = ConcreteDsl.lift(right)
      ite(a <= b, a, b)
    end

    def max(left, right)
      a = ConcreteDsl.lift(left)
      b = ConcreteDsl.lift(right)
      ite(a >= b, a, b)
    end

    def implies(premise, conclusion) = ConcreteDsl.lift(premise).implies(conclusion)
    def not_(operand) = ConcreteDsl.lift(operand).not_

    def quantify_over(all, over, &block)
      if over.is_a?(CVal)
        all ? over.all?(&block) : over.any?(&block)
      else
        type = T.coerce(over)
        ConcreteDsl.quantify(all, type.values.map { |x| CVal.ok(type, x) }, &block)
      end
    end
  end

  # ---- 仕様 ----

  # 記号的な状態の代わりに、状態変数と定数の値を名前で返す。
  class StateRef
    def initialize(values) = @values = values

    def method_missing(name, *args)
      return super unless args.empty? && @values.key?(name)

      @values[name]
    end

    def respond_to_missing?(name, include_private = false) = @values.key?(name) || super
  end

  NONE = Object.new

  # 仕様の定義のブロックを実行して、状態、定数、操作、性質を集める。
  class Model
    include Functions

    attr_reader :states, :constants, :actions, :invariants, :terminal_block, :initially_block, :enums

    def initialize
      @states = []
      @constants = {}
      @actions = []
      @invariants = []
      @enums = {}
      @terminal_block = nil
      @initially_block = nil
    end

    def enum(name, *labels)
      found = @enums[name.to_s]
      return found if found && found.labels == labels

      raise BuildError, "列挙型 #{name} のラベルが違う" if found

      @enums[name.to_s] = T::Enum.new(name, labels)
    end

    def state(name, type, initial: NONE, initial_in: NONE)
      @states << { name: name.to_sym, type: T.coerce(type), initial: initial, initial_in: initial_in }
    end

    def ghost(name, type, initial:) = state(name, type, initial: initial)

    def constant(name, *args)
      value = args.last
      type = args.length == 2 ? T.coerce(args[0]) : nil
      @constants[name.to_sym] = with_enums { ConcreteDsl.lift(value, type) }
    end

    def initially(&block) = @initially_block = block
    def invariant(name, &block) = @invariants << [name.to_s, block]
    def terminal(&block) = @terminal_block = block
    def action(name, **params, &block) = @actions << Action.new(self, name.to_s, params, block)

    %i[process migration responds reference].each do |m|
      define_method(m) { |*| raise Unsupported, m.to_s }
    end

    def with_enums
      saved = Thread.current[:concrete_dsl_enums]
      Thread.current[:concrete_dsl_enums] = @enums.values
      yield
    ensure
      Thread.current[:concrete_dsl_enums] = saved
    end

    def state_ref(values)
      names = @states.map { |s| s[:name] }
      StateRef.new(@constants.merge(names.zip(values.each_with_index.map { |v, i| CVal.ok(@states[i][:type], v) }).to_h))
    end

    # 状態変数ごとの初期値の候補。
    def candidates(st)
      type = st[:type]
      raw = if st[:initial_in].equal?(NONE)
              [st[:initial]]
            elsif st[:initial_in].is_a?(T::Common)
              return st[:initial_in].values
            else
              st[:initial_in].to_a
            end
      raw.map do |x|
        v = with_enums { ConcreteDsl.lift(x, type) }
        raise BuildError, "初期値が型に属さない" if v.err? || !type.member?(v.value)

        v.value
      end
    end

    def initial_states
      combos = @states.map { |st| candidates(st) }.reduce([[]]) { |acc, vs| acc.flat_map { |p| vs.map { |v| p + [v] } } }
      combos = combos.select { |vs| holds?(@initially_block, vs) } if @initially_block
      combos.uniq
    end

    def holds?(block, values)
      r = evaluate(block, values)
      raise BuildError, "初期条件の評価が失敗した" unless r == "true" || r == "false"

      r == "true"
    end

    # 性質のブロックを状態で評価し、"true"、"false"、または失敗の種類を返す。
    def evaluate(block, values)
      r = with_enums { ConcreteDsl.lift(instance_exec(state_ref(values), &block)) }
      ConcreteDsl.result(r)
    end
  end

  def result(r)
    return r.err if r.err?

    r.value ? "true" : "false"
  end

  # 操作。ブロックを、状態と引数の値ごとに実行し直す。
  class Action
    attr_reader :name, :params

    def initialize(model, name, params, block)
      @model = model
      @name = name
      @params = params
      @block = block
    end

    # 状態と引数（公開引数、内部選択の値）での結果。
    #   [:invalid]
    #   [:error, 起こりうる失敗の集合（[箇所, 状態変数名, 種類] の配列）]
    #   [:ok, 遷移先の状態, 出力（なければ nil）, 遷移契約の名前から結果へのハッシュ]
    def run(state, args, choices)
      @model.with_enums { run_in_scope(state, args, choices) }
    end

    def run_in_scope(state, args, choices)
      ctx = Context.new(@model, self, state, choices)
      ref = @model.state_ref(state)
      bound = []
      @params.each_with_index do |(_, spec), i|
        if spec.is_a?(Proc)
          inputs = [ref, *bound]
          inputs = inputs.first(spec.arity) unless spec.arity.negative?
          domain = ConcreteDsl.lift(ctx.instance_exec(*inputs, &spec))
          ctx.domains << [domain, args[i]]
          type = domain.type.elem
        else
          type = T.coerce(spec)
        end
        bound << CVal.ok(type, args[i])
      end
      ctx.instance_exec(ref, *bound, &@block)
      ctx.outcome
    end
  end

  # 操作のブロックの中の語彙。
  class Context
    include Functions

    Branch = Struct.new(:updates, :output)

    attr_reader :domains

    def initialize(model, action, state, choices)
      @model = model
      @action = action
      @state = state
      @choices = choices
      @chosen = 0
      @domains = []
      @guards = []
      @always = Branch.new([], nil)
      @branch = @always
      @condition = nil
      @accept = nil
      @reject = nil
      @ensures = []
    end

    def enum(name, *labels) = @model.enum(name, *labels)
    def guard(condition) = (@guards << ConcreteDsl.lift(condition)) && nil
    def unchanged = nil

    def update(**assignments)
      assignments.each do |name, value|
        index = @model.states.index { |s| s[:name] == name.to_sym } or raise BuildError, "状態変数 #{name}"
        @branch.updates << [index, ConcreteDsl.lift(value, @model.states[index][:type])]
      end
      nil
    end

    def choose(_name, domain)
      value = @choices.fetch(@chosen)
      @chosen += 1
      if domain.is_a?(CVal)
        @domains << [domain, value]
        CVal.ok(domain.type.elem, value)
      else
        CVal.ok(T.coerce(domain), value)
      end
    end

    def returns(value, type = nil)
      type &&= T.coerce(type)
      @branch.output = [ConcreteDsl.lift(value, type), type]
      nil
    end

    def accept_if(condition) = (@condition = ConcreteDsl.lift(condition)) && nil

    def on_accept(&block) = (@accept = in_branch(&block)) && nil
    def on_reject(&block) = (@reject = in_branch(&block)) && nil

    def in_branch
      @branch = Branch.new([], nil)
      yield
      @branch
    ensure
      @branch = @always
    end

    def ensures(name, &block) = @ensures << [name.to_s, block]

    def preserves(*names)
      names.each do |n|
        index = @model.states.index { |s| s[:name] == n.to_sym }
        @ensures << ["#{@action.name}_preserves_#{n}", ->(after, _) { after.public_send(n).eq(@model.state_ref(@state).public_send(n)) }]
        raise BuildError, "状態変数 #{n}" unless index
      end
      nil
    end

    def outcome
      # 動的ドメイン（公開引数、内部選択の順）。評価の失敗は guard の失敗になる。
      @domains.each do |domain, value|
        return [:error, [["guard", "", domain.err]]] if domain.err?
        return [:invalid] unless domain.value.include?(value)
      end
      g = all(*@guards)
      return [:error, [["guard", "", g.err]]] if g.err?
      return [:invalid] unless g.value

      errors = []
      updates = {}
      @always.updates.each { |i, v| updates[i] = v }
      output = @always.output
      if @condition
        accept = @accept || Branch.new([], nil)
        reject = @reject || Branch.new([], nil)
        chosen = @condition.err? ? nil : (@condition.value ? accept : reject)
        targets = (accept.updates.map(&:first) | reject.updates.map(&:first))
        targets.each do |i|
          updates[i] = if chosen.nil?
                         CVal.bad(@model.states[i][:type], @condition.err)
                       else
                         chosen.updates.to_h.fetch(i) { CVal.ok(@model.states[i][:type], @state[i]) }
                       end
        end
        if accept.output || reject.output
          type = [accept.output, reject.output].compact.map(&:last).compact.find { |t| !t.any? }
          value = chosen.nil? ? CVal.bad(T::ANY_INT, @condition.err) : chosen.output&.first
          output = [value, type]
        end
      end
      after = @state.dup
      updates.each do |i, v|
        st = @model.states[i]
        if v.err?
          errors << ["update", st[:name].to_s, v.err]
        elsif !st[:type].first_out_of_range(v.value).nil?
          errors << ["update", st[:name].to_s, "out_of_range"]
        else
          after[i] = v.value
        end
      end
      out = nil
      if output
        value, type = output
        if value.err?
          errors << ["output", "", value.err]
        elsif type && !type.first_out_of_range(value.value).nil?
          errors << ["output", "", "out_of_range"]
        else
          out = value
        end
      end
      return [:error, errors] unless errors.empty?

      after_ref = @model.state_ref(after)
      contracts = @ensures.to_h do |name, block|
        [name, ConcreteDsl.result(ConcreteDsl.lift(block.call(after_ref, out)))]
      end
      [:ok, after, out&.value, contracts]
    end
  end

  # 仕様の定義のブロックを実行する。
  def define(&block)
    model = Model.new
    model.instance_eval(&block)
    model
  end
end
