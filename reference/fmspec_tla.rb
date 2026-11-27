# frozen_string_literal: true

require "json"

# fmspec の IR を TLA+ の仕様に変換する。TLC との比較テスト（reference/test/tlc_test.rb）が使う。
#
# 型は、IR のすべての型（Bool、有界Int、Enum、Tuple、Record、Option、有限Set、有限Map、有界List）を扱う。
# 式は、IR のすべての演算子を扱う。動的ドメイン（`in`）も扱う。
# TLC の整数（32ビット）に収まらない値を使いうるモデルと、量化で展開する値が多すぎるモデルは、
# Unsupported で拒否する。
#
# この変換は参照実装（fmspec_reference.rb）にもエンジンにも依存しない。
# 評価の失敗は TLA+ の値として表す。式は結果 <<"ok", 値>> か <<"err", 種類>> になり、
# 演算子は IR の評価の順序どおりに、最初の失敗を伝える。
#
# 値は、TLA+ の値で次のように表す。
#
#   Bool、Int、Enum  TRUE と FALSE、整数、ラベルの文字列
#   Tuple、Record    列 <<...>>。Record はフィールドの順に並べる
#   Option          値がなければ <<>>、あれば <<値>>
#   Set             集合
#   Map             キーの集合を定義域とする関数
#   List            列
#
# TLA+ の集合と関数の等しさは外延的なので、IR の構造の等しさと一致する。
#
# 生成する仕様の状態は、状態変数 v0, v1, ... に、次の2つの変数を加えたものである。
#
#   bad  通常の状態では <<>>。評価エラーと遷移契約の違反は、遷移前の状態変数を保ち、
#        bad に事象を記録した後続のない状態（吸い込み状態）への遷移として表す。
#          <<"apply", 操作, <<公開引数>>, <<内部選択>>, 箇所, 状態変数名, 種類, 値>>
#          <<"contract", 操作, <<公開引数>>, <<内部選択>>, 遷移契約, 結果>>
#        有効な遷移は、遷移契約が成り立たなくても、遷移先の通常の状態にも進む。
#   obs  状態変数の関数で、状態の数を変えない。
#          <<不変条件ごとの結果, ..., 有効な遷移があるか, 終端条件の結果>>
#        結果は "true"、"false"、または失敗の種類の文字列である。
#
# TLC には不変条件を与えず、到達できる状態をすべて -dump で書き出させる。
# 比較テストは、書き出された状態を json_of で IR の値の JSON に直し、fmspec の安全性の意味での事象を読み取る。
module FmspecTla
  class Unsupported < StandardError; end

  # TLC の整数は32ビットである。中間の値も含めて、絶対値がこれ以下の式だけを変換する。
  LIMIT = 2**30
  # 量化は値を正規順に並べて展開する。展開する値の数の上限。
  MAX_UNROLL = 256
  # 値を列挙する型（キー型）の値の数の上限。IR と同じ。
  MAX_KEY_VALUES = 4096

  HEADER = <<~TLA
    Ok(v) == <<"ok", v>>
    Err(k) == <<"err", k>>
    IsOk(r) == r[1] = "ok"
    Str(r) == IF IsOk(r) THEN (IF r[2] THEN "true" ELSE "false") ELSE r[2]
    FloorDiv(a, b) == IF b > 0 THEN a \\div b ELSE (-a) \\div (-b)
    FloorMod(a, b) == a - b * FloorDiv(a, b)
    EmptyMap == [k \\in {} |-> 0]
    Put(m, k, v) == [x \\in DOMAIN m \\cup {k} |-> IF x = k THEN v ELSE m[x]]
    Del(m, k) == [x \\in DOMAIN m \\ {k} |-> m[x]]
    InSeq(s, x) == \\E i \\in 1..Len(s) : s[i] = x
  TLA

  def self.str(s)
    raise Unsupported, "文字列 #{s.inspect}" unless s.is_a?(String) && s.match?(/\A[\x20-\x7e]*\z/)

    "\"#{s.gsub("\\", "\\\\\\\\").gsub('"', '\\"')}\""
  end

  # 変換した式。TLA+ の結果の式、値の中の整数の絶対値の上限、式の型。
  Expr = Struct.new(:tla, :bound, :type)

  # 式の変換の文脈。参照は [TLA+ の名前, 型] の組で、局所変数は Expr（tla は値の式）で持つ。
  Ctx = Struct.new(:vars, :params, :choices, :nexts, :output, :locals, keyword_init: true) do
    def with_local(name, value)
      dup.tap { |c| c.locals = locals.merge(name => value) }
    end
  end

  BOOL = { "bool" => {} }.freeze
  INT = { "int" => nil }.freeze

  class Translator
    attr_reader :ir

    # actions と contracts は、対象の操作と遷移契約の名前の配列（nil ならすべて）。
    # 不変条件、終端条件、有効な遷移の有無は、すべて obs に書くので、対象を選ぶのは比較の側である。
    def initialize(ir, actions: nil, contracts: nil)
      @ir = ir
      @fresh = 0
      @enums = (ir["enums"] || []).to_h { |e| [e["name"], e["variants"]] }
      @states = ir["states"]
      @actions = ir["actions"] || []
      @targets = actions || @actions.map { |a| a["name"] }
      @contracts = (ir["contracts"] || []).select { |con| contracts.nil? || contracts.include?(con["name"]) }
      @consts = {}
      @values = {}
      check_supported
    end

    def module_text
      n = @states.length
      xs = Array.new(n) { |i| ["x#{i}", @states[i]["type"]] }
      x_names = xs.map(&:first)
      body = []
      body << "---- MODULE #{module_name} ----"
      body << "EXTENDS Integers, Sequences, FiniteSets"
      body << HEADER
      constants(body)
      vs = Array.new(n) { |i| "v#{i}" }
      body << "VARIABLES #{(vs + %w[bad obs]).join(', ')}"
      invariants = (ir["invariants"] || []).each_with_index.map do |inv, i|
        body << "Inv#{i}(#{x_names.join(', ')}) == #{prop(inv['expr'], ctx(vars: xs))}"
        "Str(Inv#{i}(#{x_names.join(', ')}))"
      end
      terminal = ir["terminal"] ? "Str(#{prop(ir['terminal'], ctx(vars: xs))})" : "\"false\""
      targets = @actions.each_with_index.select { |a, _| @targets.include?(a["name"]) }
      targets.each { |a, k| body << apply(a, k, xs) << first_bad_contract(a, k, xs) }
      enabled = targets.map { |a, k| quantified(a, "Apply#{k}(#{call_args(a, x_names)})[1] = \"ok\"") }
      body << "Enabled(#{x_names.join(', ')}) == #{enabled.empty? ? 'FALSE' : enabled.join(' \\/ ')}"
      body << "Obs(#{x_names.join(', ')}) == <<#{(invariants + ["Enabled(#{x_names.join(', ')})", terminal]).join(', ')}>>"
      body << init(xs, vs)
      body << next_relation(targets, vs)
      body << "===="
      "#{body.join("\n")}\n"
    end

    def cfg_text
      "INIT Init\nNEXT Next\n"
    end

    def module_name
      "M"
    end

    # TLC が書き出した値（Dump.parse の結果）を、型 type の値の JSON（トレースや証明書と同じ形）に直す。
    def json_of(type, value)
      kind, body = type.first
      case kind
      when "int", "bool", "enum" then value
      when "tuple" then body.zip(value).map { |t, v| json_of(t, v) }
      when "record" then body.zip(value).to_h { |f, v| [f["name"], json_of(f["type"], v)] }
      when "option" then value.empty? ? nil : { "some" => json_of(body, value[0]) }
      when "set" then value.items.map { |v| json_of(body, v) }.sort_by { |v| rank(body, v) }
      when "map"
        pairs(value).map { |k, v| [json_of(body["key"], k), json_of(body["value"], v)] }
                    .sort_by { |k, _| rank(body["key"], k) }
      when "list" then value.map { |v| json_of(body["of"], v) }
      end
    end

    private

    # ---- 型 ----

    def kind(type) = type.keys.first

    def check_supported
      raise Unsupported, "状態変数がない" if @states.empty?

      @states.each { |s| type_bound(s["type"]) }
      @actions.each do |a|
        ((a["params"] || []) + (a["choices"] || [])).each { |b| type_bound(b["type"]) }
        type_bound(a["output"]["type"]) if a["output"]
      end
    end

    def fresh(prefix = "r")
      @fresh += 1
      "#{prefix}#{@fresh}"
    end

    def ctx(vars:, params: [], choices: [], nexts: nil, output: nil)
      Ctx.new(vars: vars, params: params, choices: choices, nexts: nexts, output: output, locals: {})
    end

    # 型の値の中の整数の絶対値の上限。型の検査も兼ねる。
    def type_bound(type)
      raise Unsupported, "型 #{type.inspect}" unless type.is_a?(Hash) && type.size == 1

      kind, body = type.first
      case kind
      when "int"
        raise Unsupported, "整数の範囲 #{body}" if body["min"] > body["max"]

        check_bound([body["min"].abs, body["max"].abs].max)
      when "bool" then 0
      when "enum"
        raise Unsupported, "未定義のEnum" unless @enums.key?(body)

        0
      when "tuple" then body.map { |t| type_bound(t) }.max
      when "record" then body.map { |f| type_bound(f["type"]) }.max
      when "option" then type_bound(body)
      when "set" then values_of(body) && type_bound(body)
      when "map" then values_of(body["key"]) && [type_bound(body["key"]), type_bound(body["value"])].max
      when "list" then [type_bound(body["of"]), body["max"]].max
      else raise Unsupported, "型 #{kind}"
      end
    end

    # キー型の値を、正規順に並べた JSON の値の列。
    def values_of(type)
      @values[type] ||= begin
        kind, body = type.first
        values = case kind
                 when "bool" then [false, true]
                 when "int" then (body["min"]..body["max"]).to_a
                 when "enum" then @enums.fetch(body)
                 when "tuple" then product(body.map { |t| values_of(t) })
                 when "record"
                   product(body.map { |f| values_of(f["type"]) }).map do |vs|
                     body.zip(vs).to_h { |f, v| [f["name"], v] }
                   end
                 when "option" then [nil] + values_of(body).map { |v| { "some" => v } }
                 else raise Unsupported, "キー型 #{kind}"
                 end
        raise Unsupported, "キー型の値が多すぎる" if values.length > MAX_KEY_VALUES

        values
      end
    end

    def product(lists)
      lists.reduce([[]]) do |acc, vs|
        raise Unsupported, "キー型の値が多すぎる" if acc.length * vs.length > MAX_KEY_VALUES

        acc.flat_map { |p| vs.map { |v| p + [v] } }
      end
    end

    def rank(type, value)
      (@ranks ||= {})[type] ||= values_of(type).each_with_index.to_h
      @ranks[type].fetch(value)
    end

    # JSON の値を TLA+ の値の式にする。
    def literal(type, value)
      kind, body = type.first
      case kind
      when "int" then value.to_s
      when "bool" then value ? "TRUE" : "FALSE"
      when "enum" then FmspecTla.str(value)
      when "tuple" then "<<#{body.zip(value).map { |t, v| literal(t, v) }.join(', ')}>>"
      when "record" then "<<#{body.map { |f| literal(f['type'], value.fetch(f['name'])) }.join(', ')}>>"
      when "option" then value.nil? ? "<<>>" : "<<#{literal(body, value['some'])}>>"
      end
    end

    # 型のすべての値の集合（引数のドメイン）。
    def domain_set(type)
      kind, body = type.first
      case kind
      when "int" then "(#{body['min']}..#{body['max']})"
      when "bool" then "BOOLEAN"
      when "enum" then "{#{@enums.fetch(body).map { |v| FmspecTla.str(v) }.join(', ')}}"
      when "tuple", "record"
        types = kind == "tuple" ? body : body.map { |f| f["type"] }
        names = types.map { fresh("e") }
        "{<<#{names.join(', ')}>> : #{names.zip(types).map { |n, t| "#{n} \\in #{domain_set(t)}" }.join(', ')}}"
      when "option"
        e = fresh("e")
        "({<<>>} \\cup {<<#{e}>> : #{e} \\in #{domain_set(body)}})"
      when "set" then "(SUBSET #{domain_set(body)})"
      when "map"
        d = fresh("d")
        "(UNION {[#{d} -> #{domain_set(body['value'])}] : #{d} \\in SUBSET #{domain_set(body['key'])}})"
      when "list"
        n = fresh("n")
        "(UNION {[1..#{n} -> #{domain_set(body['of'])}] : #{n} \\in 0..#{body['max']}})"
      end
    end

    # 値 v（TLA+ の式）が型に属するか。Set、Map、List の値は、式の型が要素の型を範囲まで含めて持つので、
    # 型の合う値はつねに属する。整数の範囲を区別しないのは、Int、Tuple、Record、Option の中だけである。
    def in_type(type, v)
      kind, body = type.first
      case kind
      when "int" then "(#{body['min']} <= #{v} /\\ #{v} <= #{body['max']})"
      when "tuple", "record"
        types = kind == "tuple" ? body : body.map { |f| f["type"] }
        parts = types.each_with_index.map { |t, i| in_type(t, "#{v}[#{i + 1}]") }.reject { |p| p == "TRUE" }
        parts.empty? ? "TRUE" : "(#{parts.join(' /\\ ')})"
      when "option"
        inner = in_type(body, "#{v}[1]")
        inner == "TRUE" ? "TRUE" : "(#{v} = <<>> \\/ #{inner})"
      else "TRUE"
      end
    end

    # 値 v を型の場所に置くときの、スロットの順で最初の範囲外の整数。<<>> か <<整数>>。
    def first_out_of_range(type, v)
      kind, body = type.first
      case kind
      when "int" then "(IF #{in_type(type, v)} THEN <<>> ELSE <<#{v}>>)"
      when "tuple", "record"
        types = kind == "tuple" ? body : body.map { |f| f["type"] }
        types.each_with_index.reverse_each.reduce("<<>>") do |rest, (t, i)|
          part = first_out_of_range(t, "#{v}[#{i + 1}]")
          next rest if part == "<<>>"

          f = fresh("f")
          "(LET #{f} == #{part} IN IF #{f} # <<>> THEN #{f} ELSE #{rest})"
        end
      when "option"
        part = first_out_of_range(body, "#{v}[1]")
        part == "<<>>" ? "<<>>" : "(IF #{v} = <<>> THEN <<>> ELSE #{part})"
      else "<<>>"
      end
    end

    def constants(body)
      (ir["constants"] || []).each_with_index do |c, i|
        e = expr(c["value"], ctx(vars: []))
        type_bound(c["type"])
        body << "Const#{i} == #{e.tla}"
        @consts[c["name"]] = Expr.new("Const#{i}[2]", e.bound, c["type"])
      end
    end

    def check_bound(bound)
      raise Unsupported, "整数の上限 #{bound}" if bound > LIMIT

      bound
    end

    def prop(e, c)
      expr(e, c).tla
    end

    # ---- 式 ----

    # 部分式を順に評価し、最初の失敗を伝える。steps は [Expr, 要素の型または nil] の列で、
    # 要素の型があれば、評価した値がその型に属さないとき not_in_domain で失敗する（次の部分式は評価しない）。
    # ブロックは値の式の列を受け取り、結果の式を返す。
    def chain(steps)
      names = steps.map { fresh }
      inner = yield(names.map { |n| "#{n}[2]" })
      steps.zip(names).reverse.reduce(inner) do |rest, ((e, elem), n)|
        check = elem ? in_type(elem, "#{n}[2]") : "TRUE"
        rest = "IF ~#{check} THEN Err(\"not_in_domain\") ELSE #{rest}" unless check == "TRUE"
        "(LET #{n} == #{e.tla} IN IF ~IsOk(#{n}) THEN #{n} ELSE #{rest})"
      end
    end

    def ok(tla, bound, type)
      Expr.new("Ok(#{tla})", check_bound(bound), type)
    end

    def ref(pairs, index)
      raise Unsupported, "参照 #{index}" unless index.is_a?(Integer) && index >= 0 && index < pairs.length

      name, type = pairs[index]
      ok(name, type_bound(type), type)
    end

    # 式を変換する。
    def expr(e, c)
      raise Unsupported, "式 #{e.inspect}" unless e.is_a?(Hash) && e.size == 1

      op, arg = e.first
      case op
      when "int" then ok(arg.to_s, arg.abs, INT)
      when "bool" then ok(arg ? "TRUE" : "FALSE", 0, BOOL)
      when "enum"
        raise Unsupported, "Enumのラベル" unless @enums.fetch(arg["type"]).include?(arg["variant"])

        ok(FmspecTla.str(arg["variant"]), 0, { "enum" => arg["type"] })
      when "var" then ref(c.vars, arg)
      when "next"
        raise Unsupported, "next の位置" unless c.nexts

        ref(c.nexts, arg)
      when "param" then ref(c.params, arg)
      when "choice" then ref(c.choices, arg)
      when "output"
        raise Unsupported, "output の位置" unless c.output

        ref([c.output], 0)
      when "const"
        v = @consts.fetch(arg) { raise Unsupported, "定数 #{arg}" }
        ok(v.tla, v.bound, v.type)
      when "local"
        v = c.locals.fetch(arg) { raise Unsupported, "局所変数 #{arg}" }
        ok(v.tla, v.bound, v.type)
      when "add", "sub", "mul", "div", "mod", "lt", "le", "gt", "ge", "eq", "ne" then binary(op, arg, c)
      when "not"
        a = expr(arg[0], c)
        Expr.new(chain([[a]]) { |(x)| "Ok(~#{x})" }, 0, BOOL)
      when "all", "any" then Expr.new(junction(op, arg, c), 0, BOOL)
      when "implies"
        r = fresh
        p = expr(arg[0], c)
        q = expr(arg[1], c)
        Expr.new("(LET #{r} == #{p.tla} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF ~#{r}[2] THEN Ok(TRUE) ELSE #{q.tla})", 0, BOOL)
      when "ite"
        r = fresh
        cond = expr(arg[0], c)
        a = expr(arg[1], c)
        b = expr(arg[2], c)
        Expr.new("(LET #{r} == #{cond.tla} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{r}[2] THEN #{a.tla} ELSE #{b.tla})",
                 [a.bound, b.bound].max, a.type)
      when "let"
        r = fresh
        value = expr(arg["value"], c)
        body = expr(arg["body"], c.with_local(arg["name"], Expr.new("#{r}[2]", value.bound, value.type)))
        Expr.new("(LET #{r} == #{value.tla} IN IF ~IsOk(#{r}) THEN #{r} ELSE #{body.tla})", body.bound, body.type)
      when "forall", "exists" then Expr.new(quantifier(op, arg, c), 0, BOOL)
      else composite(op, arg, c)
      end
    end

    BINARY = {
      "add" => ->(x, y) { "Ok(#{x} + #{y})" },
      "sub" => ->(x, y) { "Ok(#{x} - #{y})" },
      "mul" => ->(x, y) { "Ok(#{x} * #{y})" },
      "div" => ->(x, y) { "IF #{y} = 0 THEN Err(\"division_by_zero\") ELSE Ok(FloorDiv(#{x}, #{y}))" },
      "mod" => ->(x, y) { "IF #{y} = 0 THEN Err(\"division_by_zero\") ELSE Ok(FloorMod(#{x}, #{y}))" },
      "lt" => ->(x, y) { "Ok(#{x} < #{y})" },
      "le" => ->(x, y) { "Ok(#{x} <= #{y})" },
      "gt" => ->(x, y) { "Ok(#{x} > #{y})" },
      "ge" => ->(x, y) { "Ok(#{x} >= #{y})" },
      "eq" => ->(x, y) { "Ok(#{x} = #{y})" },
      "ne" => ->(x, y) { "Ok(#{x} # #{y})" }
    }.freeze

    def binary(op, args, c)
      a = expr(args[0], c)
      b = expr(args[1], c)
      bound = case op
              when "add", "sub" then a.bound + b.bound
              when "mul" then a.bound * b.bound
              when "div" then a.bound
              when "mod" then b.bound
              else 0
              end
      type = %w[add sub mul div mod].include?(op) ? INT : BOOL
      Expr.new(chain([[a], [b]]) { |(x, y)| BINARY.fetch(op).call(x, y) }, check_bound(bound), type)
    end

    # all は最初の偽で、any は最初の真で打ち切る。
    def junction(op, args, c)
      stop, empty, early = op == "all" ? ["~", "TRUE", "FALSE"] : ["", "FALSE", "TRUE"]
      args.reverse.reduce("Ok(#{empty})") do |rest, a|
        r = fresh
        tla = expr(a, c).tla
        "(LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{stop}#{r}[2] THEN Ok(#{early}) ELSE #{rest})"
      end
    end

    # 量化。値を正規順に展開する。forall は最初の偽で、exists は最初の真で打ち切る。
    # `in` が Set なら要素の型の値のうち含まれるもの、Map ならキー型の値のうちキーであるもの、
    # List なら位置の順に要素をたどる。
    def quantifier(op, arg, c)
      stop, empty, early = op == "forall" ? ["~", "TRUE", "FALSE"] : ["", "FALSE", "TRUE"]
      l = fresh("l")
      q = fresh("Q")
      step = lambda do |value, rest|
        r = fresh
        "(LET #{r} == #{q}(#{value}) IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{stop}#{r}[2] THEN Ok(#{early}) ELSE #{rest})"
      end
      unroll = lambda do |values|
        raise Unsupported, "量化で展開する値が多すぎる" if values.length > MAX_UNROLL

        values
      end
      if arg.key?("in")
        coll = expr(arg["in"], c)
        kind, body = coll.type.first
        s = fresh("s")
        elem = { "set" => body, "map" => body.is_a?(Hash) && body["key"], "list" => body.is_a?(Hash) && body["of"] }[kind]
        raise Unsupported, "量化の範囲 #{kind}" unless elem

        body_expr = expr(arg["body"], c.with_local(arg["name"], Expr.new(l, type_bound(elem), elem)))
        chain_text = case kind
                     when "set", "map"
                       domain = kind == "set" ? "#{s}[2]" : "DOMAIN #{s}[2]"
                       unroll.(values_of(elem)).reverse.reduce("Ok(#{empty})") do |rest, v|
                         lit = literal(elem, v)
                         "(IF #{lit} \\in #{domain} THEN #{step.(lit, rest)} ELSE #{rest})"
                       end
                     else
                       unroll.((1..body["max"]).to_a).reverse.reduce("Ok(#{empty})") do |rest, i|
                         "(IF Len(#{s}[2]) < #{i} THEN Ok(#{empty}) ELSE #{step.("#{s}[2][#{i}]", rest)})"
                       end
                     end
        "(LET #{s} == #{coll.tla} IN IF ~IsOk(#{s}) THEN #{s} ELSE LET #{q}(#{l}) == #{body_expr.tla} IN #{chain_text})"
      else
        type = arg["type"]
        type_bound(type)
        body_expr = expr(arg["body"], c.with_local(arg["name"], Expr.new(l, type_bound(type), type)))
        chain_text = unroll.(values_of(type)).reverse.reduce("Ok(#{empty})") { |rest, v| step.(literal(type, v), rest) }
        "(LET #{q}(#{l}) == #{body_expr.tla} IN #{chain_text})"
      end
    end

    def size_bound(type)
      kind, body = type.first
      case kind
      when "set" then values_of(body).length
      when "map" then values_of(body["key"]).length
      else body["max"]
      end
    end

    # 複合型の値を作る演算と、調べる演算。
    def composite(op, arg, c)
      sub = ->(e) { expr(e, c) }
      case op
      when "tuple"
        items = arg.map(&sub)
        Expr.new(chain(items.map { |i| [i] }) { |vs| "Ok(<<#{vs.join(', ')}>>)" },
                 items.map(&:bound).max || 0, { "tuple" => items.map(&:type) })
      when "record"
        items = arg.map { |f| sub.(f["expr"]) }
        type = { "record" => arg.zip(items).map { |f, i| { "name" => f["name"], "type" => i.type } } }
        Expr.new(chain(items.map { |i| [i] }) { |vs| "Ok(<<#{vs.join(', ')}>>)" }, items.map(&:bound).max || 0, type)
      when "nth"
        of = sub.(arg["of"])
        index = arg["index"]
        raise Unsupported, "nth" unless kind(of.type) == "tuple" && index.is_a?(Integer)

        Expr.new(chain([[of]]) { |(v)| "Ok(#{v}[#{index + 1}])" }, of.bound, of.type["tuple"].fetch(index))
      when "field"
        of = sub.(arg["of"])
        raise Unsupported, "field" unless kind(of.type) == "record"

        i = of.type["record"].index { |f| f["name"] == arg["name"] } or raise Unsupported, "field #{arg['name']}"
        Expr.new(chain([[of]]) { |(v)| "Ok(#{v}[#{i + 1}])" }, of.bound, of.type["record"][i]["type"])
      when "none"
        type_bound(arg)
        ok("<<>>", 0, { "option" => arg })
      when "some"
        a = sub.(arg[0])
        Expr.new(chain([[a]]) { |(v)| "Ok(<<#{v}>>)" }, a.bound, { "option" => a.type })
      when "is_some", "is_none"
        a = sub.(arg[0])
        Expr.new(chain([[a]]) { |(v)| "Ok(Len(#{v}) #{op == 'is_some' ? '>' : '='} 0)" }, 0, BOOL)
      when "unwrap"
        a = sub.(arg[0])
        Expr.new(chain([[a]]) { |(v)| "IF Len(#{v}) = 0 THEN Err(\"none\") ELSE Ok(#{v}[1])" }, a.bound, a.type["option"])
      when "set"
        type = { "set" => arg["of"] }
        items = arg["items"].map(&sub)
        Expr.new(chain(items.map { |i| [i, arg["of"]] }) { |vs| "Ok({#{vs.join(', ')}})" }, type_bound(type), type)
      when "map"
        type = { "map" => { "key" => arg["key"], "value" => arg["value"] } }
        steps = arg["items"].flat_map { |k, v| [[sub.(k), arg["key"]], [sub.(v), arg["value"]]] }
        tla = chain(steps) do |vs|
          "Ok(#{vs.each_slice(2).reduce('EmptyMap') { |m, (k, v)| "Put(#{m}, #{k}, #{v})" }})"
        end
        Expr.new(tla, type_bound(type), type)
      when "list"
        type = { "list" => { "of" => arg["of"], "max" => arg["max"] } }
        raise Unsupported, "List のリテラルが長い" if arg["items"].length > arg["max"]

        items = arg["items"].map(&sub)
        Expr.new(chain(items.map { |i| [i, arg["of"]] }) { |vs| "Ok(<<#{vs.join(', ')}>>)" }, type_bound(type), type)
      when "contains"
        coll = sub.(arg[0])
        x = sub.(arg[1])
        test = kind(coll.type) == "set" ? ->(s, v) { "#{v} \\in #{s}" } : ->(l, v) { "InSeq(#{l}, #{v})" }
        Expr.new(chain([[coll], [x]]) { |(s, v)| "Ok(#{test.(s, v)})" }, 0, BOOL)
      when "insert", "remove"
        s = sub.(arg[0])
        x = sub.(arg[1])
        elem = s.type["set"]
        tla = chain([[s], [x, op == "insert" ? elem : nil]]) do |(a, v)|
          op == "insert" ? "Ok(#{a} \\cup {#{v}})" : "Ok(#{a} \\ {#{v}})"
        end
        Expr.new(tla, s.bound, s.type)
      when "union", "intersection", "difference", "subset"
        a = sub.(arg[0])
        b = sub.(arg[1])
        sym = { "union" => "\\cup", "intersection" => "\\cap", "difference" => "\\", "subset" => "\\subseteq" }.fetch(op)
        Expr.new(chain([[a], [b]]) { |(x, y)| "Ok(#{x} #{sym} #{y})" }, op == "subset" ? 0 : a.bound,
                 op == "subset" ? BOOL : a.type)
      when "size", "is_empty"
        coll = sub.(arg[0])
        size = case kind(coll.type)
               when "set" then ->(v) { "Cardinality(#{v})" }
               when "map" then ->(v) { "Cardinality(DOMAIN #{v})" }
               else ->(v) { "Len(#{v})" }
               end
        if op == "size"
          Expr.new(chain([[coll]]) { |(v)| "Ok(#{size.(v)})" }, check_bound(size_bound(coll.type)), INT)
        else
          Expr.new(chain([[coll]]) { |(v)| "Ok(#{size.(v)} = 0)" }, 0, BOOL)
        end
      when "has_key", "get"
        m = sub.(arg[0])
        k = sub.(arg[1])
        if op == "has_key"
          Expr.new(chain([[m], [k]]) { |(a, b)| "Ok(#{b} \\in DOMAIN #{a})" }, 0, BOOL)
        else
          value = m.type["map"]["value"]
          tla = chain([[m], [k]]) { |(a, b)| "IF #{b} \\in DOMAIN #{a} THEN Ok(#{a}[#{b}]) ELSE Err(\"missing_key\")" }
          Expr.new(tla, type_bound(value), value)
        end
      when "put"
        m = sub.(arg[0])
        types = m.type["map"]
        tla = chain([[m], [sub.(arg[1]), types["key"]], [sub.(arg[2]), types["value"]]]) do |(a, k, v)|
          "Ok(Put(#{a}, #{k}, #{v}))"
        end
        Expr.new(tla, m.bound, m.type)
      when "delete"
        m = sub.(arg[0])
        Expr.new(chain([[m], [sub.(arg[1])]]) { |(a, k)| "Ok(Del(#{a}, #{k}))" }, m.bound, m.type)
      when "keys"
        m = sub.(arg[0])
        key = m.type["map"]["key"]
        Expr.new(chain([[m]]) { |(a)| "Ok(DOMAIN #{a})" }, type_bound(key), { "set" => key })
      when "at"
        l = sub.(arg[0])
        i = sub.(arg[1])
        tla = chain([[l], [i]]) do |(a, n)|
          "IF #{n} >= 0 /\\ #{n} < Len(#{a}) THEN Ok(#{a}[#{n} + 1]) ELSE Err(\"index_out_of_range\")"
        end
        Expr.new(tla, l.bound, l.type["list"]["of"])
      when "first", "last"
        l = sub.(arg[0])
        tla = chain([[l]]) do |(a)|
          "IF Len(#{a}) = 0 THEN Err(\"empty\") ELSE Ok(#{a}[#{op == 'first' ? '1' : "Len(#{a})"}])"
        end
        Expr.new(tla, l.bound, l.type["list"]["of"])
      when "push"
        l = sub.(arg[0])
        body = l.type["list"]
        tla = chain([[l], [sub.(arg[1]), body["of"]]]) do |(a, x)|
          "IF Len(#{a}) >= #{body['max']} THEN Err(\"full\") ELSE Ok(Append(#{a}, #{x}))"
        end
        Expr.new(tla, l.bound, l.type)
      when "pop", "shift"
        l = sub.(arg[0])
        tla = chain([[l]]) do |(a)|
          rest = op == "pop" ? "SubSeq(#{a}, 1, Len(#{a}) - 1)" : "Tail(#{a})"
          "IF Len(#{a}) = 0 THEN Err(\"empty\") ELSE Ok(#{rest})"
        end
        Expr.new(tla, l.bound, l.type)
      else
        raise Unsupported, "演算子 #{op}"
      end
    end

    # ---- 操作 ----

    def bindings(action)
      ps = (action["params"] || []).each_with_index.map { |p, i| ["p#{i}", p["type"]] }
      cs = (action["choices"] || []).each_with_index.map { |p, i| ["c#{i}", p["type"]] }
      [ps, cs]
    end

    def call_args(action, xs)
      ps, cs = bindings(action)
      (xs + ps.map(&:first) + cs.map(&:first)).join(", ")
    end

    # 引数を束縛して body を書く。引数がなければそのまま。
    def quantified(action, body)
      ps, cs = bindings(action)
      all = ps + cs
      return "(#{body})" if all.empty?

      "(\\E #{all.map { |n, t| "#{n} \\in #{domain_set(t)}" }.join(', ')} : #{body})"
    end

    # 置く値の範囲の検査。範囲外なら、箇所と状態変数名を付けた適用の失敗にする。
    def store_check(type, v, site, name)
      check = first_out_of_range(type, v)
      return "" if check == "<<>>"

      f = fresh("f")
      "LET #{f} == #{check} IN IF #{f} # <<>> THEN <<\"err\", #{FmspecTla.str(site)}, #{name}, \"out_of_range\", #{f}[1]>> ELSE"
    end

    # 操作の適用。<<"invalid">>、<<"err", 箇所, 状態変数名, 種類, 値>>、<<"ok", <<遷移先>>, 出力>> のどれか。
    # 動的ドメイン（宣言順。評価の失敗は guard）、guard、更新（記述順。範囲は更新ごとに調べる）、出力の順に評価する。
    def apply(action, k, xs)
      ps, cs = bindings(action)
      c = ctx(vars: xs, params: ps, choices: cs)
      nexts = xs.map(&:first)
      steps = []
      ((action["params"] || []).zip(ps) + (action["choices"] || []).zip(cs)).each do |b, (name, _)|
        next unless b["in"]

        d = expr(b["in"], c)
        r = fresh
        member = kind(d.type) == "set" ? "#{name} \\in #{r}[2]" : "InSeq(#{r}[2], #{name})"
        steps << "LET #{r} == #{d.tla} IN IF ~IsOk(#{r}) THEN <<\"err\", \"guard\", \"\", #{r}[2], 0>> " \
                 "ELSE IF ~(#{member}) THEN <<\"invalid\">> ELSE"
      end
      guard = action["guard"] ? prop(action["guard"], c) : "Ok(TRUE)"
      g = fresh
      steps << "LET #{g} == #{guard} IN IF ~IsOk(#{g}) THEN <<\"err\", \"guard\", \"\", #{g}[2], 0>> " \
               "ELSE IF ~#{g}[2] THEN <<\"invalid\">> ELSE"
      (action["updates"] || []).each do |u|
        t = u["target"]
        raise Unsupported, "更新の対象 #{t}" unless t.is_a?(Integer) && t >= 0 && t < xs.length

        tla = prop(u["expr"], c)
        r = fresh
        name = FmspecTla.str(@states[t]["name"])
        steps << "LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN <<\"err\", \"update\", #{name}, #{r}[2], 0>> ELSE"
        steps << store_check(@states[t]["type"], "#{r}[2]", "update", name)
        nexts[t] = "#{r}[2]"
      end
      out = "<<>>"
      if action["output"]
        tla = prop(action["output"]["expr"], c)
        r = fresh
        steps << "LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN <<\"err\", \"output\", \"\", #{r}[2], 0>> ELSE"
        steps << store_check(action["output"]["type"], "#{r}[2]", "output", "\"\"")
        out = "#{r}[2]"
      end
      result = "<<\"ok\", <<#{nexts.join(', ')}>>, #{out}>>"
      "Apply#{k}(#{call_args(action, xs.map(&:first))}) ==\n  #{steps.reject(&:empty?).join("\n  ")}\n  #{result}"
    end

    # 対象の遷移契約のうち、記述順で最初に真でないもの。<<>> か <<遷移契約, 結果>>。
    def first_bad_contract(action, k, xs)
      ps, cs = bindings(action)
      ns = xs.each_with_index.map { |(_, t), i| ["n#{i}", t] }
      output = action["output"] ? ["out", action["output"]["type"]] : nil
      c = ctx(vars: xs, params: ps, choices: cs, nexts: ns, output: output)
      contracts = @contracts.select { |con| con["action"] == action["name"] }
      body = contracts.reverse.reduce("<<>>") do |rest, con|
        r = fresh
        "(LET #{r} == #{prop(con['expr'], c)} IN " \
          "IF Str(#{r}) # \"true\" THEN <<#{FmspecTla.str(con['name'])}, Str(#{r})>> ELSE #{rest})"
      end
      "Contract#{k}(#{[call_args(action, xs.map(&:first)), *ns.map(&:first), 'out'].join(', ')}) == #{body}"
    end

    # 状態変数は v0, v1, ... で、演算子の引数（x0, x1, ...）とは別の名前にする。TLA+ は名前の隠蔽を許さない。
    def init(xs, vs)
      parts = @states.each_with_index.map do |s, i|
        cands = s.key?("initial_in") ? s["initial_in"] : [s["initial"]]
        "v#{i} \\in {#{cands.map { |e| "(#{prop(e, ctx(vars: []))})[2]" }.join(', ')}}"
      end
      constraint = nil
      if ir["initial_constraint"]
        r = fresh
        parts << "Constraint(#{vs.join(', ')})"
        constraint = "Constraint(#{xs.map(&:first).join(', ')}) == " \
                     "LET #{r} == #{prop(ir['initial_constraint'], ctx(vars: xs))} IN IsOk(#{r}) /\\ #{r}[2]"
      end
      parts << "bad = <<>>" << "obs = Obs(#{vs.join(', ')})"
      [constraint, "Init ==\n  /\\ #{parts.join("\n  /\\ ")}"].compact.join("\n")
    end

    def next_relation(targets, vs)
      steps = targets.map do |action, k|
        ps, cs = bindings(action)
        args = "<<#{ps.map(&:first).join(', ')}>>, <<#{cs.map(&:first).join(', ')}>>"
        name = FmspecTla.str(action["name"])
        primed = vs.each_with_index.map { |x, i| "#{x}' = r[2][#{i + 1}]" }
        ns = vs.each_index.map { |i| "r[2][#{i + 1}]" }
        unchanged = "UNCHANGED <<#{(vs + ['obs']).join(', ')}>>"
        error = "r[1] = \"err\" /\\ bad' = <<\"apply\", #{name}, #{args}, r[2], r[3], r[4], r[5]>> /\\ #{unchanged}"
        normal = "r[1] = \"ok\" /\\ #{primed.join(' /\\ ')} /\\ bad' = <<>> /\\ obs' = Obs(#{ns.join(', ')})"
        contract = "r[1] = \"ok\" /\\ (LET b == Contract#{k}(#{[call_args(action, vs), *ns, 'r[3]'].join(', ')}) IN " \
                   "b # <<>> /\\ bad' = <<\"contract\", #{name}, #{args}, b[1], b[2]>>) /\\ #{unchanged}"
        # TLA+ の箇条書き（/\ と \/ の列）は字下げに意味があるので、括弧と中置の演算子だけで書く。
        body = "LET r == Apply#{k}(#{call_args(action, vs)}) IN\n    (#{error})\n    \\/ (#{normal})\n    \\/ (#{contract})"
        quantified(action, body)
      end
      "Next ==\n  bad = <<>> /\\ (#{steps.empty? ? 'FALSE' : steps.join("\n  \\/ ")})"
    end

    # Map の値の、キーと値の組。TLC は定義域が 1..n の関数を列として、
    # 定義域が識別子の文字列の関数をレコードとして、それ以外を k :> v @@ ... として書き出す。
    def pairs(value)
      case value
      when Array then value.each_with_index.map { |v, i| [i + 1, v] }
      when Dump::Fcn then value.pairs
      when Dump::TSet
        raise ArgumentError, "Map として読めない集合" unless value.items.empty?

        []
      end
    end
  end

  # TLC の -dump が書き出す状態を読む。各状態は変数名から値へのハッシュである。
  # 値は、整数、真偽値、文字列、列（Array）、集合（TSet）、関数とレコード（Fcn）で表す。
  module Dump
    TSet = Struct.new(:items)
    Fcn = Struct.new(:pairs)

    module_function

    def parse(text)
      text.split(/^State \d+:\n/).drop(1).map { |block| state(block) }
    end

    # 状態の「/\ 変数 = 値」の並びを読む。
    def state(block)
      block.scan(%r{^/\\ (\w+) = (.*?)(?=\n/\\ |\n*\z)}m).to_h { |name, value| [name, value(value.gsub(/\s+/, " "))] }
    end

    # -dump dot の出力を読む。状態、遷移、初期状態からの最短の遷移回数を返す。
    # 状態は変数名から値へのハッシュで、"_depth" に最短の遷移回数を加える。初期状態は塗りつぶして書き出される。
    def parse_dot(text)
      nodes = {}
      initial = []
      edges = Hash.new { |h, k| h[k] = [] }
      text.each_line do |line|
        if (m = line.match(/\A(-?\d+) \[label="((?:[^"\\]|\\.)*)"(,style = filled)?\]/))
          label = m[2].gsub(/\\(.)/) { ::Regexp.last_match(1) == "n" ? "\n" : ::Regexp.last_match(1) }
          nodes[m[1]] = state(label)
          initial << m[1] if m[3]
        elsif (m = line.match(/\A(-?\d+) -> (-?\d+) /))
          edges[m[1]] << m[2]
        end
      end
      depth = initial.to_h { |id| [id, 0] }
      frontier = initial
      level = 0
      until frontier.empty?
        level += 1
        frontier = frontier.flat_map { |id| edges[id] }.uniq.reject { |id| depth.key?(id) }
        frontier.each { |id| depth[id] = level }
      end
      nodes.map { |id, st| st.merge("_depth" => depth.fetch(id)) }
    end

    def value(text)
      v, rest = read(text.strip)
      raise ArgumentError, "読めない値: #{text}" unless rest.strip.empty?

      v
    end

    # 区切り文字 sep で区切った要素の列を、close まで読む。
    def items(s, close)
      rest = s.lstrip
      return [[], rest[close.length..]] if rest.start_with?(close)

      list = []
      loop do
        item, rest = yield(rest)
        list << item
        rest = rest.lstrip
        if rest.start_with?(",") || rest.start_with?("@@")
          rest = rest.sub(/\A(,|@@)/, "")
        elsif rest.start_with?(close)
          return [list, rest[close.length..]]
        else
          raise ArgumentError, "読めない値: #{s}"
        end
      end
    end

    def read(s)
      s = s.lstrip
      if (m = s.match(/\A-?\d+/)) then [Integer(m[0]), m.post_match]
      elsif (m = s.match(/\ATRUE\b/)) then [true, m.post_match]
      elsif (m = s.match(/\AFALSE\b/)) then [false, m.post_match]
      elsif (m = s.match(/\A"((?:[^"\\]|\\.)*)"/)) then [m[1].gsub(/\\(.)/, '\1'), m.post_match]
      elsif s.start_with?("<<") then items(s[2..], ">>") { |r| read(r) }
      elsif s.start_with?("{")
        list, rest = items(s[1..], "}") { |r| read(r) }
        [TSet.new(list), rest]
      elsif s.start_with?("[")
        list, rest = items(s[1..], "]") do |r|
          m = r.lstrip.match(/\A(\w+)\s*\|->/) or raise ArgumentError, "読めないレコード: #{s}"
          v, r2 = read(m.post_match)
          [[m[1], v], r2]
        end
        [Fcn.new(list), rest]
      elsif s.start_with?("(")
        list, rest = items(s[1..], ")") do |r|
          k, r2 = read(r)
          r2 = r2.lstrip
          raise ArgumentError, "読めない関数: #{s}" unless r2.start_with?(":>")

          v, r3 = read(r2[2..])
          [[k, v], r3]
        end
        [Fcn.new(list), rest]
      else
        raise ArgumentError, "読めない値: #{s}"
      end
    end
  end
end
