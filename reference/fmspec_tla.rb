# frozen_string_literal: true

require "json"

# fmspec の IR を TLA+ の仕様に変換する。TLC との比較テスト（reference/test/tlc_test.rb）が使う。
#
# 対象は、Bool、有界Int、Enum の状態と引数を持つモデルである。式は、整数の算術と比較、
# 床除算と剰余、論理演算、条件式、let、型の全体をたどる量化、定数を扱う。
# 複合型、動的ドメイン（`in`）、TLC の整数（32ビット）に収まらない値を使うモデルは
# Unsupported で拒否する。
#
# この変換は参照実装（fmspec_reference.rb）にもエンジンにも依存しない。
# 評価の失敗は TLA+ の値として表す。式は結果 <<"ok", 値>> か <<"err", 種類>> になり、
# 演算子は IR の評価の順序どおりに、最初の失敗を伝える。
#
# 生成する仕様の状態は、状態変数 x0, x1, ... に、次の2つの変数を加えたものである。
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
# 比較テストは、書き出された状態から、fmspec の安全性の意味での事象を読み取る。
module FmspecTla
  class Unsupported < StandardError; end

  # TLC の整数は32ビットである。中間の値も含めて、絶対値がこれ以下の式だけを変換する。
  LIMIT = 2**30

  HEADER = <<~TLA
    Ok(v) == <<"ok", v>>
    Err(k) == <<"err", k>>
    IsOk(r) == r[1] = "ok"
    Str(r) == IF IsOk(r) THEN (IF r[2] THEN "true" ELSE "false") ELSE r[2]
    FloorDiv(a, b) == IF b > 0 THEN a \\div b ELSE (-a) \\div (-b)
    FloorMod(a, b) == a - b * FloorDiv(a, b)
  TLA

  def self.str(s)
    raise Unsupported, "文字列 #{s.inspect}" unless s.is_a?(String) && s.match?(/\A[\x20-\x7e]*\z/)

    "\"#{s.gsub("\\", "\\\\\\\\").gsub('"', '\\"')}\""
  end

  # 式の変換の文脈。参照の名前と、整数の絶対値の上限を持つ。
  Ctx = Struct.new(:vars, :params, :choices, :nexts, :output, :locals, keyword_init: true) do
    def with_local(name, tla, bound)
      dup.tap { |c| c.locals = locals.merge(name => [tla, bound]) }
    end
  end

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
      check_supported
    end

    def module_text
      n = @states.length
      xs = Array.new(n) { |i| "x#{i}" }
      body = []
      body << "---- MODULE #{module_name} ----"
      body << "EXTENDS Integers, Sequences"
      body << HEADER
      constants(body)
      vs = Array.new(n) { |i| "v#{i}" }
      body << "VARIABLES #{(vs + %w[bad obs]).join(', ')}"
      # 不変条件と終端条件
      invariants = (ir["invariants"] || []).each_with_index.map do |inv, i|
        body << "Inv#{i}(#{xs.join(', ')}) == #{prop(inv['expr'], ctx(vars: xs))}"
        "Str(Inv#{i}(#{xs.join(', ')}))"
      end
      terminal = ir["terminal"] ? "Str(#{prop(ir['terminal'], ctx(vars: xs))})" : "\"false\""
      # 操作
      targets = @actions.each_with_index.select { |a, _| @targets.include?(a["name"]) }
      targets.each { |a, k| body << apply(a, k, xs) << first_bad_contract(a, k, xs) }
      enabled = targets.map { |a, k| quantified(a, "Apply#{k}(#{call_args(a, xs)})[1] = \"ok\"") }
      body << "Enabled(#{xs.join(', ')}) == #{enabled.empty? ? 'FALSE' : enabled.join(' \\/ ')}"
      body << "Obs(#{xs.join(', ')}) == <<#{(invariants + ["Enabled(#{xs.join(', ')})", terminal]).join(', ')}>>"
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

    private

    def check_supported
      [*@states, *@actions.flat_map { |a| (a["params"] || []) + (a["choices"] || []) }].each do |b|
        raise Unsupported, "動的ドメイン" if b.key?("in")

        domain_bound(b["type"])
      end
      @actions.each { |a| domain_bound(a["output"]["type"]) if a["output"] }
      raise Unsupported, "状態変数がない" if @states.empty?
    end

    def fresh(prefix = "r")
      @fresh += 1
      "#{prefix}#{@fresh}"
    end

    def ctx(vars:, params: [], choices: [], nexts: nil, output: nil)
      Ctx.new(vars: vars, params: params, choices: choices, nexts: nexts, output: output, locals: {})
    end

    def kind_of(type)
      raise Unsupported, "型 #{type.keys.first}" unless type.size == 1 && %w[int bool enum].include?(type.keys.first)

      type.keys.first
    end

    # 型の値の絶対値の上限。Bool と Enum は0。
    def domain_bound(type)
      case kind_of(type)
      when "int"
        r = type["int"]
        bound = [r["min"].abs, r["max"].abs].max
        raise Unsupported, "整数の範囲 #{r}" if bound > LIMIT || r["min"] > r["max"]

        bound
      when "enum"
        raise Unsupported, "未定義のEnum" unless @enums.key?(type["enum"])

        0
      else 0
      end
    end

    # 引数のドメイン（集合）。
    def domain_set(type)
      case kind_of(type)
      when "int" then "#{type['int']['min']}..#{type['int']['max']}"
      when "bool" then "BOOLEAN"
      else "{#{@enums.fetch(type['enum']).map { |v| FmspecTla.str(v) }.join(', ')}}"
      end
    end

    # 量化でたどる値を、正規順に並べた TLA+ の値の列。
    def domain_values(type)
      case kind_of(type)
      when "int"
        r = type["int"]
        raise Unsupported, "量化の範囲が広い" if r["max"] - r["min"] > 64

        (r["min"]..r["max"]).map(&:to_s)
      when "bool" then %w[FALSE TRUE]
      else @enums.fetch(type["enum"]).map { |v| FmspecTla.str(v) }
      end
    end

    def constants(body)
      (ir["constants"] || []).each_with_index do |c, i|
        tla, bound = expr(c["value"], ctx(vars: []))
        domain_bound(c["type"])
        body << "Const#{i} == #{tla}"
        @consts[c["name"]] = ["Const#{i}[2]", bound]
      end
    end

    def check_bound(bound)
      raise Unsupported, "整数の上限 #{bound}" if bound > LIMIT

      bound
    end

    def prop(e, c)
      expr(e, c)[0]
    end

    # 式を、結果を値とする TLA+ の式と、整数の絶対値の上限の組に変換する。
    def expr(e, c)
      raise Unsupported, "式 #{e.inspect}" unless e.is_a?(Hash) && e.size == 1

      op, arg = e.first
      case op
      when "int" then ["Ok(#{arg})", check_bound(arg.abs)]
      when "bool" then ["Ok(#{arg ? 'TRUE' : 'FALSE'})", 0]
      when "enum"
        raise Unsupported, "Enumのラベル" unless @enums.fetch(arg["type"]).include?(arg["variant"])

        ["Ok(#{FmspecTla.str(arg['variant'])})", 0]
      when "var" then ref(c.vars, arg, @states.map { |s| s["type"] })
      when "next"
        raise Unsupported, "next の位置" unless c.nexts

        ref(c.nexts, arg, @states.map { |s| s["type"] })
      when "param" then ref(c.params, arg)
      when "choice" then ref(c.choices, arg)
      when "output"
        raise Unsupported, "output の位置" unless c.output

        ["Ok(#{c.output[0]})", c.output[1]]
      when "const" then @consts.fetch(arg) { raise Unsupported, "定数 #{arg}" }.then { |t, b| ["Ok(#{t})", b] }
      when "local"
        tla, bound = c.locals.fetch(arg) { raise Unsupported, "局所変数 #{arg}" }
        ["Ok(#{tla})", bound]
      when "add", "sub", "mul", "div", "mod", "lt", "le", "gt", "ge", "eq", "ne" then binary(op, arg, c)
      when "not"
        r = fresh
        a, = expr(arg[0], c)
        ["(LET #{r} == #{a} IN IF ~IsOk(#{r}) THEN #{r} ELSE Ok(~#{r}[2]))", 0]
      when "all", "any" then [junction(op, arg, c), 0]
      when "implies"
        r = fresh
        p, = expr(arg[0], c)
        q, = expr(arg[1], c)
        ["(LET #{r} == #{p} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF ~#{r}[2] THEN Ok(TRUE) ELSE #{q})", 0]
      when "ite"
        r = fresh
        cond, = expr(arg[0], c)
        a, ba = expr(arg[1], c)
        b, bb = expr(arg[2], c)
        ["(LET #{r} == #{cond} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{r}[2] THEN #{a} ELSE #{b})", [ba, bb].max]
      when "let"
        r = fresh
        value, bound = expr(arg["value"], c)
        body, bb = expr(arg["body"], c.with_local(arg["name"], "#{r}[2]", bound))
        ["(LET #{r} == #{value} IN IF ~IsOk(#{r}) THEN #{r} ELSE #{body})", bb]
      when "forall", "exists"
        raise Unsupported, "量化の範囲 in" unless arg.key?("type") && !arg.key?("in")

        l = fresh("l")
        q = fresh("Q")
        body, = expr(arg["body"], c.with_local(arg["name"], l, domain_bound(arg["type"])))
        # forall は最初の偽で、exists は最初の真で打ち切る。値を正規順に並べて展開する。
        stop, empty, early = op == "forall" ? ["~", "TRUE", "FALSE"] : ["", "FALSE", "TRUE"]
        chain = domain_values(arg["type"]).reverse.reduce("Ok(#{empty})") do |rest, v|
          r = fresh
          "(LET #{r} == #{q}(#{v}) IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{stop}#{r}[2] THEN Ok(#{early}) ELSE #{rest})"
        end
        ["(LET #{q}(#{l}) == #{body} IN #{chain})", 0]
      else
        raise Unsupported, "演算子 #{op}"
      end
    end

    def ref(names, index, types = nil)
      raise Unsupported, "参照 #{index}" unless index.is_a?(Integer) && index >= 0 && index < names.length

      name, type = names[index].is_a?(Array) ? names[index] : [names[index], types[index]]
      ["Ok(#{name})", domain_bound(type)]
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
      a, ba = expr(args[0], c)
      b, bb = expr(args[1], c)
      bound = case op
              when "add", "sub" then ba + bb
              when "mul" then ba * bb
              when "div" then ba
              when "mod" then bb
              else 0
              end
      check_bound(bound)
      ra = fresh
      rb = fresh
      tla = "(LET #{ra} == #{a} IN IF ~IsOk(#{ra}) THEN #{ra} ELSE " \
            "LET #{rb} == #{b} IN IF ~IsOk(#{rb}) THEN #{rb} ELSE #{BINARY.fetch(op).call("#{ra}[2]", "#{rb}[2]")})"
      [tla, bound]
    end

    # all は最初の偽で、any は最初の真で打ち切る。
    def junction(op, args, c)
      stop, empty, early = op == "all" ? ["~", "TRUE", "FALSE"] : ["", "FALSE", "TRUE"]
      args.reverse.reduce("Ok(#{empty})") do |rest, a|
        r = fresh
        tla, = expr(a, c)
        "(LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN #{r} ELSE IF #{stop}#{r}[2] THEN Ok(#{early}) ELSE #{rest})"
      end
    end

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

    def in_range(type, v)
      return "TRUE" unless kind_of(type) == "int"

      "(#{type['int']['min']} <= #{v} /\\ #{v} <= #{type['int']['max']})"
    end

    # 操作の適用。<<"invalid">>、<<"err", 箇所, 状態変数名, 種類, 値>>、<<"ok", <<遷移先>>, 出力>> のどれか。
    # guard、更新（記述順。範囲は更新ごとに調べる）、出力の順に評価する。
    def apply(action, k, xs)
      ps, cs = bindings(action)
      c = ctx(vars: xs, params: ps, choices: cs)
      nexts = xs.dup
      steps = []
      guard = action["guard"] ? prop(action["guard"], c) : "Ok(TRUE)"
      g = fresh
      steps << ["LET #{g} == #{guard} IN IF ~IsOk(#{g}) THEN <<\"err\", \"guard\", \"\", #{g}[2], 0>> " \
                "ELSE IF ~#{g}[2] THEN <<\"invalid\">> ELSE"]
      (action["updates"] || []).each do |u|
        t = u["target"]
        raise Unsupported, "更新の対象 #{t}" unless t.is_a?(Integer) && t >= 0 && t < xs.length

        tla, = expr(u["expr"], c)
        r = fresh
        name = FmspecTla.str(@states[t]["name"])
        steps << ["LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN <<\"err\", \"update\", #{name}, #{r}[2], 0>> " \
                  "ELSE IF ~#{in_range(@states[t]['type'], "#{r}[2]")} THEN " \
                  "<<\"err\", \"update\", #{name}, \"out_of_range\", #{r}[2]>> ELSE"]
        nexts[t] = "#{r}[2]"
      end
      out = "<<>>"
      if action["output"]
        tla, = expr(action["output"]["expr"], c)
        r = fresh
        type = action["output"]["type"]
        steps << ["LET #{r} == #{tla} IN IF ~IsOk(#{r}) THEN <<\"err\", \"output\", \"\", #{r}[2], 0>> " \
                  "ELSE IF ~#{in_range(type, "#{r}[2]")} THEN " \
                  "<<\"err\", \"output\", \"\", \"out_of_range\", #{r}[2]>> ELSE"]
        out = "#{r}[2]"
      end
      result = "<<\"ok\", <<#{nexts.join(', ')}>>, #{out}>>"
      "Apply#{k}(#{call_args(action, xs)}) ==\n  #{steps.join("\n  ")}\n  #{result}"
    end

    # 対象の遷移契約のうち、記述順で最初に真でないもの。<<>> か <<遷移契約, 結果>>。
    def first_bad_contract(action, k, xs)
      ps, cs = bindings(action)
      ns = Array.new(xs.length) { |i| "n#{i}" }
      output = action["output"] ? ["out", domain_bound(action["output"]["type"])] : nil
      c = ctx(vars: xs, params: ps, choices: cs, nexts: ns.zip(@states.map { |s| s["type"] }), output: output)
      contracts = @contracts.select { |con| con["action"] == action["name"] }
      body = contracts.reverse.reduce("<<>>") do |rest, con|
        r = fresh
        "(LET #{r} == #{prop(con['expr'], c)} IN " \
          "IF Str(#{r}) # \"true\" THEN <<#{FmspecTla.str(con['name'])}, Str(#{r})>> ELSE #{rest})"
      end
      "Contract#{k}(#{[call_args(action, xs), *ns, 'out'].join(', ')}) == #{body}"
    end

    # 状態変数は v0, v1, ... で、演算子の引数（x0, x1, ...）とは別の名前にする。TLA+ は名前の隠蔽を許さない。
    def init(xs, vs)
      parts = @states.each_with_index.map do |s, i|
        cands = s.key?("initial_in") ? s["initial_in"] : [s["initial"]]
        "v#{i} \\in {#{cands.map { |e| "(#{prop(e, ctx(vars: []))})[2]" }.join(', ')}}"
      end
      if ir["initial_constraint"]
        r = fresh
        parts << "Constraint(#{vs.join(', ')})"
        @constraint = "Constraint(#{xs.join(', ')}) == " \
                      "LET #{r} == #{prop(ir['initial_constraint'], ctx(vars: xs))} IN IsOk(#{r}) /\\ #{r}[2]"
      end
      parts << "bad = <<>>" << "obs = Obs(#{vs.join(', ')})"
      [@constraint, "Init ==\n  /\\ #{parts.join("\n  /\\ ")}"].compact.join("\n")
    end

    def next_relation(targets, xs)
      steps = targets.map do |action, k|
        ps, cs = bindings(action)
        args = "<<#{ps.map(&:first).join(', ')}>>, <<#{cs.map(&:first).join(', ')}>>"
        name = FmspecTla.str(action["name"])
        primed = xs.each_with_index.map { |x, i| "#{x}' = r[2][#{i + 1}]" }
        ns = xs.each_index.map { |i| "r[2][#{i + 1}]" }
        unchanged = "UNCHANGED <<#{(xs + ['obs']).join(', ')}>>"
        error = "r[1] = \"err\" /\\ bad' = <<\"apply\", #{name}, #{args}, r[2], r[3], r[4], r[5]>> /\\ #{unchanged}"
        normal = "r[1] = \"ok\" /\\ #{primed.join(' /\\ ')} /\\ bad' = <<>> /\\ obs' = Obs(#{ns.join(', ')})"
        contract = "r[1] = \"ok\" /\\ (LET b == Contract#{k}(#{[call_args(action, xs), *ns, 'r[3]'].join(', ')}) IN " \
                   "b # <<>> /\\ bad' = <<\"contract\", #{name}, #{args}, b[1], b[2]>>) /\\ #{unchanged}"
        # TLA+ の箇条書き（/\ と \/ の列）は字下げに意味があるので、括弧と中置の演算子だけで書く。
        body = "LET r == Apply#{k}(#{call_args(action, xs)}) IN\n    (#{error})\n    \\/ (#{normal})\n    \\/ (#{contract})"
        quantified(action, body)
      end
      "Next ==\n  bad = <<>> /\\ (#{steps.empty? ? 'FALSE' : steps.join("\n  \\/ ")})"
    end
  end

  # TLC の -dump が書き出す状態を読む。各状態は変数名から値へのハッシュである。
  module Dump
    module_function

    def parse(text)
      text.split(/^State \d+:\n/).drop(1).map do |block|
        block.scan(%r{^/\\ (\w+) = (.*?)(?=\n/\\ |\n*\z)}m).to_h { |name, value| [name, value(value.gsub(/\s+/, " "))] }
      end
    end

    def value(text)
      v, rest = read(text.strip)
      raise ArgumentError, "読めない値: #{text}" unless rest.strip.empty?

      v
    end

    def read(s)
      s = s.lstrip
      if (m = s.match(/\A-?\d+/)) then [Integer(m[0]), m.post_match]
      elsif (m = s.match(/\ATRUE/)) then [true, m.post_match]
      elsif (m = s.match(/\AFALSE/)) then [false, m.post_match]
      elsif (m = s.match(/\A"((?:[^"\\]|\\.)*)"/)) then [m[1].gsub(/\\(.)/, '\1'), m.post_match]
      elsif (m = s.match(/\A<<\s*>>/)) then [[], m.post_match]
      elsif s.start_with?("<<")
        items = []
        rest = s[2..]
        loop do
          item, rest = read(rest)
          items << item
          rest = rest.lstrip
          if rest.start_with?(",")
            rest = rest[1..]
          elsif rest.start_with?(">>")
            return [items, rest[2..]]
          else
            raise ArgumentError, "読めない列: #{s}"
          end
        end
      else
        raise ArgumentError, "読めない値: #{s}"
      end
    end
  end
end
