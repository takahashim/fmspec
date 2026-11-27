# frozen_string_literal: true

# DSL の仕様の Ruby のソースをランダムに生成する。test/dsl_concrete_test.rb が使う。
#
# 型に従って式を組み立てる。複合型の Ruby のリテラル（Array、Hash、Set、nil）は、
# DSL で型が文脈から決まる位置（update の右辺、eq と ne の右辺、要素の位置、ite のもう一方の枝）にだけ書く。
# 生成した仕様を DSL が拒否することもある（Option の位置に中身の式を書いた場合など）。比較テストはそれを数えて飛ばす。
class DslGenerator
  COLORS = %i[red green blue].freeze

  def initialize(seed)
    @rng = Random.new(seed)
    @locals = 0
  end

  def pick(items) = items[@rng.rand(items.length)]
  def chance(probability) = @rng.rand < probability

  # ---- 型 ----
  # 型は [:int, min, max]、[:bool]、[:enum]、[:set, 要素]、[:map, キー, 値]、[:list, 要素, max]、
  # [:option, 中身]、[:tuple, a, b]、[:record, a, b] で表す。

  def int_type = [:int, pick([0, 0, -1]), pick([1, 2, 3])]
  def key_type = pick([[:enum], [:bool], [:int, 0, 2]])

  def state_type
    case @rng.rand(10)
    when 0, 1 then int_type
    when 2 then [:bool]
    when 3 then [:enum]
    when 4 then [:set, key_type]
    when 5 then [:map, pick([[:enum], [:bool]]), pick([[:int, 0, 2], [:bool]])]
    when 6 then [:list, pick([[:int, 0, 2], [:enum]]), 1 + @rng.rand(2)]
    when 7 then [:option, pick([[:enum], [:int, 0, 1]])]
    when 8 then [:tuple, [:int, 0, 2], [:bool]]
    else [:record, [:int, 0, 2], [:enum]]
    end
  end

  def type_src(t)
    case t[0]
    when :int then "int(#{t[1]}..#{t[2]})"
    when :bool then "bool"
    when :enum then "_color"
    when :set then "set_of(#{type_src(t[1])})"
    when :map then "map_of(#{type_src(t[1])}, #{type_src(t[2])})"
    when :list then "list_of(#{type_src(t[1])}, max: #{t[2]})"
    when :option then "option(#{type_src(t[1])})"
    when :tuple then "tuple(#{type_src(t[1])}, #{type_src(t[2])})"
    when :record then "record(a: #{type_src(t[1])}, b: #{type_src(t[2])})"
    end
  end

  def values(t)
    case t[0]
    when :int then (t[1]..t[2]).to_a
    when :bool then [false, true]
    when :enum then COLORS
    end
  end

  # 型の値の Ruby のリテラル。範囲の外の整数も、ときどき混ぜる。
  def literal(t)
    case t[0]
    when :int then (chance(0.1) ? t[2] + 1 : @rng.rand(t[1]..t[2])).to_s
    when :bool then chance(0.5).to_s
    when :enum then pick(COLORS).inspect
    when :set then "Set[#{values(t[1]).select { chance(0.4) }.map { |v| v.inspect }.join(', ')}]"
    when :map
      pairs = values(t[1]).select { chance(0.4) }.map { |k| "#{k.inspect} => #{literal(t[2])}" }
      "{ #{pairs.join(', ')} }"
    when :list then "[#{Array.new(@rng.rand(0..t[2])) { literal(t[1]) }.join(', ')}]"
    when :option then chance(0.4) ? "nil" : literal(t[1])
    when :tuple then "[#{literal(t[1])}, #{literal(t[2])}]"
    when :record then "{ a: #{literal(t[1])}, b: #{literal(t[2])} }"
    end
  end

  # 初期値に使う、型に属するリテラル。
  def initial(t)
    case t[0]
    when :int then @rng.rand(t[1]..t[2]).to_s
    when :list then "[#{Array.new(@rng.rand(0..t[2])) { initial(t[1]) }.join(', ')}]"
    when :map then "{ #{values(t[1]).select { chance(0.4) }.map { |k| "#{k.inspect} => #{initial(t[2])}" }.join(', ')} }"
    when :option then chance(0.4) ? "nil" : initial(t[1])
    when :tuple then "[#{initial(t[1])}, #{initial(t[2])}]"
    when :record then "{ a: #{initial(t[1])}, b: #{initial(t[2])} }"
    else literal(t)
    end
  end

  # 式の型として同じか。整数は範囲を区別しない（Set、Map、List の中を除く）。
  def same?(a, b)
    return a == b if %i[set map list].include?(a[0])
    return b[0] == :int if a[0] == :int
    return b[0] == a[0] && same?(a[1], b[1]) && (a[2].nil? || same?(a[2], b[2])) if %i[option tuple record].include?(a[0])

    a[0] == b[0]
  end

  # ---- 式 ----
  # scope は [ソース, 型] の参照の列。

  def refs(t, scope) = scope.select { |_, rt| same?(rt, t) }.map(&:first)

  # 型 t の記号式のソース（Ruby のリテラルではない）。見つからなければ nil。
  def symbolic(t, scope, depth)
    found = refs(t, scope)
    return pick(found) if !found.empty? && (depth.zero? || chance(0.4))

    case t[0]
    when :int then depth.zero? ? sym_int_leaf(scope) : int_expr(scope, depth)
    when :bool then sym_bool(scope, depth)
    when :enum then chance(0.5) || depth.zero? ? "_color[#{pick(COLORS).inspect}]" : "ite(#{bool_expr(scope, depth - 1)}, #{typed(t, scope, depth - 1)}, #{symbolic(t, scope, depth - 1)})"
    when :option
      return "none(#{type_src(t[1])})" if depth.zero? || chance(0.3)

      chance(0.5) ? "some(#{free(t[1], scope, depth - 1)})" : "ite(#{bool_expr(scope, depth - 1)}, #{symbolic(t, scope, depth - 1)}, #{typed(t, scope, depth - 1)})"
    else
      composite(t, scope, depth)
    end
  end

  # 型の決まらない位置の式。整数、真偽値、ラベルは Ruby のリテラルでもよい。
  def free(t, scope, depth)
    return literal(t) if %i[int bool enum].include?(t[0]) && chance(0.25)

    symbolic(t, scope, depth) || literal_value(t)
  end

  # 型の決まる位置の式。複合型の Ruby のリテラルでもよい。
  def typed(t, scope, depth)
    chance(0.3) ? literal(t) : (symbolic(t, scope, depth) || literal(t))
  end

  # 型の決まらない位置に書く、複合型のリテラル。
  def literal_value(t) = "#{type_src(t)}.value(#{literal(t)})"

  def int_expr(scope, depth)
    return free_int_leaf(scope) if depth.zero?

    sub = -> { free([:int, 0, 2], scope, depth - 1) }
    sym = -> { symbolic([:int, 0, 2], scope, depth - 1) }
    case @rng.rand(12)
    when 0, 1 then "(#{sym.()} #{pick(%w[+ - *])} #{sub.()})"
    when 2 then "(#{pick(%w[1 2 -1])} #{pick(%w[+ - *])} #{sym.()})"
    when 3 then "(#{sym.()} #{pick(%w[/ %])} #{sub.()})"
    when 4 then "(-#{sym.()})"
    when 5 then "#{pick(%w[min max])}(#{sub.()}, #{sub.()})"
    when 6 then "ite(#{bool_expr(scope, depth - 1)}, #{sub.()}, #{sub.()})"
    when 7 then "let(#{sub.()}) { |#{(v = local)}| (#{v} + #{sub.()}) }"
    else collection_int(scope, depth) || "(#{sym.()} + 1)"
    end
  end

  # メソッドの受け手に使う、整数の記号式。
  def sym_int_leaf(scope)
    found = refs([:int, 0, 0], scope)
    found.empty? ? "ite(true, #{@rng.rand(-2..3)}, 0)" : pick(found)
  end

  # メソッドの受け手に使う、真偽値の記号式。
  def sym_bool(scope, depth)
    found = refs([:bool], scope)
    return pick(found) if !found.empty? && (depth.zero? || chance(0.3))
    return "(#{sym_int_leaf(scope)} < #{@rng.rand(-1..3)})" if depth.zero?

    bool_expr(scope, depth)
  end

  def free_int_leaf(scope)
    found = refs([:int, 0, 0], scope)
    found.empty? || chance(0.3) ? @rng.rand(-2..3).to_s : pick(found)
  end

  def local
    @locals += 1
    "q#{@locals}"
  end

  # 複合型の値から取り出す整数。
  def collection_int(scope, depth)
    options = []
    scope.each do |src, t|
      case t[0]
      when :set, :map then options << "#{src}.size"
      when :list
        options << "#{src}.size"
        options << "#{src}[#{free([:int, 0, 0], scope, depth - 1)}]" if t[1][0] == :int
        options << "#{src}.#{pick(%w[first last])}" if t[1][0] == :int
      when :tuple then options << "#{src}[0]"
      when :record then options << "#{src}[:a]"
      when :option then options << "#{src}.unwrap" if t[1][0] == :int
      end
      options << "#{src}[#{typed(t[1], scope, depth - 1)}]" if t[0] == :map && t[2][0] == :int
    end
    options.empty? ? nil : pick(options)
  end

  def bool_expr(scope, depth)
    return pick(refs([:bool], scope) + [chance(0.5).to_s, "(#{free_int_leaf(scope)} < #{free_int_leaf(scope)})"]) if depth.zero?

    d = depth - 1
    case @rng.rand(14)
    when 0, 1 then "(#{symbolic([:int, 0, 0], scope, d)} #{pick(%w[< <= > >=])} #{free([:int, 0, 0], scope, d)})"
    when 2, 3
      t = pick(scope.map(&:last) + [[:int, 0, 0], [:enum]])
      "#{symbolic(t, scope, d)}.#{pick(%w[eq ne])}(#{typed(t, scope, d)})"
    when 4 then "(#{sym_bool(scope, d)} #{pick(%w[& |])} #{free([:bool], scope, d)})"
    when 5 then "#{sym_bool(scope, d)}.not_"
    when 6 then "#{pick(%w[all any])}(#{Array.new(@rng.rand(0..3)) { free([:bool], scope, d) }.join(', ')})"
    when 7 then chance(0.5) ? "#{sym_bool(scope, d)}.implies(#{free([:bool], scope, d)})" : "implies(#{free([:bool], scope, d)}, #{free([:bool], scope, d)})"
    when 8 then "ite(#{bool_expr(scope, d)}, #{free([:bool], scope, d)}, #{free([:bool], scope, d)})"
    when 9
      t = key_type
      v = local
      "#{pick(%w[forall exists])}(#{type_src(t)}) { |#{v}| #{bool_expr(scope + [[v, t]], d)} }"
    when 10 then "let(#{free([:int, 0, 0], scope, d)}) { |#{(v = local)}| #{bool_expr(scope + [[v, [:int, 0, 0]]], d)} }"
    else collection_bool(scope, d) || "(#{sym_int_leaf(scope)} >= 0)"
    end
  end

  def collection_bool(scope, d)
    options = []
    scope.each do |src, t|
      case t[0]
      when :set
        options << "#{src}.include?(#{typed(t[1], scope, d)})"
        options << "#{src}.empty?"
        options << "(#{src} <= #{typed(t, scope, d)})"
        options << "#{src}.subset?(#{typed(t, scope, d)})"
        v = local
        options << "#{src}.#{pick(%w[all? any?])} { |#{v}| #{bool_expr(scope + [[v, t[1]]], d)} }"
        v = local
        options << "#{pick(%w[forall exists])}(#{src}) { |#{v}| #{bool_expr(scope + [[v, t[1]]], d)} }"
      when :map
        options << "#{src}.key?(#{typed(t[1], scope, d)})"
        v = local
        options << "#{src}.#{pick(%w[all? any?])} { |#{v}| #{bool_expr(scope + [[v, t[1]]], d)} }"
      when :list
        options << "#{src}.include?(#{typed(t[1], scope, d)})"
        v = local
        options << "#{src}.#{pick(%w[all? any?])} { |#{v}| #{bool_expr(scope + [[v, t[1]]], d)} }"
      when :option then options << "#{src}.#{pick(%w[some? none?])}"
      when :tuple then options << "#{src}[1]"
      end
    end
    options.empty? ? nil : pick(options)
  end

  def composite(t, scope, depth)
    found = refs(t, scope)
    return pick(found) if !found.empty? && (depth.zero? || chance(0.3))
    return literal_value(t) if depth.zero? || found.empty?

    base = pick(found)
    d = depth - 1
    case t[0]
    when :set
      case @rng.rand(5)
      when 0 then "#{base}.add(#{typed(t[1], scope, d)})"
      when 1 then "#{base}.delete(#{typed(t[1], scope, d)})"
      when 2 then "(#{base} #{pick(%w[| & - +])} #{typed(t, scope, d)})"
      when 3 then "#{base}.#{pick(%w[union intersection difference])}(#{typed(t, scope, d)})"
      else "ite(#{bool_expr(scope, d)}, #{base}, #{typed(t, scope, d)})"
      end
    when :map
      chance(0.6) ? "#{base}.put(#{typed(t[1], scope, d)}, #{typed(t[2], scope, d)})" : "#{base}.delete(#{typed(t[1], scope, d)})"
    when :list
      chance(0.5) ? "#{base}.push(#{typed(t[1], scope, d)})" : "#{base}.#{pick(%w[pop shift])}"
    else
      "ite(#{bool_expr(scope, d)}, #{base}, #{typed(t, scope, d)})"
    end
  end

  # ---- 仕様 ----

  def model
    @states = Array.new(1 + @rng.rand(3)) { |i| ["s#{i}", state_type] }
    lines = ["_color = enum(:color, :red, :green, :blue)"]
    @states.each do |name, t|
      lines << "state :#{name}, #{type_src(t)}, initial: #{initial(t)}"
    end
    state_scope = @states.map { |n, t| ["s.#{n}", t] }
    Array.new(1 + @rng.rand(3)) { |i| lines.concat(action("a#{i}", state_scope)) }
    Array.new(@rng.rand(3)) do |i|
      lines << "invariant(:inv#{i}) { |s| #{bool_expr(state_scope, 2)} }"
    end
    lines << "terminal { |s| #{bool_expr(state_scope, 2)} }" if chance(0.3)
    lines
  end

  def param_type = pick([[:int, 0, 2], [:bool], [:enum], [:int, -1, 1]])

  def action(name, state_scope)
    params = Array.new(@rng.rand(3)) { |i| ["p#{i}", param_type] }
    collections = state_scope.select { |_, t| %i[set list].include?(t[0]) }
    domains = params.each_with_index.map do |(_, t), i|
      if i.zero? && !collections.empty? && chance(0.3)
        src, ct = pick(collections)
        params[i][1] = ct[1]
        "->(s) { #{src} }"
      else
        t[0] == :int && chance(0.5) ? "#{t[1]}..#{t[2]}" : type_src(t)
      end
    end
    head = params.empty? ? "" : ", #{params.zip(domains).map { |(n, _), d| "#{n}: #{d}" }.join(', ')}"
    args = (["s"] + params.map(&:first)).join(", ")
    scope = state_scope + params
    body = []
    if chance(0.3)
      t = param_type
      body << "_c0 = choose(:c0, #{type_src(t)})"
      scope += [["_c0", t]]
    end
    @rng.rand(0..2).times { body << "guard #{bool_expr(scope, 2)}" }
    targets = @states.select { chance(0.6) }
    if chance(0.25) && !targets.empty?
      body << "accept_if #{bool_expr(scope, 2)}"
      %w[on_accept on_reject].each do |branch|
        chosen = targets.select { chance(0.7) }
        inner = chosen.map { |n, t| "#{n}: #{typed(t, scope, 2)}" }
        body << "#{branch} do"
        body << (inner.empty? ? "  unchanged" : "  update #{inner.join(', ')}")
        body << "end"
      end
    elsif !targets.empty?
      body << "update #{targets.map { |n, t| "#{n}: #{typed(t, scope, 2)}" }.join(', ')}"
    end
    out = nil
    if chance(0.3)
      out = pick([[:int, 0, 2], [:bool], [:enum]])
      ranged = out[0] == :int && chance(0.5) ? ", #{type_src(out)}" : ""
      body << "returns #{free(out, scope, 2)}#{ranged}"
    end
    if chance(0.3)
      after = @states.map { |n, t| ["after.#{n}", t] }
      outs = out ? [["out", out]] : []
      body << "ensures(:#{name}_e) { |after, out| #{bool_expr(scope + after + outs, 2)} }"
    end
    body << "preserves :#{@states.first[0]}" if chance(0.1) && targets.none? { |n, _| n == @states.first[0] }
    ["action :#{name}#{head} do |#{args}|", *body.map { |l| "  #{l}" }, "end"]
  end
end
