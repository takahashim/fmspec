# frozen_string_literal: true

require_relative "test_helper"
require "fmspec/dsl"

# 記号的条件の誤用の拒否（仕様書 §4.1、§17.2）。
class LintTest < Minitest::Test
  def base(&block)
    Fmspec.define(:m) do
      state :n, int(0..3), initial: 0
      state :on, bool, initial: false
      instance_eval(&block)
    end
  end

  def rejected(pattern, &block)
    error = assert_raises(Fmspec::BuildError) { base(&block) }
    assert_match pattern, error.message
    # 診断は、誤用のある行を指す。
    assert_match(/#{Regexp.escape(__FILE__)}:\d+/, error.message)
    error
  end

  def test_equality_operators
    rejected(/== は使えません。eq を使います/) do
      invariant(:a) { |s| s.n == 0 }
    end
    rejected(/!= は使えません。ne を使います/) do
      invariant(:a) { |s| s.n != 0 }
    end
  end

  def test_negation
    rejected(/! と not は使えません。not_ を使います/) do
      invariant(:a) { |s| !(s.n > 0) }
    end
    rejected(/! と not は使えません/) do
      invariant(:a) { |s| not s.on }
    end
  end

  def test_short_circuit_operators
    rejected(/&& と and は使えません。& を使います/) do
      invariant(:a) { |s| (s.n > 0) && (s.n < 3) }
    end
    rejected(/&& と and は使えません/) do
      invariant(:a) { |s| (s.n > 0 and s.n < 3) }
    end
    rejected(/\|\| と or は使えません。\| を使います/) do
      invariant(:a) { |s| (s.n > 0) || s.on }
    end
  end

  def test_branches
    rejected(/if と条件演算子は使えません。条件式は ite/) do
      action(:x) { |s| update n: (s.n > 2 ? 0 : s.n + 1) }
    end
    rejected(/if と条件演算子は使えません/) do
      action(:x) { |s| update n: 0 if s.n > 2 }
    end
    rejected(/unless は使えません/) do
      action(:x) { |s| update n: 0 unless s.on }
    end
    rejected(/case は使えません/) do
      action :x do |s|
        case s.n
        when 0 then update n: 1
        end
      end
    end
    rejected(/while は使えません/) do
      action :x do |s|
        update n: 1 while s.on
      end
    end
  end

  def test_every_kind_of_symbolic_block_is_checked
    rejected(/terminal: .*== は使えません/) do
      terminal { |s| s.n == 3 }
    end
    # 操作のブロックの検査は、その中の ensures や on_accept のブロックにも及ぶ。
    rejected(/操作 x: .*== は使えません/) do
      action :x do |s|
        update n: s.n
        ensures(:grows) { |after| after.n == s.n }
      end
    end
    rejected(/操作 x: .*if と条件演算子は使えません/) do
      action :x do |s|
        accept_if s.on
        on_accept do
          update n: 1 if s.on
        end
      end
    end
    # 別の場所で書いたブロックを渡しても、そのブロックを検査する。
    grows = proc { |after| after.n == 0 }
    rejected(/遷移契約 grows: .*== は使えません/) do
      action :x do |s|
        update n: s.n
        ensures(:grows, &grows)
      end
    end
  end

  # 静的な分岐も区別せずに拒否する。記号ブロックの外で選ぶ。
  def test_static_branches_are_rejected_inside_symbolic_blocks
    rejected(/if と条件演算子は使えません/) do
      action(:x) { |_s| update n: (ENV["FMSPEC_X"] ? 0 : 1) }
    end
    step = ENV["FMSPEC_X"] ? 0 : 1
    model = base do
      action(:x) { |_s| update n: step }
    end
    assert_equal({ "int" => 1 }, model.to_ir["actions"][0]["updates"][0]["expr"])
  end

  # 同じ行で始まるブロックは、どれが記号ブロックかを決めずに、すべて検査する。
  def test_blocks_starting_on_the_same_line_are_all_checked
    rejected(/== は使えません/) do
      invariant(:a) { |s| [1].map { |x| x == 1 }.first & (s.n >= 0) }
    end
  end

  def test_blocks_without_readable_source_are_rejected
    error = assert_raises(Fmspec::BuildError) do
      eval(<<~RUBY, binding, "(generated)", 1)
        Fmspec.define(:m) do
          state :n, int(0..3), initial: 0
          invariant(:a) { |s| s.n >= 0 }
        end
      RUBY
    end
    assert_match(/ブロックのソースを読めないので、構文を検査できません/, error.message)
  end

  def helper_equal(expr) = expr == 0

  # 構文検査は、ブロックから呼ぶメソッドの中までは見ない。演算子の定義が実行時に拒否する。
  def test_operators_are_also_rejected_at_run_time
    test = self
    error = assert_raises(Fmspec::BuildError) do
      base do
        invariant(:a) { |s| test.helper_equal(s.n) }
      end
    end
    assert_match(/記号式に == は使えません。eq を使ってください/, error.message)
    expr = Fmspec::Expr.lift(1)
    assert_raises(Fmspec::BuildError) { expr != 1 }
    assert_raises(Fmspec::BuildError) { !expr }
  end

  # 記号式は Ruby の値としてつねに真なので、Ruby の Enumerable の述語や、リテラルの集合の include? に渡すと、
  # 書いたつもりの条件が式に残らない。
  def test_ruby_truthiness_is_rejected
    rejected(/one\? は使えません/) do
      invariant(:a) { |s| [s.on].one? }
    end
    rejected(/ブロック付きの select は使えません/) do
      invariant(:a) { |s| [0, 1].select { |i| s.n.eq(i) }.length.positive? }
    end
    rejected(/ブロック付きの count は使えません/) do
      invariant(:a) { |s| [0, 1].count { |i| s.n.eq(i) }.positive? }
    end
    rejected(/Ruby の Array や Range の all\? は使えません/) do
      invariant(:a) { |s| (0..1).all? { |i| s.n.ne(i) } }
    end
    rejected(/Ruby の Array や Range の any\? は使えません/) do
      invariant(:a) { |s| [0, 1].map { |i| s.n.eq(i) }.any? }
    end
    rejected(/Ruby の Array、Hash、Set、Range の include\? は使えません/) do
      invariant(:a) { |s| Set[0, 1].include?(s.n) }
    end
    rejected(/include\? は使えません/) do
      invariant(:a) { |s| [0, 1].include?(s.n) }
    end
    rejected(/nil\? は使えません/) do
      invariant(:a) { |s| s.n.nil? }
    end
    rejected(/eql\? は使えません/) do
      invariant(:a) { |s| s.n.eql?(0) }
    end
  end

  # 記号式の all?、any?、include? と、ブロックのない count（状態変数の名前など）は使える。
  def test_symbolic_collections_are_allowed
    model = Fmspec.define(:m) do
      state :items, set_of(int(0..2)), initial: Set[]
      state :count, int(0..3), initial: 0
      action(:x) { |s| update count: ite(s.count < 3, s.count + 1, 0) }
      invariant(:a) { |s| s.items.all? { |i| i < 3 } & s.items.any? { |i| i >= 0 }.implies(s.items.include?(0) | true) }
      invariant(:b) { |s| all(*[0, 1].map { |i| s.items.include?(i).implies(s.count >= 0) }) }
      state :credit, map_of(int(0..1), int(0..1)), initial: {}
      state :holder, option(int(0..1)), initial: nil
      invariant(:c) { |s| s.credit.keys.all? { |k| s.credit[k] <= 1 } & s.credit.keys.include?(0).implies(s.holder.none?) }
    end
    assert_equal 3, model.to_ir["invariants"].length
  end

  def helper_and(expr) = true & expr
  def helper_or(expr) = false | expr

  # Ruby の true、false、nil の &、|、^ に記号式を渡すと、Ruby の真偽値の演算になる。ブロックの外の
  # ヘルパーでも起きるので、構文検査ではなく実行時に拒否する。
  def test_ruby_booleans_with_symbolic_operands_are_rejected_at_run_time
    test = self
    [:helper_and, :helper_or].each do |helper|
      error = assert_raises(Fmspec::BuildError) do
        base { invariant(:a) { |s| test.public_send(helper, s.on) } }
      end
      assert_match(/記号式が式に残りません。記号式を左に書くか、all\(\.\.\.\) や any\(\.\.\.\) を使います/, error.message)
      assert_match(/#{Regexp.escape(__FILE__)}:\d+/, error.message)
    end
    expr = Fmspec::Expr.lift(true)
    assert_raises(Fmspec::BuildError) { nil ^ expr }
    # 記号式が左にあれば Expr の演算子になり、Ruby の真偽値どうしの演算は変わらない。
    assert_equal({ "all" => [{ "bool" => true }, { "bool" => true }] }, (expr & true).node)
    assert_equal [false, true, true], [true & false, false | true, nil ^ true]
  end

  def test_allowed_forms
    model = base do
      action :x do |s|
        guard (s.n < 3) & s.on.not_
        update n: ite(s.n.eq(2), 0, s.n + 1), on: s.on | (0 < 1 + s.n)
      end
      invariant(:a) { |s| s.on.implies(s.n.ne(3)) }
    end
    assert_equal 1, model.to_ir["actions"].length
  end
end
