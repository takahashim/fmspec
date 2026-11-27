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
