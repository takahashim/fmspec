# frozen_string_literal: true

require_relative "test_helper"
require "fmspec/dsl"

# 仕様の記述の誤りを、仕様の構築時に診断する。
class DslTest < Minitest::Test
  def base(&block)
    Fmspec.define(:m) do
      enum(:color, :red, :green)
      state :n, int(0..3), initial: 0
      state :on, bool, initial: false
      state :c, enum(:color, :red, :green), initial: :red
      constant :limit, 3
      instance_eval(&block)
    end
  end

  def rejected(pattern, &block)
    error = assert_raises(Fmspec::BuildError) { base(&block) }
    assert_match pattern, error.message
  end

  def test_types_and_initial_values
    rejected(/整数型の範囲が不正です/) { state :x, int(3..0), initial: 0 }
    rejected(/符号付き64ビット整数に収めます/) { state :x, int(0..(2**63)), initial: 0 }
    rejected(/初期値 4 が int\(0\.\.3\) の範囲外/) { state :x, int(0..3), initial: 4 }
    rejected(/整数が必要です/) { state :x, int(0..3), initial: true }
    rejected(/true か false が必要です/) { state :x, bool, initial: 0 }
    rejected(/列挙型 color に :blue はありません/) { state :x, enum(:color, :red, :green), initial: :blue }
    rejected(/型が必要です/) { state :x, :int, initial: 0 }
    rejected(/別のラベルで宣言済み/) { enum(:color, :red) }
    rejected(/ラベルが1つ以上必要/) { enum(:empty) }
    model = base { state :x, 1...4, initial: 3 }
    assert_equal({ "int" => { "min" => 1, "max" => 3 } }, model.to_ir["states"][3]["type"])
  end

  def test_duplicate_and_undefined_names
    rejected(/状態変数 n は、状態変数として定義済み/) { state :n, bool, initial: true }
    rejected(/定数 n は、状態変数として定義済み/) { constant :n, 1 }
    rejected(/操作 a は、操作として定義済み/) do
      action(:a) { |_s| unchanged }
      action(:a) { |_s| unchanged }
    end
    rejected(/不変条件 i は、不変条件として定義済み/) do
      invariant(:i) { |_s| true }
      invariant(:i) { |_s| true }
    end
    rejected(/遷移契約 e は、遷移契約として定義済み/) do
      action :a do |_s|
        ensures(:e) { |_after| true }
        ensures(:e) { |_after| true }
      end
    end
    rejected(/未定義の状態変数または定数です: missing/) { invariant(:i) { |s| s.missing > 0 } }
    rejected(/未定義の状態変数です: missing/) { action(:a) { |_s| update missing: 1 } }
    rejected(/terminal は1つだけ/) do
      terminal { |_s| true }
      terminal { |_s| true }
    end
  end

  def test_expression_types
    rejected(/add: int の式が必要ですが、bool の式です/) { invariant(:i) { |s| (s.on + 1) > 0 } }
    rejected(/all: bool の式が必要ですが、int の式です/) { invariant(:i) { |s| s.n & s.on } }
    rejected(/不変条件 i: bool の式が必要ですが、int の式です/) { invariant(:i) { |s| s.n + 1 } }
    rejected(/eq: 同じ型の式どうしを比べます（int と bool）/) { invariant(:i) { |s| s.n.eq(s.on) } }
    rejected(/列挙型 color に :blue はありません/) { invariant(:i) { |s| s.c.eq(:blue) } }
    rejected(/ite: 2つの枝は同じ型にします/) { invariant(:i) { |s| ite(s.on, 1, true).eq(1) } }
    rejected(/ite の条件: bool の式が必要/) { invariant(:i) { |s| ite(s.n, 1, 2).eq(1) } }
    rejected(/記号式にできない値です: "x"/) { invariant(:i) { |s| s.n.eq("x") } }
    rejected(/整数リテラルが符号付き64ビット整数に収まりません/) { invariant(:i) { |s| s.n < 2**63 } }
    rejected(/状態の参照 n に引数は渡せません/) { invariant(:i) { |s| s.n(1) > 0 } }
  end

  def test_actions
    rejected(/操作 a の guard: bool の式が必要/) { action(:a) { |s| guard s.n } }
    rejected(/操作 a の n の更新: int の式が必要ですが、bool の式です/) { action(:a) { |s| update n: s.on } }
    rejected(/n への代入が重複/) do
      action :a do |s|
        update n: 1
        update n: s.n
      end
    end
    rejected(/操作 a のブロックは \|s, x, y\| を受け取ります/) { action(:a, x: 0..1, y: bool) { |s, x| guard s.on } }
    rejected(/操作 a の引数 x: 型が必要です/) { action(:a, x: [1, 2]) { |_s, _x| unchanged } }
    rejected(/引数 x は定義済み/) { action(:a, x: 0..1) { |_s, _x| choose(:x, bool) } }
    rejected(/returns が重複/) do
      action :a do |s|
        returns s.n
        returns s.n
      end
    end
    rejected(/操作 a の出力: bool の式が必要ですが、int の式です/) { action(:a) { |s| returns s.n, bool } }
    rejected(/:red がどの列挙型のラベルか決まりません（color、shade にあります）/) do
      enum(:shade, :red, :dark)
      action(:a) { |_s| returns :red }
    end
    rejected(/遷移契約 e: bool の式が必要/) { action(:a) { |_s| ensures(:e) { |after| after.n } } }
  end

  def test_accept_and_reject
    rejected(/on_accept の前に accept_if を書きます/) { action(:a) { |_s| on_accept { unchanged } } }
    rejected(/accept_if は1つだけ/) do
      action :a do |s|
        accept_if s.on
        accept_if s.on
      end
    end
    rejected(/returns は on_accept と on_reject の両方に書きます/) do
      action :a do |s|
        accept_if s.on
        on_accept { returns 1 }
      end
    end
    rejected(/n への代入が重複/) do
      action :a do |s|
        accept_if s.on
        update n: 0
        on_accept { update n: 1 }
      end
    end
    rejected(/guard は on_accept と on_reject の外に書きます/) do
      action :a do |s|
        accept_if s.on
        on_accept { guard s.on }
      end
    end
    rejected(/出力の型が合いません/) do
      action :a do |s|
        accept_if s.on
        on_accept { returns 1 }
        on_reject { returns false }
      end
    end
  end

  def test_output_types_are_inferred_from_the_expression
    model = base do
      action(:count) { |s| returns s.n + 1 }
      action(:flag) { |s| returns s.on }
      action(:shade) { |s| returns s.c }
      action(:label) { |_s| returns :green }
      action(:ranged) { |s| returns s.n, int(0..3) }
    end
    types = model.to_ir["actions"].map { |a| a["output"]["type"] }
    assert_equal [
      { "int" => { "min" => Fmspec::I64_MIN, "max" => Fmspec::I64_MAX } },
      { "bool" => {} }, { "enum" => "color" }, { "enum" => "color" }, { "int" => { "min" => 0, "max" => 3 } }
    ], types
  end

  def test_constants_and_functions_outside_a_definition
    assert_equal({ "ite" => [{ "bool" => true }, { "int" => 1 }, { "int" => 2 }] }, Fmspec.ite(true, 1, 2).node)
    assert_equal({ "all" => [] }, Fmspec.all.node)
    model = base { invariant(:i) { |s| s.n <= s.limit } }
    assert_equal({ "le" => [{ "var" => 0 }, { "int" => 3 }] }, model.to_ir["invariants"][0]["expr"])
  end
end
