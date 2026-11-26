# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# モデル合成（仕様書 §12.5）。
class ComposeTest < Minitest::Test
  # 在庫の引当て。
  def stock
    Fmspec.define(:stock) do
      state :reserved, int(0..3), initial: 0
      action :reserve, quantity: 1..2 do |s, quantity|
        guard s.reserved + quantity <= 3
        update reserved: s.reserved + quantity
        ensures(:grows) { |after| after.reserved > s.reserved }
      end
      action :release do |s|
        guard s.reserved > 0
        update reserved: s.reserved - 1
      end
      invariant(:within_capacity) { |s| s.reserved <= 3 }
      terminal { |s| s.reserved.eq(3) }
    end
  end

  # 支払い。
  def payment
    Fmspec.define(:payment) do
      state :charged, int(0..3), initial: 0
      action :charge, quantity: 1..2 do |s, quantity|
        guard s.charged + quantity <= 3
        update charged: s.charged + quantity
        returns s.charged + quantity, int(0..3)
      end
      action :refund do |s|
        guard s.charged > 0
        update charged: s.charged - 1
      end
      terminal { |s| s.charged.eq(3) }
    end
  end

  # 引当てと支払いを checkout で同期させる。release と refund は同期させない。
  def shop(cancel: false)
    Fmspec.compose(:shop, stock: stock, payment: payment) do
      sync :checkout, stock: :reserve, payment: :charge
      sync :cancel, stock: :release, payment: :refund if cancel
      invariant(:charged_for_reserved) { |s| s.payment.charged.eq(s.stock.reserved) }
    end
  end

  def test_composition_expands_into_a_single_ir_with_namespaces
    ir = shop.to_ir
    assert_equal %w[stock.reserved payment.charged], ir["states"].map { |s| s["name"] }
    assert_equal %w[stock.release payment.refund checkout], ir["actions"].map { |a| a["name"] }
    assert_equal %w[stock.within_capacity charged_for_reserved], ir["invariants"].map { |i| i["name"] }
    assert_equal [%w[stock.grows checkout]], ir["contracts"].map { |c| [c["name"], c["action"]] }

    checkout = ir["actions"].last
    # 同じ名前の公開引数は1つに揃え、guard は連言、更新は連結になる。
    assert_equal ["quantity"], checkout["params"].map { |p| p["name"] }
    assert_equal 2, checkout["guard"]["all"].length
    assert_equal [0, 1], checkout["updates"].map { |u| u["target"] }
    assert_equal({ "int" => { "min" => 0, "max" => 3 } }, checkout["output"]["type"])
    # refund は payment の状態変数（添字1）を更新する。
    assert_equal [1], ir["actions"][1]["updates"].map { |u| u["target"] }
    assert_equal({ "var" => 1 }, ir["actions"][1]["guard"]["gt"][0])
    # 終端条件は、両方のモデルが終端であること。
    assert_equal 2, ir["terminal"]["all"].length
  end

  def test_properties_across_models_are_checked_on_the_composition
    assert stock.check.verified?
    assert payment.check.verified?

    # release と refund は同期していないので、片方だけを実行でき、引当てと支払いがずれる。
    result = shop.check
    assert_equal :violated, result.status
    assert_equal "charged_for_reserved", result.property["name"]
    assert_equal %i[checkout stock.release], result.trace.steps.map(&:action)

    fixed = shop(cancel: true)
    assert fixed.check(deadlock: true).verified?
    assert_equal :verified, fixed.check(contracts: ["stock.grows"]).status
  end

  # 同期しない操作はインターリーブし、同期した操作は両方のモデルで同時に進む。
  def test_the_state_space_is_the_synchronized_product
    # 同期がなければ、到達可能な状態は各モデルの状態の直積（4 × 4）になる。
    independent = Fmspec.compose(:independent, stock: stock, payment: payment)
    assert_equal 16, independent.check.visited_states
    # checkout と cancel で同期すると、引当てと支払いは常に等しく、0..3 の4状態になる。
    assert_equal 4, shop(cancel: true).check.visited_states
    # checkout だけを同期すると、release と refund は単独で進み、引当てと支払いがずれた状態にも届く。
    assert_equal 16, shop.check(invariants: []).visited_states
  end

  def test_a_composed_model_is_tested_against_an_implementation
    order = Struct.new(:reserved, :charged)
    model = shop(cancel: true)
    binding = model.bind do
      setup { order.new(0, 0) }
      command(:checkout) do |o, quantity:|
        o.reserved += quantity
        o.charged += quantity
      end
      command(:cancel) do |o|
        o.reserved -= 1
        o.charged -= 1
      end
      observe(:"stock.reserved", &:reserved)
      observe(:"payment.charged", &:charged)
    end
    result = model.test(binding, cases: 20, steps: 10, seed: 1)
    assert_equal :passed, result.status
  end

  def test_choices_initial_states_and_ghosts_are_kept
    coin = Fmspec.define(:coin) do
      state :heads, bool, initial_in: bool
      ghost :flips, int(0..1), initial: 0
      action :flip do |s|
        guard s.flips.eq(0)
        update heads: choose(:side, bool), flips: 1
      end
    end
    light = Fmspec.define(:light) do
      state :on, bool, initial_in: bool
      initially { |s| s.on.not_ }
      action :toggle do |s|
        update on: s.on.not_
      end
    end
    model = Fmspec.compose(:both, coin: coin, light: light) do
      sync :play, coin: :flip, light: :toggle
      initially { |s| s.coin.heads }
    end
    ir = model.to_ir
    assert_equal ["side"], ir["actions"][0]["choices"].map { |c| c["name"] }
    assert_equal 2, ir["initial_constraint"]["all"].length
    assert_equal %i[coin.flips], model.ghosts
    # 初期状態は heads が真で on が偽の1つ。play で on が真になり、flips が1になって止まる。
    result = model.check(deadlock: true)
    assert_equal :violated, result.status
    assert_equal %i[play], result.trace.steps.map(&:action)
    assert_equal [1, true], result.trace.states.last.values_at("coin.flips", "light.on")
    assert_equal({ "coin.heads" => true, "coin.flips" => 0, "light.on" => false }, result.trace.initial)
  end

  def test_enums_with_the_same_name_and_labels_are_shared
    a = Fmspec.define(:a) do
      color = enum(:color, :red, :green)
      state :c, color, initial: :red
    end
    b = Fmspec.define(:b) do
      color = enum(:color, :red, :green)
      state :c, color, initial: :green
    end
    model = Fmspec.compose(:ab, a: a, b: b) do
      invariant(:differ) { |s| s.a.c.ne(s.b.c) }
    end
    assert_equal [{ "name" => "color", "variants" => %w[red green] }], model.to_ir["enums"]
    assert model.check.verified?

    other = Fmspec.define(:other) do
      state :c, enum(:color, :red, :blue), initial: :red
    end
    error = assert_raises(Fmspec::BuildError) { Fmspec.compose(:bad, a: a, other: other) }
    assert_match(/列挙型 color/, error.message)
  end

  def test_invalid_compositions_are_rejected
    assert_raises(Fmspec::BuildError) { Fmspec.compose(:empty) }
    assert_raises(Fmspec::BuildError) { Fmspec.compose(:bad, stock: 1) }
    assert_raises(Fmspec::BuildError) { Fmspec.compose(:bad, "a.b": stock) }
    errors = {
      /stock に操作 missing がありません/ => proc { sync :x, stock: :missing },
      /合成にないモデルです: nothing/ => proc { sync :x, nothing: :reserve },
      /stock.reserve は sync x で同期済みです/ => proc {
        sync :x, stock: :reserve
        sync :y, stock: :reserve
      },
      /未定義の状態変数です: stock.missing/ => proc { invariant(:x) { |s| s.stock.missing.eq(0) } },
      /\. は使えません/ => proc { sync :"stock.release", stock: :reserve }
    }
    errors.each do |message, block|
      error = assert_raises(Fmspec::BuildError) { Fmspec.compose(:bad, stock: stock, payment: payment, &block) }
      assert_match message, error.message
    end

    two_outputs = Fmspec.define(:two) do
      state :n, int(0..3), initial: 0
      action :charge, quantity: 1..2 do |_s, quantity|
        returns quantity, int(0..3)
      end
    end
    error = assert_raises(Fmspec::BuildError) do
      Fmspec.compose(:bad, payment: payment, two: two_outputs) { sync :x, payment: :charge, two: :charge }
    end
    assert_match(/出力を持つ操作は1つまでです/, error.message)

    other_type = Fmspec.define(:other) do
      state :n, int(0..3), initial: 0
      action(:take, quantity: 1..3) { |_s, _quantity| unchanged }
    end
    error = assert_raises(Fmspec::BuildError) do
      Fmspec.compose(:bad, stock: stock, other: other_type) { sync :x, stock: :reserve, other: :take }
    end
    assert_match(/公開引数 quantity の型/, error.message)
  end
end
