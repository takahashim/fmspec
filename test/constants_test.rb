# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 定数を上書きして作り直す `Model#with` と、値の候補ごとに検査する `Model#sweep`。
class ConstantsTest < Minitest::Test
  # 販売上限で状態の型を決めるチケットの仕様。上限を超える1枚分まで表せる。
  Tickets = Fmspec.define(:tickets) do
    capacity = constant :capacity, 3
    state :sold, int(0..capacity + 1), initial: 0

    action :purchase, quantity: 1..2 do |s, quantity|
      guard s.sold + quantity <= s.capacity
      update sold: s.sold + quantity
    end

    action :cancel do |s|
      guard s.sold > 0
      update sold: s.sold - 1
    end

    invariant(:capacity_respected) { |s| s.sold <= s.capacity }
  end

  def counter(&block)
    Fmspec.define(:counter) do
      workers = constant :workers, 2
      state :count, int(0..workers), initial: 0

      process :incr, count: workers do
        local :seen, int(0..workers), initial: 0
        step(:load) { |s| update seen: s.count }
        step(:store) { |s| update count: s.seen + 1 }
      end

      instance_eval(&block) if block
    end
  end

  def test_constant_returns_its_value
    assert_equal({ "int" => { "min" => 0, "max" => 4 } }, Tickets.to_ir["states"][0]["type"])
    assert_equal({ "int" => { "min" => 0, "max" => 5 } }, Tickets.with(capacity: 4).to_ir["states"][0]["type"])
  end

  def test_with_without_overrides_rebuilds_the_same_model
    assert_equal Tickets.to_ir, Tickets.with.to_ir
    assert_empty Tickets.overrides
  end

  def test_with_rebuilds_the_model_with_the_overridden_value
    direct = Fmspec.define(:tickets) do
      capacity = constant :capacity, 4
      state :sold, int(0..capacity + 1), initial: 0

      action :purchase, quantity: 1..2 do |s, quantity|
        guard s.sold + quantity <= s.capacity
        update sold: s.sold + quantity
      end

      action :cancel do |s|
        guard s.sold > 0
        update sold: s.sold - 1
      end

      invariant(:capacity_respected) { |s| s.sold <= s.capacity }
    end
    overridden = Tickets.with(capacity: 4)
    assert_equal without_sources(direct.to_ir), without_sources(overridden.to_ir)
    assert_equal({ capacity: 4 }, overridden.overrides)
    refute_equal Tickets.digest, overridden.digest
    assert_equal direct.digest, overridden.digest
  end

  def test_overrides_accumulate
    model = Fmspec.define(:two) do
      a = constant :a, 1
      b = constant "b", 2
      state :x, int(0..(a + b)), initial: 0
    end
    both = model.with(a: 3).with("b" => 4)
    assert_equal({ a: 3, b: 4 }, both.overrides)
    assert_equal 7, both.to_ir["states"][0]["type"]["int"]["max"]
    assert_equal 5, both.with(a: 1).to_ir["states"][0]["type"]["int"]["max"]
  end

  def test_overrides_are_checked_against_the_declared_type
    error = assert_raises(Fmspec::BuildError) { Tickets.with(capacity: true) }
    assert_match(/定数 capacity の上書きの値: int の式が必要ですが、bool の式です/, error.message)

    error = assert_raises(Fmspec::BuildError) { Tickets.with(limit: 3) }
    assert_match(/宣言していない定数は上書きできません: limit/, error.message)

    menu = Fmspec.define(:menu) do
      item = enum(:item, :apple, :bread)
      constant :menu, set_of(item), Set[:apple]
      constant :favorite, :apple
      state :x, bool, initial: false
      invariant(:listed) { |s| s.menu.include?(s.favorite) | s.x }
    end
    assert_includes JSON.generate(menu.to_ir["invariants"]), '"variant":"apple"'
    refute_includes JSON.generate(menu.to_ir["invariants"]), '"variant":"bread"'
    assert_includes JSON.generate(menu.with(menu: Set[:bread]).to_ir["invariants"]), '"variant":"bread"'
    error = assert_raises(Fmspec::BuildError) { menu.with(menu: Set[:milk]) }
    assert_match(/定数 menu の上書きの値/, error.message)
    error = assert_raises(Fmspec::BuildError) { menu.with(favorite: :milk) }
    assert_match(/列挙型 item に :milk はありません/, error.message)
  end

  def test_the_number_of_processes_can_depend_on_a_constant
    assert_equal({ incr: 2 }, counter.processes.transform_values { |p| p[:count] })
    assert_equal({ incr: 3 }, counter.with(workers: 3).processes.transform_values { |p| p[:count] })
  end

  def test_sweep_checks_each_combination
    results = Tickets.sweep(capacity: 2..4)
    assert_equal [{ capacity: 2 }, { capacity: 3 }, { capacity: 4 }], results.map(&:first)
    assert_equal [:verified] * 3, results.map { |_, r| r.status }
    assert_equal [3, 4, 5], results.map { |_, r| r.visited_states }
  end

  def test_sweep_finds_the_values_where_a_property_fails
    racy = counter do
      invariant(:no_lost_update) { |s| implies(s.incr[0].done & s.incr[1].done, s.count >= 2) }
    end
    results = racy.sweep(workers: [2, 3]) { |m| m.check(deadlock: true) }
    assert_equal [:violated, :violated], results.map { |_, r| r.status }
  end

  def test_sweep_takes_the_product_of_the_candidates
    model = Fmspec.define(:pair) do
      a = constant :a, 1
      b = constant :b, false
      state :x, int(0..a), initial: 0
      invariant(:fine) { |s| s.b | s.x.eq(s.x) }
    end
    results = model.sweep(a: [1, 2], b: [false, true]) { |m| m.overrides }
    assert_equal [[{ a: 1, b: false }, { a: 1, b: false }], [{ a: 1, b: true }, { a: 1, b: true }],
                  [{ a: 2, b: false }, { a: 2, b: false }], [{ a: 2, b: true }, { a: 2, b: true }]], results
  end

  def test_sweep_rejects_malformed_candidates
    assert_raises(ArgumentError) { Tickets.sweep }
    assert_match(/範囲か配列/, assert_raises(ArgumentError) { Tickets.sweep(capacity: 3) }.message)
    assert_match(/終わりがありません/, assert_raises(ArgumentError) { Tickets.sweep(capacity: (2..)) }.message)
    assert_match(/候補が空/, assert_raises(ArgumentError) { Tickets.sweep(capacity: []) }.message)
  end

  def test_composed_models_cannot_be_rebuilt
    shop = Fmspec.compose(:shop, tickets: Tickets)
    error = assert_raises(Fmspec::BuildError) { shop.with(capacity: 4) }
    assert_match(/Fmspec.define で定義した仕様ではない/, error.message)
  end
end
