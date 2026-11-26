# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require "set"

# 複合型、量化、let、除算の DSL。IRへの変換と、検査の結果を確かめる。
class CompositeTest < Minitest::Test
  def basket
    Fmspec.define(:basket) do
      item = enum(:item, :apple, :bread, :milk)
      state :items, set_of(item), initial: Set[]

      action :add, x: item do |s, x|
        guard s.items.include?(x).not_
        update items: s.items.add(x)
      end

      action :drop, x: item do |s, x|
        guard s.items.include?(x)
        update items: s.items.delete(x)
      end

      invariant(:small) { |s| s.items.size <= 3 }
      invariant(:no_milk_alone) { |s| s.items.include?(:milk).implies(s.items.any? { |y| y.ne(:milk) }) }
    end
  end

  def test_sets_are_explored_as_values
    result = basket.check
    assert_predicate result, :violated?
    assert_equal({ "violation" => "invariant", "name" => "no_milk_alone" }, result.property.except("source"))
    assert_equal [{ "items" => ["milk"] }], result.trace.states
  end

  def test_set_expressions_lower_to_ir
    ir = without_sources(basket.to_ir)
    add = ir["actions"][0]
    assert_equal({ "not" => [{ "contains" => [{ "var" => 0 }, { "param" => 0 }] }] }, add["guard"])
    assert_equal [{ "target" => 0, "expr" => { "insert" => [{ "var" => 0 }, { "param" => 0 }] } }], add["updates"]
    assert_equal({ "set" => { "of" => { "enum" => "item" }, "items" => [] } }, ir["states"][0]["initial"])
  end

  def wallet(limit)
    Fmspec.define(:wallet) do
      item = enum(:item, :apple, :bread, :milk)
      state :balance, map_of(item, int(0..2)), initial: { bread: 1 }

      action :deposit, k: item do |s, k|
        current = ite(s.balance.key?(k), s.balance[k], 0)
        guard current < limit
        update balance: s.balance.put(k, current + 1)
      end

      action :close, k: item do |s, k|
        guard s.balance.key?(k)
        update balance: s.balance.delete(k)
      end

      invariant(:bounded) { |s| s.balance.keys.all? { |k| s.balance[k] <= 2 } }
    end
  end

  def test_maps_hold_values_per_key
    result = wallet(2).check
    assert_predicate result, :verified?
    assert_equal 27, result.visited_states

    result = wallet(3).check
    assert_predicate result, :error?
    assert_equal({ "kind" => "not_in_domain" }, result.property["error"])
    assert_equal({ "balance" => [["bread", 1]] }, result.trace.initial)
  end

  def queue
    Fmspec.define(:queue) do
      state :q, list_of(int(0..3), max: 2), initial: []

      action :enqueue, x: 0..3 do |s, x|
        guard s.q.size < 2
        update q: s.q.push(x)
        ensures(:last) { |after| after.q.last.eq(x) }
      end

      action :dequeue do |s|
        guard s.q.empty?.not_
        update q: s.q.shift
        returns s.q.first, int(0..3)
        ensures(:fifo) { |_, out| out.eq(s.q[0]) }
      end
    end
  end

  def test_lists_behave_as_queues
    result = queue.check
    assert_predicate result, :verified?
    assert_equal 21, result.visited_states
  end

  def test_options_and_records
    model = Fmspec.define(:robot) do
      user = enum(:user, :alice, :bob)
      point = record(x: int(0..2), y: int(0..2))
      state :holder, option(user), initial: nil
      state :pos, point, initial: { x: 0, y: 0 }

      action :acquire, u: user do |s, u|
        guard s.holder.none?
        update holder: some(u)
      end

      action :release do |s|
        guard s.holder.some?
        update holder: nil
      end

      action :step, d: tuple(0..1, 0..1) do |s, d|
        guard s.holder.some? & ((s.pos[:x] + d[0]) < 3) & ((s.pos[:y] + d[1]) < 3)
        update pos: { x: s.pos[:x] + d[0], y: s.pos[:y] + d[1] }
      end

      invariant(:not_corner_alone) { |s| s.pos.ne({ x: 2, y: 2 }) | s.holder.eq(:bob) }
    end
    result = model.check
    assert_predicate result, :violated?
    steps = result.trace.steps
    assert_equal [:acquire, :step, :step], steps.map(&:action)
    assert_equal({ "u" => "alice" }, steps[0].args)
    assert_equal({ "d" => [1, 1] }, steps[1].args)
    assert_equal({ "holder" => { "some" => "alice" }, "pos" => { "x" => 2, "y" => 2 } }, steps.last.state)
  end

  def test_division_rounds_toward_negative_infinity
    model = Fmspec.define(:arith) do
      state :n, int(0..0), initial: 0
      invariant(:floor) do
        forall(int(-7..7)) do |x|
          forall(int(-3..3)) do |y|
            y.ne(0).implies(let(x / y) { |q| ((q * y) + (x % y)).eq(x) & (x % y).ne(y) })
          end
        end
      end
      invariant(:ruby) { |s| ((s.n - 7) / 2).eq(-7 / 2) & ((s.n + 7) % -2).eq(7 % -2) & ((s.n - 7) / -2).eq(-7 / -2) }
      invariant(:exists_type) { exists(option(bool)) { |o| o.none? } }
    end
    assert_predicate model.check, :verified?
  end

  def test_typed_constants
    model = Fmspec.define(:menu) do
      item = enum(:item, :apple, :bread, :milk)
      constant :menu, set_of(item), Set[:apple, :bread]
      state :order, set_of(item), initial: Set[]

      action :order, x: item do |s, x|
        guard s.menu.include?(x)
        update order: s.order.add(x)
      end

      invariant(:on_menu) { |s| s.order <= s.menu }
      invariant(:no_milk) { |s| s.order.include?(:milk).not_ }
    end
    result = model.check
    assert_predicate result, :verified?
    assert_equal 4, result.visited_states
  end

  def test_build_errors
    error = ->(&block) { assert_raises(Fmspec::BuildError) { Fmspec.define(:bad, &block) }.message }
    assert_match(/set_of の要素の型/, error.call { state :s, set_of(set_of(bool)), initial: [] })
    assert_match(/初期値 \[5\] は set_of\(int\(0\.\.3\)\) の値ではありません/,
                 error.call { state :s, set_of(int(0..3)), initial: [5] })
    assert_match(/上限 1 を超えます/, error.call { state :s, list_of(bool, max: 1), initial: [true, false] })
    assert_match(/出力の型は bool、int、enum に限ります/, error.call do
      state :s, int(0..0), initial: 0
      action(:get) { |s| returns some(s.s) }
    end)
    assert_match(/型が決まりません/, error.call do
      state :s, int(0..0), initial: 0
      invariant(:p) { |s| some(s.s).eq(nil) | Fmspec::Expr.lift(nil).eq(nil) }
    end)
  end

  def seats_model(full_swap:)
    least = full_swap ? 2 : 0
    Fmspec.define(:seats) do
      user = enum(:user, :ann, :bob, :cy)
      seats = list_of(user, max: 2)
      state :waiting, set_of(user), initial: Set[:ann, :bob, :cy]
      state :seated, seats, initial: []

      action :seat, u: ->(s) { s.waiting } do |s, u|
        guard s.seated.size < 2
        update waiting: s.waiting.delete(u), seated: s.seated.push(u)
      end

      action :swap, out: ->(s) { s.seated }, inn: ->(s, out) { s.waiting.delete(out) } do |s, out, inn|
        guard s.seated.size >= least
        update waiting: s.waiting.add(out).delete(inn),
               seated: ite(s.seated[0].eq(out), seats.value([inn, s.seated[1]]), [s.seated[0], inn])
      end

      action :leave do |s|
        victim = choose(:victim, s.seated)
        update waiting: s.waiting.add(victim), seated: ite(s.seated.first.eq(victim), s.seated.shift, s.seated.pop)
      end

      invariant(:everyone) { |s| forall(user) { |x| s.waiting.include?(x) | s.seated.include?(x) } }
    end
  end

  def test_dynamic_domains
    model = seats_model(full_swap: false)
    seat, swap, leave = model.to_ir["actions"]
    assert_equal({ "name" => "u", "type" => { "enum" => "user" }, "in" => { "var" => 0 } }, seat["params"][0])
    assert_equal({ "remove" => [{ "var" => 0 }, { "param" => 0 }] }, swap["params"][1]["in"])
    assert_equal({ "var" => 1 }, leave["choices"][0]["in"])

    # 1人だけ座っているときの swap は、2番目の席を読んで評価エラーになる。
    result = model.check
    assert_predicate result, :error?
    assert_equal ["swap", "update", { "kind" => "index_out_of_range" }], result.property.values_at("action", "site", "error")
    assert_equal [:seat], result.trace.steps.map(&:action)

    # leave は、座っている人がいなければ選択肢がなく、無効になる。
    result = seats_model(full_swap: true).check(deadlock: true)
    assert_predicate result, :verified?
  end

  # ---- 実装との適合性検査 ----

  class Cart
    def initialize(bug: false)
      @items = Set.new
      @history = []
      @bug = bug
    end

    attr_reader :items, :history

    def add(x)
      @items << x unless @bug && x == :milk
      @history << x
      @history.shift if @history.length > 2
    end
  end

  def cart_model
    Fmspec.define(:cart) do
      item = enum(:item, :apple, :milk)
      state :items, set_of(item), initial: Set[]
      state :history, list_of(item, max: 2), initial: []

      action :add, x: item do |s, x|
        update items: s.items.add(x),
               history: ite(s.history.size < 2, s.history.push(x), s.history.shift.push(x))
      end
    end
  end

  def cart_binding(model, bug: false)
    model.bind do
      setup { Cart.new(bug: bug) }
      command(:add) { |cart, x:| cart.add(x) }
      observe(:items) { |cart| cart.items }
      observe(:history) { |cart| cart.history }
    end
  end

  def test_composite_observations_are_compared
    model = cart_model
    assert_predicate model.check, :verified?
    assert_equal :passed, model.test(cart_binding(model), cases: 20, steps: 6, seed: 1).status
    result = model.test(cart_binding(model, bug: true), cases: 20, steps: 6, seed: 1)
    assert_equal :conformance_failure, result.status
    assert_equal [[:add, { x: :milk }]], result.inputs
    assert_match(/expected items: \["milk"\]\n  observed items: #{Regexp.escape(Set.new.inspect)}/, result.to_s)
  end
end
