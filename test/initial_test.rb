# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 初期状態が複数あるモデルの DSL。IRへの変換、検査、実装との適合性検査を確かめる。
class InitialTest < Minitest::Test
  def lights
    Fmspec.define(:lights) do
      color = enum(:color, :red, :green)
      state :a, color, initial_in: color
      state :b, color, initial_in: color
      state :n, int(0..2), initial_in: 0..1
      initially { |s| s.a.ne(s.b) }

      action :inc do |s|
        guard s.n < 2
        update n: s.n + 1
      end

      invariant(:red_or_small) { |s| (s.n < 2) | s.a.eq(:red) }
    end
  end

  def test_candidates_and_the_constraint_lower_to_ir
    ir = lights.to_ir
    red = { "enum" => { "type" => "color", "variant" => "red" } }
    green = { "enum" => { "type" => "color", "variant" => "green" } }
    assert_equal [red, green], ir["states"][0]["initial_in"]
    assert_equal [{ "int" => 0 }, { "int" => 1 }], ir["states"][2]["initial_in"]
    refute ir["states"][0].key?("initial")
    assert_equal({ "ne" => [{ "var" => 0 }, { "var" => 1 }] }, ir["initial_constraint"])
  end

  def test_search_starts_from_every_initial_state
    result = lights.check
    assert_predicate result, :violated?
    # 初期状態は (red, green, 0)、(red, green, 1)、(green, red, 0)、(green, red, 1) の順に起点になる。
    assert_equal({ "a" => "green", "b" => "red", "n" => 1 }, result.trace.initial)
    assert_equal [:inc], result.trace.steps.map(&:action)
    assert_equal 6, result.visited_states
  end

  class Counter
    def initialize(start)
      @n = start
    end

    attr_reader :n

    def inc
      @n += 1
    end
  end

  def counter_model
    Fmspec.define(:counter) do
      state :n, int(0..3), initial_in: [0, 2]

      action :inc do |s|
        guard s.n < 3
        update n: s.n + 1
      end
    end
  end

  def counter_binding(model, start)
    model.bind do
      setup { Counter.new(start) }
      command(:inc) { |counter| counter.inc }
      observe(:n, &:n)
    end
  end

  def test_the_implementation_may_start_in_any_initial_state
    model = counter_model
    [0, 2].each do |start|
      assert_equal :passed, model.test(counter_binding(model, start), cases: 5, steps: 4, seed: 1).status
    end
    result = model.test(counter_binding(model, 1), cases: 5, steps: 4, seed: 1)
    assert_equal :conformance_failure, result.status
    assert_match(/expected n: one of 0, 2\n  observed n: 1/, result.to_s)
  end

  def test_build_errors
    error = ->(&block) { assert_raises(Fmspec::BuildError) { Fmspec.define(:bad, &block) }.message }
    assert_match(/initial と initial_in のどちらか一方/, error.call { state :s, int(0..1) })
    assert_match(/initial と initial_in のどちらか一方/, error.call { state :s, int(0..1), initial: 0, initial_in: [1] })
    assert_match(/initial_in が空です/, error.call { state :s, int(0..1), initial_in: [] })
    assert_match(/範囲外です/, error.call { state :s, int(0..1), initial_in: [0, 2] })
    assert_match(/bool、int、enum だけ/, error.call { state :s, set_of(bool), initial_in: set_of(bool) })
    assert_match(/initially は1つだけ/, error.call do
      state :s, int(0..1), initial_in: 0..1
      initially { |s| s.s.eq(0) }
      initially { |s| s.s.eq(1) }
    end)
  end

  def test_an_unsatisfiable_constraint_is_rejected_on_load
    model = Fmspec.define(:none) do
      state :s, int(0..1), initial_in: 0..1
      initially { |s| s.s > 1 }
    end
    error = assert_raises(Fmspec::Error) { model.check }
    assert_match(/初期条件を満たす初期状態がありません/, error.message)
  end
end
