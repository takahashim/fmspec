# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 詳細化の検査（docs/plans/refinement_symmetry_constants.md の2）。
class RefinementTest < Minitest::Test
  # 抽象モデル。increment は atomic で、終えた回数を数える。
  ATOMIC = Fmspec.define(:atomic) do
    state :count, int(0..2), initial: 0
    state :finished, int(0..2), initial: 0

    action :incr do |s|
      guard s.finished < 2
      update count: s.count + 1, finished: s.finished + 1
    end

    invariant(:counted) { |s| s.count.eq(s.finished) }
  end

  # 具体モデル。2つの作業者が、読んでから書く。`locked` なら、読んでから書くまでをロックで守る。
  def counter(locked:)
    Fmspec.define(:counter) do
      pc = enum(:pc, :load, :store, :done)
      constant :locked, locked
      state :count, int(0..2), initial: 0
      state :lock, bool, initial: false
      %i[a b].each do |w|
        state :"pc_#{w}", pc, initial: :load
        state :"seen_#{w}", int(0..2), initial: 0
      end

      %i[a b].each do |w|
        action :"load_#{w}" do |s|
          guard s.__send__(:"pc_#{w}").eq(:load)
          guard s.lock.not_ | s.locked.not_
          update :"seen_#{w}" => s.count, :"pc_#{w}" => :store, lock: s.locked
        end

        action :"store_#{w}" do |s|
          guard s.__send__(:"pc_#{w}").eq(:store)
          update count: s.__send__(:"seen_#{w}") + 1, :"pc_#{w}" => :done, lock: false
        end
      end
    end
  end

  def refinement(concrete, abstract = ATOMIC, &block)
    block ||= lambda do |_|
      map(:count) { |s| s.count }
      map(:finished) { |s| ite(s.pc_a.eq(:done), 1, 0) + ite(s.pc_b.eq(:done), 1, 0) }
    end
    Fmspec.refinement(:r, concrete: concrete, abstract: abstract, &block)
  end

  def test_a_model_refines_itself
    r = Fmspec.refinement(:identity, concrete: ATOMIC, abstract: ATOMIC) do
      map(:count) { |s| s.count }
      map(:finished) { |s| s.finished }
    end
    result = r.check
    assert_predicate result, :refines?, result.to_s
    assert_equal 3, result.visited_states
    assert_match(/\ARefines: identity（atomic → atomic）/, result.to_s)
  end

  def test_the_locked_counter_refines_the_atomic_increment
    result = refinement(counter(locked: true)).check
    assert_predicate result, :refines?, result.to_s
  end

  def test_the_lost_update_does_not_refine_the_atomic_increment
    result = refinement(counter(locked: false)).check
    assert_predicate result, :not_refines?, result.to_s
    assert_equal "step", result.property["violation"]
    assert_equal "store_b", result.property["action"]
    trace = result.trace
    assert_equal %i[load_a load_b store_a store_b], trace.steps.map(&:action)
    # 最後の遷移は、抽象モデルの (1, 1) から (1, 2) への移動になり、increment ではない。
    assert_equal [{ "count" => 0, "finished" => 0 }, { "count" => 0, "finished" => 0 },
                  { "count" => 0, "finished" => 0 }, { "count" => 1, "finished" => 1 },
                  { "count" => 1, "finished" => 2 }], result.abstract_states
    assert_match(/NotRefines: r（counter → atomic）/, result.to_s)
    assert_match(/抽象 /, result.to_s)
  end

  def test_steps_that_do_not_change_the_mapped_state_are_stutter_steps
    # 読むだけの操作は、抽象モデルの状態を変えない。
    result = refinement(counter(locked: true)).check(actions: %i[load_a])
    assert_predicate result, :refines?, result.to_s
  end

  def test_an_initial_state_that_maps_outside_the_abstract_initial_states
    concrete = Fmspec.define(:one) do
      state :count, int(0..2), initial: 1
      state :finished, int(0..2), initial: 0
    end
    r = Fmspec.refinement(:init, concrete: concrete, abstract: ATOMIC) do
      map(:count) { |s| s.count }
      map(:finished) { |s| s.finished }
    end
    result = r.check
    assert_predicate result, :not_refines?, result.to_s
    assert_equal "initial", result.property["violation"]
    assert_equal 0, result.trace.length
  end

  def test_a_mapping_out_of_the_abstract_type_is_an_error
    concrete = Fmspec.define(:big) do
      state :n, int(0..5), initial: 0
      action :up do |s|
        guard s.n < 5
        update n: s.n + 1
      end
    end
    abstract = Fmspec.define(:small) do
      state :m, int(0..2), initial: 0
      action :up do |s|
        guard s.m < 2
        update m: s.m + 1
      end
    end
    r = Fmspec.refinement(:range, concrete: concrete, abstract: abstract) { map(:m) { |s| s.n } }
    result = r.check
    assert_predicate result, :error?, result.to_s
    assert_equal "mapping", result.property["violation"]
    assert_equal "m", result.property["state"]
    assert_equal 3, result.trace.length
    assert_nil result.abstract_states.last
  end

  def test_an_error_in_the_concrete_model_is_an_error
    concrete = Fmspec.define(:divides) do
      state :n, int(0..2), initial: 0
      action :up do |s|
        update n: 2 / s.n
      end
    end
    abstract = Fmspec.define(:any) { state :n, int(0..2), initial: 0 }
    result = Fmspec.refinement(:div, concrete: concrete, abstract: abstract) { map(:n) { |s| s.n } }.check
    assert_predicate result, :error?, result.to_s
    assert_equal "update", result.property["site"]
  end

  def test_the_search_limit_is_inconclusive
    result = refinement(counter(locked: true)).check(max_states: 2)
    assert_predicate result, :inconclusive?, result.to_s
    assert_equal :max_states, result.reason
  end

  def test_an_abstract_model_that_fails_at_the_mapped_state_is_inconclusive
    concrete = Fmspec.define(:c) do
      state :n, int(0..1), initial: 0
      action :up do |s|
        guard s.n.eq(0)
        update n: 1
      end
    end
    # 写した状態 0 で、抽象モデルの唯一の操作の評価が失敗する。移れないとは言えない。
    abstract = Fmspec.define(:a) do
      state :n, int(0..1), initial: 0
      action :broken do |s|
        update n: 1 / s.n
      end
    end
    result = Fmspec.refinement(:fails, concrete: concrete, abstract: abstract) { map(:n) { |s| s.n } }.check
    assert_predicate result, :inconclusive?, result.to_s
    assert_equal :abstract_failed, result.reason
  end

  def test_enumerations_are_shared_by_name
    concrete = Fmspec.define(:c) do
      c = enum(:color, :red, :green)
      state :x, c, initial: :red
      action :flip do |s|
        update x: ite(s.x.eq(:red), c[:green], c[:red])
      end
    end
    abstract = Fmspec.define(:a) do
      c = enum(:color, :red, :green)
      state :y, c, initial: :red
      action :flip do |s|
        update y: ite(s.y.eq(:red), c[:green], c[:red])
      end
    end
    result = Fmspec.refinement(:colors, concrete: concrete, abstract: abstract) { map(:y) { |s| s.x } }.check
    assert_predicate result, :refines?, result.to_s

    other = Fmspec.define(:o) { state :y, enum(:color, :red, :blue), initial: :red }
    error = assert_raises(Fmspec::BuildError) do
      Fmspec.refinement(:clash, concrete: concrete, abstract: other) { map(:y) { |s| s.x } }
    end
    assert_match(/列挙型 color のラベル/, error.message)
  end

  def test_the_mapping_must_cover_every_abstract_state_variable
    assert_match(/finished の写像がありません/, assert_raises(Fmspec::BuildError) do
      refinement(counter(locked: true)) { |_| map(:count) { |s| s.count } }
    end.message)
    assert_match(/状態変数 nope はありません/, assert_raises(Fmspec::BuildError) do
      refinement(counter(locked: true)) { |_| map(:nope) { |s| s.count } }
    end.message)
    assert_match(/状態変数 missing はありません/, assert_raises(Fmspec::BuildError) do
      refinement(counter(locked: true)) do |_|
        map(:count) { |s| s.missing }
      end
    end.message)
    assert_match(/定義済み/, assert_raises(Fmspec::BuildError) do
      refinement(counter(locked: true)) do |_|
        map(:count) { |s| s.count }
        map(:count) { |s| s.count }
      end
    end.message)
    assert_match(/int の式が必要/, assert_raises(Fmspec::BuildError) do
      refinement(counter(locked: true)) do |_|
        map(:count) { |s| s.lock }
        map(:finished) { |s| s.count }
      end
    end.message)
  end

  def test_the_document_has_both_models_and_the_mapping
    ir = refinement(counter(locked: true)).to_ir
    assert_equal %w[abstract concrete ir_version mapping name], ir.keys.sort
    assert_equal %w[count finished], ir["mapping"].map { |m| m["state"] }
    assert_equal "counter", ir["concrete"]["name"]
  end

  def test_an_unknown_action_is_a_usage_error
    assert_raises(ArgumentError) { refinement(counter(locked: true)).check(actions: %i[nope]) }
  end
end
