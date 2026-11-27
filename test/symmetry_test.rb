# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 対称性による削減（docs/plans/refinement_symmetry_constants.md の3）。
class SymmetryTest < Minitest::Test
  # `n` 人の作業者が、ロックを取ってから共有のカウンタを読んで書く。`racy` ならロックを取らない。
  def workers(n, symmetric: true, racy: false)
    Fmspec.define(:workers) do
      constant :racy, racy
      state :count, int(0..n), initial: 0
      state :lock, bool, initial: false

      process :w, count: n, symmetric: symmetric do
        local :seen, int(0..n), initial: 0
        step(:acquire) do |s|
          guard s.lock.not_ | s.racy
          update lock: s.racy.not_
        end
        step(:load) { |s| update seen: s.count }
        step(:store) { |s| update count: s.seen + 1 }
        step(:release) { |_s| update lock: false }
      end

      # インスタンスをまたぐ不変条件。入れ替えると別の式になるので、像を加えて検査する。
      invariant(:no_lost_update) do |s|
        s.count >= (0...n).map { |i| ite(s.w[i].done, 1, 0) }.reduce(:+)
      end
    end
  end

  def test_the_reduced_check_agrees_with_the_full_check_and_visits_fewer_states
    model = workers(3)
    full = model.check(symmetry: false)
    reduced = model.check
    assert_predicate full, :verified?, full.to_s
    assert_predicate reduced, :verified?, reduced.to_s
    assert_operator reduced.visited_states, :<, full.visited_states
    assert_equal({ "groups" => [3], "swaps" => 2 }, reduced.to_h["symmetry"])
  end

  def test_the_reduction_grows_with_the_number_of_instances
    ratios = (2..4).map do |n|
      model = workers(n)
      model.check(symmetry: false).visited_states.fdiv(model.check.visited_states)
    end
    assert_equal ratios.sort, ratios
    assert_operator ratios.last, :>, 4
  end

  def test_a_violation_found_on_representatives_is_reported_as_a_concrete_trace
    result = workers(3, racy: true).check
    assert_predicate result, :violated?, result.to_s
    assert_equal "no_lost_update", result.property["name"]
    # 判定ゲートが、代表元の経路から作った具体的なトレースを、そのまま再生して受理している。
    assert_operator result.trace.length, :>, 0
    assert_predicate workers(3, racy: true).replay(result.trace), :violated?
    full = workers(3, racy: true).check(symmetry: false)
    assert_equal full.trace.length, result.trace.length
  end

  def test_a_declaration_that_is_not_a_symmetry_is_rejected
    model = Fmspec.define(:lopsided) do
      state :count, int(0..4), initial: 0
      process :w, count: 2, symmetric: true do |id|
        step(:add) { |s| update count: s.count + (id + 1) }
      end
    end
    error = assert_raises(ArgumentError) { model.check }
    assert_match(/宣言した対称性が成り立ちません/, error.message)
    assert_predicate model.check(symmetry: false), :verified?
  end

  def test_crashing_and_restarting_instances_are_symmetric
    # 3つのジョブが、それぞれ決済してから保存する。保存の前に落ちると、再試行で決済し直す。
    model = ->(symmetric) do
      Fmspec.define(:jobs) do
        state :charges, int(0..6), initial: 0
        process :job, count: 3, crash: :restart, symmetric: symmetric do
          local :paid, bool, initial: false
          step(:charge) { |s| update charges: Fmspec.min(s.charges + 1, 6) }
          step(:save) { |_s| update paid: true }
        end
        invariant(:at_most_two_charges_each) { |s| s.charges <= 6 }
      end
    end
    full = model.(false).check
    reduced = model.(true).check
    assert_predicate full, :verified?, full.to_s
    assert_predicate reduced, :verified?, reduced.to_s
    assert_operator reduced.visited_states, :<, full.visited_states
  end

  def test_explicit_blocks
    model = Fmspec.define(:pairs) do
      state :a, int(0..2), initial: 0
      state :b, int(0..2), initial: 0
      action(:inc_a) do |s|
        guard s.a < 2
        update a: s.a + 1
      end
      action(:inc_b) do |s|
        guard s.b < 2
        update b: s.b + 1
      end
      symmetric [:a], [:b]
    end
    assert_equal 9, model.check(symmetry: false).visited_states
    assert_equal 6, model.check.visited_states
    assert_equal [[["a"], ["b"]]], model.to_ir["symmetry"]
  end

  def test_declarations_are_checked_when_loaded
    bad = ->(blocks) { Fmspec.define(:bad) { state(:a, int(0..1), initial: 0); state(:b, bool, initial: false); symmetric(*blocks) } }
    assert_raises(Fmspec::InvalidModelError) { bad.([[:a], [:b]]).check }
    assert_raises(Fmspec::InvalidModelError) { bad.([[:a], [:nope]]).check }
    assert_raises(Fmspec::BuildError) { bad.([[:a]]) }
  end

  def test_certificates_and_check_cost_are_not_available_with_symmetry
    assert_raises(ArgumentError) { workers(2).check(certificate: true) }
    assert_raises(ArgumentError) { workers(2).check(max_check_cost: 10) }
  end
end
