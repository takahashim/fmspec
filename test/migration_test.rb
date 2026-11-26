# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# 移行（仕様書 §12.5）。段階の列への展開と、各段階で成り立つべき不変条件。
class MigrationTest < Minitest::Test
  # 列名の変更（old_name から new_name へ）。1行の値を、書き込みの版（0..2）で表す。new_name の -1 は NULL。
  #
  # アプリケーションは2台で、ローリングデプロイの間は旧版と新版が混在する。
  # 新版は、段階 dual_write 以後は両方の列に書き、それより前は旧列だけに書く。旧版は旧列だけに書く。
  # バックフィルは旧列を新列に写す。失敗すれば再試行する。
  #
  # `premature: true` は、すべてのインスタンスが新版になる前に dual_write へ進む誤った手順である。
  def rename(premature: false)
    Fmspec.define(:rename) do
      state :old_name, int(0..2), initial: 0
      state :new_name, int(-1..2), initial: -1
      state :new_instances, int(0..2), initial: 0
      state :writes, int(0..2), initial: 0
      state :backfilled, bool, initial: false

      migration :rename, phases: %i[initial expand dual_write backfilled contracted] do
        # 列を追加する。
        advance(:expand) { |_s| update new_name: -1 }
        advance(:dual_write) { |s| guard s.new_instances.eq(2) } unless premature
        advance(:backfilled) { |s| guard s.backfilled }
        # 新列を読むように切り替えたあとは、新列が旧列と同じ値を持つ。
        holds(:copied, during: %i[backfilled contracted]) { |s| s.new_name.eq(s.old_name) }
      end

      # 1台を新版にする。新版は新列を前提にするので、列の追加のあとに限る。
      action :deploy do |s|
        guard s.rename.reached(:expand) & (s.new_instances < 2)
        update new_instances: s.new_instances + 1
      end

      action :write do |s|
        by_new = choose(:by_new, bool)
        guard (s.writes < 2) & ite(by_new, s.new_instances > 0, s.new_instances < 2)
        version = s.writes + 1
        update writes: version, old_name: version,
               new_name: ite(by_new & s.rename.reached(:dual_write), version, s.new_name)
      end

      action :backfill do |s|
        ok = choose(:ok, bool)
        guard s.rename.during(:dual_write) & s.backfilled.not_
        update new_name: ite(ok, s.old_name, s.new_name), backfilled: ok
      end
    end
  end

  def test_phases_expand_into_a_state_variable_actions_and_invariants
    ir = rename.to_ir
    assert_includes ir["enums"], { "name" => "rename.phase", "variants" => %w[initial expand dual_write backfilled contracted] }
    phase = ir["states"].index { |s| s["name"] == "rename.phase" }
    assert_equal({ "enum" => { "type" => "rename.phase", "variant" => "initial" } }, ir["states"][phase]["initial"])
    steps = ir["actions"].select { |a| a["name"].start_with?("rename.") }
    assert_equal %w[rename.expand rename.dual_write rename.backfilled rename.contracted], steps.map { |a| a["name"] }
    # dual_write へは expand からだけ進み、guard を加える。
    dual = steps[1]
    assert_equal 2, dual["guard"]["all"].length
    assert_includes dual["updates"], { "target" => phase, "expr" => { "enum" => { "type" => "rename.phase", "variant" => "dual_write" } } }
    assert_equal ["rename.copied"], ir["invariants"].map { |i| i["name"] }
  end

  def test_each_transitional_state_keeps_its_invariant
    result = rename.check(deadlock: false)
    assert result.verified?, result.to_s
  end

  def test_a_premature_phase_is_found_with_mixed_versions
    result = rename(premature: true).check
    assert_equal :violated, result.status
    assert_equal "rename.copied", result.property["name"]
    steps = result.trace.steps
    # 旧版が残ったまま dual_write とバックフィルに進み、旧版の書き込みが新列に届かない。
    assert_includes steps.map(&:action), :"rename.backfilled"
    old_write = steps.find { |st| st.action == :write && st.choices["by_new"] == false }
    assert old_write
    assert_operator steps.index(old_write), :>, steps.index { |st| st.action == :backfill }
  end

  def test_phases_are_referenced_from_other_definitions
    model = Fmspec.define(:flag) do
      state :x, int(0..1), initial: 0
      migration(:flag, phases: %i[off on])
      action :set do |s|
        guard s.flag.reached(:on) & s.x.eq(0)
        update x: 1
      end
      invariant(:only_when_on) { |s| implies(s.x.eq(1), s.flag.phase.eq(:on)) }
    end
    result = model.check(deadlock: true)
    assert_equal :violated, result.status
    assert_equal "deadlock", result.property["violation"]
    assert_equal %i[flag.on set], result.trace.steps.map(&:action)
  end

  def test_invalid_migrations_are_rejected
    errors = {
      /2つ以上の段階/ => proc { migration(:m, phases: [:a]) },
      /重複/ => proc { migration(:m, phases: %i[a a]) },
      /段階 c はありません/ => proc { migration(:m, phases: %i[a b]) { advance(:c) { |_s| nil } } },
      /最初の段階 a へは進めません/ => proc { migration(:m, phases: %i[a b]) { advance(:a) { |_s| nil } } },
      /holds h の段階 c はありません/ => proc { migration(:m, phases: %i[a b]) { holds(:h, during: [:c]) { |_s| true } } },
      /移行 m に段階 c はありません/ => proc {
        migration(:m, phases: %i[a b])
        invariant(:i) { |s| s.m.reached(:c) }
      }
    }
    errors.each do |message, block|
      error = assert_raises(Fmspec::BuildError) { Fmspec.define(:bad, &block) }
      assert_match message, error.message
    end
  end
end
