# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
require "timeout"

# RubyとRustの境界（仕様書 §3.2、§17.2）。
class NativeTest < Minitest::Test
  # 到達可能な状態が 300^3 個あり、探索が終わるまでに数十秒以上かかるモデル。
  def huge = @huge ||= TestModels.counters(3, 299)

  def test_a_check_can_be_interrupted_by_timeout
    started = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    assert_raises(Timeout::Error) { Timeout.timeout(0.3) { huge.check } }
    elapsed = Process.clock_gettime(Process::CLOCK_MONOTONIC) - started
    assert_operator elapsed, :<, 3.0, "中断に時間がかかりすぎている"
    # 中断のあとも、同じモデルを検査できる。
    assert_equal :inconclusive, huge.check(max_states: 10).status
  end

  def test_a_simulation_can_be_interrupted_by_timeout
    assert_raises(Timeout::Error) { Timeout.timeout(0.3) { huge.simulate(traces: 10**9, max_steps: 1000, seed: 1) } }
  end

  def test_a_check_can_be_interrupted_from_another_thread
    worker = Thread.new { huge.check }
    sleep 0.2
    worker.kill
    assert_nil worker.join(3)&.value
    refute_predicate worker, :alive?
  end

  # 検査の間、GVL を解放している。
  def test_other_ruby_threads_run_during_a_check
    ticks = 0
    ticker = Thread.new { loop { ticks += 1; sleep 0.001 } }
    before = ticks
    result = huge.check(max_states: 300_000)
    during = ticks - before
    ticker.kill
    assert_equal :inconclusive, result.status
    elapsed_ms = result.search["time_ms"]
    assert_operator during, :>, [elapsed_ms / 20, 3].max, "検査の #{elapsed_ms.round}ms の間に、他のスレッドが #{during} 回しか動いていない"
  end

  def test_one_model_can_be_checked_from_several_threads_at_once
    model = TestModels.counters(2, 30)
    results = Array.new(4) { Thread.new { model.check.visited_states } }.map(&:value)
    assert_equal [961] * 4, results
  end

  def test_a_panic_becomes_an_internal_error_and_the_process_survives
    skip "この拡張はテスト用のメソッドなしでビルドされている" unless Fmspec::Native.respond_to?(:test_panic)
    _, stderr = capture_subprocess_io do
      error = assert_raises(Fmspec::InternalError) { Fmspec::Native.test_panic }
      assert_match(/fmspec: test panic/, error.message)
    end
    assert_match(/panicked/, stderr)
    # StandardError ではないので、rescue => e では捕まらない。
    refute_operator Fmspec::InternalError, :<, StandardError
    assert_operator Fmspec::InternalError, :<, Exception
    assert_equal :verified, TestModels.tickets.check.status
  end

  def test_models_are_made_only_by_load
    assert_raises(NoMethodError, TypeError) { Fmspec::Native::Model.new }
    loaded = Fmspec::Native::Model.load(TestModels.tickets.to_json)
    assert_instance_of Fmspec::Native::Model, loaded
    assert_equal "valid", JSON.parse(loaded.describe)["status"]
    GC.start
    GC.compact if GC.respond_to?(:compact)
    assert_equal "verified", JSON.parse(loaded.check("{}"))["status"]
  end

  def test_arguments_are_checked
    model = Fmspec::Native::Model.load(TestModels.tickets.to_json)
    assert_raises(TypeError) { Fmspec::Native::Model.load(42) }
    assert_raises(TypeError) { model.check(nil) }
    assert_raises(ArgumentError) { model.check("not json") }
    assert_raises(ArgumentError) { model.check("\xff".b.force_encoding("UTF-8")) }
    assert_raises(ArgumentError) { model.check }
    assert_equal "usage_error", JSON.parse(model.check('{"depth": 1}'))["status"]
    assert_equal "usage_error", JSON.parse(model.simulate("[]"))["status"]
    assert_equal "rejected", JSON.parse(model.replay("{}"))["status"]
    assert_equal "rejected", JSON.parse(model.verify_certificate("not json", "{}"))["status"]
  end

  # エンジンのIR検証は、Ruby 側で検査済みであることを信頼しない。
  def test_the_engine_validates_the_ir_itself
    ir = JSON.parse(TestModels.tickets.to_json)
    ir["invariants"][0]["expr"] = { "var" => 0 }
    rejected = Fmspec::Native::Model.load(JSON.generate(ir))
    assert_kind_of String, rejected
    assert_equal "invalid_model", JSON.parse(rejected)["status"]
    assert_match(/capacity_respected/, JSON.parse(rejected)["message"])
    assert_equal "invalid_model", JSON.parse(Fmspec::Native::Model.load("{"))["status"]

    model = Fmspec::Model.new(:broken, ir)
    error = assert_raises(Fmspec::InvalidModelError) { model.check }
    assert_match(/不変条件 "capacity_respected" が Bool 式でない/, error.message)
  end

  def test_the_extension_reports_the_gem_version
    assert_equal Fmspec::VERSION, Fmspec::Native.version
  end
end
