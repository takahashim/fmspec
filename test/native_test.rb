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

  # 1状態の検査に時間のかかる、100状態の証明書。
  def heavy_certificate
    model = Fmspec.define(:heavy) do
      state :n, int(0..99), initial: 0
      action :inc do |s|
        guard s.n < 99
        update n: s.n + 1
      end
      invariant(:slow) { |s| forall(int(0..1023)) { |x| forall(int(0..1023)) { |y| (x + y + s.n) >= 0 } } }
    end
    conditions = { "actions" => ["inc"], "invariants" => ["slow"], "contracts" => [], "deadlock" => false }
    certificate = { "certificate_version" => 1, "model_digest" => model.digest,
                    "conditions" => conditions, "states" => (0..99).map { |n| [n] } }
    [model, certificate]
  end

  def test_a_certificate_check_can_be_interrupted_by_timeout
    model, certificate = heavy_certificate
    started = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    assert_raises(Timeout::Error) { Timeout.timeout(0.3) { model.verify_certificate(certificate) } }
    elapsed = Process.clock_gettime(Process::CLOCK_MONOTONIC) - started
    assert_operator elapsed, :<, 3.0, "中断に時間がかかりすぎている"
    # 見積もりが上限を超える証明書は、検査せずに :inconclusive にする。
    result = model.verify_certificate(certificate, max_check_cost: 1000)
    assert_equal [:inconclusive, :max_check_cost], [result.status, result.reason]
  end

  # x を d（0..3）だけ増やすモデルと、d = 1 のステップを3000個並べた違反のトレース。
  # どのステップを除いても、どの引数を小さくしても違反しないので、縮小を終えるまでに数秒以上かかる。
  def long_shrink
    model = Fmspec.define(:adder) do
      state :x, int(0..3003), initial: 0
      action :add, d: 0..3 do |s, d|
        guard s.x < 3000
        update x: s.x + d
      end
      invariant(:bound) { |s| s.x < 3000 }
    end
    trace = model.check.trace.to_h.merge(
      "steps" => (1..3000).map do |x|
        { "action" => "add", "args" => { "d" => 1 }, "choices" => {}, "output" => { "unit" => true }, "state" => { "x" => x } }
      end
    )
    [model, trace]
  end

  def test_a_shrink_can_be_interrupted_by_timeout
    model, trace = long_shrink
    assert_equal :violated, model.replay(trace).status
    started = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    assert_raises(Timeout::Error) { Timeout.timeout(0.3) { model.shrink(trace) } }
    elapsed = Process.clock_gettime(Process::CLOCK_MONOTONIC) - started
    assert_operator elapsed, :<, 3.0, "中断に時間がかかりすぎている"
  end

  def test_a_shrink_can_be_interrupted_from_another_thread
    model, trace = long_shrink
    worker = Thread.new { model.shrink(trace) }
    sleep 0.2
    worker.kill
    assert_nil worker.join(3)&.value
    refute_predicate worker, :alive?
  end

  def test_a_check_can_be_interrupted_from_another_thread
    worker = Thread.new { huge.check }
    sleep 0.2
    worker.kill
    assert_nil worker.join(3)&.value
    refute_predicate worker, :alive?
  end

  def now = Process.clock_gettime(Process::CLOCK_MONOTONIC)

  # 例外を伴わない割り込みを、0.1秒後に1回起こしながらブロックを実行する。
  # 子プロセスの終了（SIGCHLD）、Thread#wakeup、例外を投げずに戻るシグナルのトラップの3通り。
  def each_interrupt_without_exception
    caller = Thread.current
    pid = spawn("sleep 0.1")
    yield :sigchld
    Process.wait(pid)

    waker = Thread.new { sleep 0.1; caller.wakeup }
    yield :wakeup
    waker.join

    previous = trap("USR1") {}
    begin
      signaler = Thread.new { sleep 0.1; Process.kill("USR1", Process.pid) }
      yield :trap
      signaler.join
    ensure
      trap("USR1", previous)
    end
  end

  # 例外を伴わない割り込みでは、探索を打ち切った結果（:interrupted）を返さず、最初からやり直す。
  def test_an_interrupt_without_an_exception_does_not_stop_a_check
    each_interrupt_without_exception do |kind|
      started = now
      result = huge.check(max_time_ms: 600)
      assert_equal [:inconclusive, :max_time_ms], [result.status, result.reason], kind
      # 時間の上限は、やり直した探索でも最初の呼び出しからの時間である。
      assert_operator now - started, :>=, 0.55, kind
      assert_operator now - started, :<, 3.0, kind
    end
    # 時間の上限がなければ、やり直した探索が終わるまで続く。
    model = TestModels.counters(2, 299)
    each_interrupt_without_exception do |kind|
      assert_equal :verified, model.check.status, kind
    end
  end

  def test_an_interrupt_without_an_exception_does_not_stop_a_simulation_or_a_shrink
    each_interrupt_without_exception do |kind|
      result = huge.simulate(traces: 10**9, max_steps: 1000, seed: 1, max_time_ms: 400)
      assert_equal [:inconclusive, :max_time_ms], [result.status, result.reason], kind
    end
    model, trace = long_shrink
    each_interrupt_without_exception do |kind|
      result = model.shrink(trace, max_time_ms: 400)
      assert_equal "max_time_ms", result.shrink["limit"], kind
    end
  end

  def test_a_certificate_check_has_a_time_limit
    model, certificate = heavy_certificate
    started = now
    result = model.verify_certificate(certificate, max_time_ms: 100)
    assert_equal [:inconclusive, :max_time_ms], [result.status, result.reason]
    assert_operator now - started, :<, 3.0
    each_interrupt_without_exception do |kind|
      result = model.verify_certificate(certificate, max_time_ms: 400)
      assert_equal [:inconclusive, :max_time_ms], [result.status, result.reason], kind
    end
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
    assert_equal "rejected", JSON.parse(model.replay("{}", "{}"))["status"]
    assert_equal "usage_error", JSON.parse(model.replay("{}", '{"allow_other_model": 1}'))["status"]
    assert_equal "rejected", JSON.parse(model.verify_certificate("not json", "{}"))["status"]
    assert_raises(ArgumentError) { Fmspec::Native.format("not json") }
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
