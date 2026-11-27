# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"

# プロセスのクラッシュの自動生成（docs/crash_design.md）。ステップの境界でクラッシュする操作への展開。
class CrashTest < Minitest::Test
  # 決済してから注文を保存するジョブ。保存の前に落ちると、再試行で二重に決済する。
  def checkout(idempotent: false)
    # 冪等キーがあれば、決済サービスはすでに決済した注文を決済しない。
    charge = idempotent ? ->(s) { Fmspec.max(s.charges, 1) } : ->(s) { Fmspec.min(s.charges + 1, 2) }
    Fmspec.define(:checkout) do
      state :charges, int(0..2), initial: 0
      state :paid, bool, initial: false
      process :job, crash: :restart do
        step(:charge) { |s| update charges: charge.call(s) }
        step(:save) { |_s| update paid: true }
      end
      invariant(:charged_at_most_once) { |s| s.charges <= 1 }
    end
  end

  # 上のジョブを、クラッシュの操作を手で書いて定義したもの。
  def checkout_by_hand
    Fmspec.define(:checkout) do
      state :charges, int(0..2), initial: 0
      state :paid, bool, initial: false
      pc = enum(:"job.pc", :charge, :save, :done)
      state :"job[0].pc", pc, initial: :charge
      state :"job[0].crashes", int(0..1), initial: 0
      action :"job[0].charge" do |s|
        guard s.__send__(:"job[0].pc").eq(:charge)
        update charges: min(s.charges + 1, 2), "job[0].pc": :save
      end
      action :"job[0].save" do |s|
        guard s.__send__(:"job[0].pc").eq(:save)
        update paid: true, "job[0].pc": :done
      end
      action :"job[0].crash" do |s|
        guard all(s.__send__(:"job[0].pc").eq(:save), s.__send__(:"job[0].crashes") < 1)
        update "job[0].pc": :charge, "job[0].crashes": s.__send__(:"job[0].crashes") + 1
      end
      invariant(:charged_at_most_once) { |s| s.charges <= 1 }
      terminal { |s| s.__send__(:"job[0].pc").eq(:done) }
    end
  end

  # 2つのワーカーが、ロックを取ってから数える。接続が切れると、DBはロックを解放する（release_on_crash）。
  def workers(release_on_crash:)
    Fmspec.define(:workers) do
      state :holder, int(-1..1), initial: -1
      state :count, int(0..2), initial: 0
      process :worker, count: 2, crash: :abort do |id|
        step(:lock) do |s|
          guard s.holder.eq(-1)
          update holder: id
        end
        step(:work) { |s| update count: s.count + 1 }
        step(:unlock) { |_s| update holder: -1 }
        on_crash { |s| update holder: ite(s.holder.eq(id), -1, s.holder) } if release_on_crash
      end
    end
  end

  def strip_sources(node)
    case node
    when Hash then node.reject { |k, _| k == "source" }.transform_values { |v| strip_sources(v) }
    when Array then node.map { |v| strip_sources(v) }
    else node
    end
  end

  def test_a_restart_reruns_the_process_from_the_first_step
    result = checkout.check
    assert_equal :violated, result.status
    assert_equal "charged_at_most_once", result.property["name"]
    assert_equal %i[job[0].charge job[0].crash job[0].charge], result.trace.steps.map(&:action)
    assert checkout(idempotent: true).check(deadlock: true).verified?
    # クラッシュの操作を検査の対象から外せば、二重決済は起きない。
    assert checkout.check(actions: %w[job[0].charge job[0].save]).verified?
  end

  def test_the_expansion_is_the_same_as_writing_the_crash_by_hand
    assert_equal strip_sources(checkout_by_hand.to_ir), strip_sources(checkout.to_ir)
    assert_equal({ job: { count: 1, steps: %i[charge save], crash: :restart } }, checkout.processes)
  end

  def test_an_abort_ends_the_instance_and_on_crash_describes_the_environment
    # 接続が切れてもロックが残れば、もう一方のワーカーは進めない。
    stuck = workers(release_on_crash: false).check(deadlock: true)
    assert_equal :violated, stuck.status
    assert_equal %i[worker[0].lock worker[0].crash], stuck.trace.steps.map(&:action)
    assert workers(release_on_crash: true).check(deadlock: true).verified?

    ir = workers(release_on_crash: true).to_ir
    assert_equal({ "name" => "worker.pc", "variants" => %w[lock work unlock done crashed] }, ir["enums"].last)
    crash = ir["actions"].find { |a| a["name"] == "worker[0].crash" }
    # 最初のステップの前は、既定ではクラッシュの位置にしない。
    assert_equal({ "any" => %w[work unlock].map { |l| { "eq" => [{ "var" => 2 }, { "enum" => { "type" => "worker.pc", "variant" => l } }] } } },
                 crash["guard"])
    assert_includes crash["updates"], { "target" => 2, "expr" => { "enum" => { "type" => "worker.pc", "variant" => "crashed" } } }
    # 終端条件の既定は、すべてのインスタンスが終えたかクラッシュしたこと。
    assert_equal 2, ir["terminal"]["all"].length
    assert_equal "any", ir["terminal"]["all"][0].keys.first
  end

  def test_crashed_and_crashes_are_visible_from_the_state
    lost = Fmspec.define(:lost) do
      state :saved, bool, initial: false
      state :mailed, bool, initial: false
      process :request, crash: :abort do
        step(:save) { |_s| update saved: true }
        step(:enqueue) { |_s| update mailed: true }
      end
      invariant(:mailed_when_saved) { |s| s.request[0].crashed.not_ | s.saved.not_ | s.mailed }
    end
    assert_equal %i[request[0].save request[0].crash], lost.check.trace.steps.map(&:action)

    retried = Fmspec.define(:retried) do
      state :runs, int(0..3), initial: 0
      process :job, crash: :restart, max_crashes: 2, crash_at: %i[run] do
        step(:run) { |s| update runs: s.runs + 1 }
        step(:finish) { |_s| unchanged }
      end
      invariant(:runs_bounded) { |s| s.runs <= s.job[0].crashes + 1 }
    end
    assert retried.check(deadlock: true).verified?
    states = retried.to_ir["states"]
    assert_equal({ "int" => { "min" => 0, "max" => 2 } }, states.find { |s| s["name"] == "job[0].crashes" }["type"])
  end

  def test_restart_resets_ephemeral_locals_and_keeps_durable_ones
    model = Fmspec.define(:locals) do
      state :out, int(0..3), initial: 0
      process :job, crash: :restart do
        local :tmp, int(0..3), initial: 0
        local :arg, int(0..3), initial: 2, durable: true
        local :pick, int(0..3), initial_in: [1, 3]
        step(:load) { |s| update tmp: s.arg }
        step(:store) { |s| update out: s.tmp }
      end
    end
    crash = model.to_ir["actions"].find { |a| a["name"] == "job[0].crash" }
    targets = model.to_ir["states"].to_h { |s| [s["id"], s["name"]] }
    assert_equal %w[job[0].pc job[0].tmp job[0].pick job[0].crashes], crash["updates"].map { |u| targets[u["target"]] }
    # 初期値の候補が複数あるローカル変数は、同じ名前の内部選択で選び直す。
    assert_equal ["pick"], crash["choices"].map { |c| c["name"] }
    assert_equal :verified, model.check.status
  end

  def test_crash_options_are_validated
    define = lambda do |**options, &extra|
      Fmspec.define(:bad) do
        state :n, int(0..1), initial: 0
        process :p, **options do
          step(:a) { |_s| unchanged }
          step(:b) { |_s| unchanged }
          instance_exec(&extra) if extra
        end
      end
    end
    assert_raises(Fmspec::BuildError) { define.call(crash: :explode) }
    assert_raises(Fmspec::BuildError) { define.call(crash: :abort, crash_at: %i[c]) }
    assert_raises(Fmspec::BuildError) { define.call(crash: :abort, max_crashes: 2) }
    assert_raises(Fmspec::BuildError) { define.call(crash: :restart, max_crashes: 0) }
    assert_raises(Fmspec::BuildError) { define.call(crash_at: %i[b]) }
    assert_raises(Fmspec::BuildError) { define.call { on_crash { |_s| unchanged } } }
    assert_raises(Fmspec::BuildError) { define.call(crash: :abort) { on_crash { |_s| returns true } } }
    assert_raises(Fmspec::BuildError) { define.call(crash: :abort) { local :x, bool, initial: false, durable: true } }
    error = assert_raises(Fmspec::BuildError) do
      define.call(crash: :abort) do
        local :x, bool, initial: false
        on_crash { |_s| update x: true }
      end
    end
    assert_match(/ローカル変数 x は on_crash で更新できません/, error.message)
    assert_raises(Fmspec::BuildError) { define.call { step(:crash) { |_s| unchanged } } }
    assert_raises(Fmspec::BuildError) { define.call { local :crashes, bool, initial: false } }

    one_step = lambda do |**options|
      Fmspec.define(:one) do
        state :n, int(0..1), initial: 0
        process(:p, **options) { step(:a) { |_s| unchanged } }
      end
    end
    error = assert_raises(Fmspec::BuildError) { one_step.call(crash: :abort) }
    assert_match(/crash_at:/, error.message)
    assert one_step.call(crash: :abort, crash_at: %i[a]).check(deadlock: true).verified?

    error = assert_raises(Fmspec::BuildError) do
      Fmspec.define(:refs) do
        state :n, int(0..1), initial: 0
        process(:p, crash: :restart) do
          step(:a) { |_s| unchanged }
          step(:b) { |_s| unchanged }
        end
        invariant(:x) { |s| s.p[0].crashed }
      end
    end
    assert_match(/crash: :abort/, error.message)
  end

  def test_crashes_survive_composition_but_cannot_be_synchronized
    model = Fmspec.compose(:both, a: workers(release_on_crash: true))
    assert_includes model.to_ir["actions"].map { |a| a["name"] }, "a.worker[0].crash"
    assert_equal :abort, model.processes[:"a.worker"][:crash]
    assert_raises(Fmspec::BuildError) do
      Fmspec.compose(:bad, a: workers(release_on_crash: true), b: checkout) do
        sync :both, a: :"worker[0].crash", b: :"job[0].charge"
      end
    end
  end

  # 実装との適合性検査は、まだクラッシュの操作を結合できない。
  def test_binding_a_model_with_crashes_is_rejected
    error = assert_raises(Fmspec::BuildError) do
      checkout.bind do
        setup { Object.new }
        process(:job) do
          step(:charge) { |_job| nil }
          step(:save) { |_job| nil }
        end
      end
    end
    assert_match(/job\[0\]\.crash/, error.message)
  end

  def test_a_lost_job_is_found_by_bounded_response
    model = Fmspec.define(:mail) do
      state :saved, bool, initial: false
      state :mailed, bool, initial: false
      process :request, crash: :abort do
        step(:save) { |_s| update saved: true }
        step(:enqueue) { |_s| update mailed: true }
      end
      responds(:mail_sent, within: 2) do
        trigger { |s| s.saved }
        response { |s| s.mailed }
      end
    end
    result = model.check
    assert_equal :violated, result.status
    assert_equal "mail_sent", result.property["name"]
    assert_equal %i[request[0].save request[0].crash], result.trace.steps.map(&:action)
  end
end
