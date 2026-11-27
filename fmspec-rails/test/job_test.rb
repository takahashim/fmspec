# frozen_string_literal: true

require_relative "test_helper"
require_relative "support/job_app"
require_relative "../../examples/crash/double_charge"

# Binding#job（docs/rails_jobs_design.md）。Active Job のジョブを、仕様のプロセスのインスタンスとして実行する。
class JobTest < Minitest::Test
  NAIVE = CrashExamples::DoubleCharge.define(:naive)
  IDEMPOTENT = CrashExamples::DoubleCharge.define(:idempotent)

  # 再試行の回数が実装の振る舞いである仕様。retry_on attempts: 3 は、再試行2回にあたる。
  def self.retrying(retries)
    Fmspec.define(:"retrying_#{retries}") do
      state :charges, int(0..3), initial: 0
      state :paid, bool, initial: false
      process :job, crash: :restart, retries: retries do
        step(:charge) { |s| update charges: min(s.charges + 1, 3) }
        step(:save) { |_s| update paid: true }
      end
    end
  end
  RETRYING = retrying(2)

  def teardown
    JobApp.gateway = nil
  end

  def binding_for(model, job_class, crash: :exception, error: JobApp::Timeout)
    Fmspec::Rails.bind(model, records: [JobOrder], isolation: :deletion, time: false) do
      setup do |c|
        c[:order] = JobOrder.create!
        c[:gateway] = JobApp.gateway = JobApp::Gateway.new
      end
      job :job, job_class, crash: crash, error: error, enqueue: ->(c, _id) { job_class.perform_later(c[:order].id) }
      # 決済の回数は、仕様の型の上限で飽和させる。
      cap = model.to_ir["states"].find { |s| s["name"] == "charges" }.dig("type", "int", "max")
      observe(:charges) { |c| [c[:gateway].charges.length, cap].min }
      observe(:paid) { |c| c[:order].reload.paid? }
    end
  end

  def actions(result) = result.steps.map(&:action)

  def test_a_crash_counterexample_is_reproduced_on_the_job
    trace = NAIVE.check.trace
    result = NAIVE.test(binding_for(NAIVE, JobApp.job_class), replay: trace)
    # 実装も、checkpoint :save で落ちたあとの再試行で、二重に決済する。
    assert_equal :model_violation, result.status, result.to_s
    assert_equal %i[job[0].charge job[0].crash job[0].charge], actions(result)
    assert_equal 2, result.steps.last.observation[:charges]
    assert_equal :save, result.steps.last.observation[:"job[0].pc"]
    assert_equal 0, JobOrder.count
  end

  def test_the_idempotent_job_conforms
    result = IDEMPOTENT.test(binding_for(IDEMPOTENT, JobApp.job_class(idempotent: true)), paths: true, steps: 6)
    assert_equal :passed, result.status, result.to_s
    assert_equal result.coverage.transitions.reachable, result.coverage.transitions.covered
    # 冪等キーを渡さないジョブは、再試行で仕様と違って二度目の決済をする。
    result = IDEMPOTENT.test(binding_for(IDEMPOTENT, JobApp.job_class), paths: true, steps: 6)
    assert_equal :conformance_failure, result.status, result.to_s
    assert_equal ["charges"], result.detail["mismatch"]
    assert_equal 0, JobOrder.count
  end

  def test_retry_on_attempts_are_checked_against_retries
    assert_equal :passed, RETRYING.test(binding_for(RETRYING, JobApp.job_class(attempts: 3)), paths: true, steps: 8).status
    # 再試行が仕様より少ない。2回目のクラッシュで、仕様はやり直し、実装はジョブを捨てる。
    fewer = RETRYING.test(binding_for(RETRYING, JobApp.job_class(attempts: 2)), paths: true, steps: 8)
    assert_equal :conformance_failure, fewer.status, fewer.to_s
    assert_equal ["job[0].pc"], fewer.detail["mismatch"]
    assert_equal :crashed, fewer.steps.last.observation[:"job[0].pc"]
    # 再試行が仕様より多い。3回目のクラッシュで、仕様はジョブを捨て、実装はやり直す。
    more = RETRYING.test(binding_for(RETRYING, JobApp.job_class(attempts: 4)), paths: true, steps: 8)
    assert_equal :conformance_failure, more.status, more.to_s
    assert_equal ["job[0].pc"], more.detail["mismatch"]
    assert_equal :charge, more.steps.last.observation[:"job[0].pc"]
  end

  def test_an_exception_retry_on_does_not_catch_is_a_crash_that_ends_the_job
    # retry_on が捕まえない例外で落とすと、ジョブは1回目で捨てられる。
    result = RETRYING.test(binding_for(RETRYING, JobApp.job_class, error: Fmspec::Rails::InjectedFailure),
                           replay: [[:"job[0].charge", {}], [:"job[0].crash", {}]])
    assert_equal :conformance_failure, result.status, result.to_s
    assert_equal :crashed, result.steps.last.observation[:"job[0].pc"]
  end

  def test_a_misplaced_checkpoint_is_detected
    in_transaction = NAIVE.test(binding_for(NAIVE, JobApp.job_class(transaction: true)), replay: [[:"job[0].charge", {}]])
    assert_equal :execution_error, in_transaction.status, in_transaction.to_s
    assert_kind_of Fmspec::Rails::CheckpointError, in_transaction.exception
    assert_match(/トランザクションの中/, in_transaction.exception.message)
    assert_equal 0, JobOrder.count

    missing = NAIVE.test(binding_for(NAIVE, JobApp.job_class(checkpoints: false)), replay: [[:"job[0].charge", {}]])
    assert_equal :conformance_failure, missing.status, missing.to_s
    assert_includes missing.detail["mismatch"], "job[0].pc"
    assert_equal :done, missing.steps.last.observation[:"job[0].pc"]
  end

  def test_a_killed_worker_redelivers_the_job_when_the_model_restarts
    result = NAIVE.test(binding_for(NAIVE, JobApp.job_class, crash: :kill), replay: NAIVE.check.trace)
    assert_equal :model_violation, result.status, result.to_s
    assert_equal 2, result.steps.last.observation[:charges]

    lost = Fmspec.define(:lost) do
      state :charges, int(0..2), initial: 0
      state :paid, bool, initial: false
      process :job, crash: :abort do
        step(:charge) { |s| update charges: min(s.charges + 1, 2) }
        step(:save) { |_s| update paid: true }
      end
    end
    killed = lost.test(binding_for(lost, JobApp.job_class, crash: :kill), paths: true, steps: 4)
    assert_equal :passed, killed.status, killed.to_s
    # :exception では、retry_on が積み直すので、ジョブは失われない。
    retried = lost.test(binding_for(lost, JobApp.job_class), replay: [[:"job[0].charge", {}], [:"job[0].crash", {}]])
    assert_equal :conformance_failure, retried.status, retried.to_s
    assert_equal :charge, retried.steps.last.observation[:"job[0].pc"]
  end

  def test_job_bindings_are_validated
    assert_raises(Fmspec::BuildError) do
      Fmspec::Rails.bind(NAIVE, records: [JobOrder], isolation: :deletion) { job :other, JobApp.job_class }
    end
    assert_raises(Fmspec::BuildError) do
      Fmspec::Rails.bind(NAIVE, records: [JobOrder], isolation: :deletion) { job :job, JobApp.job_class, crash: :explode }
    end
    assert_raises(Fmspec::BuildError) do
      Fmspec::Rails.bind(NAIVE, records: [JobOrder], isolation: :deletion) { job :job, String }
    end
    # job は process なので、:transaction では隔離できない。
    assert_raises(Fmspec::BuildError) { Fmspec::Rails.bind(NAIVE, records: [JobOrder]) { job :job, JobApp.job_class } }
  end

  # job に結合したクラスのジョブは、perform_next_job で実行しない。
  def test_perform_next_job_refuses_a_bound_job
    context = Fmspec::Rails::Context.new(app: nil, records: [JobOrder], isolation: :deletion, time: false,
                                         jobs: [JobApp.job_class])
    context.start
    begin
      JobApp.job_class.perform_later(1)
      assert_raises(Fmspec::Rails::IsolationError) { context.perform_next_job }
      assert_equal 1, context.enqueued_jobs.length
    ensure
      context.finish
    end
  end

  def test_a_missing_job_is_an_execution_error
    binding = Fmspec::Rails.bind(NAIVE, records: [JobOrder], isolation: :deletion, time: false) do
      setup { |c| c[:gateway] = JobApp.gateway = JobApp::Gateway.new }
      job :job, JobApp.job_class
    end
    result = NAIVE.test(binding, replay: [[:"job[0].charge", {}]])
    assert_equal :execution_error, result.status
    assert_kind_of Fmspec::Rails::JobNotEnqueued, result.exception
  end
end
