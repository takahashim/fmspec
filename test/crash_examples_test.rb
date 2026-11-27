# frozen_string_literal: true

require_relative "test_helper"
require "fmspec"
Dir[File.expand_path("../examples/crash/*.rb", __dir__)].each { |f| require f }

# examples/crash の例。設計の未決事項（docs/crash_design.md §9）を決めるのに使った結果を、回帰テストとして持つ。
class CrashExamplesTest < Minitest::Test
  def actions(result) = result.trace.steps.map(&:action)

  # 再試行は最初のステップからやり直す。支払い済みを見て飛ばしても、二重決済は防げない。
  def test_double_charge
    define = CrashExamples::DoubleCharge.method(:define)
    naive = define.call(:naive).check(deadlock: true)
    assert_equal %i[job[0].charge job[0].crash job[0].charge], actions(naive)
    check_paid = define.call(:check_paid).check(deadlock: true)
    assert_equal %i[job[0].check job[0].charge job[0].crash job[0].check job[0].charge], actions(check_paid)
    assert define.call(:idempotent).check(deadlock: true).verified?
  end

  # max_crashes: は環境の仮定、retries: は実装の振る舞い。前者では、捨てられたジョブの不具合が見えない。
  def test_discarded_job
    define = CrashExamples::DiscardedJob.method(:define)
    assert define.call(:bounded_faults).check(deadlock: true).verified?
    retries = define.call(:retries).check(deadlock: true)
    assert_equal "settled", retries.property["name"]
    assert_equal %i[job[0].crash job[0].crash job[0].crash], actions(retries)
    assert define.call(:after_discard).check(deadlock: true).verified?
  end

  def test_outbox
    define = CrashExamples::Outbox.method(:define)
    lost = define.call(:enqueue_after_save).check(deadlock: true)
    assert_equal "mail_sent", lost.property["name"]
    assert_equal %i[request[0].save request[0].crash], actions(lost)
    twice = define.call(:outbox).check(deadlock: true)
    assert_equal "at_most_one_mail", twice.property["name"]
    assert_equal %i[request[0].save relay[0].poll relay[0].deliver relay[0].crash relay[0].poll relay[0].deliver],
                 actions(twice)
    assert define.call(:dedup).check(deadlock: true).verified?
  end

  def test_queue_worker
    define = CrashExamples::QueueWorker.method(:define)
    default = define.call.check(deadlock: true)
    assert default.verified?
    # ループの先頭（fetch）でのクラッシュは、ローカル変数がすでに初期値なので、回数を使うだけで新しい振る舞いを生まない。
    with_fetch = define.call(crash_at: %i[fetch handle ack]).check(deadlock: true)
    assert with_fetch.verified?
    assert_equal default.visited_states, with_fetch.visited_states

    lost = define.call(lose_on_crash: true).check(deadlock: true)
    assert_equal %i[worker[0].fetch worker[0].crash], actions(lost)

    # 全体の回数の上限は、on_crash の guard と共有の状態変数で書ける。ワーカーごとの上限より状態が少ない。
    states = {
      per_worker1: define.call.check.visited_states,
      per_worker2: define.call(max_crashes: 2).check.visited_states,
      total1: define.call(max_crashes: 2, budget: 1).check.visited_states,
      three_per_worker1: define.call(workers: 3).check.visited_states,
      three_total1: define.call(workers: 3, budget: 1).check.visited_states
    }
    assert_equal({ per_worker1: 120, per_worker2: 382, total1: 75, three_per_worker1: 533, three_total1: 189 }, states)
  end
end
