# frozen_string_literal: true

require_relative "test_helper"
require_relative "support/withdrawal_app"

# crash: :kill で、ジョブの接続が切れ、DBがその接続のセッションのロックを解放すること（docs/rails_jobs_design.md §6.2）。
# PostgreSQL の advisory lock を使う。PostgreSQL に接続できなければ skip する。
class JobLockTest < Minitest::Test
  LOCK = 4242

  # advisory lock を取って作業し、解放するジョブ。解放は ensure で行う。
  class LockJob < ActiveJob::Base
    include Fmspec::Rails::Checkpoints

    def perform
      connection = PgRecord.lease_connection
      connection.select_value("SELECT pg_advisory_lock(#{LOCK})")
      begin
        checkpoint :work
        checkpoint :unlock
      ensure
        connection.select_value("SELECT pg_advisory_unlock(#{LOCK})")
      end
    end
  end

  # ワーカーが止まると、DBが接続のロックを解放する。仕様では on_crash に書く。
  MODEL = Fmspec.define(:lock_job) do
    state :held, bool, initial: false
    process :job, crash: :abort do
      step(:lock) { |_s| update held: true }
      step(:work) { |_s| unchanged }
      step(:unlock) { |_s| update held: false }
      on_crash { |_s| update held: false }
    end
  end

  def setup
    skip WithdrawalApp.unavailable unless WithdrawalApp.available?
    # 観測は、接続プールの外の専用の接続で行う。advisory lock は同じセッションなら何度でも取れるので、
    # ロックを持ったままプールに返された接続を引き当てると、ロックが空いているように見えてしまう。
    config = WithdrawalApp::CONFIG
    @observer = PG.connect(**{ dbname: config[:database], host: config[:host] }.compact)
  end

  def teardown
    @observer&.close
  end

  def binding_for(crash)
    # bind のブロックは Binding の中で評価するので、インスタンス変数はブロックの外で受け取る。
    observer = @observer
    Fmspec::Rails.bind(MODEL, records: [], isolation: :deletion, time: false) do
      job :job, LockJob, crash: crash, enqueue: ->(_c, _id) { LockJob.perform_later }
      # 別の接続から、ロックが空いているかを見る。
      observe(:held) do |_c|
        free = observer.exec("SELECT pg_try_advisory_lock(#{LOCK})").getvalue(0, 0) == "t"
        observer.exec("SELECT pg_advisory_unlock(#{LOCK})") if free
        !free
      end
    end
  end

  def test_a_killed_worker_releases_its_session_lock
    inputs = [[:"job[0].lock", {}], [:"job[0].crash", {}]]
    result = MODEL.test(binding_for(:kill), replay: inputs)
    assert_equal :passed, result.status, result.to_s
    assert_equal [true, false], result.steps.map { |s| s.observation[:held] }
    assert MODEL.test(binding_for(:kill), paths: true, steps: 4).passed?
  end
end
