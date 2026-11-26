# frozen_string_literal: true

require_relative "test_helper"
require_relative "support/withdrawal_spec"
require_relative "support/withdrawal_app"

# 分離レベル別のテスト（仕様書 §12.4、§16 段階7）。
#
# 同じ引き出しの実装を、PostgreSQL の分離レベルを変えて動かし、分離レベルごとの仕様と照合する。
# 各トランザクションは、専用のスレッドと接続で動く。ステップはテストが選んだ順に1つずつ実行する。
class IsolationTest < Minitest::Test
  READ_COMMITTED = WithdrawalSpec.define(:read_committed)
  SNAPSHOT = WithdrawalSpec.define(:snapshot)

  def setup
    skip WithdrawalApp.unavailable unless WithdrawalApp.available?
  end

  def binding(model, isolation, timeout: 2)
    Fmspec::Rails.bind(model, records: [Account], isolation: :deletion, time: false) do
      setup { |c| c[:account] = Account.create!(balance: 2) }
      process :withdraw, timeout: timeout do
        setup { |c, _id| WithdrawalApp::Teller.new(c[:account].id, isolation) }
        teardown(&:close)
        step(:read, method: :read)
        step(:write, method: :write)
        step(:commit, method: :commit)
      end
      # 確定済みの残高。テストのスレッドの接続から読む。
      observe(:balance) { |c| c[:account].reload.balance }
    end
  end

  def test_read_committed_conforms_to_its_model
    result = READ_COMMITTED.test(binding(READ_COMMITTED, "READ COMMITTED"), paths: true, steps: 6)
    assert_equal :model_violation, result.status, result.to_s
    # 経路の1つが、更新の消失に至る。実装も仕様のとおりに更新を失い、適合している。
    assert_equal "no_lost_update", result.detail.dig("property", "name")
  end

  def test_the_lost_update_schedule_is_reproduced_under_read_committed
    trace = READ_COMMITTED.check.trace
    result = READ_COMMITTED.test(binding(READ_COMMITTED, "READ COMMITTED"), replay: trace)
    assert_equal :model_violation, result.status, result.to_s
    assert_equal 6, result.matched_steps
    assert_equal 1, result.steps.last.observation[:balance]
    assert_equal 0, Account.count
  end

  def test_snapshot_levels_conform_to_the_snapshot_model
    assert SNAPSHOT.check(deadlock: true).verified?
    ["REPEATABLE READ", "SERIALIZABLE"].each do |isolation|
      result = SNAPSHOT.test(binding(SNAPSHOT, isolation), paths: true, steps: 6)
      assert_equal :passed, result.status, "#{isolation}\n#{result}"
      # 直列化の失敗を含む経路も、実装で再現した。
      assert_equal result.coverage.transitions.reachable, result.coverage.transitions.covered, isolation
    end
  end

  def test_a_model_of_the_wrong_isolation_level_does_not_conform
    # READ COMMITTED の実装は、スナップショットの仕様が直列化の失敗を求めるところで書き込みに成功する。
    result = SNAPSHOT.test(binding(SNAPSHOT, "READ COMMITTED"), paths: true, steps: 6)
    assert_equal :conformance_failure, result.status, result.to_s
    assert_equal ["output"], result.detail["mismatch"]
    assert_equal :"withdraw[1].write", result.steps.last.action
    assert_equal :ok, result.steps.last.output

    # REPEATABLE READ の実装は、READ COMMITTED の仕様が成功を求めるところで直列化に失敗する。
    result = READ_COMMITTED.test(binding(READ_COMMITTED, "REPEATABLE READ"), paths: true, steps: 6)
    assert_equal :conformance_failure, result.status, result.to_s
    assert_equal :conflict, result.steps.last.output
  end

  def test_a_schedule_blocked_by_a_row_lock_is_inconclusive
    # 行のロックを書き落とした仕様は、ロックで待たされる書き込みを含むスケジュールを許す。
    model = WithdrawalSpec.define(:read_committed, row_locks: false)
    schedule = %i[withdraw[0].read withdraw[1].read withdraw[0].write withdraw[1].write].map { |a| [a, {}] }
    result = model.test(binding(model, "READ COMMITTED", timeout: 0.5), replay: schedule)
    assert_equal :inconclusive, result.status, result.to_s
    assert_equal :step_timeout, result.reason
    assert_equal :"withdraw[1].write", result.steps.last.action
    # 待たされていた書き込みも、ロックを持つトランザクションのロールバックのあとで終わり、行は残らない。
    assert_equal 0, Account.count
    assert_equal 0, PgRecord.connection_pool.stat[:busy]
  end
end
