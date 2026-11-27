# frozen_string_literal: true

require_relative "test_helper"

# テストケースの隔離（仕様書 §12、§17.2）。隔離に失敗した実行を、成功として扱わない。
class ContextTest < Minitest::Test
  # 注文を1件ずつ作る仕様。件数を観測する。
  Orders = Fmspec.define(:orders) do
    state :count, int(0..3), initial: 0
    action :create do |s|
      guard s.count < 3
      update count: s.count + 1
    end
  end

  class EchoJob < ActiveJob::Base
    retry_on ArgumentError, wait: 5.minutes, attempts: 3

    class << self
      attr_accessor :log
    end

    def perform(fail_times)
      self.class.log << executions
      raise ArgumentError, "again" if executions <= fail_times
    end
  end

  def teardown
    Order.delete_all
  end

  def binding(**options, &extra)
    Fmspec::Rails.bind(Orders, records: [Order], **options) do
      command(:create) { |_c| Order.create!(owner_id: 0) }
      observe(:count) { |_c| Order.count }
      instance_eval(&extra) if extra
    end
  end

  def test_a_transaction_isolates_each_case
    result = Orders.test(binding, cases: 20, steps: 3, seed: 1)
    assert_equal [:passed, 60], [result.status, result.matched_steps]
    assert_equal 0, Order.count
    assert_equal 0, ActiveRecord::Base.lease_connection.open_transactions
  end

  def test_deletion_isolates_each_case
    Order.create!(owner_id: 9)
    result = Orders.test(binding(isolation: :deletion), cases: 20, steps: 3, seed: 1)
    assert_equal :passed, result.status
    assert_equal 0, Order.count
  end

  def test_leaked_rows_are_a_setup_error
    result = Orders.test(binding(isolation: false), cases: 20, steps: 3, seed: 1)
    assert_equal :setup_error, result.status
    assert_instance_of Fmspec::Rails::IsolationError, result.exception
    assert_match(/Order の行数が 0 から \d に変わったまま残っています/, result.exception.message)
    assert_raises(Fmspec::TestFailed) { result.assert_passed! }
  end

  def test_an_unbalanced_transaction_is_a_setup_error
    leaky = binding do
      teardown { |_c| ActiveRecord::Base.lease_connection.begin_transaction(joinable: false) }
    end
    result = Orders.test(leaky, cases: 1, steps: 1, seed: 1)
    assert_equal :setup_error, result.status
    assert_match(/トランザクションの深さが合いません/, result.exception.message)
    # 余分に開いたトランザクションも、巻き戻してある。
    assert_equal 0, ActiveRecord::Base.lease_connection.open_transactions
    assert_equal 0, Order.count
  end

  def test_a_failing_setup_leaves_nothing_behind
    failing = binding do
      setup do |_c|
        Order.create!(owner_id: 0)
        raise "準備に失敗"
      end
    end
    result = Orders.test(failing, cases: 1, steps: 1, seed: 1)
    assert_equal [:setup_error, "準備に失敗"], [result.status, result.exception.message]
    assert_equal 0, Order.count
    assert_equal 0, ActiveRecord::Base.lease_connection.open_transactions
  end

  def test_time_is_frozen_within_a_case_and_restored_after
    times = []
    timed = binding do
      setup { |_c| times << Time.now.utc }
      teardown do |c|
        c.travel(1.hour)
        times << Time.now.utc
      end
    end
    before = Time.now
    Orders.test(timed, cases: 2, steps: 1, seed: 1).assert_passed!
    epoch = Fmspec::Rails::EPOCH
    assert_equal [epoch, epoch + 3600, epoch, epoch + 3600], times
    assert_in_delta before.to_f, Time.now.to_f, 5.0
  end

  def test_jobs_run_one_at_a_time_and_retries_return_to_the_queue
    log = EchoJob.log = []
    sizes = []
    jobs = binding do
      setup do |c|
        EchoJob.perform_later(2)
        sizes << c.enqueued_jobs.size
        3.times do
          c.perform_next_job
          sizes << c.enqueued_jobs.size
        end
        sizes << c.perform_next_job
      end
    end
    previous = ActiveJob::Base.queue_adapter
    Orders.test(jobs, cases: 1, steps: 0, seed: 1).assert_passed!
    # 2回失敗して再試行し、3回目で終わる。そのあとキューは空で、実行するジョブはない。
    assert_equal [1, 2, 3], log
    assert_equal [1, 1, 1, 0, nil], sizes
    assert_same previous, ActiveJob::Base.queue_adapter
  end

  def test_requests_need_an_application
    no_app = Fmspec::Rails.bind(Orders, records: [Order]) do
      command(:create) { |c| c.post("/orders") }
      observe(:count) { |_c| Order.count }
    end
    result = Orders.test(no_app, cases: 1, steps: 1, seed: 1)
    assert_equal :execution_error, result.status
    assert_match(/app: を渡します/, result.exception.message)
  end

  def test_options_are_checked
    assert_raises(ArgumentError) { binding(isolation: :truncate) }
    # Rails の binding でも、登録は仕様と照合する。
    error = assert_raises(Fmspec::BuildError) { Fmspec::Rails.bind(Orders, records: [Order]) { observe(:count) { 0 } } }
    assert_match(/command が登録されていない操作があります: create/, error.message)
  end

  Workers = Fmspec.define(:workers) do
    state :count, int(0..1), initial: 0
    process(:worker) { step(:create) { |s| update count: s.count + 1 } }
  end

  def test_processes_cannot_be_isolated_by_a_transaction
    bind = lambda do |isolation|
      Fmspec::Rails.bind(Workers, records: [Order], isolation: isolation) do
        process(:worker) { step(:create) { |_c| Order.create!(owner_id: 0) } }
        observe(:count) { |_c| Order.count }
      end
    end
    error = assert_raises(Fmspec::BuildError) { bind.call(:transaction) }
    assert_match(/isolation: :transaction では隔離できません/, error.message)
    # 複数の接続での実行は、PostgreSQL を使う isolation_test.rb で確かめる。
    assert_kind_of Fmspec::Binding, bind.call(:deletion)
  end
end
