# frozen_string_literal: true

require "fmspec"
require "active_record"
require "active_job"
require "active_support/testing/time_helpers"
require "action_controller"
require "action_dispatch"
require "action_dispatch/testing/integration"
require_relative "rails/job"

module Fmspec
  # Rails アプリケーションとの結合（仕様書 §12）。
  #
  #   binding = Fmspec::Rails.bind(Checkout, app: MyApp::Application, records: [Order, Fulfillment]) do
  #     setup { |c| c[:order] = Order.create!(owner_id: 0) }
  #     command(:checkout) { |c| c.post("/orders/#{c[:order].id}/checkout") }
  #     command(:run_job, inject: [:response]) do |c, response:|
  #       FakeGateway.current.next_response = response
  #       c.perform_next_job
  #     end
  #     observe(:status) { |c| c[:order].reload.status.to_sym }
  #     observe(:queued) { |c| c.enqueued_jobs.any? }
  #   end
  #
  # 各テストケースは新しい Context で実行する。Context は、DBの変更、Active Job のキュー、時刻を
  # ケースの中に閉じ込め、ケースの終わりに元へ戻す。戻せなかった場合は例外を上げるので、
  # 隔離に失敗したテスト実行が成功として扱われることはない。
  module Rails
    # 隔離に失敗した。ケースの終わりに、DBの行やトランザクションが残っている。
    class IsolationError < Fmspec::Error; end

    # テストケースの時刻の既定値。
    EPOCH = Time.utc(2026, 1, 1).freeze

    # 仕様と Rails アプリケーションを結合する。ブロックの語彙は Fmspec::Binding と同じで、
    # setup、teardown、command、observe のブロックは Context を受け取る。
    #
    #   app        Rack アプリケーション。Context#get や #post の送り先
    #   records    隔離を検査する Active Record のクラス。ケースの前後で行数が変わっていれば失敗にする
    #   isolation  :transaction（既定。ケースをトランザクションで包み、終わりにロールバックする）、
    #              :deletion（ケースの前後に records の行をすべて削除する）、false（何もしない）
    #   time       ケースの開始時刻。false なら時刻を固定しない
    def self.bind(model, app: nil, records: [], isolation: :transaction, time: EPOCH, &block)
      unless Context::ISOLATIONS.include?(isolation)
        raise ArgumentError, "isolation は :transaction、:deletion、false のいずれかです: #{isolation.inspect}"
      end

      Binding.new(model, app: app, records: records, isolation: isolation, time: time, &block)
    end

    # Binding#job の crash: の値。
    JOB_CRASHES = %i[exception kill].freeze

    # 1つのテストケースの実行環境。command と observe のブロックに渡る。
    class Context
      include ActiveSupport::Testing::TimeHelpers

      ISOLATIONS = [:transaction, :deletion, false].freeze

      # jobs は、Binding#job に結合したジョブのクラス。perform_next_job では実行しない。
      def initialize(app:, records:, isolation:, time:, jobs: [])
        @app = app
        @records = records
        @isolation = isolation
        @time = time
        @jobs = jobs
        @values = {}
        @session = nil
        @started = false
        @runners = {}
        @claimed = {}
        @lock = Mutex.new
      end

      # ケースの中で使う値の置き場。setup で作ったレコードや fake を入れる。
      def [](key) = @values.fetch(key)

      def []=(key, value)
        @values[key] = value
      end

      # ---- リクエスト ----

      %i[get post put patch delete].each do |verb|
        define_method(verb) do |path, **options|
          session.public_send(verb, path, **options)
          session.response
        end
      end

      # 直前のリクエストのレスポンス。
      def response = session.response

      # ---- Active Job ----

      # キューにあるジョブ。キューに入った順に並ぶ。
      def enqueued_jobs = adapter.enqueued_jobs

      # キューの先頭のジョブを1つ実行する。ジョブが再試行を予約すれば、そのジョブはキューに戻る。
      # ジョブがなければ nil を返す。ジョブが処理しなかった例外は、そのまま上がる。
      def perform_next_job
        payload = adapter.enqueued_jobs.first
        return nil unless payload
        if @jobs.any? { |job| job.name == payload["job_class"] }
          raise IsolationError, "#{payload['job_class']} は Binding#job に結合しているので、perform_next_job では実行しません"
        end

        adapter.enqueued_jobs.shift
        ActiveJob::Base.execute(Context.job_data(payload))
        true
      end

      # ActiveJob::Base.execute に渡す形にする。
      def self.job_data(payload) = payload.transform_keys(&:to_s).slice(*JOB_KEYS)

      # ---- Binding#job の実行器（Fmspec::Rails::JobRunner）が使う ----

      # インスタンスの実行器。なければ、ブロックで作る。
      def job_runner(name, id, &create)
        @lock.synchronize { @runners[[name, id]] ||= create&.call }
      end

      # キューからジョブを取り出す。job_id を渡せば、そのジョブ（再試行で積み直されたもの）を取り出す。
      # 渡さなければ、そのクラスのジョブのうち、まだ取り出していないもので、ブロックが真になる最初のもの。
      def claim_job(job_class, job_id, &accept)
        @lock.synchronize do
          jobs = adapter.enqueued_jobs
          index = jobs.index do |payload|
            if job_id
              payload["job_id"] == job_id
            else
              payload["job_class"] == job_class.name && !@claimed.key?(payload["job_id"]) && accept.call(payload)
            end
          end
          next nil unless index

          jobs.delete_at(index).tap { |payload| @claimed[payload["job_id"]] = true }
        end
      end

      # キューに、その job_id のジョブがあるか。
      def enqueued?(job_id) = @lock.synchronize { adapter.enqueued_jobs.any? { |payload| payload["job_id"] == job_id } }

      # 取り出したジョブを、同じ内容でキューに戻す。
      def redeliver(payload)
        @lock.synchronize { adapter.enqueued_jobs << payload }
      end

      # ---- ケースの開始と終了（Binding が呼ぶ） ----

      def start
        # :deletion は、ケースの前にあった行も削除する。行数の基準は、削除したあとに取る。
        delete_records if @isolation == :deletion
        @baseline = counts
        @previous_adapter = ActiveJob::Base.queue_adapter
        ActiveJob::Base.queue_adapter = ActiveJob::QueueAdapters::TestAdapter.new
        travel_to(@time) if @time
        case @isolation
        when :transaction
          @connection = ActiveRecord::Base.lease_connection
          @open_transactions = @connection.open_transactions
          @connection.begin_transaction(joinable: false)
        end
        @started = true
      end

      # 変更を元へ戻し、戻ったことを確かめる。
      def finish
        return unless @started

        @started = false
        problems = []
        case @isolation
        when :transaction
          extra = @connection.open_transactions - @open_transactions
          problems << "トランザクションの深さが合いません（開始時より #{extra - 1} 段ずれています）" unless extra == 1
          @connection.rollback_transaction while @connection.open_transactions > @open_transactions
        when :deletion then delete_records
        end
        travel_back if @time
        ActiveJob::Base.queue_adapter = @previous_adapter
        leaked = counts.reject { |name, count| @baseline[name] == count }
        leaked.each { |name, count| problems << "#{name} の行数が #{@baseline[name]} から #{count} に変わったまま残っています" }
        raise IsolationError, "テストケースの隔離に失敗しました: #{problems.join('、')}" unless problems.empty?
      end

      private

      JOB_KEYS = %w[job_class job_id provider_job_id queue_name priority arguments executions exception_executions
                    locale timezone enqueued_at scheduled_at].freeze

      def session
        raise ArgumentError, "リクエストを送るには、Fmspec::Rails.bind に app: を渡します" unless @app

        @session ||= ActionDispatch::Integration::Session.new(@app)
      end

      def adapter
        adapter = ActiveJob::Base.queue_adapter
        return adapter if adapter.is_a?(ActiveJob::QueueAdapters::TestAdapter)

        raise IsolationError, "Active Job のアダプターが、テストケースの途中で差し替えられました"
      end

      def counts = @records.to_h { |record| [record.name, record.unscoped.count] }

      def delete_records = @records.reverse_each { |record| record.unscoped.delete_all }
    end

    # Rails アプリケーションとの結合。setup と teardown を、Context の開始と終了で包む。
    class Binding < Fmspec::Binding
      def initialize(model, app:, records:, isolation:, time:, &block)
        @context_options = { app: app, records: records, isolation: isolation, time: time }
        @user_setup = nil
        super(model, &block)
      end

      # setup のブロックは Context を受け取る。省略できる。
      def setup(&block)
        raise BuildError, "setup にはブロックが必要です" unless block
        raise BuildError, "setup は1つだけ書けます" if @user_setup

        @user_setup = block
      end

      # 仕様のプロセスを、Active Job のジョブに結合する（docs/rails_jobs_design.md §4）。
      # ジョブは Fmspec::Rails::Checkpoints を include し、perform の中の checkpoint でステップの境界を示す。
      #
      #   crash    :exception（既定。checkpoint から error: の例外を上げ、retry_on に処理させる）か
      #            :kill（ワーカーの停止。retry_on を通らず、仕様が :restart ならジョブを同じ内容でキューに戻す）
      #   error    crash: :exception で上げる例外のクラス。既定は Fmspec::Rails::InjectedFailure
      #   claim    ->(payload, id) { ... }。インスタンスが取り出すジョブを選ぶ。既定は、そのクラスの最初のジョブ
      #   enqueue  ->(context, id) { ... }。インスタンスの最初の setup で、ジョブを積む
      #
      # プロセスの setup、各ステップ、crash と、プログラムカウンタ `プロセス[i].pc` の observe を組み立てる。
      def job(name, job_class, crash: :exception, error: InjectedFailure, claim: nil, enqueue: nil, timeout: DEFAULT_TIMEOUT)
        name = name.to_sym
        declared = model.processes[name]
        raise BuildError, "仕様にないプロセスです: #{name}" unless declared
        raise BuildError, "job #{name} のジョブのクラスは ActiveJob::Base の子です: #{job_class.inspect}" unless job_class.is_a?(Class) && job_class <= ActiveJob::Base
        raise BuildError, "job #{name} の crash: は :exception か :kill です: #{crash.inspect}" unless JOB_CRASHES.include?(crash)
        raise BuildError, "job #{name} の error: は例外のクラスです: #{error.inspect}" unless error.is_a?(Class) && error <= Exception

        steps = declared[:steps]
        spec_crash = declared[:crash]
        runner = lambda do |c, id|
          c.job_runner(name, id) do
            enqueue&.call(c, id)
            JobRunner.new(context: c, name: name, id: id, job_class: job_class, steps: steps, spec_crash: spec_crash,
                          crash: crash, error: error, claim: claim)
          end
        end
        @context_options[:jobs] = [*@context_options[:jobs], job_class]
        process(name, timeout: timeout) do
          setup { |c, id| runner.call(c, id) }
          teardown(&:unwind)
          steps.each { |label| step(label) { |r| r.step(label) } }
          crash(&:crash) if spec_crash
        end
        declared[:count].times do |id|
          observe(:"#{name}[#{id}].pc") { |c| runner.call(c, id).pc }
        end
        nil
      end

      def setup_block
        options = @context_options
        user_setup = @user_setup
        lambda do
          context = Context.new(**options)
          context.start
          begin
            user_setup&.call(context)
          rescue StandardError
            context.finish
            raise
          end
          context
        end
      end

      def teardown_block
        user_teardown = super
        lambda do |context|
          user_teardown&.call(context)
        ensure
          context.finish
        end
      end

      private

      # プロセスは、それぞれ別のスレッドと接続で動く。テストのスレッドの接続のトランザクションでは、
      # プロセスの接続での変更は戻らないので、:transaction では隔離できない（仕様書 §12.4）。
      def validate!
        super
        return if processes.empty? || @context_options[:isolation] != :transaction

        raise BuildError, "process を使う binding は、isolation: :transaction では隔離できません。" \
                          ":deletion と専用のデータ、または専用のDBを使います"
      end

      # setup は Context の開始で代えられるので、省略を許す。
      def setup_required? = false
    end
  end
end
