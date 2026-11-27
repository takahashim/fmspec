# frozen_string_literal: true

module Fmspec
  module Rails
    # ジョブの checkpoint が、仕様と食い違う（トランザクションの中にある、名前が仕様のステップにない）。
    class CheckpointError < Fmspec::Error; end

    # ステップを実行しようとしたが、キューに取り出すジョブがない。
    class JobNotEnqueued < Fmspec::Error; end

    # crash: :exception で、checkpoint から上げる例外の既定。retry_on で捕まえる。
    class InjectedFailure < StandardError; end

    # crash: :kill で、checkpoint から上げる例外。ワーカーのプロセスが止まったことを表す。
    # StandardError の子ではないので、rescue、retry_on、discard_on では捕まらない。ensure は実行される。
    class Killed < Exception # rubocop:disable Lint/InheritException
      def initialize(msg = "fmspec-rails がワーカーの停止を模して上げた例外です") = super
    end

    # ジョブの側の語彙（docs/rails_jobs_design.md §3）。ジョブのクラスに include する。
    #
    #   class ChargeJob < ApplicationJob
    #     include Fmspec::Rails::Checkpoints
    #
    #     def perform(order_id)
    #       PaymentGateway.client.charge(...)
    #       checkpoint :save
    #       Order.find(order_id).update!(status: :paid)
    #     end
    #   end
    #
    # fmspec-rails の Binding#job の外（本番、普通のテスト）では、checkpoint は何もしない。
    module Checkpoints
      def self.included(base)
        # perform の始め。最初のステップの前で落とせるように、ここでも止まる。
        base.before_perform { |job| JobRunner.current&.started(job) }
      end

      # ここから、仕様のステップ `step` が始まる。
      def checkpoint(step)
        JobRunner.current&.reached(self, step.to_sym)
        nil
      end
    end

    # 1つのインスタンスのジョブの実行器（docs/rails_jobs_design.md §5）。
    # 取り出したジョブの内容（payload）と、perform を実行する Fiber と、プログラムカウンタを持つ。
    # Context に1つずつ登録し、再起動したインスタンスのスレッドでも同じ実行器を使う。
    class JobRunner
      KEY = :fmspec_rails_job_runner

      attr_reader :pc

      # perform を実行している Fiber の実行器。Fiber ごとの値なので、Fiber の外では nil。
      def self.current = Thread.current[KEY]

      # steps は仕様のステップの名前の列、spec_crash は仕様の crash:（なければ nil）。
      def initialize(context:, name:, id:, job_class:, steps:, spec_crash:, crash:, error:, claim:)
        @context = context
        @name = name
        @id = id
        @job_class = job_class
        @steps = steps
        @spec_crash = spec_crash
        @crash = crash
        @error = error
        @claim = claim
        @pc = steps.first
        @payload = nil
        @job_id = nil
        @fiber = nil
      end

      # ---- インスタンスのスレッドから（Binding#job のハンドラ） ----

      # ステップを実行する。次の checkpoint で止まるか、perform が終わるまで進める。
      def step(_step)
        start unless @fiber
        settle(resume(nil), crashing: false)
      end

      # 止まっている位置で落とす（§6）。
      def crash
        start unless @fiber
        payload = @payload
        result = resume(@crash == :kill ? :kill : :raise)
        if @crash == :kill && result[0] == :killed
          finish_fiber
          if @spec_crash == :restart
            # 止まったワーカーのジョブを、別のワーカーが同じ内容で拾い直す。
            @context.redeliver(payload)
            @pc = @steps.first
          else
            @pc = :crashed
          end
          return nil
        end
        settle(result, crashing: true)
      end

      # テストケースの終わりに、止まったままの perform を巻き戻す。
      def unwind
        resume(:kill) if @fiber&.alive?
        finish_fiber
      end

      # ---- perform の中から（Checkpoints） ----

      def started(job)
        pause(job, [:start])
      end

      def reached(job, step)
        pause(job, [:at, step, in_transaction?])
      end

      private

      # 自分が取り出したジョブのときだけ止まる。perform の中で別のジョブを perform_now したときは止まらない。
      def pause(job, event)
        return unless job.job_id == @job_id

        case Fiber.yield(event)
        when :raise then raise @error, "fmspec-rails が #{@name}[#{@id}] のクラッシュとして上げた例外です"
        when :kill then raise Killed
        end
      end

      # キューからジョブを取り出し、perform を始める（before_perform で止まる）。
      def start
        @payload = @context.claim_job(@job_class, @job_id) { |payload| @claim.nil? || @claim.call(payload, @id) }
        unless @payload
          what = @job_id ? "再試行される #{@job_class.name}（job_id: #{@job_id}）" : @job_class.name
          raise JobNotEnqueued, "#{@name}[#{@id}]: キューに #{what} がありません"
        end

        @job_id = @payload["job_id"]
        payload = @payload
        runner = self
        @fiber = Fiber.new do
          Thread.current[KEY] = runner
          ActiveJob::Base.execute(Context.job_data(payload))
          [:finished]
        rescue Killed
          [:killed]
        rescue Exception => e # rubocop:disable Lint/RescueException
          [:raised, e]
        end
        result = @fiber.resume
        return if result == [:start]

        # Checkpoints を include していないジョブは、止まらずに終わる。
        finish_fiber
        raise CheckpointError, "#{@job_class.name} は Fmspec::Rails::Checkpoints を include していません" if result[0] == :finished

        raise result[1]
      end

      def resume(command) = @fiber.resume(command)

      # Fiber が止まった、または終わったあとのプログラムカウンタを決める。
      def settle(result, crashing:)
        case result[0]
        when :at
          _, step, in_transaction = result
          unless @steps.include?(step)
            raise CheckpointError, "#{@job_class.name} の checkpoint #{step.inspect} は、仕様のプロセス #{@name} のステップにありません"
          end
          if in_transaction
            raise CheckpointError, "#{@job_class.name} の checkpoint #{step.inspect} がトランザクションの中にあります。" \
                                   "仕様のステップはatomicなので、checkpoint はトランザクションの外に書きます"
          end

          @pc = step
        when :start
          @pc = @steps.first
        when :finished
          finish_fiber
          # 同じ job_id のジョブが積み直されていれば、再試行が予約された。
          @pc = if @context.enqueued?(@job_id) then @steps.first
                elsif crashing then :crashed
                else :done
                end
        when :raised
          finish_fiber
          raise result[1] unless crashing

          # 落とした例外が perform の外へ出た（retry_on の回数が尽きた）。
          @pc = :crashed
        when :killed
          finish_fiber
          @pc = :crashed
        end
        nil
      end

      def finish_fiber
        @fiber = nil
        @payload = nil
      end

      def in_transaction?
        ActiveRecord::Base.connection_handler.connection_pool_list.any? do |pool|
          connection = pool.active_connection?
          connection.respond_to?(:transaction_open?) && connection.transaction_open?
        end
      end
    end
  end
end
