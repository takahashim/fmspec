# frozen_string_literal: true

module Fmspec
  # 並行するプロセスの実装を、スケジュールを固定して実行する（仕様書 §12.4）。`TestCase` が1ケースごとに作る。
  #
  # プロセスのインスタンスごとに専用のスレッドを立て、そのスレッドで process の setup、各ステップ、teardown を実行する。
  # テストは、選んだステップを対応するスレッドに渡し、そのステップが終わるまで待つ。
  # 他のスレッドは次のステップを待って止まっているので、実装のステップは、テストが選んだ順に1つずつ実行される。
  #
  # ステップが `timeout` 秒以内に終わらなければ、スケジュールを再現できなかったとして StepTimeout を raise する。
  # 実装のロックで待たされたステップが典型である。これはスケジュールを固定した検査であり、
  # スレッドを自由に走らせるストレステストではない。
  class Scheduler
    # ステップが時間内に終わらなかった。
    class StepTimeout < StandardError
      attr_reader :action

      def initialize(action, timeout)
        @action = action
        super("ステップ #{action} が #{timeout} 秒以内に終わりませんでした")
      end
    end

    # 1つのインスタンスのスレッド。
    class Worker
      def initialize(spec, context, id)
        @spec = spec
        @jobs = Thread::Queue.new
        @results = Thread::Queue.new
        @stuck = false
        @thread = Thread.new { serve(context, id) }
        @thread.report_on_exception = false
      end

      # スレッドの setup が終わるまで待つ。
      def start = wait("#{@spec.name} の setup")

      # ステップが時間内に終わらず、まだ実行中かもしれない。
      def stuck? = @stuck

      # スレッドでブロックを実行し、終わるまで待つ。ブロックは process の setup が返したコンテキストを受け取る。
      def call(action, &job)
        @jobs << job
        wait(action)
      end

      # teardown を実行してスレッドを終える。時間内に終わらなければスレッドを止める。teardown の例外を返す。
      def stop
        @jobs << nil
        return @error if @thread.join(@spec.timeout)

        @thread.kill
        @thread.join(@spec.timeout)
        @error
      end

      private

      def wait(action)
        status, value = @results.pop(timeout: @spec.timeout)
        unless status
          @stuck = true
          raise StepTimeout.new(action, @spec.timeout)
        end
        raise value if status == :error

        value
      end

      def serve(context, id)
        begin
          local = @spec.setup ? @spec.setup.call(context, id) : context
        rescue StandardError => e
          @results << [:error, e]
          return
        end
        begin
          @results << [:ok, nil]
          while (job = @jobs.pop)
            @results << begin
              [:ok, job.call(local)]
            rescue StandardError => e
              [:error, e]
            end
          end
        ensure
          finish(local)
        end
      end

      def finish(local)
        @spec.teardown&.call(local)
      rescue StandardError => e
        @error = e
      end
    end

    # インスタンスごとにスレッドを立てる。各スレッドは、すぐに process の setup を実行する。
    def initialize(binding, context)
      @workers = {}
      binding.processes.each do |name, spec|
        binding.model.processes.fetch(name)[:count].times do |id|
          @workers[[name, id]] = Worker.new(spec, context, id)
        end
      end
    end

    # すべてのスレッドの setup が終わるまで待つ。setup の例外か StepTimeout を raise する。
    def start = @workers.each_value(&:start)

    # ステップを、そのインスタンスのスレッドで実行する。
    def run(handler, args)
      @workers.fetch(handler.worker).call(handler.name) { |local| handler.callable.call(local, **args) }
    end

    # すべてのスレッドを終える。最初の teardown の例外を返す。
    # 時間内に終わらなかったステップを持つスレッドは、他のスレッドの teardown がロックを解放すれば終わることがあるので、最後に終える。
    def stop
      stuck, others = @workers.values.partition(&:stuck?)
      (others + stuck).map(&:stop).compact.first
    end
  end
end
