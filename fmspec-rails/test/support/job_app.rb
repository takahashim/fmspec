# frozen_string_literal: true

# Binding#job のテストの実装（docs/rails_jobs_design.md §8）。決済してから注文を保存するジョブ。
#
# ジョブはインスタンスのスレッドの接続で動くので、メモリ上の SQLite ではなく、ファイルの SQLite を使う。
# テスト用の Rails アプリケーション（CheckoutApp）とは別の接続プールを持つ。
require "tmpdir"

class JobRecord < ActiveRecord::Base
  self.abstract_class = true
end

class JobOrder < JobRecord
  def paid? = status == "paid"
end

module JobApp
  DATABASE = File.join(Dir.tmpdir, "fmspec_rails_job_test_#{Process.pid}.sqlite3")

  # 決済サービスの fake。冪等キーの付いた請求は、同じキーで2回目以降、新しい決済にならない。
  class Gateway
    attr_reader :charges

    def initialize
      @charges = []
      @keys = {}
      @lock = Mutex.new
    end

    def charge(order_id:, idempotency_key: nil)
      @lock.synchronize do
        next if idempotency_key && @keys[idempotency_key]

        @charges << order_id
        @keys[idempotency_key] = true if idempotency_key
      end
    end
  end

  class Timeout < StandardError; end

  class << self
    attr_accessor :gateway

    def connect
      File.delete(DATABASE) if File.exist?(DATABASE)
      JobRecord.establish_connection(adapter: "sqlite3", database: DATABASE, pool: 5, timeout: 1000)
      JobRecord.connection_pool.with_connection do |c|
        c.create_table(:job_orders, force: true) { |t| t.string :status, null: false, default: "pending" }
      end
      at_exit { File.delete(DATABASE) if File.exist?(DATABASE) }
    end

    # ジョブのクラスを作る。名前はキューに積むときに要るので、定数にする。
    #
    #   attempts        retry_on の attempts:
    #   idempotent      決済に冪等キーを渡すか
    #   transaction     誤り。checkpoint をトランザクションの中に書く
    #   checkpoints     誤り。false なら checkpoint を書き落とす
    def job_class(attempts: 3, idempotent: false, transaction: false, checkpoints: true)
      name = "ChargeJob_#{attempts}_#{idempotent}_#{transaction}_#{checkpoints}"
      return const_get(name) if const_defined?(name)

      job = Class.new(ActiveJob::Base) do
        include Fmspec::Rails::Checkpoints
        retry_on JobApp::Timeout, attempts: attempts

        define_method(:perform) do |order_id|
          order = JobOrder.find(order_id)
          JobApp.gateway.charge(order_id: order.id, idempotency_key: idempotent ? "order-#{order.id}" : nil)
          if transaction
            JobOrder.transaction do
              checkpoint :save
              order.update!(status: "paid")
            end
          else
            checkpoint :save if checkpoints
            order.update!(status: "paid")
          end
        end
      end
      const_set(name, job)
    end
  end
end

JobApp.connect
