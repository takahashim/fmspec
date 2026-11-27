# frozen_string_literal: true

# 分離レベル別のテストの実装。PostgreSQL の口座から、トランザクションごとに1ずつ引き出す。
#
# 接続先は環境変数 FMSPEC_PG_DATABASE（既定は fmspec_rails_test）と FMSPEC_PG_HOST で決める。
# データベースがなければ作る。PostgreSQL に接続できなければ、WithdrawalApp.available? は偽になる。
require "pg"

# PostgreSQL の接続。テスト用の Rails アプリケーション（SQLite）とは別の接続プールを持つ。
class PgRecord < ActiveRecord::Base
  self.abstract_class = true
end

class Account < PgRecord; end

module WithdrawalApp
  CONFIG = {
    adapter: "postgresql",
    database: ENV.fetch("FMSPEC_PG_DATABASE", "fmspec_rails_test"),
    host: ENV.fetch("FMSPEC_PG_HOST", nil),
    pool: 5
  }.compact.freeze

  class << self
    # 接続できなかった理由。接続できれば nil。
    attr_reader :unavailable

    def available? = @unavailable.nil?

    def connect
      create_database
      PgRecord.establish_connection(CONFIG)
      PgRecord.connection_pool.with_connection do |c|
        c.create_table(:accounts, force: true) { |t| t.integer :balance, null: false }
      end
      @unavailable = nil
    rescue PG::Error, ActiveRecord::ActiveRecordError => e
      @unavailable = "PostgreSQL に接続できません（#{e.class}: #{e.message.lines.first&.strip}）"
    end

    private

    def create_database
      admin = PG.connect(**{ dbname: "postgres", host: CONFIG[:host] }.compact)
      exists = admin.exec_params("SELECT 1 FROM pg_database WHERE datname = $1", [CONFIG[:database]]).ntuples.positive?
      admin.exec("CREATE DATABASE #{admin.quote_ident(CONFIG[:database])}") unless exists
    ensure
      admin&.close
    end
  end

  # 1つのトランザクションで引き出す。接続は、作ったスレッドが持つ。
  # read は残高を読み、write は読んだ値から1を引いて書き、commit で確定する。
  class Teller
    def initialize(account_id, isolation)
      @id = Integer(account_id)
      @isolation = isolation
      @connection = PgRecord.connection_pool.checkout
    end

    def read
      @connection.execute("BEGIN TRANSACTION ISOLATION LEVEL #{@isolation}")
      @seen = Integer(@connection.select_value("SELECT balance FROM accounts WHERE id = #{@id}"))
    end

    # 直列化の失敗（SQLSTATE 40001）なら、ロールバックして :conflict を返す。
    def write
      @connection.execute("UPDATE accounts SET balance = #{@seen - 1} WHERE id = #{@id}")
      :ok
    rescue ActiveRecord::SerializationFailure
      @connection.execute("ROLLBACK")
      :conflict
    end

    def commit = @connection.execute("COMMIT")

    # 確定していないトランザクションを捨て、接続を返す。
    def close
      @connection.execute("ROLLBACK") if @connection.transaction_open? || in_transaction?
    ensure
      PgRecord.connection_pool.checkin(@connection)
    end

    private

    def in_transaction? = @connection.raw_connection.transaction_status != PG::PQTRANS_IDLE
  end
end

WithdrawalApp.connect
