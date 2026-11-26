# frozen_string_literal: true

# 2つのトランザクションが、同じ口座から1ずつ引き出す仕様（仕様書 §12.4）。
#
# 各トランザクションは、残高を読み（read）、読んだ値から1を引いて書き（write）、確定する（commit）。
# DBの分離レベルとロックは仕様の仮定で、ステップの guard と更新で書く。
#
#   :read_committed  各文は、確定済みの最新の値を読む。書いた行のロックは確定まで持つ。
#                    読んでから書くまでに他のトランザクションが確定しても、気付かずに上書きする
#   :snapshot        最初の文の時点のスナップショットを読む（PostgreSQL の REPEATABLE READ、SERIALIZABLE）。
#                    スナップショットより後に確定した変更のある行に書くと、直列化の失敗でロールバックする
#
# `row_locks: false` は、書いた行のロックを書き落とした誤った仕様である。
module WithdrawalSpec
  def self.define(isolation, row_locks: true)
    Fmspec.define(:"withdrawal_#{isolation}") do
      result = enum(:result, :ok, :conflict)
      # 確定済みの残高と、確定した書き込みの数（行の版）。
      state :balance, int(0..2), initial: 2
      state :version, int(0..2), initial: 0
      # 行のロックを持つトランザクション。-1 はなし。
      state :locker, int(-1..1), initial: -1
      # 確定した引き出しの数。
      ghost :withdrawn, int(0..2), initial: 0

      process :withdraw, count: 2 do |id|
        local :seen, int(0..2), initial: 0
        local :seen_version, int(0..2), initial: 0
        # 書いたが確定していない値。
        local :pending, int(0..2), initial: 0
        local :wrote, bool, initial: false

        step(:read) { |s| update seen: s.balance, seen_version: s.version }

        # 他のトランザクションがロックを持つ行への書き込みは、ロックが外れるまで待つ。
        free = row_locks ? ->(s) { s.locker.eq(-1) | s.locker.eq(id) } : ->(_s) { true }
        if isolation == :snapshot
          step(:write) do |s|
            guard free.call(s)
            conflict = s.version.ne(s.seen_version)
            accept_if conflict.not_
            on_accept do
              update locker: id, pending: s.seen - 1, wrote: true
              returns :ok, result
            end
            on_reject { returns :conflict, result }
            # 直列化の失敗で、トランザクションはロールバックして終わる。
            goto :done, conflict
          end
        else
          step(:write) do |s|
            guard free.call(s)
            update locker: id, pending: s.seen - 1, wrote: true
            returns :ok, result
          end
        end

        step(:commit) do |s|
          update balance: ite(s.wrote, s.pending, s.balance),
                 version: ite(s.wrote, s.version + 1, s.version),
                 withdrawn: ite(s.wrote, s.withdrawn + 1, s.withdrawn),
                 locker: -1
        end
      end

      # 確定した引き出しは、すべて残高に反映される（更新が失われない）。
      invariant(:no_lost_update) { |s| (s.balance + s.withdrawn).eq(2) }
    end
  end
end
