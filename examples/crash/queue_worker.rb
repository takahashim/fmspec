# frozen_string_literal: true

# キューからメッセージを取り出して処理するワーカー（Sidekiq や Solid Queue のワーカーのループ）。
# 取り出したメッセージは、確認応答（ack）するまで消えない。ワーカーが落ちると、処理中のメッセージはキューに戻る。
#
# オプション
#   workers:      ワーカーの数
#   crash_at:     クラッシュしうる位置。既定は crash: の既定（最初のステップ fetch を除く）
#   max_crashes:  ワーカーごとのクラッシュの回数の上限
#   budget:       全体のクラッシュの回数の上限。on_crash の guard と共有の状態変数で書く。nil なら上限なし
#   lose_on_crash: 誤り。落ちたときに処理中のメッセージをキューに戻さない
module CrashExamples
  module QueueWorker
    MESSAGES = 2

    def self.define(workers: 2, crash_at: nil, max_crashes: 1, budget: nil, lose_on_crash: false)
      options = { crash: :restart, max_crashes: max_crashes }
      options[:crash_at] = crash_at if crash_at
      Fmspec.define(:queue_worker) do
        state :queue, int(0..MESSAGES), initial: MESSAGES
        # 確認応答したメッセージの数と、処理した回数（同じメッセージを2回処理すれば2と数える）。
        state :acked, int(0..MESSAGES), initial: 0
        state :handled, int(0..(2 * MESSAGES)), initial: 0
        state :faults, int(0..(budget || 0)), initial: 0

        process :worker, count: workers, **options do |_id|
          local :holding, bool, initial: false
          step(:fetch) do |s|
            guard s.queue > 0
            update queue: s.queue - 1, holding: true
          end
          step(:handle) { |s| update handled: min(s.handled + 1, 2 * MESSAGES) }
          step(:ack) do |s|
            update acked: s.acked + 1, holding: false
            goto :fetch
          end
          back = lose_on_crash ? ->(s) { s.queue } : ->(s) { ite(s.holding, s.queue + 1, s.queue) }
          if budget
            on_crash do |s|
              guard s.faults < budget
              update queue: back.call(s), faults: s.faults + 1
            end
          else
            on_crash { |s| update queue: back.call(s) }
          end
        end

        # メッセージは、キューにあるか、処理中か、確認応答済みである。
        invariant(:no_message_lost) do |s|
          holding = Array.new(workers) { |i| ite(s.worker[i].holding, 1, 0) }.reduce(:+)
          (s.queue + holding + s.acked).eq(MESSAGES)
        end
        # すべて確認応答し、どのワーカーも次のメッセージを待っている。
        terminal { |s| s.acked.eq(MESSAGES) & all(*Array.new(workers) { |i| s.worker[i].pc.eq(:fetch) }) }
      end
    end
  end
end
