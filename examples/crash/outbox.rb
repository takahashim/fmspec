# frozen_string_literal: true

# 注文を保存してから、確認メールのジョブを積むリクエスト。
#
#   :enqueue_after_save  保存してからジョブを積む。その間でリクエストが落ちると、メールが送られない
#   :outbox              注文とOutboxの行を1つのトランザクションで保存し、別のリレーがOutboxを読んでメールを送る。
#                        リレーは送ってから行を消すので、その間で落ちると、再起動したリレーがもう一度送る
#   :dedup               :outbox に加え、メールサービスが同じ注文のメールを2回送らない（冪等キー）
#
# リクエストは再試行しない（crash: :abort）。リレーは落ちても再起動する（crash: :restart）。
module CrashExamples
  module Outbox
    VARIANTS = %i[enqueue_after_save outbox dedup].freeze

    def self.define(variant)
      raise ArgumentError, "unknown variant: #{variant}" unless VARIANTS.include?(variant)

      Fmspec.define(:"outbox_#{variant}") do
        state :saved, bool, initial: false
        state :outbox, bool, initial: false
        # メールサービスが送ったメールの数。
        state :mails, int(0..2), initial: 0

        if variant == :enqueue_after_save
          process :request, crash: :abort do
            step(:save) { |_s| update saved: true }
            step(:enqueue) { |_s| update outbox: true }
          end
        else
          # 1つのトランザクションなので、1つのステップである。ステップの途中では落ちない。
          process(:request) { step(:save) { |_s| update saved: true, outbox: true } }
        end

        process :relay, crash: :restart do
          # Outboxに行があるまで待つ。
          step(:poll) { |s| guard s.outbox }
          if variant == :dedup
            step(:deliver) { |s| update mails: max(s.mails, 1) }
          else
            step(:deliver) { |s| update mails: min(s.mails + 1, 2) }
          end
          step(:delete) { |_s| update outbox: false }
        end

        # リクエストが終わり（落ちてもよい）、リレーが終わったか、空のOutboxを待っている。
        ended = if variant == :enqueue_after_save
                  ->(s) { s.request[0].done | s.request[0].crashed }
                else
                  ->(s) { s.request[0].done }
                end
        terminal { |s| ended.call(s) & (s.relay[0].done | (s.relay[0].pc.eq(:poll) & s.outbox.not_)) }

        invariant(:at_most_one_mail) { |s| s.mails <= 1 }
        # 保存した注文の確認メールは、いずれ送られる。
        responds(:mail_sent, within: 4) do
          trigger { |s| s.saved }
          response { |s| s.mails >= 1 }
        end
      end
    end
  end
end
