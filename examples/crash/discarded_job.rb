# frozen_string_literal: true

# 再試行の回数が尽きたジョブ（Active Job の retry_on attempts:）。注文は pending のまま残ってはならない。
#
#   :bounded_faults   max_crashes: 2。「落ちるのは2回まで」という環境の仮定。3回目は落ちないので、ジョブは必ず終わる
#   :retries          retries: 2。実装が2回まで再試行し、3回目に落ちたらジョブを捨てる。注文は pending のまま残る
#   :after_discard    retries: 2 に加え、捨てるときに注文を failed にする（after_discard のコールバック）
#
# max_crashes: と retries: は、どちらもクラッシュの回数を有限にするが、意味が違う。
# max_crashes: は環境についての仮定で、それを超えて落ちる実行は検査しない。
# retries: は実装の振る舞いで、尽きたあとに落ちる実行も検査する。
module CrashExamples
  module DiscardedJob
    VARIANTS = %i[bounded_faults retries after_discard].freeze

    def self.define(variant)
      raise ArgumentError, "unknown variant: #{variant}" unless VARIANTS.include?(variant)

      options = variant == :bounded_faults ? { max_crashes: 2 } : { retries: 2 }
      Fmspec.define(:"discarded_job_#{variant}") do
        status = enum(:status, :pending, :paid, :failed)
        state :order, status, initial: :pending

        process :job, crash: :restart, crash_at: %i[pay], **options do |id|
          # 決済サービスへの問い合わせ。ここで落ちうる（タイムアウトで例外になる）。
          step(:pay) { |_s| unchanged }
          step(:save) { |_s| update order: :paid }
          if variant == :after_discard
            # 再試行が尽きたあとのクラッシュ（ジョブを捨てるとき）にだけ、注文を failed にする。
            on_crash { |s| update order: ite(s.job[id].crashes.eq(2), :failed, s.order) }
          end
        end

        # ジョブが終われば（捨てられても）、注文は pending ではない。
        ended = variant == :bounded_faults ? ->(s) { s.job[0].done } : ->(s) { s.job[0].done | s.job[0].crashed }
        invariant(:settled) { |s| ended.call(s).implies(s.order.ne(:pending)) }
      end
    end
  end
end
