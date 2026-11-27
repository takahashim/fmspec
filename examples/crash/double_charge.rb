# frozen_string_literal: true

# 決済してから注文を保存するジョブ（Active Job の retry_on）。保存の前に落ちると、再試行で決済をやり直す。
#
#   :naive        決済して、保存する
#   :check_paid   最初に注文が支払い済みかを見て、済んでいれば何もしない。それでも二重に決済する
#                 （決済は済んだが、保存する前に落ちたので、注文は支払い済みになっていない）
#   :idempotent   決済に冪等キー（注文の番号）を渡す。決済サービスは、同じキーの2回目の決済をしない
#
# 再試行は perform の最初からやり直すので、仕様でも最初のステップからやり直す（crash: :restart）。
# 途中から再開したように振る舞うのは、ステップが永続化された状態（DB、決済サービス）を見て処理を飛ばすからであり、
# それはステップの guard と goto で書く。
module CrashExamples
  module DoubleCharge
    VARIANTS = %i[naive check_paid idempotent].freeze

    def self.define(variant)
      raise ArgumentError, "unknown variant: #{variant}" unless VARIANTS.include?(variant)

      Fmspec.define(:"double_charge_#{variant}") do
        # 決済サービス側の決済の回数と、冪等キーを受け取ったか。
        state :charges, int(0..2), initial: 0
        state :key_used, bool, initial: false
        # DBの注文の支払い済みフラグ。
        state :paid, bool, initial: false

        process :job, crash: :restart do
          if variant == :check_paid
            step(:check) { |s| goto :done, s.paid }
          end
          if variant == :idempotent
            step(:charge) { |s| update charges: ite(s.key_used, s.charges, s.charges + 1), key_used: true }
          else
            step(:charge) { |s| update charges: min(s.charges + 1, 2) }
          end
          step(:save) { |_s| update paid: true }
        end

        invariant(:charged_at_most_once) { |s| s.charges <= 1 }
      end
    end
  end
end
