# frozen_string_literal: true

# 注文の決済の仕様。決済API、ジョブの再試行、Webhook の重複を、有限の状態と遷移として書く（仕様書 §12.3）。
Checkout = Fmspec.define(:checkout) do
  enum(:status, :pending, :paid, :cancelled)
  enum(:result, :success, :forbidden)
  # 決済APIの応答。タイムアウトは「決済なし」と「決済済みだが応答喪失」を区別する。
  responses = enum(:response, :ok, :declined, :timeout_lost, :timeout_charged)

  state :status, enum(:status, :pending, :paid, :cancelled), initial: :pending
  # 決済ジョブがキューにある。
  state :queued, bool, initial: false
  # 決済APIが実際に行った決済の数と、出荷の指示の数。0、1、2以上の3値に飽和させる。
  ghost :charges, int(0..2), initial: 0
  ghost :fulfillments, int(0..2), initial: 0

  action :checkout do |s|
    guard s.status.eq(:pending) & s.queued.not_
    update queued: true
  end

  # ワーカーが決済ジョブを実行する。決済APIの応答は内部選択で、テストでは fake に注入する。
  action :run_job do |s|
    response = choose(:response, responses)
    # 決済済みの注文に、決済APIが「拒否」を返すことはない。
    guard s.queued & (response.ne(:declined) | s.charges.eq(0))
    # 支払い済みの注文では、ジョブは決済APIを呼ばずに終わる。
    calls = s.status.eq(:pending)
    charged = calls & (response.eq(:ok) | response.eq(:timeout_charged))
    paid = calls & response.eq(:ok)
    update queued: calls & (response.eq(:timeout_lost) | response.eq(:timeout_charged)),
           # 再試行の請求は、冪等キーによって新しい決済にならない。
           charges: ite(charged, max(s.charges, 1), s.charges),
           status: ite(paid, :paid, s.status),
           fulfillments: ite(paid, min(s.fulfillments + 1, 2), s.fulfillments)
  end

  # 決済APIからの payment.succeeded。決済が行われたあとなら、何度でも届きうる。
  action :webhook do |s|
    guard s.charges >= 1
    pays = s.status.eq(:pending)
    update status: ite(pays, :paid, s.status), fulfillments: ite(pays, min(s.fulfillments + 1, 2), s.fulfillments)
  end

  # 取消。所有者（利用者0）が、決済を始めていない未払いの注文に対して行うときだけ受理する。
  action :cancel, user: 0..1 do |s, user|
    accept_if user.eq(0) & s.status.eq(:pending) & s.queued.not_
    on_accept do
      update status: :cancelled
      returns :success
    end
    on_reject do
      unchanged
      returns :forbidden
    end
    preserves :charges, :fulfillments
  end

  invariant(:no_double_charge) { |s| s.charges <= 1 }
  invariant(:fulfilled_once) { |s| s.fulfillments <= 1 }
  invariant(:paid_means_charged) { |s| s.status.eq(:paid).implies(s.charges.eq(1)) }
  invariant(:fulfilled_exactly_when_paid) { |s| s.status.eq(:paid).eq(s.fulfillments.eq(1)) }
  invariant(:cancelled_orders_are_not_charged) { |s| s.status.eq(:cancelled).implies(s.charges.eq(0)) }
end
