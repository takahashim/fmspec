# frozen_string_literal: true

# テスト用の小さなRailsアプリケーション。注文の決済、取消、決済APIからのWebhookを扱う。
#
# CheckoutApp.bug に名前を入れると、仕様から外れる振る舞い（変異）に切り替わる。
#
#   :cancel_side_effect      拒否した取消が、注文を取り消してしまう
#   :no_idempotency_key      決済ジョブが冪等キーを付けず、再試行で二重に決済する
#   :webhook_not_idempotent  重複して届いたWebhookが、出荷をもう一度指示する
#   :job_not_retried         決済APIのタイムアウトで、ジョブが再試行されない
require "rails"
require "active_record/railtie"
require "active_job/railtie"
require "action_controller/railtie"
require "logger"

# メモリ上の SQLite を使う。config/database.yml の代わりに、接続先を環境変数で渡す。
ENV["DATABASE_URL"] = "sqlite3::memory:"

class CheckoutApp < Rails::Application
  config.load_defaults Rails::VERSION::STRING.to_f
  config.eager_load = false
  config.secret_key_base = "fmspec-rails-test"
  config.logger = Logger.new(nil)
  config.hosts.clear
  config.active_job.queue_adapter = :test
  config.action_dispatch.show_exceptions = :none

  class << self
    attr_accessor :bug
  end
end

CheckoutApp.initialize!
ActiveJob::Base.logger = Logger.new(nil)

ActiveRecord::Schema.verbose = false
ActiveRecord::Schema.define do
  create_table :orders do |t|
    t.integer :owner_id, null: false
    t.string :status, null: false, default: "pending"
  end
  create_table :fulfillments do |t|
    t.references :order, null: false
  end
end

# 外部の決済API。テストでは fake に差し替える。
module PaymentGateway
  class Timeout < StandardError; end

  class << self
    attr_accessor :client
  end
end

# 決済APIの fake。次の応答を指示でき、実際に行った決済を記録する。
# 冪等キーの付いた請求は、同じキーで2回目以降、新しい決済にならない。
class FakeGateway
  attr_accessor :next_response
  attr_reader :charges

  def initialize
    @charges = []
    @keys = {}
  end

  def charge(order_id:, idempotency_key: nil)
    return :declined if next_response == :declined

    if %i[ok timeout_charged].include?(next_response) && !(idempotency_key && @keys[idempotency_key])
      @charges << order_id
      @keys[idempotency_key] = true if idempotency_key
    end
    raise PaymentGateway::Timeout unless next_response == :ok

    :ok
  end
end

class Fulfillment < ActiveRecord::Base
  belongs_to :order
end

class Order < ActiveRecord::Base
  has_many :fulfillments

  def pending? = status == "pending"

  # 支払い済みにして、出荷を指示する。すでに支払い済みなら何もしない。
  def mark_paid!
    with_lock do
      if pending?
        update!(status: "paid")
        fulfillments.create!
      elsif CheckoutApp.bug == :webhook_not_idempotent
        fulfillments.create!
      end
    end
  end
end

class ChargeJob < ActiveJob::Base
  retry_on PaymentGateway::Timeout, wait: 1.minute, attempts: 1000

  def perform(order_id)
    order = Order.find(order_id)
    return unless order.pending?

    key = CheckoutApp.bug == :no_idempotency_key ? nil : "order-#{order.id}"
    order.mark_paid! if PaymentGateway.client.charge(order_id: order.id, idempotency_key: key) == :ok
  rescue PaymentGateway::Timeout
    raise unless CheckoutApp.bug == :job_not_retried
  end
end

class OrdersController < ActionController::API
  def checkout
    ChargeJob.perform_later(Order.find(params[:id]).id)
    head :accepted
  end

  # 取消できるのは、所有者が、決済を始めていない未払いの注文に対して行うときだけ。
  def cancel
    order = Order.find(params[:id])
    charging = ActiveJob::Base.queue_adapter.enqueued_jobs.any?
    allowed = order.owner_id == params[:user_id].to_i && order.pending? && !charging
    order.update!(status: "cancelled") if allowed || (CheckoutApp.bug == :cancel_side_effect && order.pending? && !charging)
    head(allowed ? :ok : :forbidden)
  end
end

class WebhooksController < ActionController::API
  # 決済APIからの payment.succeeded。同じ通知が重複して届くことがある。
  def payments
    Order.find(params[:order_id]).mark_paid!
    head :ok
  end
end

CheckoutApp.routes.draw do
  post "/orders/:id/checkout", to: "orders#checkout"
  post "/orders/:id/cancel", to: "orders#cancel"
  post "/webhooks/payments", to: "webhooks#payments"
end
