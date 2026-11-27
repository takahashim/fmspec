# frozen_string_literal: true

# 仕様記述DSL。native extension を読み込まずに、仕様の定義とIRの生成までを行える。
# 検査（check、simulate など）には `require "fmspec"` が要る。
require "json"
require_relative "version"
require_relative "errors"
require_relative "types"
require_relative "expr"
require_relative "lint"
require_relative "builder"
require_relative "process"
require_relative "response"
require_relative "migration"
require_relative "model"
require_relative "result"
require_relative "binding"
require_relative "testing"
require_relative "coverage"
require_relative "scheduler"
require_relative "compose"

# Ruby で書く実行可能な形式仕様と、モデル検査。
#
#   Tickets = Fmspec.define(:tickets) do
#     state :sold, int(0..4), initial: 0
#     constant :capacity, 3
#
#     action :purchase, quantity: 1..2 do |s, quantity|
#       guard s.sold + quantity <= s.capacity
#       update sold: s.sold + quantity
#     end
#
#     invariant(:capacity_respected) { |s| s.sold <= s.capacity }
#   end
#
#   Tickets.check(max_states: 10_000).verified?
module Fmspec
  # 仕様を定義する。ブロックの中の語彙は Fmspec::Builder にある。
  def self.define(name, &block)
    raise BuildError, "Fmspec.define にはブロックが必要です" unless block

    builder = Builder.new(name)
    builder.instance_eval(&block)
    builder.build
  end

  # モデルを合成する（仕様書 §12.5）。キーワードの名前が、各モデルの名前空間の接頭辞になる。
  # ブロックの中の語彙（sync、invariant、terminal、initially）は Fmspec::Composer にある。
  #
  #   Shop = Fmspec.compose(:shop, cart: Cart, stock: Stock) do
  #     sync :checkout, cart: :pay, stock: :ship
  #     invariant(:paid_items_shipped) { |s| s.cart.paid <= s.stock.shipped }
  #   end
  def self.compose(name, **components, &block)
    composer = Composer.new(name, components)
    composer.instance_eval(&block) if block
    composer.build
  end
end
