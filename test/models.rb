# frozen_string_literal: true

# テストで使う仕様。DSL で書く。
module TestModels
  module_function

  # 仕様書 §4.1 のチケット例。guard と初期値、購入の更新式を差し替えられる。
  # 差し替えは記号ブロックの外で選ぶ。記号ブロックの中には、静的な分岐も書けない。
  def tickets(guarded: true, initial: 0, constant_update: nil)
    purchase_guard = guarded ? ->(s, quantity) { s.sold + quantity <= s.capacity } : ->(_s, _quantity) { true }
    purchase_update = constant_update ? ->(_s, _quantity) { constant_update } : ->(s, quantity) { s.sold + quantity }
    Fmspec.define(:tickets) do
      state :sold, int(0..4), initial: initial
      constant :capacity, 3

      action :purchase, quantity: 1..2 do |s, quantity|
        guard purchase_guard.call(s, quantity)
        update sold: purchase_update.call(s, quantity)
      end

      action :cancel do |s|
        guard s.sold > 0
        update sold: s.sold - 1
      end

      invariant(:capacity_respected) { |s| s.sold <= s.capacity }
    end
  end

  # 1状態で、同じ公開入力が内部選択に応じて success または forbidden を返す自己ループ。
  def responder
    Fmspec.define(:responder) do
      result = enum(:result, :success, :forbidden)
      state :x, int(0..0), initial: 0

      action :request, id: 7..7 do |_s, _id|
        allowed = choose(:allowed, bool)
        returns ite(allowed, :success, :forbidden), result
        ensures(:succeeds) { |_after, out| out.eq(:success) }
      end
    end
  end

  # 0 から `max` まで1ずつ数えるカウンタを `width` 個持つ。到達可能な状態は (max + 1) ** width 個。
  def counters(width, max)
    Fmspec.define(:counters) do
      width.times do |i|
        state :"c#{i}", int(0..max), initial: 0
        action :"inc#{i}" do |s|
          guard s.__send__(:"c#{i}") < max
          update "c#{i}": s.__send__(:"c#{i}") + 1
        end
      end
    end
  end

  # i64 の最大値を持つ状態変数 big と、不変条件 p を持つ。ブロックは big の式を受け取る。
  def big(&invariant)
    Fmspec.define(:big) do
      state :big, int(0..Fmspec::I64_MAX), initial: Fmspec::I64_MAX
      invariant(:p) { |s| invariant.call(s.big) }
    end
  end
end
