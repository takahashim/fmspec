# frozen_string_literal: true

# vendor/tlaplus-examples/DieHard.tla（映画 Die Hard 3 の水差しの問題）を DSL で書いたもの。
# 状態変数は TLA+ の big、small と同じである。
Fmspec.define(:die_hard) do
  state :big, int(0..5), initial: 0
  state :small, int(0..3), initial: 0

  action(:fill_small_jug) { |_s| update small: 3 }
  action(:fill_big_jug) { |_s| update big: 5 }
  action(:empty_small_jug) { |_s| update small: 0 }
  action(:empty_big_jug) { |_s| update big: 0 }

  action :small_to_big do |s|
    poured = min(s.big + s.small, 5)
    update big: poured, small: s.small - (poured - s.big)
  end

  action :big_to_small do |s|
    poured = min(s.big + s.small, 3)
    update small: poured, big: s.big - (poured - s.small)
  end

  invariant(:not_solved) { |s| s.big.ne(4) }
end
