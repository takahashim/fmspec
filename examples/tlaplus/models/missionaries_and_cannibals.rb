# frozen_string_literal: true

# vendor/tlaplus-examples/MissionariesAndCannibals.tla を DSL で書いたもの。
# Missionaries = {m1, m2, m3}、Cannibals = {c1, c2, c3}。
# 不変条件 solution（東岸が空でない）が破れることが、川を渡りきる手順の発見にあたる。
Fmspec.define(:missionaries_and_cannibals) do
  person = enum(:person, :m1, :m2, :m3, :c1, :c2, :c3)
  side = enum(:side, :e, :w)
  constant :missionaries, set_of(person), Set[:m1, :m2, :m3]
  constant :cannibals, set_of(person), Set[:c1, :c2, :c3]
  state :bank_of_boat, side, initial: :e
  state :who_is_on_bank, map_of(side, set_of(person)), initial: { e: Set[:m1, :m2, :m3, :c1, :c2, :c3], w: Set[] }

  # 宣教師がいないか、宣教師が人食い人種より少なくない。
  safe = ->(s, group) { (group <= s.cannibals) | ((group & s.cannibals).size <= (group & s.missionaries).size) }

  action :move, boat: set_of(person) do |s, boat|
    here = s.bank_of_boat
    there = ite(here.eq(:e), side[:w], side[:e])
    left = s.who_is_on_bank[here] - boat
    arrived = s.who_is_on_bank[there] | boat
    guard boat <= s.who_is_on_bank[here]
    guard (boat.size >= 1) & (boat.size <= 2)
    guard safe.(s, left) & safe.(s, arrived)
    update bank_of_boat: there, who_is_on_bank: s.who_is_on_bank.put(here, left).put(there, arrived)
  end

  invariant(:solution) { |s| s.who_is_on_bank[:e].empty?.not_ }
end
