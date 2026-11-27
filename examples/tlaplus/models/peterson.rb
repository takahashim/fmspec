# frozen_string_literal: true

# vendor/tlaplus-examples/Peterson.tla（Peterson の排他アルゴリズム）を、DSL の process で書いたもの。
# PlusCal のプロセス proc \in 1..2 は、インスタンスが2つのプロセス worker になる。
# インスタンスの番号 id（0 と 1）が、PlusCal の self（1 と 2）の id + 1 にあたる。
Fmspec.define(:peterson) do
  me = int(1..2)
  state :c, map_of(me, bool), initial: { 1 => false, 2 => false }
  state :turn, me, initial: 1

  process :worker, count: 2 do |id|
    this = id + 1
    other = this == 1 ? 2 : 1
    step(:a0) { |_s| unchanged }
    step(:a1) { |s| update c: s.c.put(this, true) }
    step(:a2) { |_s| update turn: other }
    step(:a3) { |s| guard s.c[other].not_ | s.turn.eq(this) }
    step(:cs) { |_s| unchanged }
    step(:a4) do |s|
      update c: s.c.put(this, false)
      goto :a0
    end
  end

  invariant(:inv) do |s|
    at = ->(i, *labels) { any(*labels.map { |l| s.worker[i].pc.eq(l) }) }
    flags = all(*[0, 1].map { |i| s.c[i + 1].eq(at.(i, :a2, :a3, :cs, :a4)) })
    waiting = all(*[0, 1].map { |i| at.(i, :cs, :a4).implies(s.turn.eq(i + 1) | at.(1 - i, :a0, :a1, :a2)) })
    exclusive = (at.(0, :cs, :a4) & at.(1, :cs, :a4)).not_
    flags & waiting & exclusive
  end
end
