# frozen_string_literal: true

# vendor/tlaplus-examples/Bakery.tla（Lamport のパン屋のアルゴリズム）を、DSL の process で書いたもの。
# 定数は MCBakery.cfg と同じく N = 2 で、Nat を 0..2（MaxNat = 2）に置き換える。
# PlusCal のプロセス p \in Procs は、インスタンスが2つのプロセス p になる。
# インスタンスの番号 id（0 から）が、PlusCal の self（1 から）の id + 1 にあたる。
# プロセスの変数 unchecked、max、nxt はローカル変数に、ラベルはステップにあたる。
#
# PlusCal の either A or B は、内部選択した真偽値で A と B を選び、goto で行き先を分ける。
# while (unchecked # {}) の本体の with (i \in unchecked) は、unchecked が空なら選ばずに次のラベルに進む。
# DSL の choose は空のドメインでは遷移を持たないので、空のときだけ自分の番号を選ぶ範囲にする。
# このとき更新はすべて元の値を保つので、遷移先は PlusCal と同じである。
Fmspec.define(:bakery) do
  n = 2
  max_nat = 2
  procs = int(1..n)
  nat = int(0..max_nat)
  state :num, map_of(procs, nat), initial: (1..n).to_h { |i| [i, 0] }
  state :flag, map_of(procs, bool), initial: (1..n).to_h { |i| [i, false] }

  process :p, count: n do |id|
    me = id + 1
    others = Set[*(1..n)] - [me]
    local :unchecked, set_of(procs), initial: Set[]
    local :max, nat, initial: 0
    local :nxt, procs, initial: 1
    # unchecked が空なら、選ぶ値は使わない。
    pick = ->(s) { ite(s.unchecked.empty?, set_of(procs).value([me]), s.unchecked) }

    step(:ncs) { |_s| unchanged }

    step(:e1) do |s|
      again = choose(:again, bool)
      update flag: s.flag.put(me, ite(again, s.flag[me].not_, true)),
             unchecked: ite(again, s.unchecked, others), max: ite(again, s.max, 0)
      goto :e1, again
    end

    step(:e2) do |s|
      i = choose(:i, pick.(s))
      empty = s.unchecked.empty?
      update unchecked: ite(empty, s.unchecked, s.unchecked.delete(i)),
             max: ite(empty | (s.num[i] <= s.max), s.max, s.num[i])
      goto :e2, empty.not_
    end

    step(:e3) do |s|
      again = choose(:again, bool)
      k = choose(:k, nat)
      guard again | (k > s.max)
      update num: s.num.put(me, k)
      goto :e3, again
    end

    step(:e4) do |s|
      again = choose(:again, bool)
      update flag: s.flag.put(me, ite(again, s.flag[me].not_, false)), unchecked: ite(again, s.unchecked, others)
      goto :e4, again
    end

    step(:w1) do |s|
      i = choose(:i, pick.(s))
      empty = s.unchecked.empty?
      guard empty | s.flag[i].not_
      update nxt: ite(empty, s.nxt, i)
      goto :cs, empty
    end

    step(:w2) do |s|
      ours = s.num[me]
      theirs = s.num[s.nxt]
      guard theirs.eq(0) | (ours < theirs) | (ours.eq(theirs) & (s.nxt > me))
      update unchecked: s.unchecked.delete(s.nxt)
      goto :w1
    end

    step(:cs) { |_s| unchanged }

    step(:exit) do |s|
      again = choose(:again, bool)
      k = choose(:k, nat)
      update num: s.num.put(me, ite(again, k, 0))
      goto :exit, again
      goto :ncs
    end
  end

  invariant(:mutual_exclusion) { |s| (s.p[0].pc.eq(:cs) & s.p[1].pc.eq(:cs)).not_ }
end
