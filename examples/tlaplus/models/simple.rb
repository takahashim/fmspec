# frozen_string_literal: true

# vendor/tlaplus-examples/Simple.tla（Lamport の Teaching Concurrency の例）を、DSL の process で書いたもの。N = 5。
# PlusCal のプロセス proc \in 0..N-1 は、インスタンスが5つのプロセス worker になる。
# PlusCal のラベル a、b はステップに、pc はインスタンスごとのプログラムカウンタに、"Done" は :done にあたる。
# PlusCal の翻訳は、すべてのプロセスが終わった状態に足踏みの遷移（Terminating）を加える。
# DSL の process は、terminal を書かなければ「すべてのインスタンスが :done」を終端条件にする。
Fmspec.define(:simple) do
  n = 5
  index = int(0..(n - 1))
  bit = int(0..1)
  zeros = (0...n).to_h { |i| [i, 0] }
  state :x, map_of(index, bit), initial: zeros
  state :y, map_of(index, bit), initial: zeros

  process :worker, count: n do |id|
    step(:a) { |s| update x: s.x.put(id, 1) }
    step(:b) { |s| update y: s.y.put(id, s.x[(id - 1) % n]) }
  end

  invariant(:p_correct) do |s|
    all(*(0...n).map { |i| s.worker[i].done }).implies(any(*(0...n).map { |i| s.y[i].eq(1) }))
  end

  invariant(:inv) do |s|
    all(*(0...n).map { |i| (s.worker[i].pc.eq(:b) | s.worker[i].done).implies(s.x[i].eq(1)) }) &
      (any(*(0...n).map { |i| s.worker[i].done.not_ }) | any(*(0...n).map { |i| s.y[i].eq(1) }))
  end
end
