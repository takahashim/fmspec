# frozen_string_literal: true

# vendor/tlaplus-examples/TCommit.tla（トランザクションのコミットの仕様）を DSL で書いたもの。RM = {r1, r2, r3}。
# 状態変数 rmState は、RM の全体を定義域とする関数なので、すべてのキーを持つ Map で表す。
Fmspec.define(:t_commit) do
  rm = enum(:rm, :r1, :r2, :r3)
  rm_state = enum(:rm_state, :working, :prepared, :committed, :aborted)
  state :rm_state, map_of(rm, rm_state), initial: { r1: :working, r2: :working, r3: :working }

  action :prepare, r: rm do |s, r|
    guard s.rm_state[r].eq(:working)
    update rm_state: s.rm_state.put(r, :prepared)
  end

  action :decide_commit, r: rm do |s, r|
    guard s.rm_state[r].eq(:prepared)
    guard forall(rm) { |x| s.rm_state[x].eq(:prepared) | s.rm_state[x].eq(:committed) }
    update rm_state: s.rm_state.put(r, :committed)
  end

  action :decide_abort, r: rm do |s, r|
    guard s.rm_state[r].eq(:working) | s.rm_state[r].eq(:prepared)
    guard forall(rm) { |x| s.rm_state[x].ne(:committed) }
    update rm_state: s.rm_state.put(r, :aborted)
  end

  invariant(:consistent) do |s|
    forall(rm) { |a| forall(rm) { |b| (s.rm_state[a].eq(:aborted) & s.rm_state[b].eq(:committed)).not_ } }
  end
end
