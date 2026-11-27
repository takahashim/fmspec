# frozen_string_literal: true

# vendor/tlaplus-examples/EWD840.tla（Dijkstra のリング上の終了検出）を DSL で書いたもの。N = 3。
# active と color は、ノードの全体を定義域とする関数なので、すべてのキーを持つ Map で表す。
# 初期状態は、active と color のすべての組み合わせと、トークンのすべての位置である。
Fmspec.define(:ewd840) do
  n = 3
  node = int(0..(n - 1))
  color = enum(:color, :white, :black)
  all_maps = ->(values) { values.repeated_permutation(n).map { |vs| (0...n).zip(vs).to_h } }
  state :active, map_of(node, bool), initial_in: all_maps.([false, true])
  state :color, map_of(node, color), initial_in: all_maps.(%i[white black])
  state :tpos, node, initial_in: node
  state :tcolor, color, initial: :black

  action :initiate_probe do |s|
    guard s.tpos.eq(0) & (s.tcolor.eq(:black) | s.color[0].eq(:black))
    update tpos: n - 1, tcolor: :white, color: s.color.put(0, :white)
  end

  action :pass_token, i: 1..(n - 1) do |s, i|
    guard s.tpos.eq(i) & (s.active[i].not_ | s.color[i].eq(:black) | s.tcolor.eq(:black))
    update tpos: i - 1, tcolor: ite(s.color[i].eq(:black), :black, s.tcolor), color: s.color.put(i, :white)
  end

  action :send_msg, i: node, j: node do |s, i, j|
    guard s.active[i] & i.ne(j)
    update active: s.active.put(j, true), color: s.color.put(i, ite(j > i, :black, s.color[i]))
  end

  action :deactivate, i: node do |s, i|
    guard s.active[i]
    update active: s.active.put(i, false)
  end

  invariant(:termination_detection) do |s|
    detected = s.tpos.eq(0) & s.tcolor.eq(:white) & s.color[0].eq(:white) & s.active[0].not_
    detected.implies(forall(node) { |i| s.active[i].not_ })
  end

  invariant(:inv) do |s|
    forall(node) { |i| (s.tpos < i).implies(s.active[i].not_) } |
      exists(node) { |j| (j <= s.tpos) & s.color[j].eq(:black) } |
      s.tcolor.eq(:black)
  end
end
