# frozen_string_literal: true

# vendor/tlaplus-examples/DiningPhilosophers.tla を DSL で書いたもの。N = 5。
# 偶数番の哲学者は右のフォークから、奇数番は左のフォークから取る。
# TLA+ の不変条件 NoDeadlock（ENABLED Next）は、fmspec のデッドロック検査にあたる。
Fmspec.define(:dining_philosophers) do
  n = 5
  phil = int(1..n)
  state :philosophers, map_of(phil, set_of(phil)), initial: (1..n).to_h { |p| [p, Set[]] }
  state :forks, set_of(phil), initial: Set[*1..n]

  action :take_left, p: phil do |s, p|
    guard ((p % 2).eq(0)).implies(s.philosophers[p].eq(Set[(p % n) + 1]))
    guard s.forks.include?(p)
    update forks: s.forks.delete(p), philosophers: s.philosophers.put(p, s.philosophers[p].add(p))
  end

  action :take_right, p: phil do |s, p|
    right = (p % n) + 1
    guard ((p % 2).eq(1)).implies(s.philosophers[p].eq(Set[p]))
    guard s.forks.include?(right)
    update forks: s.forks.delete(right), philosophers: s.philosophers.put(p, s.philosophers[p].add(right))
  end

  action :release, p: phil do |s, p|
    right = (p % n) + 1
    guard s.philosophers[p].eq(Set[p, right])
    update forks: s.forks | Set[p, right], philosophers: s.philosophers.put(p, Set[])
  end
end
