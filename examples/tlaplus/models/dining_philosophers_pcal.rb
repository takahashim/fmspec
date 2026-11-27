# frozen_string_literal: true

# vendor/tlaplus-examples/DiningPhilosophersPCal.tla（Chandy と Misra の、汚れたフォークを手渡す食事する哲学者）を、
# DSL の process で書いたもの。NP = 5。
# PlusCal のプロセス Philosopher \in 1..NP は、インスタンスが5つのプロセス philosopher になる。
# インスタンスの番号 id（0 から）が、PlusCal の self（1 から）の id + 1 にあたる。
# プロセスの変数 hungry はローカル変数に、ラベル Loop、Eat、Think はステップにあたる。
# Loop は、空腹でフォークがそろえば Eat に、空腹でなければ Think に、それ以外は Loop に進む。
# PlusCal の翻訳と同じく、行き先の条件は遷移前の状態で評価する。
Fmspec.define(:dining_philosophers_pcal) do
  np = 5
  phil = int(1..np)
  fork = record(holder: phil, clean: bool)
  # 各フォークは、隣り合う哲学者のうち番号の小さいほうが、汚れたまま持って始める。
  state :forks, map_of(phil, fork), initial: (1..np).to_h { |f| [f, { holder: f == 2 ? 1 : f, clean: false }] }

  left_fork = ->(p) { p }
  right_fork = ->(p) { p == np ? 1 : p + 1 }
  left_philosopher = ->(p) { p == 1 ? np : p - 1 }
  right_philosopher = ->(p) { p == np ? 1 : p + 1 }

  process :philosopher, count: np do |id|
    me = id + 1
    left = left_fork.(me)
    right = right_fork.(me)
    local :hungry, bool, initial: true

    step(:loop) do |s|
      holds = ->(f) { s.forks[f][:holder].eq(me) }
      dirty_left = holds.(left) & s.forks[left][:clean].not_
      dirty_right = holds.(right) & s.forks[right][:clean].not_
      can_eat = holds.(left) & holds.(right) & s.forks[left][:clean] & s.forks[right][:clean]
      # 持っている汚れたフォークを、きれいにして隣に渡す（左を優先する）。
      update forks: ite(dirty_left, s.forks.put(left, { holder: left_philosopher.(me), clean: true }),
                        ite(dirty_right, s.forks.put(right, { holder: right_philosopher.(me), clean: true }), s.forks))
      goto :eat, s.hungry & can_eat
      goto :think, s.hungry.not_
      goto :loop
    end

    step(:eat) do |s|
      dirty = ->(m, f) { m.put(f, { holder: s.forks[f][:holder], clean: false }) }
      update hungry: false, forks: dirty.(dirty.(s.forks, left), right)
      goto :loop
    end

    step(:think) do |_s|
      update hungry: true
      goto :loop
    end
  end

  # フォークを共有する2人の哲学者は、同時に食べない。
  sharing = (1..np).to_a.combination(2).select do |p, q|
    !([left_fork.(p), right_fork.(p)] & [left_fork.(q), right_fork.(q)]).empty?
  end
  invariant(:exclusive_access) do |s|
    all(*sharing.map { |p, q| (s.philosopher[p - 1].pc.eq(:eat) & s.philosopher[q - 1].pc.eq(:eat)).not_ })
  end
end
