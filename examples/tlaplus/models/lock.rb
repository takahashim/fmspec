# frozen_string_literal: true

# vendor/tlaplus-examples/Lock.tla（1つのロックによる排他）を、DSL の process で書いたもの。
# PlusCal のプロセス proc \in 1..2 は、インスタンスが2つのプロセス worker になる。
# while (TRUE) の繰り返しは、最後のステップの goto :l0 で表す。
Fmspec.define(:lock) do
  state :lock, int(0..1), initial: 1

  process :worker, count: 2 do |_id|
    step(:l0) { |_s| unchanged }
    step(:l1) do |s|
      guard s.lock.eq(1)
      update lock: 0
    end
    step(:cs) { |_s| unchanged }
    step(:l2) do |_s|
      update lock: 1
      goto :l0
    end
  end

  invariant(:lock_inv) do |s|
    lockcs = ->(i) { s.worker[i].pc.eq(:cs) | s.worker[i].pc.eq(:l2) }
    (lockcs.(0) & lockcs.(1)).not_ & (lockcs.(0) | lockcs.(1)).implies(s.lock.eq(0))
  end
end
