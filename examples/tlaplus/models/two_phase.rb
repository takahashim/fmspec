# frozen_string_literal: true

# vendor/tlaplus-examples/TwoPhase.tla（2相コミット）を DSL で書いたもの。RM = {r1, r2, r3}。
# TLA+ の msgs は、[type |-> "Prepared", rm |-> r]、[type |-> "Commit"]、[type |-> "Abort"] の集合である。
# これを、Prepared を送った RM の集合と、Commit と Abort を送ったかどうかの2つの真偽値で表す。
# この対応は一対一なので、到達できる状態の数は変わらない。
Fmspec.define(:two_phase) do
  rm = enum(:rm, :r1, :r2, :r3)
  rm_state = enum(:rm_state, :working, :prepared, :committed, :aborted)
  tm_state = enum(:tm_state, :init, :committed, :aborted)
  state :rm_state, map_of(rm, rm_state), initial: { r1: :working, r2: :working, r3: :working }
  state :tm_state, tm_state, initial: :init
  state :tm_prepared, set_of(rm), initial: Set[]
  state :prepared_msgs, set_of(rm), initial: Set[]
  state :commit_msg, bool, initial: false
  state :abort_msg, bool, initial: false

  action :tm_rcv_prepared, r: rm do |s, r|
    guard s.tm_state.eq(:init) & s.prepared_msgs.include?(r)
    update tm_prepared: s.tm_prepared.add(r)
  end

  action :tm_commit do |s|
    guard s.tm_state.eq(:init) & s.tm_prepared.eq(Set[:r1, :r2, :r3])
    update tm_state: :committed, commit_msg: true
  end

  action :tm_abort do |s|
    guard s.tm_state.eq(:init)
    update tm_state: :aborted, abort_msg: true
  end

  action :rm_prepare, r: rm do |s, r|
    guard s.rm_state[r].eq(:working)
    update rm_state: s.rm_state.put(r, :prepared), prepared_msgs: s.prepared_msgs.add(r)
  end

  action :rm_choose_to_abort, r: rm do |s, r|
    guard s.rm_state[r].eq(:working)
    update rm_state: s.rm_state.put(r, :aborted)
  end

  action :rm_rcv_commit_msg, r: rm do |s, r|
    guard s.commit_msg
    update rm_state: s.rm_state.put(r, :committed)
  end

  action :rm_rcv_abort_msg, r: rm do |s, r|
    guard s.abort_msg
    update rm_state: s.rm_state.put(r, :aborted)
  end
end
