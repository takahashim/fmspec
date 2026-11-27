# frozen_string_literal: true

# vendor/tlaplus-examples/GermanControl.tla（German のキャッシュコヒーレンスのプロトコルの制御部分）を DSL で書いたもの。
# NODE = {n1, n2}。NoNode は Option の値なしで表す。
# MCGermanControl.cfg は SYMMETRY でノードの入れ替えをまとめるが、fmspec に対称性の削減はないので、
# 比較では SYMMETRY を外して TLC にかける。
Fmspec.define(:german_control) do
  node = enum(:node, :n1, :n2)
  cache_state = enum(:cache_state, :i, :s, :e)
  req = enum(:req, :empty, :req_s, :req_e)
  msg2 = enum(:msg2, :empty, :inv, :gnt_s, :gnt_e)
  msg3 = enum(:msg3, :empty, :inv_ack)
  all = ->(value) { node.labels.to_h { |n| [n, value] } }
  state :cache, map_of(node, cache_state), initial: all.(:i)
  state :chan1, map_of(node, req), initial: all.(:empty)
  state :chan2, map_of(node, msg2), initial: all.(:empty)
  state :chan3, map_of(node, msg3), initial: all.(:empty)
  state :inv_set, set_of(node), initial: Set[]
  state :shr_set, set_of(node), initial: Set[]
  state :ex_gntd, bool, initial: false
  state :cur_cmd, req, initial: :empty
  state :cur_ptr, option(node), initial: nil

  action :send_req, i: node, exclusive: bool do |s, i, exclusive|
    guard s.chan1[i].eq(:empty)
    guard ite(exclusive, s.cache[i].ne(:e), s.cache[i].eq(:i))
    update chan1: s.chan1.put(i, ite(exclusive, req[:req_e], req[:req_s]))
  end

  action :recv_req, i: node do |s, i|
    guard s.cur_cmd.eq(:empty) & s.chan1[i].ne(:empty)
    update cur_cmd: s.chan1[i], cur_ptr: some(i), chan1: s.chan1.put(i, :empty), inv_set: s.shr_set
  end

  action :send_inv, i: node do |s, i|
    guard s.chan2[i].eq(:empty) & s.inv_set.include?(i)
    guard s.cur_cmd.eq(:req_e) | (s.cur_cmd.eq(:req_s) & s.ex_gntd)
    update chan2: s.chan2.put(i, :inv), inv_set: s.inv_set.delete(i)
  end

  action :send_inv_ack, i: node do |s, i|
    guard s.chan2[i].eq(:inv) & s.chan3[i].eq(:empty)
    update chan2: s.chan2.put(i, :empty), chan3: s.chan3.put(i, :inv_ack), cache: s.cache.put(i, :i)
  end

  action :recv_inv_ack, i: node do |s, i|
    guard s.chan3[i].eq(:inv_ack) & s.cur_cmd.ne(:empty)
    update chan3: s.chan3.put(i, :empty), shr_set: s.shr_set.delete(i), ex_gntd: false
  end

  action :send_gnt, i: node do |s, i|
    guard s.cur_cmd.ne(:empty) & s.cur_ptr.eq(some(i)) & s.chan2[i].eq(:empty) & s.ex_gntd.not_
    guard s.cur_cmd.eq(:req_e).implies(s.shr_set.empty?)
    update chan2: s.chan2.put(i, ite(s.cur_cmd.eq(:req_s), msg2[:gnt_s], msg2[:gnt_e])),
           shr_set: s.shr_set.add(i), ex_gntd: s.cur_cmd.eq(:req_e), cur_cmd: :empty, cur_ptr: none(node)
  end

  action :recv_gnt, i: node do |s, i|
    guard s.chan2[i].eq(:gnt_s) | s.chan2[i].eq(:gnt_e)
    update cache: s.cache.put(i, ite(s.chan2[i].eq(:gnt_s), cache_state[:s], cache_state[:e])),
           chan2: s.chan2.put(i, :empty)
  end

  invariant(:coherence) do |s|
    forall(node) do |i|
      forall(node) do |j|
        i.ne(j).implies(s.cache[i].eq(:e).implies(s.cache[j].eq(:i)) &
                        s.cache[i].eq(:s).implies(s.cache[j].eq(:i) | s.cache[j].eq(:s)))
      end
    end
  end
end
