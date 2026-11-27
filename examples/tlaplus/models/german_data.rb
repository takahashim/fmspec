# frozen_string_literal: true

# vendor/tlaplus-examples/GermanData.tla（German のプロトコルにデータの値を加えたもの）を DSL で書いたもの。
# NODE = {n1, n2}、DATA = {d1, d2}。NoNode と NoData は Option の値なしで表す。
# MCGermanData.cfg は SYMMETRY でノードとデータの入れ替えをまとめるが、比較では SYMMETRY を外して TLC にかける。
Fmspec.define(:german_data) do
  node = enum(:node, :n1, :n2)
  data = enum(:data, :d1, :d2)
  cache_state = enum(:cache_state, :i, :s, :e)
  req = enum(:req, :empty, :req_s, :req_e)
  msg2 = enum(:msg2, :empty, :inv, :gnt_s, :gnt_e)
  msg3 = enum(:msg3, :empty, :inv_ack)
  payload = option(data)
  line = record(state: cache_state, data: payload)
  all = ->(value) { node.labels.to_h { |n| [n, value] } }
  state :cache, map_of(node, line), initial: all.({ state: :i, data: nil })
  state :chan1, map_of(node, record(cmd: req, data: payload)), initial: all.({ cmd: :empty, data: nil })
  state :chan2, map_of(node, record(cmd: msg2, data: payload)), initial: all.({ cmd: :empty, data: nil })
  ack = record(cmd: msg3, data: payload)
  state :chan3, map_of(node, ack), initial: all.({ cmd: :empty, data: nil })
  state :inv_set, set_of(node), initial: Set[]
  state :shr_set, set_of(node), initial: Set[]
  state :ex_gntd, bool, initial: false
  state :cur_cmd, req, initial: :empty
  state :cur_ptr, option(node), initial: nil
  state :mem_data, data, initial_in: data
  state :aux_data, data, initial_in: data
  initially { |s| s.mem_data.eq(s.aux_data) }

  # [chan EXCEPT ![i].cmd = c] のように、メッセージの種類だけを変える。
  with_cmd = ->(msg, cmd) { { cmd: cmd, data: msg[:data] } }

  action :store, i: node, d: data do |s, i, d|
    guard s.cache[i][:state].eq(:e)
    update cache: s.cache.put(i, { state: s.cache[i][:state], data: some(d) }), aux_data: d
  end

  action :send_req, i: node, exclusive: bool do |s, i, exclusive|
    guard s.chan1[i][:cmd].eq(:empty)
    guard ite(exclusive, s.cache[i][:state].ne(:e), s.cache[i][:state].eq(:i))
    update chan1: s.chan1.put(i, with_cmd.(s.chan1[i], ite(exclusive, req[:req_e], req[:req_s])))
  end

  action :recv_gnt, i: node do |s, i|
    guard s.chan2[i][:cmd].eq(:gnt_s) | s.chan2[i][:cmd].eq(:gnt_e)
    granted = ite(s.chan2[i][:cmd].eq(:gnt_s), cache_state[:s], cache_state[:e])
    update cache: s.cache.put(i, { state: granted, data: s.chan2[i][:data] }),
           chan2: s.chan2.put(i, { cmd: :empty, data: nil })
  end

  action :send_inv_ack, i: node do |s, i|
    guard s.chan2[i][:cmd].eq(:inv) & s.chan3[i][:cmd].eq(:empty)
    written = ite(s.cache[i][:state].eq(:e), s.cache[i][:data], none(data))
    update chan2: s.chan2.put(i, { cmd: :empty, data: nil }),
           chan3: s.chan3.put(i, { cmd: :inv_ack, data: written }),
           cache: s.cache.put(i, { state: :i, data: nil })
  end

  action :recv_req, i: node do |s, i|
    guard s.cur_cmd.eq(:empty) & s.chan1[i][:cmd].ne(:empty)
    update cur_cmd: s.chan1[i][:cmd], cur_ptr: some(i), chan1: s.chan1.put(i, with_cmd.(s.chan1[i], :empty)),
           inv_set: s.shr_set
  end

  action :send_inv, i: node do |s, i|
    guard s.chan2[i][:cmd].eq(:empty) & s.inv_set.include?(i)
    guard s.cur_cmd.eq(:req_e) | (s.cur_cmd.eq(:req_s) & s.ex_gntd)
    update chan2: s.chan2.put(i, with_cmd.(s.chan2[i], :inv)), inv_set: s.inv_set.delete(i)
  end

  # 排他的に与えていたなら、書き戻されたデータをメモリに入れ、チャネルのデータも消す。
  # そうでなければ、メッセージの種類だけを Empty にし、データは残す（元の仕様のとおり）。
  action :recv_inv_ack, i: node do |s, i|
    guard s.chan3[i][:cmd].eq(:inv_ack) & s.cur_cmd.ne(:empty)
    update shr_set: s.shr_set.delete(i), ex_gntd: false,
           mem_data: ite(s.ex_gntd, s.chan3[i][:data].unwrap, s.mem_data),
           chan3: s.chan3.put(i, ite(s.ex_gntd, ack.value({ cmd: :empty, data: nil }), with_cmd.(s.chan3[i], :empty)))
  end

  action :send_gnt, i: node do |s, i|
    guard s.cur_cmd.ne(:empty) & s.cur_ptr.eq(some(i)) & s.chan2[i][:cmd].eq(:empty) & s.ex_gntd.not_
    guard s.cur_cmd.eq(:req_e).implies(s.shr_set.empty?)
    granted = ite(s.cur_cmd.eq(:req_s), msg2[:gnt_s], msg2[:gnt_e])
    update chan2: s.chan2.put(i, { cmd: granted, data: some(s.mem_data) }),
           shr_set: s.shr_set.add(i), ex_gntd: s.cur_cmd.eq(:req_e), cur_cmd: :empty, cur_ptr: none(node)
  end

  pairs = ->(&body) { forall(node) { |i| forall(node) { |j| i.ne(j).implies(body.(i, j)) } } }

  invariant(:coherence) do |s|
    pairs.() do |i, j|
      s.cache[i][:state].eq(:e).implies(s.cache[j][:state].eq(:i)) &
        s.cache[i][:state].eq(:s).implies(s.cache[j][:state].eq(:i) | s.cache[j][:state].eq(:s))
    end
  end

  invariant(:data_prop) do |s|
    s.ex_gntd.not_.implies(s.mem_data.eq(s.aux_data)) &
      forall(node) { |i| s.cache[i][:state].ne(:i).implies(s.cache[i][:data].eq(some(s.aux_data))) }
  end

  invariant(:transaction_consistency) { |s| s.cur_cmd.eq(:empty).eq(s.cur_ptr.none?) }

  invariant(:directory_accurate) do |s|
    forall(node) { |i| (s.cache[i][:state].eq(:s) | s.cache[i][:state].eq(:e)).implies(s.shr_set.include?(i)) }
  end

  invariant(:exclusive_isolation) do |s|
    forall(node) do |i|
      s.cache[i][:state].eq(:e).implies(
        s.ex_gntd & forall(node) do |j|
          i.eq(j) | (s.cache[j][:state].eq(:i) & s.chan2[j][:cmd].ne(:gnt_s) & s.chan2[j][:cmd].ne(:gnt_e) &
                     s.chan3[j][:cmd].ne(:inv_ack))
        end
      )
    end
  end

  invariant(:writeback_carries_latest) do |s|
    forall(node) do |i|
      (s.chan3[i][:cmd].eq(:inv_ack) & s.cur_cmd.ne(:empty) & s.ex_gntd).implies(
        s.chan3[i][:data].eq(some(s.aux_data)) & forall(node) do |j|
          i.eq(j) | (s.cache[j][:state].ne(:e) & s.chan2[j][:cmd].ne(:gnt_e) & s.chan3[j][:cmd].ne(:inv_ack))
        end
      )
    end
  end
end
