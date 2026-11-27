# frozen_string_literal: true

# vendor/tlaplus-examples/MCInnerFIFO.tla（Specifying Systems 4章の FIFO の内部）を DSL で書いたもの。
# Message = {m1, m2, m3}、qLen = 3。
# MCInnerFIFO.cfg は CONSTRAINT Len(q) <= qLen で探索を打ち切る。TLC は制約を満たさない状態を、
# 到達した状態の集合に加えない。DSL では、キューに入れる BufRcv の guard に長さの制約を加える。
Fmspec.define(:inner_fifo) do
  q_len = 3
  message = enum(:message, :m1, :m2, :m3)
  chan = record(val: message, rdy: int(0..1), ack: int(0..1))
  initial = message.labels.product([0, 1]).map { |m, b| { val: m, rdy: b, ack: b } }
  state :in, chan, initial_in: initial
  state :out, chan, initial_in: initial
  state :q, list_of(message, max: q_len), initial: []

  # Channel.tla の Send と Rcv。
  ready = ->(c) { c[:rdy].eq(c[:ack]) }
  sent = ->(c, m) { { val: m, rdy: 1 - c[:rdy], ack: c[:ack] } }
  received = ->(c) { { val: c[:val], rdy: c[:rdy], ack: 1 - c[:ack] } }

  action :s_send, msg: message do |s, msg|
    guard ready.(s.in)
    update in: sent.(s.in, msg)
  end

  action :buf_rcv do |s|
    guard ready.(s.in).not_
    guard s.q.size < q_len
    update in: received.(s.in), q: s.q.push(s.in[:val])
  end

  action :buf_send do |s|
    guard s.q.empty?.not_ & ready.(s.out)
    update out: sent.(s.out, s.q.first), q: s.q.shift
  end

  action :r_rcv do |s|
    guard ready.(s.out).not_
    update out: received.(s.out)
  end
end
