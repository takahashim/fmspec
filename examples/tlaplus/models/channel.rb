# frozen_string_literal: true

# vendor/tlaplus-examples/Channel.tla（Specifying Systems 3章の非同期のチャネル）を DSL で書いたもの。
# Data = {d1, d2, d3}。初期状態は、ack = rdy となるすべての chan である。
Fmspec.define(:channel) do
  data = enum(:data, :d1, :d2, :d3)
  initial = data.labels.product([0, 1]).map { |d, b| { val: d, rdy: b, ack: b } }
  state :chan, record(val: data, rdy: int(0..1), ack: int(0..1)), initial_in: initial

  action :send, d: data do |s, d|
    guard s.chan[:rdy].eq(s.chan[:ack])
    update chan: { val: d, rdy: 1 - s.chan[:rdy], ack: s.chan[:ack] }
  end

  action :rcv do |s|
    guard s.chan[:rdy].ne(s.chan[:ack])
    update chan: { val: s.chan[:val], rdy: s.chan[:rdy], ack: 1 - s.chan[:ack] }
  end
end
