# frozen_string_literal: true

# vendor/tlaplus-examples/AsynchInterface.tla（Specifying Systems 3章の非同期のインタフェース）を DSL で書いたもの。
# Data = {d1, d2, d3}。
Fmspec.define(:asynch_interface) do
  data = enum(:data, :d1, :d2, :d3)
  state :val, data, initial_in: data
  state :rdy, int(0..1), initial_in: 0..1
  state :ack, int(0..1), initial_in: 0..1
  initially { |s| s.ack.eq(s.rdy) }

  action :send, d: data do |s, d|
    guard s.rdy.eq(s.ack)
    update val: d, rdy: 1 - s.rdy
  end

  action :rcv do |s|
    guard s.rdy.ne(s.ack)
    update ack: 1 - s.ack
  end
end
