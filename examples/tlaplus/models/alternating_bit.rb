# frozen_string_literal: true

# vendor/tlaplus-examples/MCAlternatingBit.tla（Specifying Systems 14章の交互ビットプロトコル）を DSL で書いたもの。
# Data = {d1, d2}、msgQLen = ackQLen = 2。
# MCAlternatingBit.cfg は CONSTRAINT で2つのキューの長さを2以下に打ち切る。DSL では、キューに加える操作の
# guard に長さの制約を加える。
# Lose(q) は、キューの任意の位置の要素を1つ失う。キューの長さは2以下なので、失うのは先頭か末尾で、
# 内部選択した真偽値で shift と pop を選ぶ。
Fmspec.define(:alternating_bit) do
  q_len = 2
  data = enum(:data, :d1, :d2)
  bit = int(0..1)
  state :msg_q, list_of(tuple(bit, data), max: q_len), initial: []
  state :ack_q, list_of(bit, max: q_len), initial: []
  state :s_bit, bit, initial_in: 0..1
  state :s_ack, bit, initial_in: 0..1
  state :r_bit, bit, initial_in: 0..1
  state :sent, data, initial_in: data
  state :rcvd, data, initial_in: data
  initially { |s| s.s_ack.eq(s.s_bit) & s.r_bit.eq(s.s_bit) }

  action :snd_new_value, d: data do |s, d|
    guard s.s_ack.eq(s.s_bit) & (s.msg_q.size < q_len)
    update sent: d, s_bit: 1 - s.s_bit, msg_q: s.msg_q.push([1 - s.s_bit, d])
  end

  action :re_snd_msg do |s|
    guard s.s_ack.ne(s.s_bit) & (s.msg_q.size < q_len)
    update msg_q: s.msg_q.push([s.s_bit, s.sent])
  end

  action :rcv_msg do |s|
    guard s.msg_q.empty?.not_
    update msg_q: s.msg_q.shift, r_bit: s.msg_q.first[0], rcvd: s.msg_q.first[1]
  end

  action :snd_ack do |s|
    guard s.ack_q.size < q_len
    update ack_q: s.ack_q.push(s.r_bit)
  end

  action :rcv_ack do |s|
    guard s.ack_q.empty?.not_
    update ack_q: s.ack_q.shift, s_ack: s.ack_q.first
  end

  action :lose_msg do |s|
    first = choose(:first, bool)
    guard s.msg_q.empty?.not_
    update msg_q: ite(first, s.msg_q.shift, s.msg_q.pop)
  end

  action :lose_ack do |s|
    first = choose(:first, bool)
    guard s.ack_q.empty?.not_
    update ack_q: ite(first, s.ack_q.shift, s.ack_q.pop)
  end
end
