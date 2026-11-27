# frozen_string_literal: true

# 性能測定用のモデル（仕様書 §13）。`ruby -Ilib bench/models.rb DIR` で、各モデルのIRを DIR に書く。
require "fmspec"
require "fileutils"
require "json"

module Bench
  MODELS = {}

  # 小規模カウンタ。3つの整数を独立に増減する。状態は 80^3 = 512000。
  MODELS[:counters] = Fmspec.define(:counters) do
    %i[a b c].each { |v| state v, int(0..79), initial: 0 }
    %i[a b c].each do |v|
      action(:"inc_#{v}") do |s|
        guard s.__send__(v) < 79
        update v => s.__send__(v) + 1
      end
      action(:"dec_#{v}") do |s|
        guard s.__send__(v) > 0
        update v => s.__send__(v) - 1
      end
    end
    invariant(:bounded) { |s| s.a + s.b + s.c <= 237 }
  end

  # 引数のある操作。5つの整数に、0..9 の値を直接書く。状態は 10^5 = 100000、各状態から50の遷移。
  MODELS[:registers] = Fmspec.define(:registers) do
    %i[r0 r1 r2 r3 r4].each { |v| state v, int(0..9), initial: 0 }
    %i[r0 r1 r2 r3 r4].each do |v|
      action(:"set_#{v}", x: 0..9) { |_s, x| update v => x }
    end
    invariant(:sum) { |s| s.r0 + s.r1 + s.r2 + s.r3 + s.r4 <= 45 }
  end

  # 複数レコード。注文ごとの状態を Map に持つ。
  MODELS[:orders] = Fmspec.define(:orders) do
    order = enum(:order, :o1, :o2, :o3, :o4, :o5, :o6, :o7)
    status = enum(:status, :new, :paid, :shipped, :cancelled)
    state :orders, map_of(order, status), initial: {}
    state :paid, int(0..7), initial: 0

    action :place, o: order do |s, o|
      guard s.orders.key?(o).not_
      update orders: s.orders.put(o, :new)
    end
    action :pay, o: order do |s, o|
      guard s.orders.key?(o) & s.orders[o].eq(:new)
      update orders: s.orders.put(o, :paid), paid: s.paid + 1
    end
    action :ship, o: order do |s, o|
      guard s.orders.key?(o) & s.orders[o].eq(:paid)
      update orders: s.orders.put(o, :shipped)
    end
    action :cancel, o: order do |s, o|
      guard s.orders.key?(o) & s.orders[o].eq(:new)
      update orders: s.orders.put(o, :cancelled)
    end
    invariant(:paid_count) { |s| s.paid <= s.orders.size }
    invariant(:shipped_were_paid) { |s| s.orders.keys.all? { |o| s.orders[o].ne(:shipped) | (s.paid > 0) } }
  end

  # 集合。部分集合を作り、要素を出し入れする。
  MODELS[:sets] = Fmspec.define(:sets) do
    item = enum(:item, :i0, :i1, :i2, :i3, :i4, :i5, :i6, :i7, :i8, :i9)
    state :left, set_of(item), initial: Set[]
    state :right, set_of(item), initial: Set[]
    action :add_left, x: item do |s, x|
      guard s.right.include?(x).not_
      update left: s.left.add(x)
    end
    action :move, x: item do |s, x|
      guard s.left.include?(x)
      update left: s.left.delete(x), right: s.right.add(x)
    end
    action :drop, x: item do |s, x|
      guard s.right.include?(x)
      update right: s.right.delete(x)
    end
    invariant(:disjoint) { |s| (s.left & s.right).empty? }
  end

  # 並行するプロセス。4つのプロセスがロックなしで読み書きする。
  MODELS[:processes] = Fmspec.define(:processes) do
    state :count, int(0..9), initial: 0
    process :incr, count: 4 do
      local :seen, int(0..9), initial: 0
      step(:load) { |s| update seen: s.count }
      step(:store) { |s| update count: ite(s.seen < 9, s.seen + 1, s.seen) }
    end
    invariant(:bounded) { |s| s.count <= 9 }
  end
end

if $PROGRAM_NAME == __FILE__
  dir = ARGV.fetch(0, "tmp/bench")
  FileUtils.mkdir_p(dir)
  Bench::MODELS.each do |name, model|
    File.write(File.join(dir, "#{name}.json"), model.to_json)
    puts File.join(dir, "#{name}.json")
  end
end
