# frozen_string_literal: true

# vendor/tlaplus-examples/MCInternalMemory.tla（Specifying Systems 5章のメモリの内部）を DSL で書いたもの。
# Proc = {p1, p2}、Adr = {a1, a2, a3}、Val = {v1, v2}。
# buf の値は、読み出しの要求 [op |-> "Rd", adr]、書き込みの要求 [op |-> "Wr", adr, val]、値、NoVal のどれかである。
# これを、種類 op と、使う欄だけに値のある adr と val のレコードで表す。使わない欄はいつも値を持たないので、
# この対応は一対一である。memInt は、MCSend と MCReply のとおり、最後に送ったプロセスと値の組である。
Fmspec.define(:internal_memory) do
  proc_t = enum(:proc, :p1, :p2)
  adr = enum(:adr, :a1, :a2, :a3)
  val = enum(:val, :v1, :v2)
  kind = enum(:kind, :rd, :wr, :value, :no_val)
  ctl = enum(:ctl, :rdy, :busy, :done)
  item = record(op: kind, adr: option(adr), val: option(val))
  no_val = { op: :no_val, adr: nil, val: nil }
  memories = val.labels.repeated_permutation(adr.labels.length).map { |vs| adr.labels.zip(vs).to_h }
  state :mem, map_of(adr, val), initial_in: memories
  state :ctl, map_of(proc_t, ctl), initial: proc_t.labels.to_h { |p| [p, :rdy] }
  state :buf, map_of(proc_t, item), initial: proc_t.labels.to_h { |p| [p, no_val] }
  # MCInitMemInt は <<CHOOSE p \in Proc : TRUE, NoVal>> で、TLC は p1 を選ぶ。
  state :mem_int, tuple(proc_t, item), initial: [:p1, no_val]

  action :req, p: proc_t, write: bool, a: adr, v: val do |s, p, write, a, v|
    guard s.ctl[p].eq(:rdy)
    request = { op: ite(write, kind[:wr], kind[:rd]), adr: some(a), val: ite(write, some(v), none(val)) }
    update mem_int: [p, request], buf: s.buf.put(p, request), ctl: s.ctl.put(p, :busy)
  end

  action :do, p: proc_t do |s, p|
    guard s.ctl[p].eq(:busy)
    b = s.buf[p]
    wr = b[:op].eq(:wr)
    update mem: ite(wr, s.mem.put(b[:adr].unwrap, b[:val].unwrap), s.mem),
           buf: s.buf.put(p, ite(wr, item.value(no_val), { op: :value, adr: nil, val: some(s.mem[b[:adr].unwrap]) })),
           ctl: s.ctl.put(p, :done)
  end

  action :rsp, p: proc_t do |s, p|
    guard s.ctl[p].eq(:done)
    update mem_int: [p, s.buf[p]], ctl: s.ctl.put(p, :rdy)
  end
end
