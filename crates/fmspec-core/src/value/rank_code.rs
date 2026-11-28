//! キーの型の値の符号の列から、正規順の番号（u64）を求める。
//!
//! [`rank_codes`] は、符号の列 `xs` が値 `v` の符号化（`codes(enc(v, t))`）で `v` が型 `t` に属すなら、
//! `v` の番号 `rank(v, t)`（`crate::value::keys`）を返す（[`lemma_code_rank`]）。
//! 型に属する値の符号化でない列には `None` を返す。ただし、空のOptionの中身の符号は見ない。
//! 逆に、[`unrank_codes`] は番号 `r` の値の符号化を返す。

#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{codes, enc, enc_seq, keys, keys_product, lemma_codes_concat};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{default_val, default_vals, lemma_default_vals_len, sty, width, width_sum, STy};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_enc_len, lemma_enc_seq_len, lemma_stys, member, members, stys};
use crate::value::encoding::{SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::keys::{lemma_keys_product_prefix, radix, rank, rank_seq};
#[cfg(verus_keep_ghost)]
use crate::value::limits::lemma_width_sum_prefix;
use crate::value::stype_exec::keys_exec;
use vstd::prelude::*;

verus! {

/// スカラーの符号の、閉区間での番号。
fn rank_interval_code(value: i64, min: i64, max: i64) -> (out: Option<u64>)
    ensures
        out is Some <==> min <= value <= max,
        out matches Some(rank) ==> rank as int == value as int - min as int,
{
    if value < min || value > max {
        return None;
    }
    let offset = (value as i128) - (min as i128);
    Some(offset as u64)
}

// ---- 符号の列の番号 ----

/// 型 `t` の値の符号の列 `xs` の番号。キーの型でないか、長さが幅と違うか、符号が範囲の外なら `None`。
/// Optionが空なら、中身の符号は見ない。
pub open spec fn code_rank(t: STy, xs: Seq<i64>, enums: Seq<i64>) -> Option<nat>
    decreases t, 0nat,
{
    if keys(t, enums) is None || xs.len() != width(t, enums) {
        None
    } else {
        match t {
            STy::Bool => if 0 <= xs[0] <= 1 {
                Some(xs[0] as nat)
            } else {
                None
            },
            STy::Int(lo, hi) => if lo <= xs[0] <= hi {
                Some((xs[0] - lo) as nat)
            } else {
                None
            },
            STy::Enum(id) => if 0 <= xs[0] < enums[id as int] {
                Some(xs[0] as nat)
            } else {
                None
            },
            STy::Tuple(ts) => code_rank_seq(ts, xs, enums),
            STy::Record(_, ts) => code_rank_seq(ts, xs, enums),
            STy::Option(x) => if xs[0] == 0 {
                Some(0)
            } else if xs[0] == 1 {
                match code_rank(*x, xs.subrange(1, xs.len() as int), enums) {
                    Some(r) => Some(r + 1),
                    None => None,
                }
            } else {
                None
            },
            _ => None,
        }
    }
}

/// 要素の型の列 `ts` の値の組の符号の列の番号。要素の番号を、混合基数の桁として左から順にたたむ。
pub open spec fn code_rank_seq(ts: Seq<STy>, xs: Seq<i64>, enums: Seq<i64>) -> Option<nat>
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        if xs.len() == 0 {
            Some(0)
        } else {
            None
        }
    } else if xs.len() < width(ts.last(), enums) {
        None
    } else {
        let at = xs.len() - width(ts.last(), enums);
        match (
            code_rank_seq(ts.drop_last(), xs.take(at), enums),
            code_rank(ts.last(), xs.subrange(at, xs.len() as int), enums),
        ) {
            (Some(p), Some(d)) => Some((p * radix(ts.last(), enums) + d) as nat),
            _ => None,
        }
    }
}

/// 番号は値の数より小さい。
pub proof fn lemma_code_rank_bound(t: STy, xs: Seq<i64>, enums: Seq<i64>)
    ensures
        code_rank(t, xs, enums) matches Some(r) ==> keys(t, enums) is Some && r < keys(t, enums)->0,
    decreases t, 0nat,
{
    if code_rank(t, xs, enums) is Some {
        match t {
            STy::Tuple(ts) => lemma_code_rank_seq_bound(ts, xs, enums),
            STy::Record(_, ts) => lemma_code_rank_seq_bound(ts, xs, enums),
            STy::Option(x) => if xs[0] == 1 {
                lemma_code_rank_bound(*x, xs.subrange(1, xs.len() as int), enums);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_code_rank_seq_bound(ts: Seq<STy>, xs: Seq<i64>, enums: Seq<i64>)
    ensures
        keys_product(ts, enums) is Some ==> (code_rank_seq(ts, xs, enums) matches Some(r) ==> r < keys_product(
            ts,
            enums,
        )->0),
    decreases ts, 1nat,
{
    if ts.len() > 0 && keys_product(ts, enums) is Some && code_rank_seq(ts, xs, enums) is Some {
        let at = xs.len() - width(ts.last(), enums);
        lemma_code_rank_seq_bound(ts.drop_last(), xs.take(at), enums);
        lemma_code_rank_bound(ts.last(), xs.subrange(at, xs.len() as int), enums);
        let p = code_rank_seq(ts.drop_last(), xs.take(at), enums)->0 as int;
        let d = code_rank(ts.last(), xs.subrange(at, xs.len() as int), enums)->0 as int;
        let n = keys_product(ts.drop_last(), enums)->0 as int;
        let k = keys(ts.last(), enums)->0 as int;
        assert(p * k + d < n * k) by (nonlinear_arith)
            requires
                0 <= p < n,
                0 <= d < k,
        ;
    }
}

/// キーの型 `t` の値の符号の列の幅。`None` なら、幅は `usize` に収まらない。
fn key_width(t: &SType, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        keys(sty(*t), enums@) is Some,
    ensures
        match r {
            Some(w) => w == width(sty(*t), enums@),
            None => width(sty(*t), enums@) > usize::MAX,
        },
    decreases t, 1nat,
{
    match t {
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            key_width_sum(t, ts, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            key_width_sum(t, ts, enums)
        },
        SType::Option(x) => match key_width(x, enums) {
            Some(w) => w.checked_add(1),
            None => None,
        },
        _ => Some(1),
    }
}

fn key_width_sum(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        decreases_to!(*_parent => *ts),
        keys_product(stys(ts@), enums@) is Some,
    ensures
        match r {
            Some(w) => w == width_sum(stys(ts@), enums@),
            None => width_sum(stys(ts@), enums@) > usize::MAX,
        },
    decreases _parent, 0nat,
{
    let ghost all = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
    }
    let mut acc: usize = 0;
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            keys_product(all, enums@) is Some,
            acc == width_sum(all.take(i as int), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            lemma_keys_product_prefix(all, i as int, enums@);
            assert(all.take(i + 1).drop_last() =~= all.take(i as int));
            assert(all.take(i + 1).last() == all[i as int]);
            lemma_width_sum_prefix(all, enums@, i + 1);
        }
        let w = match key_width(&ts[i], enums) {
            Some(w) => w,
            None => return None,
        };
        acc = match acc.checked_add(w) {
            Some(a) => a,
            None => return None,
        };
        i = i + 1;
    }
    proof {
        assert(all.take(i as int) =~= all);
    }
    Some(acc)
}

/// キーの型の値の符号の列 `xs` の番号。型に属する値の符号化でなければ `None`（[`code_rank`]）。
/// `enums` は各列挙型のラベルの数。
pub fn rank_codes(t: &SType, enums: &Vec<i64>, xs: &Vec<i64>) -> (r: Option<u64>)
    ensures
        match code_rank(sty(*t), xs@, enums@) {
            Some(n) => r == Some(n as u64),
            None => r is None,
        },
{
    if keys_exec(t, enums).is_none() {
        return None;
    }
    match key_width(t, enums) {
        Some(w) if w == xs.len() => {
            proof {
                assert(xs@.subrange(0, w as int) =~= xs@);
            }
            rank_at(t, enums, xs, 0)
        },
        _ => None,
    }
}

/// `xs` の位置 `pos` からの型 `t` の値の符号の番号。
fn rank_at(t: &SType, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<u64>)
    requires
        keys(sty(*t), enums@) is Some,
        pos + width(sty(*t), enums@) <= xs.len(),
    ensures
        match code_rank(sty(*t), xs@.subrange(pos as int, pos + width(sty(*t), enums@)), enums@) {
            Some(n) => r == Some(n as u64),
            None => r is None,
        },
    decreases t, 1nat,
{
    let ghost s = xs@.subrange(pos as int, pos + width(sty(*t), enums@));
    match t {
        SType::Bool => {
            let x = xs[pos];
            if 0 <= x && x <= 1 {
                Some(x as u64)
            } else {
                None
            }
        },
        SType::Int(lo, hi) => rank_interval_code(xs[pos], *lo, *hi),
        SType::Enum(id) => {
            let x = xs[pos];
            if 0 <= x && x < enums[*id] {
                Some(x as u64)
            } else {
                None
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            rank_seq_at(t, ts, enums, xs, pos)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            rank_seq_at(t, ts, enums, xs, pos)
        },
        SType::Option(x) => {
            let tag = xs[pos];
            if tag == 0 {
                Some(0)
            } else if tag == 1 {
                proof {
                    assert(s.subrange(1, s.len() as int) =~= xs@.subrange(pos + 1, pos + 1 + width(sty(**x), enums@)));
                    lemma_code_rank_bound(sty(**x), s.subrange(1, s.len() as int), enums@);
                }
                match rank_at(x, enums, xs, pos + 1) {
                    Some(n) => Some(n + 1),
                    None => None,
                }
            } else {
                None
            }
        },
        _ => None,
    }
}

fn rank_seq_at(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<u64>)
    requires
        decreases_to!(*_parent => *ts),
        keys_product(stys(ts@), enums@) is Some,
        pos + width_sum(stys(ts@), enums@) <= xs.len(),
    ensures
        match code_rank_seq(stys(ts@), xs@.subrange(pos as int, pos + width_sum(stys(ts@), enums@)), enums@) {
            Some(n) => r == Some(n as u64),
            None => r is None,
        },
    decreases _parent, 0nat,
{
    let ghost all = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
        assert(xs@.subrange(pos as int, pos as int) =~= Seq::<i64>::empty());
    }
    let mut acc: Option<u64> = Some(0);
    let mut cur = pos;
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            keys_product(all, enums@) is Some,
            pos + width_sum(all, enums@) <= xs.len(),
            cur == pos + width_sum(all.take(i as int), enums@),
            match code_rank_seq(all.take(i as int), xs@.subrange(pos as int, cur as int), enums@) {
                Some(n) => acc == Some(n as u64),
                None => acc is None,
            },
        decreases ts.len() - i,
    {
        let ghost pre = all.take(i as int);
        let ghost ti = all[i as int];
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            lemma_keys_product_prefix(all, i as int, enums@);
            lemma_keys_product_prefix(all, i + 1, enums@);
            assert(all.take(i + 1).drop_last() =~= pre);
            assert(all.take(i + 1).last() == ti);
            lemma_width_sum_prefix(all, enums@, i + 1);
        }
        let k = match keys_exec(&ts[i], enums) {
            Some(k) => k,
            None => return None,
        };
        let w = match key_width(&ts[i], enums) {
            Some(w) => w,
            None => return None,
        };
        let d = rank_at(&ts[i], enums, xs, cur);
        let ghost s1 = xs@.subrange(pos as int, cur + w);
        proof {
            let at = s1.len() - w;
            assert(s1.take(at) =~= xs@.subrange(pos as int, cur as int));
            assert(s1.subrange(at, s1.len() as int) =~= xs@.subrange(cur as int, cur + w));
            lemma_code_rank_seq_bound(pre, xs@.subrange(pos as int, cur as int), enums@);
            lemma_code_rank_bound(ti, xs@.subrange(cur as int, cur + w), enums@);
            assert(keys_product(all.take(i + 1), enums@)->0 <= 4096);
        }
        acc = match (acc, d) {
            (Some(p), Some(d)) => {
                proof {
                    let n = keys_product(pre, enums@)->0 as int;
                    assert(p as int * k as int + d as int <= 4096 * 4096) by (nonlinear_arith)
                        requires
                            p < n,
                            d < k,
                            n * k <= 4096,
                            k <= 4096,
                    ;
                }
                Some(p * k + d)
            },
            _ => None,
        };
        cur = cur + w;
        i = i + 1;
    }
    proof {
        assert(all.take(i as int) =~= all);
    }
    acc
}

/// 型に属する値の符号化の番号は、値の番号である。
pub proof fn lemma_code_rank(v: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v, t, enums),
        keys(t, enums) is Some,
    ensures
        code_rank(t, codes(enc(v, t, enums)), enums) == Some(rank(v, t, enums) as nat),
    decreases t, 0nat,
{
    lemma_enc_len(v, t, enums);
    crate::value::keys::lemma_rank_in_domain(v, t, enums);
    let xs = codes(enc(v, t, enums));
    match (t, v) {
        (STy::Tuple(ts), SVal::Tuple(vs)) => lemma_code_rank_seq(vs, ts, enums),
        (STy::Record(_, ts), SVal::Tuple(vs)) => lemma_code_rank_seq(vs, ts, enums),
        (STy::Option(x), SVal::Some(w)) => {
            lemma_codes_concat(seq![Value::Bool(true)], enc(*w, *x, enums));
            assert(xs.subrange(1, xs.len() as int) =~= codes(enc(*w, *x, enums)));
            lemma_code_rank(*w, *x, enums);
        },
        (STy::Option(x), SVal::None) => {
            lemma_codes_concat(seq![Value::Bool(false)], enc(crate::value::encoding::default_val(*x, enums), *x, enums));
        },
        _ => {},
    }
}

pub proof fn lemma_code_rank_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
        keys_product(ts, enums) is Some,
    ensures
        code_rank_seq(ts, codes(enc_seq(vs, ts, enums)), enums) == Some(rank_seq(vs, ts, enums) as nat),
    decreases ts, 1nat,
{
    crate::value::keys::lemma_rank_seq_in_product(vs, ts, enums);
    if ts.len() == 0 {
        assert(codes(enc_seq(vs, ts, enums)) =~= Seq::<i64>::empty());
    } else {
        let pre = vs.drop_last();
        let a = enc_seq(pre, ts.drop_last(), enums);
        let b = enc(vs.last(), ts.last(), enums);
        lemma_keys_product_prefix(ts, ts.len() - 1, enums);
        assert(ts.take(ts.len() - 1) =~= ts.drop_last());
        lemma_enc_seq_len(pre, ts.drop_last(), enums);
        lemma_enc_len(vs.last(), ts.last(), enums);
        lemma_codes_concat(a, b);
        let xs = codes(a + b);
        let at = xs.len() - width(ts.last(), enums);
        assert(xs.take(at) =~= codes(a));
        assert(xs.subrange(at, xs.len() as int) =~= codes(b));
        lemma_code_rank_seq(pre, ts.drop_last(), enums);
        lemma_code_rank(vs.last(), ts.last(), enums);
        crate::value::keys::lemma_rank_seq_in_product(pre, ts.drop_last(), enums);
        crate::value::keys::lemma_rank_in_domain(vs.last(), ts.last(), enums);
    }
}

// ---- 番号から符号の列へ ----

/// キーの型 `t` の既定値の符号を `out` に加える。
fn push_default_codes(t: &SType, enums: &Vec<i64>, out: &mut Vec<i64>)
    requires
        keys(sty(*t), enums@) is Some,
    ensures
        final(out)@ == old(out)@ + codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)),
    decreases t, 1nat,
{
    let ghost before = out@;
    match t {
        SType::Bool => {
            out.push(0);
            proof {
                assert(out@ =~= before + codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Int(lo, _) => {
            out.push(*lo);
            proof {
                assert(out@ =~= before + codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Enum(_) => {
            out.push(0);
            proof {
                assert(out@ =~= before + codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            push_default_seq(t, ts, enums, out);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            push_default_seq(t, ts, enums, out);
        },
        SType::Option(x) => {
            out.push(0);
            let ghost mid = out@;
            push_default_codes(x, enums, out);
            proof {
                let d = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                lemma_codes_concat(seq![Value::Bool(false)], d);
                assert(codes(seq![Value::Bool(false)]) =~= seq![0i64]);
                assert(out@ =~= before + codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        _ => {},
    }
}

fn push_default_seq(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, out: &mut Vec<i64>)
    requires
        decreases_to!(*_parent => *ts),
        keys_product(stys(ts@), enums@) is Some,
    ensures
        final(out)@ == old(out)@ + codes(enc_seq(default_vals(stys(ts@), enums@), stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let ghost all = stys(ts@);
    let ghost before = out@;
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
        assert(codes(enc_seq(default_vals(all.take(0), enums@), all.take(0), enums@)) =~= Seq::<i64>::empty());
        assert(out@ =~= before + Seq::<i64>::empty());
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            keys_product(all, enums@) is Some,
            out@ == before + codes(enc_seq(default_vals(all.take(i as int), enums@), all.take(i as int), enums@)),
        decreases ts.len() - i,
    {
        let ghost mid = out@;
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            lemma_keys_product_prefix(all, i as int, enums@);
        }
        push_default_codes(&ts[i], enums, out);
        proof {
            let pre = all.take(i as int);
            let nx = all.take(i + 1);
            assert(nx.drop_last() =~= pre);
            assert(nx.last() == all[i as int]);
            lemma_default_vals_len(nx, enums@);
            let dv = default_vals(nx, enums@);
            assert(dv.drop_last() == default_vals(pre, enums@));
            assert(dv.last() == default_val(all[i as int], enums@));
            let a = enc_seq(default_vals(pre, enums@), pre, enums@);
            let b = enc(default_val(all[i as int], enums@), all[i as int], enums@);
            assert(enc_seq(dv, nx, enums@) == a + b);
            lemma_codes_concat(a, b);
            assert(out@ =~= before + codes(enc_seq(dv, nx, enums@)));
        }
        i = i + 1;
    }
    proof {
        assert(all.take(i as int) =~= all);
    }
}

/// キーの型の、正規順で `r` 番目の値の符号の列。`r` が値の数以上なら `None`。
/// `enums` は各列挙型のラベルの数。
pub fn unrank_codes(t: &SType, enums: &Vec<i64>, r: u64) -> (out: Option<Vec<i64>>)
    ensures
        out is Some <==> (keys(sty(*t), enums@) matches Some(k) && r < k),
        out matches Some(xs) ==> exists|v: SVal|
            member(v, sty(*t), enums@) && rank(v, sty(*t), enums@) == r && #[trigger] codes(enc(v, sty(*t), enums@))
                == xs@,
{
    match keys_exec(t, enums) {
        Some(k) if r < k => {
            let mut out = Vec::new();
            let Ghost(v) = unrank_at(t, enums, r, &mut out);
            proof {
                assert(out@ =~= codes(enc(v, sty(*t), enums@)));
            }
            Some(out)
        },
        _ => None,
    }
}

/// 正規順で `r` 番目の値の符号を `out` に加える。その値を返す。
fn unrank_at(t: &SType, enums: &Vec<i64>, r: u64, out: &mut Vec<i64>) -> (v: Ghost<SVal>)
    requires
        keys(sty(*t), enums@) matches Some(k) && r < k,
    ensures
        member(v@, sty(*t), enums@),
        rank(v@, sty(*t), enums@) == r,
        final(out)@ == old(out)@ + codes(enc(v@, sty(*t), enums@)),
    decreases t, 1nat, 0nat,
{
    let ghost before = out@;
    match t {
        SType::Bool => {
            out.push(r as i64);
            let ghost v = SVal::Bool(r == 1);
            proof {
                assert(out@ =~= before + codes(enc(v, sty(*t), enums@)));
            }
            Ghost(v)
        },
        SType::Int(lo, _) => {
            let x = *lo + r as i64;
            out.push(x);
            let ghost v = SVal::Int(x);
            proof {
                assert(out@ =~= before + codes(enc(v, sty(*t), enums@)));
            }
            Ghost(v)
        },
        SType::Enum(_id) => {
            out.push(r as i64);
            let ghost v = SVal::Enum(*_id, r as i64);
            proof {
                assert(out@ =~= before + codes(enc(v, sty(*t), enums@)));
            }
            Ghost(v)
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_stys(ts@);
                assert(stys(ts@).take(ts.len() as int) =~= stys(ts@));
            }
            let Ghost(vs) = unrank_seq_at(t, ts, ts.len(), enums, r, out);
            Ghost(SVal::Tuple(vs))
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_stys(ts@);
                assert(stys(ts@).take(ts.len() as int) =~= stys(ts@));
            }
            let Ghost(vs) = unrank_seq_at(t, ts, ts.len(), enums, r, out);
            Ghost(SVal::Tuple(vs))
        },
        SType::Option(x) => {
            if r == 0 {
                out.push(0);
                push_default_codes(x, enums, out);
                let ghost v = SVal::None;
                proof {
                    let d = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                    lemma_codes_concat(seq![Value::Bool(false)], d);
                    assert(codes(seq![Value::Bool(false)]) =~= seq![0i64]);
                    assert(out@ =~= before + codes(enc(v, sty(*t), enums@)));
                }
                Ghost(v)
            } else {
                out.push(1);
                let Ghost(w) = unrank_at(x, enums, r - 1, out);
                let ghost v = SVal::Some(Box::new(w));
                proof {
                    lemma_codes_concat(seq![Value::Bool(true)], enc(w, sty(**x), enums@));
                    assert(codes(seq![Value::Bool(true)]) =~= seq![1i64]);
                    assert(out@ =~= before + codes(enc(v, sty(*t), enums@)));
                }
                Ghost(v)
            }
        },
        _ => Ghost(SVal::None),
    }
}

/// 先頭の `n` 個の要素の型の、`r` 番目の値の組の符号を `out` に加える。その組を返す。
fn unrank_seq_at(
    _parent: &SType,
    ts: &Vec<SType>,
    n: usize,
    enums: &Vec<i64>,
    r: u64,
    out: &mut Vec<i64>,
) -> (vs: Ghost<Seq<SVal>>)
    requires
        decreases_to!(*_parent => *ts),
        n <= ts.len(),
        keys_product(stys(ts@).take(n as int), enums@) matches Some(k) && r < k,
    ensures
        members(vs@, stys(ts@).take(n as int), enums@),
        rank_seq(vs@, stys(ts@).take(n as int), enums@) == r,
        final(out)@ == old(out)@ + codes(enc_seq(vs@, stys(ts@).take(n as int), enums@)),
    decreases _parent, 0nat, n,
{
    let ghost all = stys(ts@);
    let ghost us = all.take(n as int);
    let ghost before = out@;
    proof {
        lemma_stys(ts@);
    }
    if n == 0 {
        proof {
            assert(out@ =~= before + codes(enc_seq(Seq::<SVal>::empty(), us, enums@)));
        }
        return Ghost(Seq::<SVal>::empty());
    }
    let ghost pre = all.take(n - 1);
    proof {
        vstd::std_specs::vec::axiom_vec_index_decreases(*ts, n - 1);
        assert(us.drop_last() =~= pre);
        assert(us.last() == all[n - 1]);
        assert(all[n - 1] == sty(ts@[n - 1]));
    }
    let k = keys_exec(&ts[n - 1], enums).unwrap();
    proof {
        let p = keys_product(pre, enums@)->0 as int;
        assert(r < p * k);
        assert(k > 0 && (r as int) / (k as int) < p) by (nonlinear_arith)
            requires
                0 <= r < p * k,
                p >= 0,
                k >= 0,
        {
            assert(k > 0) by (nonlinear_arith)
                requires
                    0 <= r < p * k,
                    p >= 0,
                    k >= 0,
            ;
            if (r as int) / (k as int) >= p {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r as int, k as int);
                vstd::arithmetic::mul::lemma_mul_inequality(p, (r as int) / (k as int), k as int);
                assert(p * k == k * p) by (nonlinear_arith);
            }
        }
    }
    let Ghost(head) = unrank_seq_at(_parent, ts, n - 1, enums, r / k, out);
    let ghost mid = out@;
    let Ghost(last) = unrank_at(&ts[n - 1], enums, r % k, out);
    let ghost vs = head.push(last);
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r as int, k as int);
        assert(vs.drop_last() =~= head);
        assert(vs.last() == last);
        crate::value::keys::lemma_rank_seq_in_product(head, pre, enums@);
        let a = enc_seq(head, pre, enums@);
        let b = enc(last, all[n - 1], enums@);
        lemma_codes_concat(a, b);
        assert(enc_seq(vs, us, enums@) == a + b);
        assert(rank_seq(vs, us, enums@) == (r / k) as int * k as int + (r % k) as int);
        assert(out@ =~= before + codes(enc_seq(vs, us, enums@)));
    }
    Ghost(vs)
}

} // verus!
