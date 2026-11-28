//! 値の木（[`Val`]）と、符号の列の相互の変換。
//!
//! [`Val`] は、`fmspec-ir` がJSONから読んだ値の実行時の表現である。仕様の値（`SVal`）との対応は [`sval_of`] で定める。
//! SetとMapは要素とキーを任意の順に並べた列で持ち、[`sval_of`] は番号（`rank`）の位置に置いた正規形にする。
//! Enumはラベルの添字だけを持つ（列挙型は型から決まる）。Recordの値はフィールドを宣言の順に並べたTupleで持つ。
//!
//! - [`encode_val`]：値の木を符号の列にする。結果は `codes(enc(sval_of(v, t), t))` である。
//! - [`decode_val`]：符号の列を値の木にする。結果 `v` について、元の列は `codes(enc(sval_of(v, t), t))` である。
//!
//! 整数の範囲は検査しない（判定ゲートが状態の型を検査する）。ただしSetの要素とMapのキーは番号を付けるので、型に属さなければ失敗する。

#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
use crate::value::default_codes::{append, default_codes};
use crate::value::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{codes, default_val, enc, enc_items, enc_repeat, enc_rows, enc_seq};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{keys, keys_or_zero, keys_product, lemma_codes_concat, lemma_default_len};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_stys, member, members, sty, stys, width};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{width_sum, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::keys::{lemma_keys_product_prefix, rank, rank_seq};
#[cfg(verus_keep_ghost)]
use crate::value::limits::lemma_width_sum_prefix;
use crate::value::map_encoding::encode_map_rows;
#[cfg(verus_keep_ghost)]
use crate::value::map_encoding::{prefix_fits, rows_encode};
#[cfg(verus_keep_ghost)]
use crate::value::rank_code::lemma_code_rank_bound;
#[cfg(verus_keep_ghost)]
use crate::value::rank_code::{code_rank, code_rank_seq};
use crate::value::rank_code::{rank_codes, unrank_codes};
use crate::value::stype_exec::{keys_exec, keys_or_zero_exec, stype_width};
use vstd::prelude::*;

verus! {

/// 値の木。
pub enum Val {
    Bool(bool),
    Int(i64),
    /// ラベルの添字。
    Enum(i64),
    /// TupleとRecordの値。
    Tuple(Vec<Val>),
    None,
    Some(Box<Val>),
    /// 要素の列。順は問わない。
    Set(Vec<Val>),
    /// キーの列と、対応する値の列。順は問わない。
    Map(Vec<Val>, Vec<Val>),
    List(Vec<Val>),
}

// ---- 仕様の値との対応 ----

/// 型 `t` の場所にある値の木 `v` の、仕様の値。型に合わない木は `SVal::None` にする。
pub open spec fn sval_of(v: Val, t: STy, enums: Seq<i64>) -> SVal
    decreases t, 1nat, 0nat,
{
    match (t, v) {
        (STy::Bool, Val::Bool(b)) => SVal::Bool(b),
        (STy::Int(_, _), Val::Int(x)) => SVal::Int(x),
        (STy::Enum(id), Val::Enum(k)) => SVal::Enum(id, k),
        (STy::Tuple(ts), Val::Tuple(vs)) => SVal::Tuple(svals_of(vs@, ts, enums)),
        (STy::Record(_, ts), Val::Tuple(vs)) => SVal::Tuple(svals_of(vs@, ts, enums)),
        (STy::Option(_), Val::None) => SVal::None,
        (STy::Option(x), Val::Some(w)) => SVal::Some(Box::new(sval_of(*w, *x, enums))),
        (STy::Set(_), Val::Set(es)) => SVal::Set(set_bits(es@, t, enums)),
        (STy::Map(_, _), Val::Map(ks, vs)) => SVal::Map(map_rows(ks@, vs@, t, enums)),
        (STy::List(_, _), Val::List(items)) => SVal::List(list_items(items@, t, enums)),
        _ => SVal::None,
    }
}

/// 値の木の列の、要素の型の列 `ts` での仕様の値の列。
pub open spec fn svals_of(vs: Seq<Val>, ts: Seq<STy>, enums: Seq<i64>) -> Seq<SVal>
    decreases ts, 0nat, 0nat,
{
    if ts.len() == 0 || vs.len() == 0 {
        Seq::empty()
    } else {
        svals_of(vs.drop_last(), ts.drop_last(), enums).push(sval_of(vs.last(), ts.last(), enums))
    }
}

/// Setの型 `t` の要素の列の、含むかどうかの列。要素の番号の位置を真にする。
pub open spec fn set_bits(es: Seq<Val>, t: STy, enums: Seq<i64>) -> Seq<bool>
    decreases t, 0nat, es.len(),
{
    match t {
        STy::Set(e) => if es.len() == 0 {
            Seq::new(keys_or_zero(*e, enums), |_i: int| false)
        } else {
            set_bits(es.drop_last(), t, enums).update(rank(sval_of(es.last(), *e, enums), *e, enums), true)
        },
        _ => Seq::empty(),
    }
}

/// Mapの型 `t` のキーの列と値の列の、行の列。キーの番号の位置に値を置く。
pub open spec fn map_rows(ks: Seq<Val>, vs: Seq<Val>, t: STy, enums: Seq<i64>) -> Seq<Option<SVal>>
    decreases t, 0nat, ks.len(),
{
    match t {
        STy::Map(k, x) => if ks.len() == 0 {
            Seq::new(keys_or_zero(*k, enums), |_i: int| None)
        } else {
            map_rows(ks.drop_last(), vs.drop_last(), t, enums).update(
                rank(sval_of(ks.last(), *k, enums), *k, enums),
                Some(sval_of(vs.last(), *x, enums)),
            )
        },
        _ => Seq::empty(),
    }
}

/// Listの型 `t` の要素の列の、仕様の値の列。
pub open spec fn list_items(items: Seq<Val>, t: STy, enums: Seq<i64>) -> Seq<SVal>
    decreases t, 0nat, items.len(),
{
    match t {
        STy::List(e, _) => if items.len() == 0 {
            Seq::empty()
        } else {
            list_items(items.drop_last(), t, enums).push(sval_of(items.last(), *e, enums))
        },
        _ => Seq::empty(),
    }
}

/// キーの型の値の形が型に合う（整数とラベルの範囲は問わない）。
pub open spec fn shaped(v: SVal, t: STy) -> bool
    decreases t, 0nat,
{
    match t {
        STy::Bool => v is Bool,
        STy::Int(_, _) => v is Int,
        STy::Enum(id) => v is Enum && v->Enum_0 == id,
        STy::Tuple(ts) => v is Tuple && shaped_seq(v->Tuple_0, ts),
        STy::Record(_, ts) => v is Tuple && shaped_seq(v->Tuple_0, ts),
        STy::Option(x) => v is None || (v is Some && shaped(*v->Some_0, *x)),
        _ => true,
    }
}

pub open spec fn shaped_seq(vs: Seq<SVal>, ts: Seq<STy>) -> bool
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        vs.len() == 0
    } else {
        vs.len() == ts.len() && shaped_seq(vs.drop_last(), ts.drop_last()) && shaped(vs.last(), ts.last())
    }
}

// ---- 補題 ----

pub proof fn lemma_svals_len(vs: Seq<Val>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        vs.len() == ts.len(),
    ensures
        svals_of(vs, ts, enums).len() == ts.len(),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_svals_len(vs.drop_last(), ts.drop_last(), enums);
    }
}

/// 形の合うキーの型の値の符号化の長さは、型の幅である。
proof fn lemma_shaped_len(v: SVal, t: STy, enums: Seq<i64>)
    requires
        shaped(v, t),
        keys(t, enums) is Some,
    ensures
        enc(v, t, enums).len() == width(t, enums),
    decreases t, 0nat,
{
    match t {
        STy::Tuple(ts) => lemma_shaped_seq_len(v->Tuple_0, ts, enums),
        STy::Record(_, ts) => lemma_shaped_seq_len(v->Tuple_0, ts, enums),
        STy::Option(x) => match v {
            SVal::Some(w) => lemma_shaped_len(*w, *x, enums),
            _ => lemma_default_len(*x, enums),
        },
        _ => {},
    }
}

proof fn lemma_shaped_seq_len(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        shaped_seq(vs, ts),
        keys_product(ts, enums) is Some,
    ensures
        enc_seq(vs, ts, enums).len() == width_sum(ts, enums),
    decreases ts, 1nat,
{
    if ts.len() > 0 {
        lemma_keys_product_prefix(ts, ts.len() - 1, enums);
        assert(ts.take(ts.len() - 1) =~= ts.drop_last());
        lemma_shaped_seq_len(vs.drop_last(), ts.drop_last(), enums);
        lemma_shaped_len(vs.last(), ts.last(), enums);
    }
}

/// 形の合う値の符号化に番号が付くなら、値は型に属し、その番号は値の番号である。
pub proof fn lemma_code_rank_shaped(v: SVal, t: STy, enums: Seq<i64>)
    requires
        shaped(v, t),
        keys(t, enums) is Some,
        code_rank(t, codes(enc(v, t, enums)), enums) is Some,
    ensures
        member(v, t, enums),
        code_rank(t, codes(enc(v, t, enums)), enums) == Some(rank(v, t, enums) as nat),
    decreases t, 0nat,
{
    let xs = codes(enc(v, t, enums));
    lemma_shaped_len(v, t, enums);
    match t {
        STy::Tuple(ts) => {
            lemma_code_rank_shaped_seq(v->Tuple_0, ts, enums);
            crate::value::keys::lemma_rank_seq_in_product(v->Tuple_0, ts, enums);
            assert(code_rank(t, codes(enc(v, t, enums)), enums) == Some(rank(v, t, enums) as nat));
        },
        STy::Record(_, ts) => {
            lemma_code_rank_shaped_seq(v->Tuple_0, ts, enums);
            crate::value::keys::lemma_rank_seq_in_product(v->Tuple_0, ts, enums);
            assert(code_rank(t, codes(enc(v, t, enums)), enums) == Some(rank(v, t, enums) as nat));
        },
        STy::Option(x) => match v {
            SVal::Some(w) => {
                lemma_codes_concat(seq![Value::Bool(true)], enc(*w, *x, enums));
                assert(xs.subrange(1, xs.len() as int) =~= codes(enc(*w, *x, enums)));
                lemma_code_rank_shaped(*w, *x, enums);
                crate::value::keys::lemma_rank_in_domain(*w, *x, enums);
                assert(xs[0] == 1);
            },
            _ => {
                lemma_codes_concat(seq![Value::Bool(false)], enc(default_val(*x, enums), *x, enums));
                assert(xs[0] == 0);
            },
        },
        _ => {
            assert(xs[0] == crate::kernel::eval::code_of(enc(v, t, enums)[0]));
        },
    }
}

proof fn lemma_code_rank_shaped_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        shaped_seq(vs, ts),
        keys_product(ts, enums) is Some,
        code_rank_seq(ts, codes(enc_seq(vs, ts, enums)), enums) is Some,
    ensures
        members(vs, ts, enums),
        code_rank_seq(ts, codes(enc_seq(vs, ts, enums)), enums) == Some(rank_seq(vs, ts, enums) as nat),
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        assert(codes(enc_seq(vs, ts, enums)) =~= Seq::<i64>::empty());
    } else {
        let pre = vs.drop_last();
        let a = enc_seq(pre, ts.drop_last(), enums);
        let b = enc(vs.last(), ts.last(), enums);
        lemma_keys_product_prefix(ts, ts.len() - 1, enums);
        assert(ts.take(ts.len() - 1) =~= ts.drop_last());
        lemma_keys_product_prefix(ts, ts.len() - 1, enums);
        lemma_shaped_seq_len(pre, ts.drop_last(), enums);
        lemma_shaped_len(vs.last(), ts.last(), enums);
        lemma_codes_concat(a, b);
        let xs = codes(a + b);
        let at = xs.len() - width(ts.last(), enums);
        assert(xs.take(at) =~= codes(a));
        assert(xs.subrange(at, xs.len() as int) =~= codes(b));
        lemma_code_rank_shaped_seq(pre, ts.drop_last(), enums);
        lemma_code_rank_shaped(vs.last(), ts.last(), enums);
        assert(pre.push(vs.last()) =~= vs);
        crate::value::keys::lemma_rank_seq_in_product(pre, ts.drop_last(), enums);
        crate::value::keys::lemma_rank_in_domain(vs.last(), ts.last(), enums);
    }
}

pub proof fn lemma_list_items_len(items: Seq<Val>, t: STy, enums: Seq<i64>)
    requires
        t is List,
    ensures
        list_items(items, t, enums).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_list_items_len(items.drop_last(), t, enums);
    }
}

/// 含むかどうかの列の符号。
pub open spec fn bit_codes(bs: Seq<bool>) -> Seq<i64> {
    Seq::new(bs.len(), |j: int| if bs[j] { 1i64 } else { 0i64 })
}

// ---- 値の木から符号の列へ ----

/// 値の木を、型 `t` の符号の列にする。木の形が型に合わないか、Setの要素やMapのキーが型に属さないか重複していれば `None`。
/// `enums` は各列挙型のラベルの数。
pub fn encode_val(t: &SType, enums: &Vec<i64>, v: &Val) -> (r: Option<Vec<i64>>)
    ensures
        r matches Some(xs) ==> xs@ == codes(enc(sval_of(*v, sty(*t), enums@), sty(*t), enums@)),
{
    let mut out = Vec::new();
    if push_val(t, enums, v, &mut out) {
        proof {
            assert(out@ =~= codes(enc(sval_of(*v, sty(*t), enums@), sty(*t), enums@)));
        }
        Some(out)
    } else {
        None
    }
}

/// 値の木の符号を `out` に加える。失敗すれば `false`（`out` は途中まで書かれている）。
fn push_val(t: &SType, enums: &Vec<i64>, v: &Val, out: &mut Vec<i64>) -> (ok: bool)
    ensures
        ok ==> final(out)@ == old(out)@ + codes(enc(sval_of(*v, sty(*t), enums@), sty(*t), enums@)),
        ok ==> shaped(sval_of(*v, sty(*t), enums@), sty(*t)),
    decreases v, 1nat,
{
    let ghost start = out@;
    let ghost tt = sty(*t);
    match (t, v) {
        (SType::Bool, Val::Bool(b)) => {
            out.push(if *b { 1 } else { 0 });
            proof {
                assert(out@ =~= start + codes(enc(sval_of(*v, tt, enums@), tt, enums@)));
            }
            true
        },
        (SType::Int(_, _), Val::Int(x)) => {
            out.push(*x);
            proof {
                assert(out@ =~= start + codes(enc(sval_of(*v, tt, enums@), tt, enums@)));
            }
            true
        },
        (SType::Enum(_), Val::Enum(k)) => {
            out.push(*k);
            proof {
                assert(out@ =~= start + codes(enc(sval_of(*v, tt, enums@), tt, enums@)));
            }
            true
        },
        (SType::Tuple(ts), Val::Tuple(vs)) => {
            proof {
                assert(decreases_to!(*v => *vs));
            }
            push_seq(v, ts, vs, enums, out)
        },
        (SType::Record(_, ts), Val::Tuple(vs)) => {
            proof {
                assert(decreases_to!(*v => *vs));
            }
            push_seq(v, ts, vs, enums, out)
        },
        (SType::Option(x), Val::None) => {
            out.push(0);
            let d = default_codes(x, enums);
            append(out, &d);
            proof {
                let dv = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                lemma_codes_concat(seq![Value::Bool(false)], dv);
                assert(out@ =~= start + codes(seq![Value::Bool(false)] + dv));
            }
            true
        },
        (SType::Option(x), Val::Some(w)) => {
            out.push(1);
            let ghost mid = out@;
            if !push_val(x, enums, w, out) {
                return false;
            }
            proof {
                let ev = enc(sval_of(**w, sty(**x), enums@), sty(**x), enums@);
                lemma_codes_concat(seq![Value::Bool(true)], ev);
                assert(out@ =~= start + codes(seq![Value::Bool(true)] + ev));
            }
            true
        },
        (SType::Set(e), Val::Set(es)) => {
            let n = match keys_exec(e, enums) {
                Some(n) => n as usize,
                None => return false,
            };
            let mut bits: Vec<i64> = Vec::new();
            let mut j = 0;
            while j < n
                invariant
                    j <= n,
                    bits@ == Seq::new(j as nat, |_q: int| 0i64),
                decreases n - j,
            {
                bits.push(0);
                proof {
                    assert(bits@ =~= Seq::new((j + 1) as nat, |_q: int| 0i64));
                }
                j += 1;
            }
            proof {
                assert(es@.take(0) =~= Seq::<Val>::empty());
                assert(bits@ =~= bit_codes(set_bits(es@.take(0), tt, enums@)));
            }
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*v => *es),
                    i <= es.len(),
                    tt == sty(*t),
                    tt == STy::Set(Box::new(sty(**e))),
                    keys(sty(**e), enums@) == Some(n as nat),
                    n <= 4096,
                    set_bits(es@.take(i as int), tt, enums@).len() == n,
                    bits@ == bit_codes(set_bits(es@.take(i as int), tt, enums@)),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let mut c: Vec<i64> = Vec::new();
                if !push_val(e, enums, &es[i], &mut c) {
                    return false;
                }
                let ghost sv = sval_of(es@[i as int], sty(**e), enums@);
                proof {
                    assert(c@ =~= codes(enc(sv, sty(**e), enums@)));
                }
                let r = match rank_codes(e, enums, &c) {
                    Some(r) => r,
                    None => return false,
                };
                proof {
                    lemma_code_rank_bound(sty(**e), c@, enums@);
                    lemma_code_rank_shaped(sv, sty(**e), enums@);
                    crate::value::keys::lemma_rank_in_domain(sv, sty(**e), enums@);
                    assert(rank(sv, sty(**e), enums@) == r as int);
                }
                let r = r as usize;
                if bits[r] != 0 {
                    return false;
                }
                bits.set(r, 1);
                proof {
                    let nx = es@.take(i + 1);
                    assert(nx.drop_last() =~= es@.take(i as int));
                    assert(nx.last() == es@[i as int]);
                    let b0 = set_bits(es@.take(i as int), tt, enums@);
                    assert(set_bits(nx, tt, enums@) == b0.update(r as int, true));
                    assert(bits@ =~= bit_codes(b0.update(r as int, true)));
                }
                i += 1;
            }
            append(out, &bits);
            proof {
                assert(es@.take(i as int) =~= es@);
                let b = set_bits(es@, tt, enums@);
                assert(codes(enc(SVal::Set(b), tt, enums@)) =~= bit_codes(b));
            }
            true
        },
        (SType::Map(k, x), Val::Map(ks, vs)) => {
            if ks.len() != vs.len() {
                return false;
            }
            let n = match keys_exec(k, enums) {
                Some(n) => n as usize,
                None => return false,
            };
            let d = default_codes(x, enums);
            let mut rows: Vec<Option<Vec<i64>>> = Vec::new();
            let mut j = 0;
            while j < n
                invariant
                    j <= n,
                    rows@ == Seq::new(j as nat, |_q: int| None::<Vec<i64>>),
                decreases n - j,
            {
                rows.push(None);
                proof {
                    assert(rows@ =~= Seq::new((j + 1) as nat, |_q: int| None::<Vec<i64>>));
                }
                j += 1;
            }
            proof {
                assert(ks@.take(0) =~= Seq::<Val>::empty());
            }
            let mut i = 0;
            while i < ks.len()
                invariant
                    decreases_to!(*v => *ks),
                    decreases_to!(*v => *vs),
                    i <= ks.len(),
                    ks.len() == vs.len(),
                    tt == sty(*t),
                    tt == STy::Map(Box::new(sty(**k)), Box::new(sty(**x))),
                    keys(sty(**k), enums@) == Some(n as nat),
                    n <= 4096,
                    d@ == codes(enc(default_val(sty(**x), enums@), sty(**x), enums@)),
                    rows@.len() == n,
                    prefix_fits(rows@, d@.len(), n as int),
                    rows_encode(rows@, map_rows(ks@.take(i as int), vs@.take(i as int), tt, enums@), sty(**x), enums@),
                decreases ks.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*ks, i as int);
                    vstd::std_specs::vec::axiom_vec_index_decreases(*vs, i as int);
                }
                let mut c: Vec<i64> = Vec::new();
                if !push_val(k, enums, &ks[i], &mut c) {
                    return false;
                }
                let ghost sk = sval_of(ks@[i as int], sty(**k), enums@);
                proof {
                    assert(c@ =~= codes(enc(sk, sty(**k), enums@)));
                }
                let r = match rank_codes(k, enums, &c) {
                    Some(r) => r,
                    None => return false,
                };
                proof {
                    lemma_code_rank_bound(sty(**k), c@, enums@);
                    lemma_code_rank_shaped(sk, sty(**k), enums@);
                    crate::value::keys::lemma_rank_in_domain(sk, sty(**k), enums@);
                    assert(rank(sk, sty(**k), enums@) == r as int);
                }
                let r = r as usize;
                if rows[r].is_some() {
                    return false;
                }
                let mut cv: Vec<i64> = Vec::new();
                if !push_val(x, enums, &vs[i], &mut cv) {
                    return false;
                }
                if cv.len() != d.len() {
                    return false;
                }
                let ghost sx = sval_of(vs@[i as int], sty(**x), enums@);
                proof {
                    assert(cv@ =~= codes(enc(sx, sty(**x), enums@)));
                }
                let ghost r0 = rows@;
                rows.set(r, Some(cv));
                proof {
                    let nk = ks@.take(i + 1);
                    let nv = vs@.take(i + 1);
                    assert(nk.drop_last() =~= ks@.take(i as int));
                    assert(nv.drop_last() =~= vs@.take(i as int));
                    assert(nk.last() == ks@[i as int]);
                    assert(nv.last() == vs@[i as int]);
                    let m0 = map_rows(ks@.take(i as int), vs@.take(i as int), tt, enums@);
                    assert(map_rows(nk, nv, tt, enums@) == m0.update(r as int, Some(sx)));
                    let m1 = m0.update(r as int, Some(sx));
                    assert forall|q: int| 0 <= q < rows@.len() implies match (#[trigger] rows@[q], m1[q]) {
                        (Some(p), Some(w)) => p@ == codes(enc(w, sty(**x), enums@)),
                        (None, None) => true,
                        _ => false,
                    } by {
                        if q != r {
                            assert(rows@[q] == r0[q]);
                        }
                    }
                    assert forall|q: int| 0 <= q < n as int implies match #[trigger] rows@[q] {
                        Some(p) => p@.len() == d@.len(),
                        None => true,
                    } by {
                        if q != r {
                            assert(rows@[q] == r0[q]);
                        }
                    }
                }
                i += 1;
            }
            let flat = match encode_map_rows(&rows, &d) {
                Some(f) => f,
                None => return false,
            };
            proof {
                assert(ks@.take(i as int) =~= ks@);
                assert(vs@.take(i as int) =~= vs@);
                crate::value::map_encoding::lemma_encodes_enc_rows(
                    rows@,
                    map_rows(ks@, vs@, tt, enums@),
                    sty(**x),
                    enums@,
                    d@,
                    flat@,
                );
            }
            append(out, &flat);
            true
        },
        (SType::List(e, max), Val::List(items)) => {
            if items.len() > *max {
                return false;
            }
            out.push(items.len() as i64);
            let ghost se = sty(**e);
            proof {
                assert(items@.take(0) =~= Seq::<Val>::empty());
                assert(enc_items(list_items(items@.take(0), tt, enums@), se, enums@) =~= Seq::<Value>::empty());
                assert(out@ =~= start + codes(seq![Value::Int(items.len() as i64)] + enc_items(
                    list_items(items@.take(0), tt, enums@),
                    se,
                    enums@,
                )));
            }
            let mut i = 0;
            while i < items.len()
                invariant
                    decreases_to!(*v => *items),
                    i <= items.len(),
                    tt == sty(*t),
                    tt == STy::List(Box::new(se), *max),
                    se == sty(**e),
                    out@ == start + codes(seq![Value::Int(items.len() as i64)] + enc_items(
                        list_items(items@.take(i as int), tt, enums@),
                        se,
                        enums@,
                    )),
                decreases items.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*items, i as int);
                }
                let ghost before = out@;
                if !push_val(e, enums, &items[i], out) {
                    return false;
                }
                proof {
                    let nx = items@.take(i + 1);
                    assert(nx.drop_last() =~= items@.take(i as int));
                    assert(nx.last() == items@[i as int]);
                    let l0 = list_items(items@.take(i as int), tt, enums@);
                    let w = sval_of(items@[i as int], se, enums@);
                    assert(list_items(nx, tt, enums@) == l0.push(w));
                    assert(l0.push(w).drop_last() =~= l0);
                    let head = seq![Value::Int(items.len() as i64)] + enc_items(l0, se, enums@);
                    let ew = enc(w, se, enums@);
                    assert(enc_items(l0.push(w), se, enums@) == enc_items(l0, se, enums@) + ew);
                    lemma_codes_concat(head, ew);
                    assert(seq![Value::Int(items.len() as i64)] + enc_items(l0.push(w), se, enums@) =~= head + ew);
                }
                i += 1;
            }
            let d = default_codes(e, enums);
            let ghost dv = enc(default_val(se, enums@), se, enums@);
            let ghost li = list_items(items@, tt, enums@);
            proof {
                assert(items@.take(i as int) =~= items@);
                lemma_list_items_len(items@, tt, enums@);
            }
            let rest = *max - items.len();
            let mut j = 0;
            proof {
                assert(enc_repeat(dv, 0) =~= Seq::<Value>::empty());
                assert(out@ =~= start + codes(seq![Value::Int(items.len() as i64)] + enc_items(li, se, enums@)
                    + enc_repeat(dv, 0)));
            }
            while j < rest
                invariant
                    j <= rest,
                    d@ == codes(dv),
                    out@ == start + codes(seq![Value::Int(items.len() as i64)] + enc_items(li, se, enums@)
                        + enc_repeat(dv, j as nat)),
                decreases rest - j,
            {
                append(out, &d);
                proof {
                    let head = seq![Value::Int(items.len() as i64)] + enc_items(li, se, enums@) + enc_repeat(
                        dv,
                        j as nat,
                    );
                    assert(enc_repeat(dv, (j + 1) as nat) == enc_repeat(dv, j as nat) + dv);
                    lemma_codes_concat(head, dv);
                    assert(seq![Value::Int(items.len() as i64)] + enc_items(li, se, enums@) + enc_repeat(
                        dv,
                        (j + 1) as nat,
                    ) =~= head + dv);
                }
                j += 1;
            }
            proof {
                assert(sval_of(*v, tt, enums@) == SVal::List(li));
                assert(li.len() == items.len());
            }
            true
        },
        _ => false,
    }
}

/// 要素の値の木の列の符号を `out` に加える。
fn push_seq(_parent: &Val, ts: &Vec<SType>, vs: &Vec<Val>, enums: &Vec<i64>, out: &mut Vec<i64>) -> (ok: bool)
    requires
        decreases_to!(*_parent => *vs),
    ensures
        ok ==> vs.len() == ts.len(),
        ok ==> final(out)@ == old(out)@ + codes(enc_seq(svals_of(vs@, stys(ts@), enums@), stys(ts@), enums@)),
        ok ==> shaped_seq(svals_of(vs@, stys(ts@), enums@), stys(ts@)),
    decreases _parent, 0nat,
{
    if vs.len() != ts.len() {
        return false;
    }
    let ghost start = out@;
    let ghost all = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
        assert(vs@.take(0) =~= Seq::<Val>::empty());
        assert(out@ =~= start + codes(enc_seq(svals_of(vs@.take(0), all.take(0), enums@), all.take(0), enums@)));
    }
    let mut i = 0;
    while i < vs.len()
        invariant
            decreases_to!(*_parent => *vs),
            i <= vs.len(),
            vs.len() == ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            out@ == start + codes(enc_seq(
                svals_of(vs@.take(i as int), all.take(i as int), enums@),
                all.take(i as int),
                enums@,
            )),
            shaped_seq(svals_of(vs@.take(i as int), all.take(i as int), enums@), all.take(i as int)),
        decreases vs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*vs, i as int);
        }
        if !push_val(&ts[i], enums, &vs[i], out) {
            return false;
        }
        proof {
            let pv = vs@.take(i as int);
            let pt = all.take(i as int);
            let nv = vs@.take(i + 1);
            let nt = all.take(i + 1);
            assert(nv.drop_last() =~= pv);
            assert(nt.drop_last() =~= pt);
            assert(nv.last() == vs@[i as int]);
            assert(nt.last() == all[i as int]);
            let s0 = svals_of(pv, pt, enums@);
            let w = sval_of(vs@[i as int], all[i as int], enums@);
            assert(svals_of(nv, nt, enums@) == s0.push(w));
            lemma_svals_len(pv, pt, enums@);
            assert(s0.push(w).drop_last() =~= s0);
            let a = enc_seq(s0, pt, enums@);
            let b = enc(w, all[i as int], enums@);
            assert(enc_seq(s0.push(w), nt, enums@) == a + b);
            lemma_codes_concat(a, b);
            assert(shaped_seq(s0.push(w), nt));
        }
        i += 1;
    }
    proof {
        assert(vs@.take(i as int) =~= vs@);
        assert(all.take(i as int) =~= all);
    }
    true
}

// ---- 符号の列から値の木へ ----

/// 符号の列を、型 `t` の値の木にする。正規形の符号化でなければ `None`
/// （Boolの符号が0と1以外、空のOption、Mapにないキー、Listの長さより後ろの要素のスロットが既定値でない、など）。
/// `enums` は各列挙型のラベルの数。
pub fn decode_val(t: &SType, enums: &Vec<i64>, xs: &Vec<i64>) -> (r: Option<Val>)
    ensures
        r matches Some(v) ==> xs@ == codes(enc(sval_of(v, sty(*t), enums@), sty(*t), enums@)),
        r matches Some(v) ==> shaped(sval_of(v, sty(*t), enums@), sty(*t)),
    decreases t, 2nat,
{
    let w = match stype_width(t, enums) {
        Some(w) => w,
        None => return None,
    };
    if w != xs.len() {
        return None;
    }
    proof {
        assert(xs@.subrange(0, w as int) =~= xs@);
    }
    decode_at(t, enums, xs, 0)
}

/// `xs` の位置 `at` からの列が `d` に等しい。
fn slice_eq(xs: &Vec<i64>, at: usize, d: &Vec<i64>) -> (r: bool)
    requires
        at + d.len() <= xs.len(),
    ensures
        r == (xs@.subrange(at as int, at + d.len()) == d@),
{
    let mut i = 0;
    while i < d.len()
        invariant
            i <= d.len(),
            at + d.len() <= xs.len(),
            forall|j: int| 0 <= j < i ==> xs@[at + j] == d@[j],
        decreases d.len() - i,
    {
        if xs[at + i] != d[i] {
            proof {
                assert(xs@.subrange(at as int, at + d.len())[i as int] != d@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(xs@.subrange(at as int, at + d.len()) =~= d@);
    }
    true
}

/// `xs` の位置 `pos` からの、型 `t` の符号の列を値の木にする。
fn decode_at(t: &SType, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<Val>)
    requires
        pos + width(sty(*t), enums@) <= xs.len(),
    ensures
        r matches Some(v) ==> xs@.subrange(pos as int, pos + width(sty(*t), enums@)) == codes(
            enc(sval_of(v, sty(*t), enums@), sty(*t), enums@),
        ),
        r matches Some(v) ==> shaped(sval_of(v, sty(*t), enums@), sty(*t)),
    decreases t, 1nat,
{
    let ghost tt = sty(*t);
    let ghost s = xs@.subrange(pos as int, pos + width(tt, enums@));
    match t {
        SType::Bool => {
            let x = xs[pos];
            if x == 0 || x == 1 {
                let v = Val::Bool(x == 1);
                proof {
                    assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
                }
                Some(v)
            } else {
                None
            }
        },
        SType::Int(_, _) => {
            let v = Val::Int(xs[pos]);
            proof {
                assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
            }
            Some(v)
        },
        SType::Enum(_) => {
            let v = Val::Enum(xs[pos]);
            proof {
                assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
            }
            Some(v)
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            let vs = decode_seq(t, ts, enums, xs, pos)?;
            Some(Val::Tuple(vs))
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            let vs = decode_seq(t, ts, enums, xs, pos)?;
            Some(Val::Tuple(vs))
        },
        SType::Option(x) => {
            let ghost sx = sty(**x);
            let d = default_codes(x, enums);
            proof {
                lemma_default_len(sx, enums@);
            }
            let tag = xs[pos];
            if tag == 0 {
                if !slice_eq(xs, pos + 1, &d) {
                    return None;
                }
                let v = Val::None;
                proof {
                    let dv = enc(default_val(sx, enums@), sx, enums@);
                    lemma_codes_concat(seq![Value::Bool(false)], dv);
                    assert(s =~= seq![0i64] + xs@.subrange(pos + 1, pos + 1 + d.len()));
                    assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
                }
                Some(v)
            } else if tag == 1 {
                let w = decode_at(x, enums, xs, pos + 1)?;
                let v = Val::Some(Box::new(w));
                proof {
                    let ew = enc(sval_of(w, sx, enums@), sx, enums@);
                    lemma_codes_concat(seq![Value::Bool(true)], ew);
                    assert(s =~= seq![1i64] + xs@.subrange(pos + 1, pos + 1 + width(sx, enums@)));
                    assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
                }
                Some(v)
            } else {
                None
            }
        },
        SType::Set(e) => {
            proof {
                assert(decreases_to!(*t => **e));
            }
            decode_set(t, e, enums, xs, pos)
        },
        SType::Map(k, x) => {
            proof {
                assert(decreases_to!(*t => **k));
                assert(decreases_to!(*t => **x));
            }
            decode_map(t, k, x, enums, xs, pos)
        },
        SType::List(e, max) => {
            proof {
                assert(decreases_to!(*t => **e));
            }
            decode_list(t, e, max, enums, xs, pos)
        },
    }
}

fn decode_set(_parent: &SType, e: &Box<SType>, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<Val>)
    requires
        decreases_to!(*_parent => **e),
        sty(*_parent) == STy::Set(Box::new(sty(**e))),
        pos + width(sty(*_parent), enums@) <= xs.len(),
    ensures
        r matches Some(v) ==> xs@.subrange(pos as int, pos + width(sty(*_parent), enums@)) == codes(
            enc(sval_of(v, sty(*_parent), enums@), sty(*_parent), enums@),
        ),
        r matches Some(v) ==> shaped(sval_of(v, sty(*_parent), enums@), sty(*_parent)),
    decreases _parent, 0nat,
{
    let ghost tt = sty(*_parent);
    let ghost s = xs@.subrange(pos as int, pos + width(tt, enums@));
        let ghost se = sty(**e);
        let n = keys_or_zero_exec(e, enums);
        let mut es: Vec<Val> = Vec::new();
        let mut i = 0;
        proof {
            assert(es@ =~= Seq::<Val>::empty());
        }
        while i < n
            invariant
                decreases_to!(*_parent => **e),
                i <= n,
                n == keys_or_zero(se, enums@),
                n <= 4096,
                tt == STy::Set(Box::new(se)),
                se == sty(**e),
                width(tt, enums@) == n,
                pos + n <= xs.len(),
                s == xs@.subrange(pos as int, pos + n),
                forall|j: int| 0 <= j < i ==> (#[trigger] xs@[pos + j] == 0 || xs@[pos + j] == 1),
                set_bits(es@, tt, enums@) == Seq::new(n as nat, |j: int| j < i && xs@[pos + j] == 1),
            decreases n - i,
        {
            let b = xs[pos + i];
            if b == 1 {
                let c = unrank_codes(e, enums, i as u64)?;
                let ev = decode_val(e, enums, &c)?;
                proof {
                    let u = choose|u: SVal|
                        member(u, se, enums@) && rank(u, se, enums@) == i && #[trigger] codes(enc(u, se, enums@))
                            == c@;
                    crate::value::rank_code::lemma_code_rank(u, se, enums@);
                    let sv = sval_of(ev, se, enums@);
                    lemma_code_rank_shaped(sv, se, enums@);
                    crate::value::keys::lemma_rank_in_domain(sv, se, enums@);
                    assert(rank(sv, se, enums@) == i as int);
                }
                let ghost e0 = es@;
                es.push(ev);
                proof {
                    assert(es@.drop_last() =~= e0);
                    assert(es@.last() == ev);
                    assert(set_bits(es@, tt, enums@) =~= Seq::new(
                        n as nat,
                        |j: int| j < i + 1 && xs@[pos + j] == 1,
                    ));
                }
            } else if b == 0 {
                proof {
                    assert(set_bits(es@, tt, enums@) =~= Seq::new(
                        n as nat,
                        |j: int| j < i + 1 && xs@[pos + j] == 1,
                    ));
                }
            } else {
                return None;
            }
            i += 1;
        }
        let v = Val::Set(es);
        proof {
            let bs = set_bits(es@, tt, enums@);
            assert(codes(enc(SVal::Set(bs), tt, enums@)) =~= bit_codes(bs));
            assert forall|j: int| 0 <= j < n implies #[trigger] s[j] == bit_codes(bs)[j] by {
                assert(s[j] == xs@[pos + j]);
            }
            assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
        }
        Some(v)
}

fn decode_map(_parent: &SType, k: &Box<SType>, x: &Box<SType>, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<
    Val,
>)
    requires
        decreases_to!(*_parent => **k),
        decreases_to!(*_parent => **x),
        sty(*_parent) == STy::Map(Box::new(sty(**k)), Box::new(sty(**x))),
        pos + width(sty(*_parent), enums@) <= xs.len(),
    ensures
        r matches Some(v) ==> xs@.subrange(pos as int, pos + width(sty(*_parent), enums@)) == codes(
            enc(sval_of(v, sty(*_parent), enums@), sty(*_parent), enums@),
        ),
        r matches Some(v) ==> shaped(sval_of(v, sty(*_parent), enums@), sty(*_parent)),
    decreases _parent, 0nat,
{
    let ghost tt = sty(*_parent);
    let ghost s = xs@.subrange(pos as int, pos + width(tt, enums@));
        let ghost sk = sty(**k);
        let ghost sx = sty(**x);
        let n = keys_or_zero_exec(k, enums);
        let wx = match stype_width(x, enums) {
            Some(w) => w,
            None => return None,
        };
        let d = default_codes(x, enums);
        proof {
            lemma_default_len(sx, enums@);
            assert(width(tt, enums@) == n * (1 + wx));
        }
        let stride = match wx.checked_add(1) {
            Some(w) => w,
            None => return None,
        };
        let mut ks: Vec<Val> = Vec::new();
        let mut vs: Vec<Val> = Vec::new();
        let ghost mut g: Seq<Option<SVal>> = Seq::new(n as nat, |_j: int| None::<SVal>);
        proof {
            assert(ks@ =~= Seq::<Val>::empty());
            assert(map_rows(ks@, vs@, tt, enums@) =~= g);
            assert(g.take(0) =~= Seq::<Option<SVal>>::empty());
            assert(xs@.subrange(pos as int, pos as int) =~= codes(enc_rows(g.take(0), sx, enums@)));
        }
        let mut i = 0;
        let mut base = pos;
        while i < n
            invariant
                decreases_to!(*_parent => **k),
                decreases_to!(*_parent => **x),
                i <= n,
                n == keys_or_zero(sk, enums@),
                n <= 4096,
                tt == STy::Map(Box::new(sk), Box::new(sx)),
                sk == sty(**k),
                sx == sty(**x),
                wx == width(sx, enums@),
                stride == wx + 1,
                d@ == codes(enc(default_val(sx, enums@), sx, enums@)),
                d@.len() == wx,
                pos + n * stride <= xs.len(),
                base == pos + i * stride,
                g.len() == n,
                forall|j: int| i <= j < n ==> #[trigger] g[j] is None,
                map_rows(ks@, vs@, tt, enums@) == g,
                xs@.subrange(pos as int, base as int) == codes(enc_rows(g.take(i as int), sx, enums@)),
            decreases n - i,
        {
            proof {
                vstd::arithmetic::mul::lemma_mul_inequality(i + 1, n as int, stride as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride as int, i as int, 1);
            }
            let tag = xs[base];
            let ghost before = xs@.subrange(pos as int, base as int);
            let ghost row = xs@.subrange(base as int, base + stride);
            let ghost g0 = g;
            if tag == 0 {
                if !slice_eq(xs, base + 1, &d) {
                    return None;
                }
                proof {
                    let dv = enc(default_val(sx, enums@), sx, enums@);
                    let re = seq![Value::Bool(false)] + dv;
                    assert(g.take(i + 1) =~= g.take(i as int).push(None));
                    assert(g.take(i + 1).drop_last() =~= g.take(i as int));
                    assert(enc_rows(g.take(i + 1), sx, enums@) == enc_rows(g.take(i as int), sx, enums@) + re);
                    lemma_codes_concat(enc_rows(g.take(i as int), sx, enums@), re);
                    lemma_codes_concat(seq![Value::Bool(false)], dv);
                    assert(row =~= seq![0i64] + xs@.subrange(base + 1, base + 1 + d.len()));
                    assert(xs@.subrange(pos as int, base + stride) =~= before + row);
                }
            } else if tag == 1 {
                let c = unrank_codes(k, enums, i as u64)?;
                let kv = decode_val(k, enums, &c)?;
                let vv = decode_at(x, enums, xs, base + 1)?;
                let ghost svk = sval_of(kv, sk, enums@);
                let ghost svv = sval_of(vv, sx, enums@);
                proof {
                    let u = choose|u: SVal|
                        member(u, sk, enums@) && rank(u, sk, enums@) == i && #[trigger] codes(enc(u, sk, enums@))
                            == c@;
                    crate::value::rank_code::lemma_code_rank(u, sk, enums@);
                    lemma_code_rank_shaped(svk, sk, enums@);
                    crate::value::keys::lemma_rank_in_domain(svk, sk, enums@);
                    assert(rank(svk, sk, enums@) == i as int);
                }
                let ghost k0 = ks@;
                let ghost v0 = vs@;
                ks.push(kv);
                vs.push(vv);
                proof {
                    g = g0.update(i as int, Some(svv));
                    assert(ks@.drop_last() =~= k0);
                    assert(vs@.drop_last() =~= v0);
                    assert(ks@.last() == kv);
                    assert(vs@.last() == vv);
                    assert(map_rows(ks@, vs@, tt, enums@) == g);
                    let ev = enc(svv, sx, enums@);
                    let re = seq![Value::Bool(true)] + ev;
                    assert(g.take(i as int) =~= g0.take(i as int));
                    assert(g.take(i + 1) =~= g0.take(i as int).push(Some(svv)));
                    assert(g.take(i + 1).drop_last() =~= g0.take(i as int));
                    assert(enc_rows(g.take(i + 1), sx, enums@) == enc_rows(g0.take(i as int), sx, enums@) + re);
                    lemma_codes_concat(enc_rows(g0.take(i as int), sx, enums@), re);
                    lemma_codes_concat(seq![Value::Bool(true)], ev);
                    assert(row =~= seq![1i64] + xs@.subrange(base + 1, base + 1 + wx));
                    assert(xs@.subrange(pos as int, base + stride) =~= before + row);
                }
            } else {
                return None;
            }
            base = base + stride;
            i += 1;
        }
        let v = Val::Map(ks, vs);
        proof {
            assert(g.take(n as int) =~= g);
            assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
        }
        Some(v)
}

fn decode_list(_parent: &SType, e: &Box<SType>, max: &usize, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<Val>)
    requires
        decreases_to!(*_parent => **e),
        sty(*_parent) == STy::List(Box::new(sty(**e)), *max),
        pos + width(sty(*_parent), enums@) <= xs.len(),
    ensures
        r matches Some(v) ==> xs@.subrange(pos as int, pos + width(sty(*_parent), enums@)) == codes(
            enc(sval_of(v, sty(*_parent), enums@), sty(*_parent), enums@),
        ),
        r matches Some(v) ==> shaped(sval_of(v, sty(*_parent), enums@), sty(*_parent)),
    decreases _parent, 0nat,
{
    let ghost tt = sty(*_parent);
    let ghost s = xs@.subrange(pos as int, pos + width(tt, enums@));
        let ghost se = sty(**e);
        let we = match stype_width(e, enums) {
            Some(w) => w,
            None => return None,
        };
        proof {
            assert(width(tt, enums@) == 1 + *max * we);
        }
        let len = xs[pos];
        if len < 0 || len as u64 > *max as u64 {
            return None;
        }
        let len = len as usize;
        let mut items: Vec<Val> = Vec::new();
        let mut i = 0;
        let mut at = pos + 1;
        proof {
            assert(items@ =~= Seq::<Val>::empty());
            assert(enc_items(list_items(items@, tt, enums@), se, enums@) =~= Seq::<Value>::empty());
            lemma_codes_concat(seq![Value::Int(len as i64)], Seq::<Value>::empty());
            assert(xs@.subrange(pos as int, at as int) =~= codes(seq![Value::Int(len as i64)] + enc_items(
                list_items(items@, tt, enums@),
                se,
                enums@,
            )));
        }
        while i < len
            invariant
                decreases_to!(*_parent => **e),
                i <= len,
                len <= *max,
                len as i64 == xs@[pos as int],
                tt == STy::List(Box::new(se), *max),
                se == sty(**e),
                we == width(se, enums@),
                pos + 1 + *max * we <= xs.len(),
                at == pos + 1 + i * we,
                items@.len() == i,
                xs@.subrange(pos as int, at as int) == codes(seq![Value::Int(len as i64)] + enc_items(
                    list_items(items@, tt, enums@),
                    se,
                    enums@,
                )),
            decreases len - i,
        {
            proof {
                vstd::arithmetic::mul::lemma_mul_inequality(i + 1, *max as int, we as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(we as int, i as int, 1);
            }
            let w = decode_at(e, enums, xs, at)?;
            let ghost i0 = items@;
            let ghost before = xs@.subrange(pos as int, at as int);
            items.push(w);
            proof {
                assert(items@.drop_last() =~= i0);
                assert(items@.last() == w);
                let l0 = list_items(i0, tt, enums@);
                let sw = sval_of(w, se, enums@);
                assert(list_items(items@, tt, enums@) == l0.push(sw));
                assert(l0.push(sw).drop_last() =~= l0);
                let head = seq![Value::Int(len as i64)] + enc_items(l0, se, enums@);
                let ew = enc(sw, se, enums@);
                assert(enc_items(l0.push(sw), se, enums@) == enc_items(l0, se, enums@) + ew);
                lemma_codes_concat(head, ew);
                assert(seq![Value::Int(len as i64)] + enc_items(l0.push(sw), se, enums@) =~= head + ew);
                assert(xs@.subrange(pos as int, at + we) =~= before + xs@.subrange(at as int, at + we));
            }
            at = at + we;
            i += 1;
        }
        let d = default_codes(e, enums);
        let ghost dv = enc(default_val(se, enums@), se, enums@);
        let ghost li = list_items(items@, tt, enums@);
        proof {
            lemma_default_len(se, enums@);
            lemma_list_items_len(items@, tt, enums@);
            assert(enc_repeat(dv, 0) =~= Seq::<Value>::empty());
            assert(seq![Value::Int(len as i64)] + enc_items(li, se, enums@) + enc_repeat(dv, 0) =~= seq![
                Value::Int(len as i64),
            ] + enc_items(li, se, enums@));
        }
        let mut j = len;
        while j < *max
            invariant
                len <= j <= *max,
                d@ == codes(dv),
                d@.len() == we,
                we == width(se, enums@),
                pos + 1 + *max * we <= xs.len(),
                at == pos + 1 + j * we,
                xs@.subrange(pos as int, at as int) == codes(seq![Value::Int(len as i64)] + enc_items(
                    li,
                    se,
                    enums@,
                ) + enc_repeat(dv, (j - len) as nat)),
            decreases *max - j,
        {
            proof {
                vstd::arithmetic::mul::lemma_mul_inequality(j + 1, *max as int, we as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(we as int, j as int, 1);
            }
            if !slice_eq(xs, at, &d) {
                return None;
            }
            proof {
                let head = seq![Value::Int(len as i64)] + enc_items(li, se, enums@) + enc_repeat(
                    dv,
                    (j - len) as nat,
                );
                assert(enc_repeat(dv, (j + 1 - len) as nat) == enc_repeat(dv, (j - len) as nat) + dv);
                lemma_codes_concat(head, dv);
                assert(seq![Value::Int(len as i64)] + enc_items(li, se, enums@) + enc_repeat(
                    dv,
                    (j + 1 - len) as nat,
                ) =~= head + dv);
                assert(xs@.subrange(pos as int, at + we) =~= xs@.subrange(pos as int, at as int)
                    + xs@.subrange(at as int, at + we));
            }
            at = at + we;
            j += 1;
        }
        let v = Val::List(items);
        proof {
            assert(sval_of(v, tt, enums@) == SVal::List(li));
            assert(s =~= codes(enc(sval_of(v, tt, enums@), tt, enums@)));
        }
        Some(v)
}

/// `xs` の位置 `pos` からの、要素の型の列 `ts` の符号の列を値の木の列にする。
fn decode_seq(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, xs: &Vec<i64>, pos: usize) -> (r: Option<
    Vec<Val>,
>)
    requires
        decreases_to!(*_parent => *ts),
        pos + width_sum(stys(ts@), enums@) <= xs.len(),
    ensures
        r matches Some(vs) ==> vs@.len() == ts@.len(),
        r matches Some(vs) ==> xs@.subrange(pos as int, pos + width_sum(stys(ts@), enums@)) == codes(
            enc_seq(svals_of(vs@, stys(ts@), enums@), stys(ts@), enums@),
        ),
        r matches Some(vs) ==> shaped_seq(svals_of(vs@, stys(ts@), enums@), stys(ts@)),
    decreases _parent, 0nat,
{
    let ghost all = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
        assert(xs@.subrange(pos as int, pos as int) =~= Seq::<i64>::empty());
    }
    let mut vs: Vec<Val> = Vec::new();
    let mut cur = pos;
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            pos + width_sum(all, enums@) <= xs.len(),
            cur == pos + width_sum(all.take(i as int), enums@),
            vs@.len() == i,
            xs@.subrange(pos as int, cur as int) == codes(enc_seq(
                svals_of(vs@, all.take(i as int), enums@),
                all.take(i as int),
                enums@,
            )),
            shaped_seq(svals_of(vs@, all.take(i as int), enums@), all.take(i as int)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            assert(all.take(i + 1).drop_last() =~= all.take(i as int));
            assert(all.take(i + 1).last() == all[i as int]);
            lemma_width_sum_prefix(all, enums@, i + 1);
        }
        let w = match stype_width(&ts[i], enums) {
            Some(w) => w,
            None => return None,
        };
        let v = decode_at(&ts[i], enums, xs, cur)?;
        let ghost v0 = vs@;
        let ghost before = xs@.subrange(pos as int, cur as int);
        vs.push(v);
        proof {
            let pt = all.take(i as int);
            let nt = all.take(i + 1);
            assert(vs@.drop_last() =~= v0);
            assert(vs@.last() == v);
            let s0 = svals_of(v0, pt, enums@);
            let sw = sval_of(v, all[i as int], enums@);
            assert(svals_of(vs@, nt, enums@) == s0.push(sw));
            lemma_svals_len(v0, pt, enums@);
            assert(s0.push(sw).drop_last() =~= s0);
            let a = enc_seq(s0, pt, enums@);
            let b = enc(sw, all[i as int], enums@);
            assert(enc_seq(s0.push(sw), nt, enums@) == a + b);
            lemma_codes_concat(a, b);
            assert(xs@.subrange(pos as int, cur + w) =~= before + xs@.subrange(cur as int, cur + w));
            assert(shaped_seq(s0.push(sw), nt));
        }
        cur = cur + w;
        i += 1;
    }
    proof {
        assert(all.take(i as int) =~= all);
    }
    Some(vs)
}

} // verus!
