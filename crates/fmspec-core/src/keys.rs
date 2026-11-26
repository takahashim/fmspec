//! キーの型の値の正規順と、値の番号（rank）の仕様。
//!
//! キーの型（Setの要素とMapのキーになれる型）の値を、正規順に並べた列が [`domain`] である。
//! 正規順は、Boolが偽、真の順、Intが昇順、Enumがラベルの定義順、TupleとRecordが要素の辞書順
//! （最後の要素が最も速く変わる）、Optionが空、中身の順である。参照実装の `domain` と同じ順である。
//!
//! 値の番号 [`rank`] は、正規順での位置である。TupleとRecordの番号は、要素の番号を混合基数の桁として
//! 左から順にたたんだ値である。[`lemma_rank_in_domain`] と [`lemma_domain_rank`] により、
//! `domain` は型に属する値と番号 `0..keys` の1対1の対応である。

#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, keys_product, member, members, STy, SVal};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_strict_inequality};
use vstd::prelude::*;

verus! {

/// キーの型の値を正規順に並べた列。キーの型でなければ空。
pub open spec fn domain(t: STy, enums: Seq<i64>) -> Seq<SVal>
    decreases t, 0nat,
{
    if keys(t, enums) is None {
        Seq::empty()
    } else {
        match t {
            STy::Bool => seq![SVal::Bool(false), SVal::Bool(true)],
            STy::Int(lo, hi) => Seq::new((hi - lo + 1) as nat, |i: int| SVal::Int((lo + i) as i64)),
            STy::Enum(id) => Seq::new(enums[id as int] as nat, |i: int| SVal::Enum(id, i as i64)),
            STy::Tuple(ts) => product(ts, enums).map_values(|vs: Seq<SVal>| SVal::Tuple(vs)),
            STy::Record(_, ts) => product(ts, enums).map_values(|vs: Seq<SVal>| SVal::Tuple(vs)),
            STy::Option(x) => seq![SVal::None] + domain(*x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))),
            _ => Seq::empty(),
        }
    }
}

/// 要素の型の列の値の組を、辞書順に並べた列。最後の要素が最も速く変わる。
pub open spec fn product(ts: Seq<STy>, enums: Seq<i64>) -> Seq<Seq<SVal>>
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        seq![Seq::empty()]
    } else {
        let p = product(ts.drop_last(), enums);
        let d = domain(ts.last(), enums);
        Seq::new(p.len() * d.len(), |i: int| p[i / d.len() as int].push(d[i % d.len() as int]))
    }
}

/// 値の番号。値が型に属し、型がキーの型のときに意味を持つ。
pub open spec fn rank(v: SVal, t: STy, enums: Seq<i64>) -> int
    decreases t, 0nat,
{
    match (t, v) {
        (STy::Bool, SVal::Bool(b)) => if b {
            1
        } else {
            0
        },
        (STy::Int(lo, _), SVal::Int(x)) => x - lo,
        (STy::Enum(_), SVal::Enum(_, k)) => k as int,
        (STy::Tuple(ts), SVal::Tuple(vs)) => rank_seq(vs, ts, enums),
        (STy::Record(_, ts), SVal::Tuple(vs)) => rank_seq(vs, ts, enums),
        (STy::Option(_), SVal::None) => 0,
        (STy::Option(x), SVal::Some(w)) => 1 + rank(*w, *x, enums),
        _ => 0,
    }
}

/// 要素の番号を、混合基数の桁として左から順にたたむ。
pub open spec fn rank_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>) -> int
    decreases ts, 1nat,
{
    if ts.len() == 0 || vs.len() == 0 {
        0
    } else {
        rank_seq(vs.drop_last(), ts.drop_last(), enums) * radix(ts.last(), enums) + rank(vs.last(), ts.last(), enums)
    }
}

pub open spec fn radix(t: STy, enums: Seq<i64>) -> int {
    match keys(t, enums) {
        Some(k) => k as int,
        None => 0,
    }
}

// ---- 補題 ----

/// 正規順の列の長さは、値の数である。
pub proof fn lemma_domain_len(t: STy, enums: Seq<i64>)
    requires
        keys(t, enums) is Some,
    ensures
        domain(t, enums).len() == keys(t, enums)->0,
    decreases t, 0nat,
{
    match t {
        STy::Tuple(ts) => lemma_product_len(ts, enums),
        STy::Record(_, ts) => lemma_product_len(ts, enums),
        STy::Option(x) => lemma_domain_len(*x, enums),
        _ => {},
    }
}

proof fn lemma_product_len(ts: Seq<STy>, enums: Seq<i64>)
    requires
        keys_product(ts, enums) is Some,
    ensures
        product(ts, enums).len() == keys_product(ts, enums)->0,
    decreases ts, 1nat,
{
    if ts.len() > 0 {
        lemma_product_len(ts.drop_last(), enums);
        lemma_domain_len(ts.last(), enums);
    }
}

/// 型に属する値の番号は `0..keys` にあり、正規順の列のその位置に値がある。
pub proof fn lemma_rank_in_domain(v: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v, t, enums),
        keys(t, enums) is Some,
    ensures
        0 <= rank(v, t, enums) < keys(t, enums)->0,
        domain(t, enums)[rank(v, t, enums)] == v,
    decreases t, 0nat,
{
    lemma_domain_len(t, enums);
    match (t, v) {
        (STy::Tuple(ts), SVal::Tuple(vs)) => {
            lemma_rank_seq_in_product(vs, ts, enums);
            lemma_product_len(ts, enums);
        },
        (STy::Record(_, ts), SVal::Tuple(vs)) => {
            lemma_rank_seq_in_product(vs, ts, enums);
            lemma_product_len(ts, enums);
        },
        (STy::Option(x), SVal::Some(w)) => {
            lemma_rank_in_domain(*w, *x, enums);
            lemma_domain_len(*x, enums);
        },
        _ => {},
    }
}

proof fn lemma_rank_seq_in_product(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
        keys_product(ts, enums) is Some,
    ensures
        0 <= rank_seq(vs, ts, enums) < keys_product(ts, enums)->0,
        product(ts, enums)[rank_seq(vs, ts, enums)] == vs,
    decreases ts, 1nat,
{
    lemma_product_len(ts, enums);
    if ts.len() == 0 {
        assert(vs =~= Seq::<SVal>::empty());
    } else {
        let pre = vs.drop_last();
        lemma_rank_seq_in_product(pre, ts.drop_last(), enums);
        lemma_rank_in_domain(vs.last(), ts.last(), enums);
        lemma_product_len(ts.drop_last(), enums);
        lemma_domain_len(ts.last(), enums);
        let a = rank_seq(pre, ts.drop_last(), enums);
        let b = rank(vs.last(), ts.last(), enums);
        let n = keys_product(ts.drop_last(), enums)->0 as int;
        let k = keys(ts.last(), enums)->0 as int;
        let r = a * k + b;
        // r / k == a、r % k == b。
        lemma_fundamental_div_mod_converse(r, k, a, b);
        // r < n * k。
        lemma_mul_inequality(a + 1, n, k);
        assert((a + 1) * k == a * k + k) by (nonlinear_arith);
        assert(0 <= a * k) by (nonlinear_arith)
            requires
                0 <= a,
                0 < k,
        ;
        assert(pre.push(vs.last()) == vs);
    }
}

/// 正規順の列の位置 `i` の値は型に属し、その番号は `i` である。
pub proof fn lemma_domain_rank(t: STy, enums: Seq<i64>, i: int)
    requires
        keys(t, enums) is Some,
        0 <= i < keys(t, enums)->0,
    ensures
        member(domain(t, enums)[i], t, enums),
        rank(domain(t, enums)[i], t, enums) == i,
    decreases t, 0nat,
{
    lemma_domain_len(t, enums);
    match t {
        STy::Tuple(ts) => {
            lemma_product_len(ts, enums);
            lemma_product_rank(ts, enums, i);
        },
        STy::Record(_, ts) => {
            lemma_product_len(ts, enums);
            lemma_product_rank(ts, enums, i);
        },
        STy::Option(x) => {
            if i > 0 {
                lemma_domain_len(*x, enums);
                lemma_domain_rank(*x, enums, i - 1);
            }
        },
        _ => {},
    }
}

proof fn lemma_product_rank(ts: Seq<STy>, enums: Seq<i64>, i: int)
    requires
        keys_product(ts, enums) is Some,
        0 <= i < keys_product(ts, enums)->0,
    ensures
        members(product(ts, enums)[i], ts, enums),
        rank_seq(product(ts, enums)[i], ts, enums) == i,
    decreases ts, 1nat,
{
    lemma_product_len(ts, enums);
    if ts.len() > 0 {
        let p = product(ts.drop_last(), enums);
        let d = domain(ts.last(), enums);
        lemma_product_len(ts.drop_last(), enums);
        lemma_domain_len(ts.last(), enums);
        let n = p.len() as int;
        let k = d.len() as int;
        assert(k > 0) by (nonlinear_arith)
            requires
                0 <= i < n * k,
                n >= 0,
                k >= 0,
        ;
        let q = i / k;
        let r = i % k;
        lemma_fundamental_div_mod(i, k);
        assert(0 <= r < k);
        assert(0 <= q < n) by {
            if q >= n {
                lemma_mul_inequality(n, q, k);
                assert(q * k == k * q) by (nonlinear_arith);
            }
            if q < 0 {
                lemma_mul_strict_inequality(q, 0, k);
            }
        }
        lemma_product_rank(ts.drop_last(), enums, q);
        lemma_domain_rank(ts.last(), enums, r);
        let vs = product(ts, enums)[i];
        assert(vs == p[q].push(d[r]));
        assert(vs.drop_last() == p[q]);
        assert(q * k == k * q) by (nonlinear_arith);
    }
}

} // verus!
