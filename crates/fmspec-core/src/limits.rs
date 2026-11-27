//! 下ろしが大きさの理由で失敗しないための条件（仕様）。
//!
//! 下ろしは、スロットの数や位置を `usize` で計算し、Listの長さと添字を整数のスロットに入れる。
//! そのため、型が付いていても、幅が大きすぎる型や、長さの上限が大きすぎるListでは失敗する。
//! [`lim_s`] と [`lim_x`] は、型とその部分の型の幅が [`LIM`] 以下で、Listの長さの上限も [`LIM`] 以下であることを表す。
//! `fmspec-ir` の上限（幅が65536以下、Listの長さが1024以下）を満たす宣言の型は、この条件を満たす。

#[cfg(verus_keep_ghost)]
use crate::encoding::xwidth_sum;
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_xwidth_of, to_xty, to_xtys, width, width_sum, xwidth, STy, XTy};
use vstd::prelude::*;

verus! {

/// 幅と長さの上限。`usize` が32ビットでも、和や積の途中で溢れない。
pub open spec fn lim() -> nat {
    0x7fff_ffff
}

/// 格納の型とその部分の型の幅が上限以下で、Listの長さの上限も上限以下である。
pub open spec fn lim_s(t: STy, enums: Seq<i64>) -> bool
    decreases t,
{
    &&& width(t, enums) <= lim()
    &&& match t {
        STy::Tuple(ts) => lim_ss(ts, enums),
        STy::Record(_, ts) => lim_ss(ts, enums),
        STy::Option(x) => lim_s(*x, enums),
        STy::Set(e) => lim_s(*e, enums),
        STy::Map(k, v) => lim_s(*k, enums) && lim_s(*v, enums),
        STy::List(e, max) => max <= lim() && lim_s(*e, enums),
        _ => true,
    }
}

pub open spec fn lim_ss(ts: Seq<STy>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        lim_ss(ts.drop_last(), enums) && lim_s(ts.last(), enums)
    }
}

/// 式の型について、[`lim_s`] と同じ条件。
pub open spec fn lim_x(t: XTy, enums: Seq<i64>) -> bool
    decreases t,
{
    &&& xwidth(t, enums) <= lim()
    &&& match t {
        XTy::Tuple(ts) => lim_xs(ts, enums),
        XTy::Record(_, ts) => lim_xs(ts, enums),
        XTy::Option(x) => lim_x(*x, enums),
        XTy::Set(e) => lim_s(*e, enums),
        XTy::Map(k, v) => lim_s(*k, enums) && lim_s(*v, enums),
        XTy::List(e, max) => max <= lim() && lim_s(*e, enums),
        _ => true,
    }
}

pub open spec fn lim_xs(ts: Seq<XTy>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        lim_xs(ts.drop_last(), enums) && lim_x(ts.last(), enums)
    }
}

/// 列の各要素は条件を満たす。
pub proof fn lemma_lim_ss_at(ts: Seq<STy>, enums: Seq<i64>, i: int)
    requires
        lim_ss(ts, enums),
        0 <= i < ts.len(),
    ensures
        lim_s(ts[i], enums),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        assert(ts.drop_last()[i] == ts[i]);
        lemma_lim_ss_at(ts.drop_last(), enums, i);
    }
}

pub proof fn lemma_lim_xs_at(ts: Seq<XTy>, enums: Seq<i64>, i: int)
    requires
        lim_xs(ts, enums),
        0 <= i < ts.len(),
    ensures
        lim_x(ts[i], enums),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        assert(ts.drop_last()[i] == ts[i]);
        lemma_lim_xs_at(ts.drop_last(), enums, i);
    }
}

/// 幅の和は、先頭の部分の和以上である。
pub proof fn lemma_width_sum_prefix(ts: Seq<STy>, enums: Seq<i64>, i: int)
    requires
        0 <= i <= ts.len(),
    ensures
        width_sum(ts.take(i), enums) <= width_sum(ts, enums),
    decreases ts.len(),
{
    if i < ts.len() {
        assert(ts.drop_last().take(i) =~= ts.take(i));
        lemma_width_sum_prefix(ts.drop_last(), enums, i);
    } else {
        assert(ts.take(i) =~= ts);
    }
}

pub proof fn lemma_xwidth_sum_prefix(ts: Seq<XTy>, enums: Seq<i64>, i: int)
    requires
        0 <= i <= ts.len(),
    ensures
        xwidth_sum(ts.take(i), enums) <= xwidth_sum(ts, enums),
    decreases ts.len(),
{
    if i < ts.len() {
        assert(ts.drop_last().take(i) =~= ts.take(i));
        lemma_xwidth_sum_prefix(ts.drop_last(), enums, i);
    } else {
        assert(ts.take(i) =~= ts);
    }
}

/// 格納の型から作った式の型は、その格納の型に合う。
pub proof fn lemma_to_fits(t: STy)
    ensures
        fits_s(to_xty(t), t),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_to_fits_seq(ts),
        STy::Record(_, ts) => lemma_to_fits_seq(ts),
        STy::Option(x) => lemma_to_fits(*x),
        _ => {},
    }
}

pub proof fn lemma_to_fits_seq(ts: Seq<STy>)
    ensures
        fits_all_s(to_xtys(ts), ts),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_to_fits_seq(ts.drop_last());
        lemma_to_fits(ts.last());
        assert(to_xtys(ts).drop_last() == to_xtys(ts.drop_last()));
    }
}

/// 合う型の幅は等しい。
pub proof fn lemma_fits_width(t: XTy, st: STy, enums: Seq<i64>)
    requires
        fits_s(t, st),
    ensures
        xwidth(t, enums) == width(st, enums),
{
    lemma_fits_to(t, st);
    lemma_xwidth_of(st, enums);
}

/// 格納の型が大きさの条件を満たせば、それから作った式の型も満たす。
pub proof fn lemma_lim_to_x(t: STy, enums: Seq<i64>)
    requires
        lim_s(t, enums),
    ensures
        lim_x(to_xty(t), enums),
    decreases t, 1nat,
{
    lemma_xwidth_of(t, enums);
    match t {
        STy::Tuple(ts) => lemma_lim_to_xs(ts, enums),
        STy::Record(_, ts) => lemma_lim_to_xs(ts, enums),
        STy::Option(x) => lemma_lim_to_x(*x, enums),
        _ => {},
    }
}

pub proof fn lemma_lim_to_xs(ts: Seq<STy>, enums: Seq<i64>)
    requires
        lim_ss(ts, enums),
    ensures
        lim_xs(to_xtys(ts), enums),
        to_xtys(ts).len() == ts.len(),
        xwidth_sum(to_xtys(ts), enums) == width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_lim_to_xs(ts.drop_last(), enums);
        lemma_lim_to_x(ts.last(), enums);
        lemma_xwidth_of(ts.last(), enums);
        assert(to_xtys(ts).drop_last() == to_xtys(ts.drop_last()));
        assert(to_xtys(ts).last() == to_xty(ts.last()));
    }
}

/// 上限を満たす型は、Listの長さの上限が小さい。
pub proof fn lemma_lim_small(t: STy, enums: Seq<i64>)
    requires
        lim_s(t, enums),
    ensures
        small(t),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_lim_smalls(ts, enums),
        STy::Record(_, ts) => lemma_lim_smalls(ts, enums),
        STy::Option(x) => lemma_lim_small(*x, enums),
        STy::Map(_, v) => lemma_lim_small(*v, enums),
        STy::List(e, _) => lemma_lim_small(*e, enums),
        _ => {},
    }
}

pub proof fn lemma_lim_smalls(ts: Seq<STy>, enums: Seq<i64>)
    requires
        lim_ss(ts, enums),
    ensures
        smalls(ts),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_lim_smalls(ts.drop_last(), enums);
        lemma_lim_small(ts.last(), enums);
    }
}

/// 式の型 `t` を格納の型 `st` の場所に置けるなら、`t` は `st` の式の型である。
pub proof fn lemma_fits_to(t: XTy, st: STy)
    requires
        fits_s(t, st),
    ensures
        t == to_xty(st),
    decreases t,
{
    match (t, st) {
        (XTy::Tuple(xs), STy::Tuple(ts)) => lemma_fits_to_seq(xs, ts),
        (XTy::Record(_, xs), STy::Record(_, ts)) => lemma_fits_to_seq(xs, ts),
        (XTy::Option(x), STy::Option(u)) => lemma_fits_to(*x, *u),
        _ => {},
    }
}

pub proof fn lemma_fits_to_seq(xs: Seq<XTy>, ts: Seq<STy>)
    requires
        fits_all_s(xs, ts),
    ensures
        xs == to_xtys(ts),
    decreases xs,
{
    if xs.len() > 0 {
        lemma_fits_to_seq(xs.drop_last(), ts.drop_last());
        lemma_fits_to(xs.last(), ts.last());
        assert(xs =~= xs.drop_last().push(xs.last()));
    } else {
        assert(xs =~= Seq::<XTy>::empty());
    }
}

/// 型の中のどのListも、長さの上限が `0x7fff_ffff` 以下である。
pub open spec fn small(t: STy) -> bool
    decreases t,
{
    match t {
        STy::Tuple(ts) => smalls(ts),
        STy::Record(_, ts) => smalls(ts),
        STy::Option(x) => small(*x),
        STy::Map(_, x) => small(*x),
        STy::List(e, max) => max <= 0x7fff_ffff && small(*e),
        _ => true,
    }
}

pub open spec fn smalls(ts: Seq<STy>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        smalls(ts.drop_last()) && small(ts.last())
    }
}

/// 式の型 `x` の値を、格納の型 `s` の場所に置ける（整数の範囲は問わない）。
pub open spec fn fits_s(x: XTy, s: STy) -> bool
    decreases x,
{
    match (x, s) {
        (XTy::Bool, STy::Bool) => true,
        (XTy::Int, STy::Int(_, _)) => true,
        (XTy::Enum(a), STy::Enum(b)) => a == b,
        (XTy::Tuple(xs), STy::Tuple(ts)) => fits_all_s(xs, ts),
        (XTy::Record(a, xs), STy::Record(b, ts)) => a == b && fits_all_s(xs, ts),
        (XTy::Option(x), STy::Option(u)) => fits_s(*x, *u),
        (XTy::Set(a), STy::Set(b)) => a == b,
        (XTy::Map(ka, va), STy::Map(kb, vb)) => ka == kb && va == vb,
        (XTy::List(a, n), STy::List(b, m)) => n == m && a == b,
        _ => false,
    }
}

pub open spec fn fits_all_s(xs: Seq<XTy>, ts: Seq<STy>) -> bool
    decreases xs,
{
    if xs.len() == 0 {
        ts.len() == 0
    } else {
        ts.len() == xs.len() && fits_all_s(xs.drop_last(), ts.drop_last()) && fits_s(xs.last(), ts.last())
    }
}

} // verus!
