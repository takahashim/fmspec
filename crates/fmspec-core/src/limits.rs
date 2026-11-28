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
#[cfg(verus_keep_ghost)]
use crate::fits::{fits_s, lemma_fits_to};
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

/// 型の中のどのListも、長さの上限が `lim()` 以下である。
pub open spec fn small(t: STy) -> bool
    decreases t,
{
    match t {
        STy::Tuple(ts) => smalls(ts),
        STy::Record(_, ts) => smalls(ts),
        STy::Option(x) => small(*x),
        STy::Map(_, x) => small(*x),
        STy::List(e, max) => max <= lim() && small(*e),
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

pub proof fn lemma_lim_ss_intro(ts: Seq<STy>, enums: Seq<i64>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> lim_s(#[trigger] ts[i], enums),
    ensures
        lim_ss(ts, enums),
    decreases ts.len(),
{
    if ts.len() > 0 {
        assert forall|i: int| 0 <= i < ts.len() - 1 implies lim_s(#[trigger] ts.drop_last()[i], enums) by {
            assert(ts.drop_last()[i] == ts[i]);
        }
        lemma_lim_ss_intro(ts.drop_last(), enums);
    }
}

pub proof fn lemma_lim_xs_intro(ts: Seq<XTy>, enums: Seq<i64>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> lim_x(#[trigger] ts[i], enums),
    ensures
        lim_xs(ts, enums),
    decreases ts.len(),
{
    if ts.len() > 0 {
        assert forall|i: int| 0 <= i < ts.len() - 1 implies lim_x(#[trigger] ts.drop_last()[i], enums) by {
            assert(ts.drop_last()[i] == ts[i]);
        }
        lemma_lim_xs_intro(ts.drop_last(), enums);
    }
}

} // verus!
