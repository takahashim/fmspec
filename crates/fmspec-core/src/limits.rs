//! 下ろしが大きさの理由で失敗しないための条件（仕様）。
//!
//! 下ろしは、スロットの数や位置を `usize` で計算し、Listの長さと添字を整数のスロットに入れる。
//! そのため、型が付いていても、幅が大きすぎる型や、長さの上限が大きすぎるListでは失敗する。
//! [`lim_s`] と [`lim_x`] は、型とその部分の型の幅が [`LIM`] 以下で、Listの長さの上限も [`LIM`] 以下であることを表す。
//! `fmspec-ir` の上限（幅が65536以下、Listの長さが1024以下）を満たす宣言の型は、この条件を満たす。

#[cfg(verus_keep_ghost)]
use crate::encoding::{width, width_sum, xwidth, xwidth_sum, STy, XTy};
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

} // verus!
