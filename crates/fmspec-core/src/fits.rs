//! 値の型を、格納の型の場所に置けるか（`fits_s`）の仕様と、両向きの補題。実行時の検査（`fits`）は `stype_exec` にある。`fits_s(t, st)` は `t == to_xty(st)` と同値である（`lemma_fits_iff`）。

#[cfg(verus_keep_ghost)]
use crate::encoding::{STy, to_xty, to_xtys, XTy};
use vstd::prelude::*;

verus! {

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


/// 値の型を格納の型の場所に置けるのは、値の型が格納の型の値の型であるときだけである。
pub proof fn lemma_fits_iff(t: XTy, st: STy)
    ensures
        fits_s(t, st) <==> t == to_xty(st),
{
    if fits_s(t, st) {
        lemma_fits_to(t, st);
    }
    if t == to_xty(st) {
        lemma_to_fits(st);
    }
}

pub proof fn lemma_fits_all(xs: Seq<XTy>, ts: Seq<STy>)
    ensures
        fits_all_s(xs, ts) <==> (xs.len() == ts.len() && forall|i: int|
            0 <= i < xs.len() ==> #[trigger] fits_s(xs[i], ts[i])),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_fits_all(xs.drop_last(), ts.drop_last());
        if xs.len() == ts.len() && forall|i: int| 0 <= i < xs.len() ==> #[trigger] fits_s(xs[i], ts[i]) {
            assert forall|i: int| 0 <= i < xs.drop_last().len() implies #[trigger] fits_s(
                xs.drop_last()[i],
                ts.drop_last()[i],
            ) by {
                assert(fits_s(xs[i], ts[i]));
            }
            assert(fits_s(xs[xs.len() - 1], ts[ts.len() - 1]));
        }
        if fits_all_s(xs, ts) {
            assert forall|i: int| 0 <= i < xs.len() implies #[trigger] fits_s(xs[i], ts[i]) by {
                if i < xs.len() - 1 {
                    assert(fits_s(xs.drop_last()[i], ts.drop_last()[i]));
                }
            }
        }
    }
}

} // verus!
