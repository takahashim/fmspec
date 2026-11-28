//! Tuple、Record、Option の下ろし（`low_struct`）。意味の保存は `preserve_tuple` にある。

#[cfg(verus_keep_ghost)]
use crate::canon::lemma_defaults_typed;
use crate::encoding::XType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, lemma_default_len, lemma_xtys, lemma_xwidth_of, sty};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, xty, xtys, xwidth, xwidth_sum, XTy};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, pure_below, split_ok, xoff};
use crate::expr_build::{cb, defaults, split, sub_exprs};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::{lemma_types_of_iff, type_of, types_of};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::extends;
use crate::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{blt, has_ty, lemma_check_typed, lemma_lim_x_small, lemma_tok_ext};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_typed_blk, lemma_typed_concat, lemma_typed_sub, lemma_xetys_of};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_xetys_part, lenv, tok, ty_post, typed, xetys, xetys_seq};
use crate::lowering::{append, copy_usizes, low};
use crate::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::preserve::{frag, lemma_extends_trans, lemma_frag_seq, lemma_lits, lowers};
#[cfg(verus_keep_ghost)]
use crate::preserve_tuple::{lemma_is_some, lemma_none, lemma_part, lemma_seq_base, lemma_seq_step};
#[cfg(verus_keep_ghost)]
use crate::preserve_tuple::{lemma_some, lemma_tuple_done, lemma_unwrap, lowers_seq};
#[cfg(verus_keep_ghost)]
use crate::slots::lemma_extends_refl;
use crate::slots::{check, copy_exprs, need, not};
use crate::source::{TExpr, FAIL_NONE};
use crate::stype_exec::{copy_xtype, to_xtype};
#[cfg(verus_keep_ghost)]
use crate::total::{bound_tys, here_ok, lemma_all_pure_mono, lemma_lim_ok_seq_at, lemma_sc_wf_mono};
#[cfg(verus_keep_ghost)]
use crate::total::{lim_ok, low_post, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::typing::ETy;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// 量化、Tuple、Record、Option。
pub(crate) fn low_struct(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Tuple || e is Record || e is Nth || e is Field || e is None || e is Some || e is IsSome || e is IsNone || e is Unwrap,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 2nat,
{
    match e {
        TExpr::Tuple(_) | TExpr::Record(_, _) => low_tuple(e, cx, sc, blk),
        TExpr::Nth(_, _) | TExpr::Field(_, _, _) => low_proj(e, cx, sc, blk),
        _ => low_opt(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_tuple(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Tuple || e is Record,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Tuple(es) | TExpr::Record(_, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            if es.len() == 0 {
                return Err(Fail::Type);
            }
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            proof {
                lemma_types_of_iff(es@, c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
                lemma_xtys(Seq::<XType>::empty());
            }
            proof {
                lemma_extends_refl(*blk);
                lemma_seq_base(*cx, sc0, b0);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
            }
            let mut ts: Vec<XType> = Vec::new();
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= es@.len(),
                    ts@.len() == i,
                    (e is Tuple || e is Record) && (e is Tuple ==> e->Tuple_0 == *es) && (e is Record ==> e->Record_1 == *es),
                    frag(*e) ==> lowers_seq(es@.take(i as int), *cx, sc0, b0, *blk, xtys(ts@), out@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> type_of(#[trigger] es@[j], c, bt) is Some && lim_ok(
                        es@[j],
                        c,
                        bt,
                    ),
                    pre ==> types_of(es@.take(i as int), c, bt) == Some(xtys(ts@)),
                    pre ==> out@.len() == xwidth_sum(xtys(ts@), cx.enums@) && all_pure(out@, blk.depth_s()),
                    tp == (pre && tok(*cx, sc0, b0)),
                    tv == lenv(*cx),
                    tp ==> tok(*cx, sc0, *blk) && typed(out@, xetys_seq(xtys(ts@), cx.enums@), tv, blt(*blk, *cx)),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost o1 = out@;
                let ghost t1 = ts@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(type_of(es@[i as int], c, bt) is Some && lim_ok(es@[i as int], c, bt));
                    }
                }
                let (t, s) = low(&es[i], cx, sc, blk)?;
                let ghost tg = t;
                ts.push(t);
                append(&mut out, &s);
                proof {
                    assert(ts@.drop_last() == t1);
                    assert(xtys(ts@) == xtys(t1).push(xty(t)));
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    assert(es@.take(i + 1).last() == es@[i as int]);
                    if pre {
                        lemma_all_pure_mono(o1, b1.depth_s(), blk.depth_s());
                        assert(xtys(ts@).drop_last() == xtys(t1));
                        assert(all_pure(out@, blk.depth_s())) by {
                            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                                if j < o1.len() {
                                    assert(out@[j] == o1[j]);
                                } else {
                                    assert(out@[j] == s@[j - o1.len()]);
                                }
                            }
                        }
                    }
                }
                proof {
                    if tp {
                        lemma_typed_blk(o1, xetys_seq(xtys(t1), cx.enums@), *cx, b1, *blk);
                        lemma_typed_concat(o1, xetys_seq(xtys(t1), cx.enums@), s@, xetys(xty(tg), cx.enums@), tv, blt(*blk, *cx));
                        assert(xtys(ts@).drop_last() == xtys(t1));
                        assert(xtys(ts@).last() == xty(tg));
                        assert(xetys_seq(xtys(ts@), cx.enums@) == xetys_seq(xtys(t1), cx.enums@) + xetys(xty(tg), cx.enums@));
                        lemma_tok_ext(*cx, sc0, b1, *blk);
                    }
                    lemma_extends_trans(*old(blk), b1, *blk);
                    lemma_xtys(t1);
                    lemma_xtys(ts@);
                    assert(xtys(ts@) =~= xtys(t1).push(xty(tg)));
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    if frag(*e) {
                        lemma_frag_seq(es@, i as int);
                        lemma_seq_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, xtys(t1), o1, xty(tg), s@);
                    }
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
                if tp {
                    lemma_xtys(ts@);
                }
            }
            match e {
                TExpr::Record(names, _) => {
                    let nm = copy_usizes(names);
                    proof {
                        if frag(*e) {
                            lemma_tuple_done(*e, es@, *cx, sc0, b0, *blk, xtys(ts@), out@);
                        }
                    }
                    Ok((XType::Record(nm, ts), out))
                },
                _ => {
                    proof {
                        if frag(*e) {
                            lemma_tuple_done(*e, es@, *cx, sc0, b0, *blk, xtys(ts@), out@);
                        }
                    }
                    Ok((XType::Tuple(ts), out))
                },
            }
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_proj(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Nth || e is Field,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Nth(a, i) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Tuple(ts) => {
                    proof {
                        lemma_xtys(ts@);
                        if pre {
                            assert(lim_ok(**a, c, bt));
                            assert(here_ok(**a, c, bt));
                        }
                    }
                    let parts = need(split(&ts, &slots, enums))?;
                    if *i < ts.len() && *i < parts.len() {
                        let x = copy_exprs(&parts[*i]);
                        let u = copy_xtype(&ts[*i]);
                        proof {
                            if pre {
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                let o = xoff(xtys(ts@), *i as int, enums@);
                                assert(all_pure(x@, blk.depth_s())) by {
                                    assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                                        assert(x@[j] == slots@[o + j]);
                                    }
                                }
                            }
                        }
                        proof {
                            if tp {
                                let xt = xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xt, *i as int, enums@));
                                lemma_xetys_part(xt, *i as int, enums@);
                                assert(typed(slots@, xetys_seq(xt, enums@), tv, blt(*blk, *cx)));
                                lemma_typed_sub(slots@, xetys_seq(xt, enums@), tv, blt(*blk, *cx), xoff(xt, *i as int, enums@), xoff(xt, *i as int, enums@) + xwidth(xt[*i as int], enums@));
                                assert(xty(u) == xt[*i as int]);
                            }
                            if frag(*e) {
                                lemma_xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                lemma_part(*e, **a, *i, *cx, sc@, b0, *blk, xtys(ts@), slots@, x@);
                            }
                        }
                        Ok((u, x))
                    } else {
                        Err(Fail::Type)
                    }
                },
                _ => Err(Fail::Type),
            }
        },
        TExpr::Field(a, name, i) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Record(names, ts) => {
                    proof {
                        lemma_xtys(ts@);
                        if pre {
                            assert(lim_ok(**a, c, bt));
                            assert(here_ok(**a, c, bt));
                        }
                    }
                    let parts = need(split(&ts, &slots, enums))?;
                    if *i < ts.len() && *i < parts.len() && *i < names.len() && names[*i] == *name {
                        let x = copy_exprs(&parts[*i]);
                        let u = copy_xtype(&ts[*i]);
                        proof {
                            if pre {
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                let o = xoff(xtys(ts@), *i as int, enums@);
                                assert(all_pure(x@, blk.depth_s())) by {
                                    assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                                        assert(x@[j] == slots@[o + j]);
                                    }
                                }
                            }
                        }
                        proof {
                            if tp {
                                let xt = xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xt, *i as int, enums@));
                                lemma_xetys_part(xt, *i as int, enums@);
                                assert(typed(slots@, xetys_seq(xt, enums@), tv, blt(*blk, *cx)));
                                lemma_typed_sub(slots@, xetys_seq(xt, enums@), tv, blt(*blk, *cx), xoff(xt, *i as int, enums@), xoff(xt, *i as int, enums@) + xwidth(xt[*i as int], enums@));
                                assert(xty(u) == xt[*i as int]);
                            }
                            if frag(*e) {
                                lemma_xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                lemma_part(*e, **a, *i, *cx, sc@, b0, *blk, xtys(ts@), slots@, x@);
                            }
                        }
                        Ok((u, x))
                    } else {
                        Err(Fail::Type)
                    }
                },
                _ => Err(Fail::Type),
            }
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
pub(crate) fn low_opt(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is None || e is Some || e is IsSome || e is IsNone || e is Unwrap,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::None(_) => low_none(e, cx, sc, blk),
        TExpr::Some(_) => low_some(e, cx, sc, blk),
        TExpr::IsSome(_) | TExpr::IsNone(_) => low_is_some(e, cx, sc, blk),
        _ => low_unwrap(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
#[allow(unused_variables)]
pub(crate) fn low_none(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is None,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::None(t) => {
            proof {
                lemma_extends_refl(*blk);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(false));
            let ds = defaults(t, enums);
            append(&mut out, &ds);
            let u = to_xtype(t);
            proof {
                lemma_default_len(sty(*t), enums@);
                lemma_xwidth_of(sty(*t), enums@);
                lemma_lits(enc(default_val(sty(*t), enums@), sty(*t), enums@), arbitrary(), Seq::empty());
                if pre {
                    assert(all_pure(out@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(out@[j] == ds@[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                if tp {
                    let st = sty(*t);
                    assert(type_of(*e, c, bt) == Some(XTy::Option(Box::new(to_xty(st)))));
                    assert(here_ok(*e, c, bt));
                    assert(crate::encoding::wf_stype(st, enums@));
                    lemma_lim_x_small(st, enums@);
                    lemma_defaults_typed(st, tv, blt(*blk, *cx));
                    lemma_xetys_of(st, enums@);
                    assert(xty(u) == to_xty(st));
                    let ys = xetys(to_xty(st), enums@);
                    assert(xetys(xty(XType::Option(Box::new(u))), enums@) == seq![ETy::Bool] + ys);
                    assert forall|j: int| 0 <= j < out@.len() implies #[trigger] has_ty(out@[j], tv, blt(*blk, *cx), (seq![ETy::Bool] + ys)[j]) by {
                        if j > 0 {
                            assert(out@[j] == ds@[j - 1]);
                        }
                    }
                }
                lemma_none(*e, sty(*t), *cx, sc@, *blk, out@);
            }
            Ok((XType::Option(Box::new(u)), out))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
#[allow(unused_variables)]
pub(crate) fn low_some(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Some,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Some(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(true));
            append(&mut out, &s);
            proof {
                if pre {
                    assert(all_pure(out@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(out@[j] == s@[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                if frag(*e) {
                    lemma_some(*e, **a, *cx, sc@, b0, *blk, xty(t), s@, out@);
                }
                if tp {
                    let ys = xetys(xty(t), enums@);
                    assert(xetys(xty(XType::Option(Box::new(t))), enums@) == seq![ETy::Bool] + ys);
                    assert forall|j: int| 0 <= j < out@.len() implies #[trigger] has_ty(out@[j], tv, blt(*blk, *cx), (seq![ETy::Bool] + ys)[j]) by {
                        if j > 0 {
                            assert(out@[j] == s@[j - 1]);
                        }
                    }
                }
            }
            Ok((XType::Option(Box::new(t)), out))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
#[allow(unused_variables)]
pub(crate) fn low_is_some(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is IsSome || e is IsNone,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::IsSome(a) | TExpr::IsNone(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let ghost xt = xty(t);
            match t {
                XType::Option(_) => {},
                _ => return Err(Fail::Type),
            }
            if s.len() == 0 {
                return Err(Fail::Type);
            }
            let tag = copy_expr(&s[0]);
            let mut out: Vec<Expr> = Vec::new();
            match e {
                TExpr::IsSome(_) => out.push(tag),
                _ => out.push(not(tag)),
            }
            proof {
                if pre {
                    assert(pure_below(s@[0], blk.depth_s()));
                    assert(pure_below(out@[0], blk.depth_s()));
                }
            }
            proof {
                if frag(*e) {
                    lemma_is_some(*e, **a, *cx, sc@, b0, *blk, xt, s@, out@);
                }
                if tp {
                    assert(xetys(xt, enums@)[0] == ETy::Bool);
                    assert(has_ty(tag, tv, blt(*blk, *cx), ETy::Bool));
                }
            }
            Ok((XType::Bool, out))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
#[allow(unused_variables)]
pub(crate) fn low_unwrap(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Unwrap,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Unwrap(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let inner = match t {
                XType::Option(x) => *x,
                _ => return Err(Fail::Type),
            };
            if s.len() == 0 {
                return Err(Fail::Type);
            }
            let ghost cond = s@[0];
            proof {
                if tp {
                    assert(xetys(xty(t), enums@) == seq![ETy::Bool] + xetys(xty(inner), enums@));
                    assert((seq![ETy::Bool] + xetys(xty(inner), enums@))[0] == ETy::Bool);
                    assert(has_ty(cond, tv, blt(b1, *cx), (seq![ETy::Bool] + xetys(xty(inner), enums@))[0]));
                }
            }
            check(blk, copy_expr(&s[0]), FAIL_NONE)?;
            let x = sub_exprs(&s, 1, s.len());
            proof {
                if tp {
                    lemma_check_typed(b1, *blk, cond, FAIL_NONE, *cx);
                    let ys = xetys(xty(inner), enums@);
                    lemma_typed_sub(s@, seq![ETy::Bool] + ys, tv, blt(b1, *cx), 1, s@.len() as int);
                    assert((seq![ETy::Bool] + ys).subrange(1, s@.len() as int) =~= ys);
                    assert(x@ =~= s@.subrange(1, s@.len() as int));
                    lemma_all_pure_mono(s@, b1.depth_s(), b1.depth_s());
                    assert(all_pure(x@, b1.depth_s()));
                    lemma_typed_blk(x@, ys, *cx, b1, *blk);
                }
            }
            proof {
                if pre {
                    lemma_all_pure_mono(s@, b1.depth_s(), blk.depth_s());
                    assert(all_pure(x@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                            assert(x@[j] == s@[j + 1]);
                        }
                    }
                }
            }
            proof {
                lemma_extends_trans(b0, b1, *blk);
                if frag(*e) {
                    lemma_unwrap(*e, **a, *cx, sc@, b0, b1, *blk, xty(inner), s@, x@);
                }
            }
            Ok((inner, x))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

} // verus!
