//! Set のリテラル、所属、要素の追加と削除、和と積と差の下ろし。意味の保存は `preserve_set` にある。

use crate::encoding::XType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, keys_or_zero, sty, to_xty, wf_stype, wf_xtype, xty, STy, XTy};
use crate::expr_build::{all_of, and, bin, cb, ci, eq, implies, or};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, mark_s, pure_below, setop_s, Join};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::{ir_type_of, lemma_all_typed_iff};
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_small, small};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::extends;
use crate::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{all_ty, blt, has_ty, lemma_and_typed, lemma_bools_typed, lemma_ge0_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_has_ty_blk, lemma_tok_ext, lemma_tree_typed, lemma_typed_blk};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_typed_bools, lenv, tok, ty_post, xetys};
use crate::lowering::{element_rank, lookup_rank, low};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
use crate::model::{BinOp, Expr};
#[cfg(verus_keep_ghost)]
use crate::preserve::{frag, lemma_extends_trans, lemma_frag_seq, lemma_tree_pure, lowers};
#[cfg(verus_keep_ghost)]
use crate::preserve_set::{lemma_insert, lemma_remove, lemma_set_contains, lemma_setbin};
#[cfg(verus_keep_ghost)]
use crate::preserve_set::{lemma_setlit_base, lemma_setlit_step, setlit_ok};
use crate::quant::pick_slot;
#[cfg(verus_keep_ghost)]
use crate::slots::lemma_extends_refl;
use crate::slots::not;
use crate::source::{SetOp, TExpr};
use crate::stype_exec::{copy_stype, keys_exec, keys_or_zero_exec, stype_eq, xtype_eq};
#[cfg(verus_keep_ghost)]
use crate::total::{bound_tys, here_ok, lemma_all_pure_mono, lemma_lim_ok_seq_at, lemma_mark_pure};
#[cfg(verus_keep_ghost)]
use crate::total::{lemma_sc_wf_mono, lemma_setop_pure, lim_ok, low_post, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

/// Bool の式どうしの集合の演算の式は Bool の型を持つ。
pub(crate) proof fn lemma_setop_typed(op: SetOp, x: Expr, y: Expr, tv: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(x, tv, lt, ETy::Bool),
        has_ty(y, tv, lt, ETy::Bool),
    ensures
        has_ty(setop_s(op, x, y), tv, lt, ETy::Bool),
{
    assert(has_ty(Expr::Not(Box::new(y)), tv, lt, ETy::Bool));
    lemma_and_typed(x, y, tv, lt);
    lemma_and_typed(x, Expr::Not(Box::new(y)), tv, lt);
    match op {
        SetOp::Union => {
            assert(has_ty(Expr::Or(Box::new(x), Box::new(y)), tv, lt, ETy::Bool));
        },
        SetOp::Subset => {
            assert(has_ty(Expr::Implies(Box::new(x), Box::new(y)), tv, lt, ETy::Bool));
        },
        _ => {},
    }
}

/// Setのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_set_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is SetLit,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::SetLit(t, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            if keys_exec(t, enums).is_none() {
                return Err(Fail::Type);
            }
            let n = keys_or_zero_exec(t, enums);
            if n > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let mut bits: Vec<Expr> = Vec::new();
            let mut k = 0;
            while k < n
                invariant
                    k <= n,
                    bits@ =~= Seq::new(k as nat, |_j: int| bool_lit(false)),
                decreases n - k,
            {
                bits.push(cb(false));
                k += 1;
            }
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            proof {
                lemma_all_typed_iff(es@, to_xty(sty(*t)), c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
            }
            proof {
                lemma_setlit_base(*cx, sc0, b0, sty(*t), bits@);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
                if tp {
                    assert(here_ok(*e, c, bt));
                    assert(wf_stype(sty(*t), enums@));
                    lemma_lim_small(sty(*t), enums@);
                    assert forall|j: int| 0 <= j < bits@.len() implies #[trigger] has_ty(bits@[j], tv, blt(b0, *cx), ETy::Bool) by {
                        assert(bits@[j] == bool_lit(false));
                    }
                }
            }
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= es@.len(),
                    bits@.len() == n,
                    n <= 0x7fff_ffff,
                    e is SetLit && e->SetLit_1 == *es && e->SetLit_0 == *t,
                    frag(*e) ==> setlit_ok(es@.take(i as int), *cx, sc0, b0, *blk, sty(*t), bits@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> keys(sty(*t), enums@) is Some && n == keys_or_zero(sty(*t), enums@),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> ir_type_of(#[trigger] es@[j], c, bt) == Some(to_xty(sty(*t)))
                        && lim_ok(es@[j], c, bt),
                    pre ==> all_pure(bits@, blk.depth_s()),
                    tp == (pre && tok(*cx, sc0, b0)),
                    tv == lenv(*cx),
                    tp ==> wf_stype(sty(*t), enums@) && small(sty(*t)),
                    tp ==> tok(*cx, sc0, *blk) && all_ty(bits@, ETy::Bool, tv, blt(*blk, *cx)),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost bv = bits@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(ir_type_of(es@[i as int], c, bt) == Some(to_xty(sty(*t))) && lim_ok(es@[i as int], c, bt));
                    }
                }
                let r = element_rank(&es[i], cx, sc, blk, t)?;
                let ghost bv2 = bits@;
                bits = mark(&bits, &r, true);
                proof {
                    if pre {
                        lemma_all_pure_mono(bv2, b1.depth_s(), blk.depth_s());
                        lemma_mark_pure(true, bv2, r, bits@, blk.depth_s());
                    }
                    if tp {
                        assert forall|j: int| 0 <= j < bv2.len() implies #[trigger] has_ty(bv2[j], tv, blt(*blk, *cx), ETy::Bool) by {
                            assert(has_ty(bv2[j], tv, blt(b1, *cx), ETy::Bool));
                            lemma_has_ty_blk(bv2[j], ETy::Bool, *cx, b1, *blk);
                        }
                        lemma_mark_typed(true, bv2, r, bits@, tv, blt(*blk, *cx));
                        lemma_tok_ext(*cx, sc0, b1, *blk);
                    }
                }
                proof {
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    if frag(*e) {
                        lemma_frag_seq(es@, i as int);
                        lemma_setlit_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, sty(*t), bv, r, bits@);
                    }
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
                if tp {
                    lemma_bools_typed(bits@, n as nat, tv, blt(*blk, *cx));
                }
            }
            Ok((XType::Set(Box::new(copy_stype(t))), bits))
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
#[verifier::rlimit(120)]
pub(crate) fn low_member(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is SetContains,
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
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::SetContains(t, a, x) => {
            let ghost b0 = *blk;
            let (tc, cs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let elem = match tc {
                XType::Set(u) => *u,
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&elem, t) || cs.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    assert(wf_xtype(XTy::Set(Box::new(sty(elem))), cx.enums@));
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            proof {
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                    lemma_lim_small(sty(elem), cx.enums@);
                }
            }
            let r = lookup_rank(x, cx, sc, blk, &elem)?;
            let ghost rg = r;
            let hit = pick_slot(&cs, &r);
            let ghost hg = hit;
            let mut out: Vec<Expr> = Vec::new();
            out.push(and(bin(BinOp::Ge, r, ci(0)), hit));
            proof {
                if tp {
                    let n = keys_or_zero(sty(elem), cx.enums@);
                    lemma_all_pure_mono(cs@, b1.depth_s(), blk.depth_s());
                    lemma_typed_blk(cs@, xetys(XTy::Set(Box::new(sty(elem))), cx.enums@), *cx, b1, *blk);
                    lemma_typed_bools(cs@, n, tv, blt(*blk, *cx));
                    lemma_ge0_typed(rg, tv, blt(*blk, *cx));
                    if cs@.len() > 0 {
                        assert(all_ty(cs@, ETy::Bool, tv, blt(*blk, *cx)));
                    }
                    lemma_and_typed(
                        Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                        hg,
                        tv,
                        blt(*blk, *cx),
                    );
                }
                if pre {
                    lemma_all_pure_mono(cs@, b1.depth_s(), blk.depth_s());
                    crate::quant::lemma_hit_pure(rg, cs@, hg, blk.depth_s());
                    assert(out@[0] == crate::expr_build::and_s(
                        Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                        hg,
                    ));
                }
            }
            proof {
                if frag(*e) {
                    lemma_set_contains(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, cs@, rg, hg, out@);
                }
            }
            Ok((XType::Bool, out))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_setop(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Insert || e is Remove || e is SetBin,
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
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Insert(t, a, x) | TExpr::Remove(t, a, x) => {
            let ghost b0 = *blk;
            let (ts, bits) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let elem = match &ts {
                XType::Set(u) => copy_stype(u),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&elem, t) || bits.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    assert(wf_xtype(XTy::Set(Box::new(sty(elem))), cx.enums@));
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                    lemma_lim_small(sty(elem), cx.enums@);
                }
            }
            let ghost nk = keys_or_zero(sty(elem), cx.enums@);
            let slots = match e {
                TExpr::Insert(_, _, _) => {
                    let r = element_rank(x, cx, sc, blk, &elem)?;
                    let out = mark(&bits, &r, true);
                    proof {
                        if pre {
                            lemma_all_pure_mono(bits@, b1.depth_s(), blk.depth_s());
                            lemma_mark_pure(true, bits@, r, out@, blk.depth_s());
                        }
                        if tp {
                            lemma_typed_blk(bits@, xetys(xty(ts), cx.enums@), *cx, b1, *blk);
                            lemma_typed_bools(bits@, nk, tv, blt(*blk, *cx));
                            lemma_mark_typed(true, bits@, r, out@, tv, blt(*blk, *cx));
                            lemma_bools_typed(out@, nk, tv, blt(*blk, *cx));
                        }
                    }
                    proof {
                        if frag(*e) {
                            lemma_insert(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, bits@, r, out@);
                        }
                    }
                    out
                },
                _ => {
                    let r = lookup_rank(x, cx, sc, blk, &elem)?;
                    let out = mark(&bits, &r, false);
                    proof {
                        if pre {
                            lemma_all_pure_mono(bits@, b1.depth_s(), blk.depth_s());
                            lemma_mark_pure(false, bits@, r, out@, blk.depth_s());
                        }
                        if tp {
                            lemma_typed_blk(bits@, xetys(xty(ts), cx.enums@), *cx, b1, *blk);
                            lemma_typed_bools(bits@, nk, tv, blt(*blk, *cx));
                            lemma_mark_typed(false, bits@, r, out@, tv, blt(*blk, *cx));
                            lemma_bools_typed(out@, nk, tv, blt(*blk, *cx));
                        }
                    }
                    proof {
                        if frag(*e) {
                            lemma_remove(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, bits@, r, out@);
                        }
                    }
                    out
                },
            };
            Ok((ts, slots))
        },
        TExpr::SetBin(op, a, b) => {
            let ghost b0 = *blk;
            let (ta, xs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (tb, ys) = low(b, cx, sc, blk)?;
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_all_pure_mono(xs@, b1.depth_s(), b2.depth_s());
                }
            }
            let ghost u = match xty(ta) {
                XTy::Set(u) => *u,
                _ => STy::Bool,
            };
            match &ta {
                XType::Set(_) => {},
                _ => return Err(Fail::Type),
            }
            if !xtype_eq(&tb, &ta) {
                return Err(Fail::Type);
            }
            let ghost nk = keys_or_zero(u, cx.enums@);
            proof {
                if tp {
                    lemma_typed_blk(xs@, xetys(xty(ta), cx.enums@), *cx, b1, b2);
                    lemma_typed_bools(xs@, nk, tv, blt(b2, *cx));
                    lemma_typed_bools(ys@, nk, tv, blt(b2, *cx));
                }
            }
            let n = if xs.len() < ys.len() {
                xs.len()
            } else {
                ys.len()
            };
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= xs.len(),
                    n <= ys.len(),
                    i <= n,
                    out@.len() == i,
                    forall|q: int| 0 <= q < i ==> #[trigger] out@[q] == setop_s(*op, xs@[q], ys@[q]),
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    *blk == b2,
                    pre ==> all_pure(xs@, b2.depth_s()) && all_pure(ys@, b2.depth_s()) && xs@.len() == ys@.len(),
                    pre ==> all_pure(out@, b2.depth_s()),
                    tp == (pre && tok(*cx, old(sc)@, *old(blk))),
                    tv == lenv(*cx),
                    tp ==> all_ty(xs@, ETy::Bool, tv, blt(b2, *cx)) && all_ty(ys@, ETy::Bool, tv, blt(b2, *cx)),
                    tp ==> all_ty(out@, ETy::Bool, tv, blt(b2, *cx)),
                decreases n - i,
            {
                let x = copy_expr(&xs[i]);
                let y = copy_expr(&ys[i]);
                out.push(
                    match op {
                        SetOp::Union => or(x, y),
                        SetOp::Intersection => and(x, y),
                        SetOp::Difference => and(x, not(y)),
                        SetOp::Subset => implies(x, y),
                    },
                );
                proof {
                    if pre {
                        lemma_setop_pure(*op, xs@[i as int], ys@[i as int], b2.depth_s());
                        assert forall|q: int| 0 <= q < out@.len() implies pure_below(#[trigger] out@[q], b2.depth_s()) by {
                            assert(out@[q] == setop_s(*op, xs@[q], ys@[q]));
                            lemma_setop_pure(*op, xs@[q], ys@[q], b2.depth_s());
                        }
                    }
                    if tp {
                        assert forall|q: int| 0 <= q < out@.len() implies #[trigger] has_ty(out@[q], tv, blt(b2, *cx), ETy::Bool) by {
                            assert(out@[q] == setop_s(*op, xs@[q], ys@[q]));
                            assert(has_ty(xs@[q], tv, blt(b2, *cx), ETy::Bool));
                            assert(has_ty(ys@[q], tv, blt(b2, *cx), ETy::Bool));
                            lemma_setop_typed(*op, xs@[q], ys@[q], tv, blt(b2, *cx));
                        }
                    }
                }
                i += 1;
            }
            proof {
                if frag(*e) {
                    lemma_setbin(*e, *op, **a, **b, *cx, sc@, b0, b1, b2, xty(ta), xs@, ys@, out@);
                }
            }
            match op {
                SetOp::Subset => {
                    let mut r: Vec<Expr> = Vec::new();
                    r.push(all_of(&out));
                    proof {
                        if pre {
                            lemma_tree_pure(out@, bool_lit(true), Join::And, b2.depth_s());
                        }
                        if tp {
                            lemma_tree_typed(out@, bool_lit(true), Join::And, tv, blt(b2, *cx), ETy::Bool);
                        }
                    }
                    Ok((XType::Bool, r))
                },
                _ => {
                    proof {
                        lemma_extends_trans(b0, b1, b2);
                        if tp {
                            lemma_bools_typed(out@, nk, tv, blt(b2, *cx));
                        }
                    }
                    Ok((ta, out))
                },
            }
        },
        _ => Err(Fail::Type),
    }
}

/// Setのスロット `bits` の、番号 `r` の位置を `on` にする。
pub(crate) fn mark(bits: &Vec<Expr>, r: &Expr, on: bool) -> (out: Vec<Expr>)
    requires
        bits@.len() <= 0x7fff_ffff,
    ensures
        out@.len() == bits@.len(),
        forall|k: int| 0 <= k < bits@.len() ==> #[trigger] out@[k] == mark_s(on, bits@[k], *r, k as i64),
{
    let mut out: Vec<Expr> = Vec::new();
    let mut k = 0;
    while k < bits.len()
        invariant
            bits@.len() <= 0x7fff_ffff,
            k <= bits@.len(),
            out@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] out@[q] == mark_s(on, bits@[q], *r, q as i64),
        decreases bits.len() - k,
    {
        let bit = copy_expr(&bits[k]);
        out.push(
            if on {
                or(bit, eq(copy_expr(r), ci(k as i64)))
            } else {
                and(bit, bin(BinOp::Ne, copy_expr(r), ci(k as i64)))
            },
        );
        k += 1;
    }
    out
}

/// 番号の位置を変えた Set のスロットは、どれも Bool の型を持つ。
pub(crate) proof fn lemma_mark_typed(on: bool, bits: Seq<Expr>, r: Expr, out: Seq<Expr>, tv: TyEnv, lt: Seq<ETy>)
    requires
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(on, bits[k], r, k as i64),
        all_ty(bits, ETy::Bool, tv, lt),
        has_ty(r, tv, lt, ETy::Int),
    ensures
        all_ty(out, ETy::Bool, tv, lt),
{
    assert forall|k: int| 0 <= k < out.len() implies #[trigger] has_ty(out[k], tv, lt, ETy::Bool) by {
        assert(out[k] == mark_s(on, bits[k], r, k as i64));
        assert(has_ty(bits[k], tv, lt, ETy::Bool));
        assert(has_ty(Expr::Const(Value::Int(k as i64)), tv, lt, ETy::Int));
        assert(has_ty(Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64)))), tv, lt, ETy::Bool));
        assert(has_ty(Expr::Bin(BinOp::Ne, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64)))), tv, lt, ETy::Bool));
    }
}

} // verus!
