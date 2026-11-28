//! 量化（`forall`、`exists`）の下ろし。たどる値の型、Set、Map、List ごとの展開。意味の保存は `preserve_quant` にある。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{as_bool, eval_l, Env, ErrKind};
use crate::kernel::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
use crate::kernel::model::{BinOp, Expr, Type};
#[cfg(verus_keep_ghost)]
use crate::kernel::typing::{ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use crate::lower::lowering::low_ok;
use crate::lower::lowering::{bool_in, low};
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_quant::{combine_ok, lemma_over_list, lemma_over_map, lemma_over_set};
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_quant::{lemma_over_type, lemma_quant, list_col, over_ok, quant_s};
#[cfg(verus_keep_ghost)]
use crate::slot::block::lemma_extends_refl;
use crate::slot::block::{bind, depth, need};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{all_pure, bool_lit, lemma_all_pure_mono, lemma_pure_mono, lits, pure_below};
use crate::slot::expr_build::{bin, cb, defaults, is_bool_lit};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{extends, ok_x, sc_wf, shaped};
use crate::slot::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{all_ty, binds_typed, blt, etys, has_ty, lemma_all_ty_push};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_bind_typed, lemma_has_ty_push, lemma_list_col_typed, lemma_lt_typed};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_map_flags_typed, lemma_tok_ext, lemma_top_typed, lemma_typed_bools};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_typed_ext, lemma_xetys_of, lenv, tok, tok_in, typed, xetys};
#[cfg(verus_keep_ghost)]
use crate::slot::members::lemma_defaults_typed;
use crate::slot::pick::pick_slot;
#[cfg(verus_keep_ghost)]
use crate::slot::pick::picks;
use crate::slot::quant::unrank;
#[cfg(verus_keep_ghost)]
use crate::slot::quant::unrank_ok;
#[cfg(verus_keep_ghost)]
use crate::slot::slot_types::slot_tys;
#[cfg(verus_keep_ghost)]
use crate::slot::total::{bound_tys, deep, here_ok, lemma_ok_to_x, lemma_sc_wf_mono, lim_ok, n_ok_set};
#[cfg(verus_keep_ghost)]
use crate::slot::total::{ok_s, quant_bound, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{default_val, enc, keys_or_zero, lemma_default_len, lemma_xwidth_of, sty, STy};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{to_xty, wf_stype, width, xty, XTy};
use crate::value::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::value::infer::ir_type_of;
#[cfg(verus_keep_ghost)]
use crate::value::limits::{lemma_lim_small, lim_s, small};
use crate::value::source::{Over, TExpr};
use crate::value::stype_exec::{copy_stype, keys_exec, stype_eq, stype_width, to_xtype};
use vstd::prelude::*;

verus! {

/// 量化がたどる値の領域（`over_ok`）。候補の位置を `count` 個並べ、位置を局所変数として、
/// `guard` がその位置をたどるかを、`slots` がその位置の値を表す。
pub(crate) struct QuantDomain {
    /// たどる値の格納の型。
    pub ty: SType,
    /// 位置を局所変数とする式で、その位置の値をたどるかを表す。
    pub guard: Expr,
    /// 候補の位置の数。
    pub count: usize,
    /// 位置を局所変数とするスロットの式で、その位置の値を表す。
    pub slots: Vec<Expr>,
}

/// 量化でたどる値の型、位置が対象に含まれるかのガード、位置の数、束縛する値のスロットを求める。
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub(crate) fn quant_over(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<QuantDomain, Fail>)
    requires
        old(blk).wf(),
        e is Quant,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> n <= 0x7fff_ffff && (over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> wf_stype(sty(st), cx.enums@) && small(sty(st)) && has_ty(
            g,
            lenv(*cx),
            blt(*final(blk), *cx).push(ETy::Int),
            ETy::Bool,
        ) && typed(us@, etys(slot_tys(sty(st), cx.enums@)), lenv(*cx), blt(*final(blk), *cx).push(ETy::Int))),
    decreases e, 1nat,
{
    match e {
        TExpr::Quant(_, Over::Type(_), _) => quant_type(e, cx, sc, blk),
        TExpr::Quant(_, Over::Set(_, _), _) => quant_set(e, cx, sc, blk),
        TExpr::Quant(_, Over::Map(_, _), _) => quant_map(e, cx, sc, blk),
        _ => quant_list(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
#[allow(unused_variables)]
pub(crate) fn quant_type(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<QuantDomain, Fail>)
    requires
        old(blk).wf(),
        e is Quant && e->Quant_1 is Type,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> n <= 0x7fff_ffff && (over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> wf_stype(sty(st), cx.enums@) && small(sty(st)) && has_ty(
            g,
            lenv(*cx),
            blt(*final(blk), *cx).push(ETy::Int),
            ETy::Bool,
        ) && typed(us@, etys(slot_tys(sty(st), cx.enums@)), lenv(*cx), blt(*final(blk), *cx).push(ETy::Int))),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let enums = &cx.enums;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let over = match e {
        TExpr::Quant(_, over, _) => over,
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    proof {
        lemma_extends_refl(*blk);
        if pre {
            assert(lim_ok(*e, c, bt));
            assert(quant_bound(*over, c, bt) is Some);
        }
    }
    match over {
        Over::Type(t) => {
            let n = need(keys_exec(t, enums))?;
            proof {
                if pre {
                    assert(n <= crate::value::encoding::MAX_KEYS);
                }
            }
            if n > 0x7fff_ffff {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                lemma_extends_refl(*blk);
                lemma_over_type(*over, *cx, sc@, *blk, n as nat, us@);
                if tp {
                    lemma_top_typed(*blk, *cx);
                    lemma_lim_small(sty(*t), cx.enums@);
                    assert(typed(us@, etys(slot_tys(sty(*t), cx.enums@)), tv, blt(*blk, *cx).push(ETy::Int)));
                    assert(has_ty(bool_lit(true), tv, blt(*blk, *cx).push(ETy::Int), ETy::Bool));
                }
            }
            Ok(QuantDomain { ty: copy_stype(t), guard: cb(true), count: n as usize, slots: us })
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub(crate) fn quant_set(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<QuantDomain, Fail>)
    requires
        old(blk).wf(),
        e is Quant && e->Quant_1 is Set,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> n <= 0x7fff_ffff && (over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> wf_stype(sty(st), cx.enums@) && small(sty(st)) && has_ty(
            g,
            lenv(*cx),
            blt(*final(blk), *cx).push(ETy::Int),
            ETy::Bool,
        ) && typed(us@, etys(slot_tys(sty(st), cx.enums@)), lenv(*cx), blt(*final(blk), *cx).push(ETy::Int))),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let enums = &cx.enums;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let over = match e {
        TExpr::Quant(_, over, _) => over,
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    proof {
        lemma_extends_refl(*blk);
        if pre {
            assert(lim_ok(*e, c, bt));
            assert(quant_bound(*over, c, bt) is Some);
        }
    }
    match over {
        Over::Set(t, s) => {
            proof {
                if pre {
                    assert(lim_ok(**s, c, bt));
                }
            }
            let (ty, cs) = low(s, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**s, c, bt));
                    assert(n_ok_set(xty(ty), sty(*t), cx.enums@));
                }
            }
            let u = match ty {
                XType::Set(u) => u,
                _ => return Err(Fail::Type),
            };
            let n = need(keys_exec(t, enums))?;
            if !stype_eq(&u, t) || n > 0x7fff_ffff || cs.len() != n as usize {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let g = pick_slot(&cs, &Expr::Local(d));
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    lemma_all_pure_mono(cs@, d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                if tp {
                    let lt = blt(*blk, *cx);
                    lemma_top_typed(*blk, *cx);
                    lemma_lim_small(sty(*t), cx.enums@);
                    lemma_typed_bools(cs@, keys_or_zero(sty(*t), cx.enums@), tv, lt);
                    lemma_all_ty_push(cs@, ETy::Bool, tv, lt, ETy::Int);
                    assert(typed(us@, etys(slot_tys(sty(*t), cx.enums@)), tv, lt.push(ETy::Int)));
                    if cs@.len() > 0 {
                        assert(all_ty(cs@, ETy::Bool, tv, lt.push(ETy::Int)));
                    }
                }
                lemma_over_set(*over, *t, **s, *cx, sc@, b0, *blk, cs@, g, n as nat, us@);
            }
            Ok(QuantDomain { ty: copy_stype(t), guard: g, count: n as usize, slots: us })
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub(crate) fn quant_map(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<QuantDomain, Fail>)
    requires
        old(blk).wf(),
        e is Quant && e->Quant_1 is Map,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> n <= 0x7fff_ffff && (over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> wf_stype(sty(st), cx.enums@) && small(sty(st)) && has_ty(
            g,
            lenv(*cx),
            blt(*final(blk), *cx).push(ETy::Int),
            ETy::Bool,
        ) && typed(us@, etys(slot_tys(sty(st), cx.enums@)), lenv(*cx), blt(*final(blk), *cx).push(ETy::Int))),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let enums = &cx.enums;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let over = match e {
        TExpr::Quant(_, over, _) => over,
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    proof {
        lemma_extends_refl(*blk);
        if pre {
            assert(lim_ok(*e, c, bt));
            assert(quant_bound(*over, c, bt) is Some);
        }
    }
    match over {
        Over::Map(t, m) => {
            proof {
                if pre {
                    assert(lim_ok(**m, c, bt));
                }
            }
            let (ty, cs) = low(m, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**m, c, bt));
                }
            }
            let (kt, vt) = match ty {
                XType::Map(k, v) => (k, v),
                _ => return Err(Fail::Type),
            };
            let n = need(keys_exec(t, enums))?;
            if !stype_eq(&kt, t) || n > 0x7fff_ffff {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_s(sty(*vt), enums@));
                    assert(n <= crate::value::encoding::MAX_KEYS);
                }
            }
            let w = need(stype_width(&vt, enums))?;
            proof {
                assert(usize::MAX >= 0xffff_ffff);
            }
            let stride = need(w.checked_add(1))?;
            let ghost b1 = *blk;
            let mut fs: Vec<Expr> = Vec::new();
            let mut j: usize = 0;
            while j < n as usize
                invariant
                    n <= 0x7fff_ffff,
                    j <= n,
                    fs@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] fs@[q] == cs@[q * stride],
                    extends(*old(blk), *blk),
                    *blk == b1,
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> cs@.len() == n * stride && all_pure(cs@, b1.depth_s()) && stride == w + 1,
                    pre ==> all_pure(fs@, b1.depth_s()),
                decreases n - j,
            {
                proof {
                    assert((j + 1) * stride <= n * stride) by (nonlinear_arith)
                        requires
                            j < n,
                    ;
                    assert(j * stride + stride == (j + 1) * stride) by (nonlinear_arith);
                    assert(usize::MAX >= 0xffff_ffff);
                }
                let at = need(j.checked_mul(stride))?;
                if at >= cs.len() {
                    return Err(Fail::Type);
                }
                let ghost f0 = fs@;
                fs.push(copy_expr(&cs[at]));
                proof {
                    if pre {
                        assert forall|q: int| 0 <= q < fs@.len() implies pure_below(#[trigger] fs@[q], b1.depth_s()) by {
                            if q < f0.len() {
                                assert(fs@[q] == f0[q]);
                            }
                        }
                    }
                }
                j += 1;
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let g = pick_slot(&fs, &Expr::Local(d));
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    lemma_all_pure_mono(fs@, d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                if tp {
                    let lt = blt(*blk, *cx);
                    let mt = STy::Map(Box::new(sty(*kt)), Box::new(sty(*vt)));
                    lemma_top_typed(*blk, *cx);
                    lemma_lim_small(sty(*t), cx.enums@);
                    lemma_xetys_of(mt, cx.enums@);
                    assert(xty(ty) == to_xty(mt));
                    crate::slot::slot_types::lemma_slot_tys_len(sty(*vt), cx.enums@);
                    let row = seq![Type::Bool] + slot_tys(sty(*vt), cx.enums@);
                    assert(row[0] == Type::Bool);
                    assert(slot_tys(mt, cx.enums@) == crate::slot::slot_types::ty_repeat(row, keys_or_zero(sty(*kt), cx.enums@)));
                    lemma_map_flags_typed(cs@, fs@, row, keys_or_zero(sty(*kt), cx.enums@), stride as int, tv, lt);
                    lemma_all_ty_push(fs@, ETy::Bool, tv, lt, ETy::Int);
                    assert(typed(us@, etys(slot_tys(sty(*t), cx.enums@)), tv, lt.push(ETy::Int)));
                    if fs@.len() > 0 {
                        assert(all_ty(fs@, ETy::Bool, tv, lt.push(ETy::Int)));
                    }
                }
                lemma_over_map(*over, *t, **m, *cx, sc@, b0, *blk, sty(*vt), stride as int, cs@, fs@, g, n as nat, us@);
            }
            Ok(QuantDomain { ty: copy_stype(t), guard: g, count: n as usize, slots: us })
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub(crate) fn quant_list(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<QuantDomain, Fail>)
    requires
        old(blk).wf(),
        e is Quant && e->Quant_1 is List,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> n <= 0x7fff_ffff && (over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(QuantDomain { ty: st, guard: g, count: n, slots: us }) ==> wf_stype(sty(st), cx.enums@) && small(sty(st)) && has_ty(
            g,
            lenv(*cx),
            blt(*final(blk), *cx).push(ETy::Int),
            ETy::Bool,
        ) && typed(us@, etys(slot_tys(sty(st), cx.enums@)), lenv(*cx), blt(*final(blk), *cx).push(ETy::Int))),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let enums = &cx.enums;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let over = match e {
        TExpr::Quant(_, over, _) => over,
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    proof {
        lemma_extends_refl(*blk);
        if pre {
            assert(lim_ok(*e, c, bt));
            assert(quant_bound(*over, c, bt) is Some);
        }
    }
    match over {
        Over::List(li) => {
            proof {
                if pre {
                    assert(lim_ok(**li, c, bt));
                }
            }
            let (ty, cs) = low(li, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**li, c, bt));
                }
            }
            let (u, max) = match ty {
                XType::List(u, max) => (u, max),
                _ => return Err(Fail::Type),
            };
            proof {
                if pre {
                    assert(lim_s(sty(*u), enums@));
                }
            }
            let w = need(stype_width(&u, enums))?;
            if max > 0x7fff_ffff || cs.len() == 0 {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let ghost b1 = *blk;
            let dv = defaults(&u, enums);
            let ghost et = slot_tys(sty(*u), cx.enums@);
            let ghost lt1 = blt(b1, *cx).push(ETy::Int);
            proof {
                lemma_default_len(sty(*u), enums@);
                if tp {
                    let lt0 = STy::List(Box::new(sty(*u)), max);
                    lemma_top_typed(b1, *cx);
                    lemma_lim_small(sty(*u), cx.enums@);
                    lemma_xetys_of(lt0, cx.enums@);
                    assert(xty(ty) == to_xty(lt0));
                    crate::slot::slot_types::lemma_slot_tys_len(sty(*u), cx.enums@);
                    lemma_defaults_typed(sty(*u), tv, lt1);
                }
            }
            let mut us: Vec<Expr> = Vec::new();
            let mut j: usize = 0;
            while j < w
                invariant
                    max <= 0x7fff_ffff,
                    j <= w,
                    us@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] picks(us@[q], list_col(cs@, w as int, max as nat, q), Expr::Local(d)),
                    extends(*old(blk), *blk),
                    *blk == b1,
                    d == b1.depth_s(),
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> cs@.len() == 1 + max * w && all_pure(cs@, d as nat) && cs@.len() <= 0x7fff_ffff,
                    pre ==> all_pure(us@, (d + 1) as nat),
                    dv@ == lits(enc(default_val(sty(*u), cx.enums@), sty(*u), cx.enums@)),
                    dv@.len() == w,
                    w == width(sty(*u), cx.enums@),
                    tp == (pre && tok(*cx, old(sc)@, *old(blk))),
                    tv == lenv(*cx),
                    et == slot_tys(sty(*u), cx.enums@),
                    lt1 == blt(b1, *cx).push(ETy::Int),
                    tp ==> et.len() == w && typed(cs@, etys(seq![Type::Int(0, max as i64)] + crate::slot::slot_types::ty_repeat(et, max as nat)), tv, blt(b1, *cx)),
                    tp ==> typed(dv@, etys(et), tv, lt1),
                    tp ==> forall|q: int| 0 <= q < j ==> #[trigger] has_ty(us@[q], tv, lt1, etys(et)[q]),
                    tp ==> blt(b1, *cx).len() == d,
                decreases w - j,
            {
                let mut col: Vec<Expr> = Vec::new();
                let mut k: usize = 0;
                while k < max
                    invariant
                        max <= 0x7fff_ffff,
                        k <= max,
                        j < w,
                        col@ =~= Seq::new(k as nat, |q: int| cs@[1 + q * w + j]),
                        extends(*old(blk), *blk),
                        *blk == b1,
                        d == b1.depth_s(),
                        pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                        pre ==> cs@.len() == 1 + max * w && all_pure(cs@, d as nat) && cs@.len() <= 0x7fff_ffff,
                        pre ==> all_pure(col@, d as nat),
                    decreases max - k,
                {
                    proof {
                        assert(k * w + w <= max * w) by (nonlinear_arith)
                            requires
                                k < max,
                        ;
                        assert(usize::MAX >= 0xffff_ffff);
                    }
                    let at = need(need(need(k.checked_mul(w))?.checked_add(1))?.checked_add(j))?;
                    if at >= cs.len() {
                        return Err(Fail::Type);
                    }
                    let ghost c0 = col@;
                    col.push(copy_expr(&cs[at]));
                    proof {
                        assert(col@ =~= Seq::new((k + 1) as nat, |q: int| cs@[1 + q * w + j]));
                        if pre {
                            assert forall|q: int| 0 <= q < col@.len() implies pure_below(#[trigger] col@[q], d as nat) by {
                                if q < c0.len() {
                                    assert(col@[q] == c0[q]);
                                }
                            }
                        }
                    }
                    k += 1;
                }
                proof {
                    assert(col@ =~= list_col(cs@, w as int, max as nat, j as int));
                }
                let ghost u0 = us@;
                let pk = if max == 0 {
                    copy_expr(&dv[j])
                } else {
                    pick_slot(&col, &Expr::Local(d))
                };
                proof {
                    if max == 0 {
                        assert(dv@[j as int] == Expr::Const(enc(default_val(sty(*u), cx.enums@), sty(*u), cx.enums@)[j as int]));
                        assert(col@.len() == 0);
                    }
                    if tp {
                        if max == 0 {
                            assert(has_ty(dv@[j as int], tv, lt1, etys(et)[j as int]));
                        } else {
                            lemma_list_col_typed(cs@, et, max as nat, j as int, tv, blt(b1, *cx));
                            assert forall|q: int| 0 <= q < col@.len() implies #[trigger] has_ty(col@[q], tv, lt1, etys(et)[j as int]) by {
                                assert(col@[q] == cs@[1 + q * w + j]);
                                assert(has_ty(cs@[1 + q * et.len() + j], tv, blt(b1, *cx), etys(et)[j as int]));
                                assert(pure_below(cs@[1 + q * w + j], d as nat));
                                lemma_has_ty_push(cs@[1 + q * w + j], etys(et)[j as int], tv, blt(b1, *cx), ETy::Int);
                            }
                            assert(all_ty(col@, etys(et)[j as int], tv, lt1));
                            assert(has_ty(Expr::Local(d), tv, lt1, ETy::Int));
                        }
                    }
                }
                proof {
                    if pre {
                        lemma_all_pure_mono(col@, d as nat, (d + 1) as nat);
                        assert(pure_below(Expr::Local(d), (d + 1) as nat));
                        assert(pure_below(pk, (d + 1) as nat));
                    }
                }
                us.push(pk);
                proof {
                    if pre {
                        assert forall|q: int| 0 <= q < us@.len() implies pure_below(#[trigger] us@[q], (d + 1) as nat) by {
                            if q < u0.len() {
                                assert(us@[q] == u0[q]);
                            }
                        }
                    }
                    if tp {
                        assert forall|q: int| 0 <= q < j + 1 implies #[trigger] has_ty(us@[q], tv, lt1, etys(et)[q]) by {
                            if q < u0.len() {
                                assert(us@[q] == u0[q]);
                            }
                        }
                    }
                }
                j += 1;
            }
            let g = bin(BinOp::Lt, Expr::Local(d), copy_expr(&cs[0]));
            proof {
                if pre {
                    assert(pure_below(cs@[0], d as nat));
                    lemma_pure_mono(cs@[0], d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(pure_below(g, (d + 1) as nat));
                }
            }
            proof {
                if tp {
                    assert(has_ty(cs@[0], tv, blt(b1, *cx), ETy::Int)) by {
                        assert(etys(seq![Type::Int(0, max as i64)] + crate::slot::slot_types::ty_repeat(et, max as nat))[0] == ETy::Int);
                    }
                    lemma_has_ty_push(cs@[0], ETy::Int, tv, blt(b1, *cx), ETy::Int);
                    lemma_lt_typed(Expr::Local(d), cs@[0], tv, lt1);
                    assert(typed(us@, etys(et), tv, lt1));
                }
                lemma_over_list(*over, **li, *cx, sc@, b0, *blk, sty(*u), max as nat, w as int, cs@, us@, g);
            }
            Ok(QuantDomain { ty: copy_stype(&u), guard: g, count: max, slots: us })
        },
        _ => Err(Fail::Type),
    }
}

/// `forall` と `exists`。型の全体、Set の要素、Map のキー、List の要素をたどる。
///
/// 位置を1つの整数の局所変数でたどる。型の全体、Set、Mapでは位置は値の正規順での番号で、
/// 束縛する値のスロットは番号から作る（[`unrank`]）。Listでは位置は添字で、スロットは
/// その位置の要素のスロットを選ぶ。位置が対象に含まれるかは、ガードで表す。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_quant(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Quant,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 2nat,
{
    let (all, _over, body) = match e {
        TExpr::Quant(all, over, body) => (*all, over, body),
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    let ghost before = sc@;
    // たどる値の型、位置が対象に含まれるかのガード、位置の数、束縛する値のスロット。
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let QuantDomain { ty: st, guard: g, count: n, slots: us } = quant_over(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    let d = depth(blk);
    let top = need(d.checked_add(1))?;
    let bd = Bound { ty: to_xtype(&st), slots: us };
    let ghost bg = bd;
    sc.push(bd);
    proof {
        if pre {
            let sc1 = sc@;
            assert(sc1 == before.push(bg));
            lemma_ok_to_x(sty(st), cx.enums@);
            lemma_xwidth_of(sty(st), cx.enums@);
            lemma_sc_wf_mono(before, b0.depth_s(), top as nat, cx.enums@);
            assert(bound_tys(sc1) =~= bt.push(to_xty(sty(st))));
            assert(sc_wf(sc1, top as nat, cx.enums@)) by {
                assert forall|i: int| 0 <= i < sc1.len() implies ok_x(xty(#[trigger] sc1[i].ty), cx.enums@) && shaped(
                    sc1[i].slots@,
                    xty(sc1[i].ty),
                    top as nat,
                    cx.enums@,
                ) by {
                    if i < before.len() {
                        assert(sc1[i] == before[i]);
                    } else {
                        assert(sc1[i] == bg);
                    }
                }
            }
            assert(lim_ok(*e, c, bt));
            assert(ir_type_of(**body, c, bt.push(to_xty(sty(st)))) == Some(XTy::Bool));
            assert(lim_ok(**body, c, bt.push(to_xty(sty(st)))));
        }
        if tp {
            let sc1 = sc@;
            let lt1 = blt(b1, *cx).push(ETy::Int);
            lemma_top_typed(b1, *cx);
            lemma_tok_ext(*cx, before, b0, b1);
            lemma_sc_wf_mono(before, b0.depth_s(), b1.depth_s(), cx.enums@);
            lemma_xetys_of(sty(st), cx.enums@);
            assert(xty(bg.ty) == to_xty(sty(st)));
            assert forall|i: int| 0 <= i < sc1.len() implies #[trigger] typed(
                sc1[i].slots@,
                xetys(xty(sc1[i].ty), cx.enums@),
                tv,
                lt1,
            ) by {
                if i < before.len() {
                    assert(sc1[i] == before[i]);
                    assert(typed(before[i].slots@, xetys(xty(before[i].ty), cx.enums@), tv, blt(b1, *cx)));
                    assert(shaped(before[i].slots@, xty(before[i].ty), b1.depth_s(), cx.enums@));
                    assert(all_pure(before[i].slots@, b1.depth_s()));
                    assert(blt(b1, *cx).take(b1.depth_s() as int) =~= lt1.take(b1.depth_s() as int));
                    lemma_typed_ext(before[i].slots@, xetys(xty(before[i].ty), cx.enums@), tv, blt(b1, *cx), lt1, b1.depth_s());
                } else {
                    assert(sc1[i] == bg);
                }
            }
            assert(tok_in(*cx, sc1, lt1, top as nat));
        }
    }
    let b = bool_in(body, cx, sc, top, Ghost(blt(*blk, *cx).push(ETy::Int)))?;
    sc.pop();
    proof {
        assert(sc@ =~= before);
    }
    let qb = combine(all, g, b);
    let hi = n as i64 - 1;
    let top_code = if n == 0 {
        0i64
    } else {
        hi
    };
    let q = quant(all, Type::Int(0, top_code), 0, hi, qb);
    proof {
        if tp {
            let lt1 = blt(b1, *cx).push(ETy::Int);
            assert(has_ty(b, tv, lt1, ETy::Bool));
            assert(has_ty(qb, tv, lt1, ETy::Bool));
            assert(crate::kernel::typing::ety_of(Type::Int(0, top_code)) == ETy::Int);
            assert(crate::kernel::typing::quant_dom_ok(tv.enums, Type::Int(0, top_code), 0, hi));
            assert(has_ty(q, tv, blt(b1, *cx), ETy::Bool));
        }
    }
    let z = bind(blk, q)?;
    proof {
        if tp {
            lemma_bind_typed(b1, *blk, q, z, *cx, ETy::Bool);
        }
    }
    let mut out: Vec<Expr> = Vec::new();
    out.push(z);
    proof {
        if pre {
            assert(pure_below(out@[0], blk.depth_s()));
        }
    }
    proof {
        lemma_quant(*e, all, *_over, **body, *cx, before, b0, b1, *blk, n as nat, g, bg, b, qb, q);
    }
    Ok((XType::Bool, out))
}

/// 量化の本体と、値が対象に含まれる条件を組み合わせる。
pub(crate) fn combine(all: bool, guard: Expr, e: Expr) -> (r: Expr)
    ensures
        combine_ok(all, guard, e, r),
        forall|n: nat| pure_below(guard, n) && pure_below(e, n) ==> #[trigger] pure_below(r, n),
        forall|tv: TyEnv, lt: Seq<ETy>|
            has_ty(guard, tv, lt, ETy::Bool) && #[trigger] has_ty(e, tv, lt, ETy::Bool) ==> has_ty(r, tv, lt, ETy::Bool),
{
    if is_bool_lit(&guard, true) {
        proof {
            assert forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(e, env, l)) == match as_bool(eval_l(guard, env, l)) {
                Err(k) => Err(k),
                Ok(true) => as_bool(eval_l(e, env, l)),
                Ok(false) => Ok::<bool, ErrKind>(all),
            } by {
                assert(eval_l(guard, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
        }
        e
    } else if all {
        Expr::Implies(Box::new(guard), Box::new(e))
    } else {
        Expr::And(Box::new(guard), Box::new(e))
    }
}

pub(crate) fn quant(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> (r: Expr)
    ensures
        r == quant_s(all, ty, lo, hi, e),
{
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

} // verus!
