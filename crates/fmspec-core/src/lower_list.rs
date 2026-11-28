//! List のリテラル、所属、添字の参照、先頭と末尾、更新、追加と取り出しの下ろし。意味の保存は `preserve_list` にある。

#[cfg(verus_keep_ghost)]
use crate::canon::lemma_defaults_typed;
use crate::encoding::XType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_repeat, lemma_default_len, lemma_xwidth_of, sty, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, wf_stype, width, xty, xwidth, XTy};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, lits, pure_below, Join};
use crate::expr_build::{and, bin, ci, defaults, extend};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::{ir_type_of, lemma_all_typed_iff};
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_small, lim_x, small};
use crate::lists::list_parts;
#[cfg(verus_keep_ghost)]
use crate::lists::{lemma_select_typed, rows_view};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::extends;
use crate::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{all_ty, blt, etys, has_ty, lemma_add_typed, lemma_added_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_and_typed, lemma_bind_typed, lemma_check_typed, lemma_etys_concat};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_ge0_typed, lemma_gt_typed, lemma_has_ty_blk, lemma_ite_rows_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_list_join_typed, lemma_lrows_typed, lemma_lt_typed, lemma_sub_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_tok_ext, lemma_tree_typed, lemma_typed_blk, lemma_typed_concat};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_xetys_of, lenv, slot_tys, tok, typed, xetys};
#[cfg(verus_keep_ghost)]
use crate::lowering::low_ok;
use crate::lowering::{element, low, sub_scalar};
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::lemma_tree_pure;
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_extends_trans, lemma_join_pure, lemma_lits, lemma_pure_mono};
#[cfg(verus_keep_ghost)]
use crate::preserve_list::{defaults_s, hit_at, lemma_at, lemma_first, lemma_last};
#[cfg(verus_keep_ghost)]
use crate::preserve_list::{lemma_list_contains, lemma_listlit_base, lemma_listlit_done};
#[cfg(verus_keep_ghost)]
use crate::preserve_list::{lemma_listlit_step, lemma_pop, lemma_push, lemma_shift, listlit_ok};
#[cfg(verus_keep_ghost)]
use crate::rows::flat;
#[cfg(verus_keep_ghost)]
use crate::slots::lemma_extends_refl;
use crate::slots::select;
use crate::slots::{any_of, atom, bind, check, copy_exprs, eq_slots, ite_rows, list_join, need};
use crate::source::{TExpr, FAIL_EMPTY, FAIL_FULL, FAIL_INDEX};
use crate::stype_exec::{copy_stype, stype_eq, to_xtype, xtype_eq};
#[cfg(verus_keep_ghost)]
use crate::total::{bound_tys, here_ok, lemma_all_pure_mono, lemma_flat_shape, lemma_ite_rows_shape};
#[cfg(verus_keep_ghost)]
use crate::total::{lemma_lim_ok_seq_at, lemma_list_rows_shape, lemma_ok_list, lemma_ok_to_x};
#[cfg(verus_keep_ghost)]
use crate::total::{lemma_sc_wf_mono, lemma_select_shape, lim_ok, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// `out` の後ろに既定値の行 `defs` を `n` 回加える。
pub(crate) fn append_rows(
    out: &mut Vec<Expr>,
    defs: &Vec<Expr>,
    n: usize,
    Ghost(dv): Ghost<Seq<Value>>,
    Ghost(hd): Ghost<Seq<Type>>,
    Ghost(et): Ghost<Seq<Type>>,
    Ghost(k0): Ghost<nat>,
)
    requires
        defs@ == lits(dv),
    ensures
        final(out)@ == old(out)@ + lits(enc_repeat(dv, n as nat)),
        final(out)@.len() == old(out)@.len() + n * dv.len(),
        forall|m: nat| #[trigger] all_pure(old(out)@, m) ==> all_pure(final(out)@, m),
        forall|tv: TyEnv, lt: Seq<ETy>|
            typed(old(out)@, etys(hd + crate::lower_types::ty_repeat(et, k0)), tv, lt) && #[trigger] typed(defs@, etys(et), tv, lt)
                ==> typed(final(out)@, etys(hd + crate::lower_types::ty_repeat(et, (k0 + n) as nat)), tv, lt),
{
    let ghost o0 = out@;
    proof {
        assert(o0 =~= o0 + lits(enc_repeat(dv, 0)));
    }
    let mut p = 0;
    while p < n
        invariant
            p <= n,
            defs@ == lits(dv),
            out@ == o0 + lits(enc_repeat(dv, p as nat)),
            out@.len() == o0.len() + p * dv.len(),
            forall|m: nat| #[trigger] all_pure(o0, m) ==> all_pure(out@, m),
            forall|tv: TyEnv, lt: Seq<ETy>|
                typed(o0, etys(hd + crate::lower_types::ty_repeat(et, k0)), tv, lt) && #[trigger] typed(defs@, etys(et), tv, lt)
                    ==> typed(out@, etys(hd + crate::lower_types::ty_repeat(et, (k0 + p) as nat)), tv, lt),
        decreases n - p,
    {
        let ghost o3 = out@;
        extend(out, defs);
        proof {
            lemma_lits(dv, arbitrary(), Seq::empty());
            assert(p * dv.len() + dv.len() == (p + 1) * dv.len()) by (nonlinear_arith);
            assert forall|m: nat| #[trigger] all_pure(o0, m) implies all_pure(out@, m) by {
                lemma_lits(dv, arbitrary(), Seq::empty());
                assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], m) by {
                    if j < o3.len() {
                        assert(out@[j] == o3[j]);
                        assert(all_pure(o3, m));
                    } else {
                        assert(out@[j] == defs@[j - o3.len()]);
                        assert(pure_below(lits(dv)[j - o3.len()], m));
                    }
                }
            }
            assert forall|tv: TyEnv, lt: Seq<ETy>|
                typed(o0, etys(hd + crate::lower_types::ty_repeat(et, k0)), tv, lt) && #[trigger] typed(defs@, etys(et), tv, lt)
                    implies typed(out@, etys(hd + crate::lower_types::ty_repeat(et, (k0 + p + 1) as nat)), tv, lt) by {
                assert(typed(o3, etys(hd + crate::lower_types::ty_repeat(et, (k0 + p) as nat)), tv, lt));
                lemma_typed_concat(o3, etys(hd + crate::lower_types::ty_repeat(et, (k0 + p) as nat)), defs@, etys(et), tv, lt);
                lemma_etys_concat(hd + crate::lower_types::ty_repeat(et, (k0 + p) as nat), et);
                assert(hd + crate::lower_types::ty_repeat(et, (k0 + p + 1) as nat) =~= (hd + crate::lower_types::ty_repeat(et, (k0 + p) as nat)) + et);
            }
            let k = p as nat;
            assert(enc_repeat(dv, (k + 1) as nat) == enc_repeat(dv, k) + dv);
            assert(lits(enc_repeat(dv, k) + dv) =~= lits(enc_repeat(dv, k)) + lits(dv));
            assert(out@ =~= o0 + lits(enc_repeat(dv, (k + 1) as nat)));
        }
        p += 1;
    }
    proof {
        assert(k0 + n == k0 + n);
    }
}

/// Listのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_list_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is ListLit,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::ListLit(t, max, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            if es.len() > *max || es.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(ci(es.len() as i64));
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            let ghost st = sty(*t);
            let ghost n = es.len() as i64;
            proof {
                lemma_all_typed_iff(es@, to_xty(sty(*t)), c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
            }
            proof {
                lemma_listlit_base(*cx, sc0, b0, st, n, out@);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
                if tp {
                    assert(here_ok(*e, c, bt));
                    assert(wf_stype(st, enums@));
                    lemma_lim_small(st, enums@);
                    lemma_etys_concat(seq![Type::Int(0, *max as i64)], crate::lower_types::ty_repeat(slot_tys(st, cx.enums@), 0));
                    assert(etys(seq![Type::Int(0, *max as i64)]) =~= seq![ETy::Int]);
                    assert(etys(crate::lower_types::ty_repeat(slot_tys(st, cx.enums@), 0)) =~= Seq::<ETy>::empty());
                    assert(has_ty(out@[0], tv, blt(*blk, *cx), ETy::Int));
                    assert(typed(out@, etys(seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(slot_tys(st, cx.enums@), 0)), tv, blt(*blk, *cx)));
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
                    st == sty(*t),
                    n == es.len() as i64,
                    e is ListLit && e->ListLit_2 == *es && e->ListLit_0 == *t,
                    listlit_ok(es@.take(i as int), *cx, sc0, b0, *blk, st, n, out@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> ir_type_of(#[trigger] es@[j], c, bt) == Some(to_xty(sty(*t)))
                        && lim_ok(es@[j], c, bt),
                    pre ==> out@.len() == 1 + i * width(st, cx.enums@) && all_pure(out@, blk.depth_s()),
                    tp == (pre && tok(*cx, sc0, b0)),
                    tv == lenv(*cx),
                    tp ==> wf_stype(st, cx.enums@) && small(st),
                    tp ==> tok(*cx, sc0, *blk) && typed(out@, etys(seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(slot_tys(st, cx.enums@), i as nat)), tv, blt(*blk, *cx)),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost o1 = out@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(ir_type_of(es@[i as int], c, bt) == Some(to_xty(sty(*t))) && lim_ok(es@[i as int], c, bt));
                    }
                }
                let x = element(&es[i], cx, sc, blk, t)?;
                extend(&mut out, &x);
                proof {
                    if pre {
                        lemma_all_pure_mono(o1, b1.depth_s(), blk.depth_s());
                        assert(1 + i * width(st, cx.enums@) + width(st, cx.enums@) == 1 + (i + 1) * width(st, cx.enums@)) by (nonlinear_arith);
                        assert(all_pure(out@, blk.depth_s())) by {
                            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                                if j < o1.len() {
                                    assert(out@[j] == o1[j]);
                                } else {
                                    assert(out@[j] == x@[j - o1.len()]);
                                }
                            }
                        }
                    }
                }
                proof {
                    if tp {
                        let et = slot_tys(st, cx.enums@);
                        let ys = etys(seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(et, i as nat));
                        lemma_typed_blk(o1, ys, *cx, b1, *blk);
                        lemma_typed_concat(o1, ys, x@, etys(et), tv, blt(*blk, *cx));
                        lemma_etys_concat(seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(et, i as nat), et);
                        assert(seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(et, (i + 1) as nat) =~= (seq![Type::Int(0, *max as i64)] + crate::lower_types::ty_repeat(et, i as nat)) + et);
                        lemma_tok_ext(*cx, sc0, b1, *blk);
                    }
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    lemma_listlit_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, st, n, o1, x@, out@);
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
            }
            let defs = defaults(t, enums);
            proof {
                lemma_default_len(st, enums@);
                lemma_xwidth_of(st, enums@);
            }
            let ghost o2 = out@;
            let ghost dv = enc(default_val(st, enums@), st, enums@);
            let ghost b2 = *blk;
            let ghost et = slot_tys(st, cx.enums@);
            let ghost hd = seq![Type::Int(0, *max as i64)];
            proof {
                if tp {
                    lemma_defaults_typed(st, tv, blt(*blk, *cx));
                }
            }
            append_rows(&mut out, &defs, *max - es.len(), Ghost(dv), Ghost(hd), Ghost(et), Ghost(es.len() as nat));
            proof {
                if pre {
                    lemma_lits(dv, arbitrary(), Seq::empty());
                    assert(1 + es.len() * width(st, cx.enums@) + (*max - es.len()) * width(st, cx.enums@) == 1 + *max * width(st, cx.enums@)) by (nonlinear_arith)
                        requires
                            es.len() <= *max,
                    ;
                }
                lemma_listlit_done(*e, *cx, sc0, b0, b2, st, *max, o2, dv, out@);
                if tp {
                    assert(xetys(XTy::List(Box::new(st), *max), cx.enums@) == etys(slot_tys(STy::List(Box::new(st), *max), cx.enums@)));
                    assert(es.len() + (*max - es.len()) == *max);
                }
            }
            Ok((XType::List(Box::new(copy_stype(t)), *max), out))
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
pub(crate) fn low_list_contains(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is ListContains,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::ListContains(a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tc, cs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                }
            }
            let (elem, max) = match tc {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let et = to_xtype(&elem);
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    lemma_ok_list(sty(elem), max, enums@);
                    lemma_ok_to_x(sty(elem), enums@);
                    lemma_xwidth_of(sty(elem), enums@);
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (tx, xv) = low(x, cx, sc, blk)?;
            if !xtype_eq(&tx, &et) {
                return Err(Fail::Type);
            }
            let (len, rows) = need(list_parts(&elem, max, &cs, enums))?;
            let ghost lg = len;
            let ghost t = xty(et);
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_all_pure_mono(cs@, b1.depth_s(), b2.depth_s());
                    lemma_list_rows_shape(cs@, len, rows_view(rows@), width(sty(elem), enums@), max as nat, b2.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == width(sty(elem), enums@)
                        && all_pure(rows@[q]@, b2.depth_s()) by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                    assert(xwidth(t, enums@) == width(sty(elem), enums@));
                    assert(lim_x(t, enums@));
                    assert(all_pure(xv@, b2.depth_s()));
                }
                if tp {
                    let es = sty(elem);
                    let lt = STy::List(Box::new(es), max);
                    lemma_typed_blk(cs@, xetys(xty(tc), cx.enums@), *cx, b1, b2);
                    lemma_xetys_of(lt, cx.enums@);
                    lemma_xetys_of(es, cx.enums@);
                    crate::lower_types::lemma_slot_tys_len(es, cx.enums@);
                    assert(xty(tc) == to_xty(lt));
                    lemma_lrows_typed(cs@, len, rows_view(rows@), slot_tys(es, cx.enums@), max as nat, tv, blt(b2, *cx));
                    assert(xetys(t, cx.enums@) == etys(slot_tys(es, cx.enums@)));
                    assert forall|q: int| 0 <= q < rows@.len() implies #[trigger] typed(rows@[q]@, xetys(t, cx.enums@), tv, blt(b2, *cx)) by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let mut hits: Vec<Expr> = Vec::new();
            let ghost mut cg: Seq<Expr> = Seq::empty();
            let mut p = 0;
            while p < rows.len()
                invariant
                    extends(*old(blk), *blk),
                    rows@.len() == max,
                    max <= 0x7fff_ffff,
                    lg == len,
                    t == xty(et),
                    p <= rows@.len(),
                    hits@.len() == p,
                    cg.len() == p,
                    forall|q: int| 0 <= q < p ==> #[trigger] hit_at(hits@[q], rows@[q]@, xv@, lg, cg[q], q, t, enums@),
                    *blk == b2,
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> pure_below(len, b2.depth_s()) && all_pure(xv@, b2.depth_s()) && xv@.len() == xwidth(t, enums@)
                        && lim_x(t, enums@),
                    pre ==> forall|q: int| 0 <= q < rows@.len() ==> (#[trigger] rows@[q])@.len() == width(sty(elem), enums@)
                        && all_pure(rows@[q]@, b2.depth_s()),
                    pre ==> xwidth(t, enums@) == width(sty(elem), enums@),
                    pre ==> all_pure(hits@, b2.depth_s()),
                    tp == (pre && tok(*cx, old(sc)@, *old(blk))),
                    tv == lenv(*cx),
                    tp ==> has_ty(len, tv, blt(b2, *cx), ETy::Int),
                    tp ==> typed(xv@, xetys(t, cx.enums@), tv, blt(b2, *cx)),
                    tp ==> forall|q: int| 0 <= q < rows@.len() ==> #[trigger] typed(rows@[q]@, xetys(t, cx.enums@), tv, blt(b2, *cx)),
                    tp ==> all_ty(hits@, ETy::Bool, tv, blt(b2, *cx)),
                    enums@ == cx.enums@,
                decreases rows.len() - p,
            {
                proof {
                    if pre {
                        assert(rows_view(rows@)[p as int] == rows@[p as int]@);
                    }
                }
                let same = need(eq_slots(&et, &rows[p], &xv, enums))?;
                let ghost h1 = hits@;
                let ghost c1 = cg;
                proof {
                    cg = cg.push(same);
                }
                let ghost hh = hits@;
                hits.push(and(bin(BinOp::Gt, copy_expr(&len), ci(p as i64)), same));
                proof {
                    if pre {
                        let gt = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(p as i64))));
                        assert(pure_below(len, b2.depth_s()));
                        assert(pure_below(Expr::Const(Value::Int(p as i64)), b2.depth_s()));
                        assert(pure_below(gt, b2.depth_s()));
                        assert(all_pure(rows@[p as int]@, b2.depth_s()));
                        assert(all_pure(xv@, b2.depth_s()));
                        assert(pure_below(same, b2.depth_s()));
                        lemma_join_pure(Join::And, gt, same, b2.depth_s());
                        if tp {
                            assert(typed(rows@[p as int]@, xetys(t, cx.enums@), tv, blt(b2, *cx)));
                            assert(typed(xv@, xetys(t, cx.enums@), tv, blt(b2, *cx)));
                            lemma_gt_typed(len, p as i64, tv, blt(b2, *cx));
                            lemma_and_typed(gt, same, tv, blt(b2, *cx));
                            assert forall|q: int| 0 <= q < hits@.len() implies #[trigger] has_ty(hits@[q], tv, blt(b2, *cx), ETy::Bool) by {
                                if q < hh.len() {
                                    assert(hits@[q] == hh[q]);
                                }
                            }
                        }
                        assert forall|q: int| 0 <= q < hits@.len() implies pure_below(#[trigger] hits@[q], b2.depth_s()) by {
                            if q < hh.len() {
                                assert(hits@[q] == hh[q]);
                            }
                        }
                    }
                }
                proof {
                    assert(hit_at(hits@[p as int], rows@[p as int]@, xv@, lg, cg[p as int], p as int, t, enums@));
                    assert forall|q: int| 0 <= q < p implies #[trigger] hit_at(hits@[q], rows@[q]@, xv@, lg, cg[q], q, t, enums@) by {
                        assert(hits@[q] == h1[q]);
                        assert(cg[q] == c1[q]);
                    }
                }
                p += 1;
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(any_of(&hits));
            proof {
                if pre {
                    lemma_tree_pure(hits@, bool_lit(false), Join::Or, b2.depth_s());
                }
                if tp {
                    lemma_tree_typed(hits@, bool_lit(false), Join::Or, tv, blt(b2, *cx), ETy::Bool);
                }
            }
            proof {
                let rv = rows_view(rows@);
                assert forall|q: int| 0 <= q < rv.len() implies #[trigger] hit_at(hits@[q], rv[q], xv@, lg, cg[q], q, t, enums@) by {
                    assert(rv[q] == rows@[q]@);
                }
                lemma_list_contains(*e, *cx, sc@, b0, b1, *blk, sty(elem), max, cs@, t, xv@, lg, rv, hits@, cg, out@);
            }
            Ok((XType::Bool, out))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_list_get(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is At || e is First || e is Last,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    match e {
        TExpr::At(..) => low_at(e, cx, sc, blk),
        TExpr::First(..) | TExpr::Last(..) => low_first_last(e, cx, sc, blk),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub(crate) fn low_at(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is At,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::At(a, ix) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                    assert(lim_ok(**ix, c, bt));
                }
            }
            let i0 = sub_scalar(ix, cx, sc, blk, &XType::Int)?;
            let ghost b2 = *blk;
            let ghost ig = i0;
            let i = atom(blk, i0)?;
            let ghost b3 = *blk;
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            proof {
                if pre {
                    lemma_pure_mono(i0, b2.depth_s(), b3.depth_s());
                    lemma_all_pure_mono(ls@, b1.depth_s(), b3.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, b3.depth_s());
                }
                if tp {
                    let st = sty(t);
                    let lt0 = STy::List(Box::new(st), max);
                    lemma_lim_small(st, cx.enums@);
                    lemma_added_typed(b2, b3, i0, i, *cx, ETy::Int);
                    lemma_extends_trans(b1, b2, b3);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, b3);
                    lemma_xetys_of(lt0, cx.enums@);
                    assert(xty(tl) == to_xty(lt0));
                    crate::lower_types::lemma_slot_tys_len(st, cx.enums@);
                    lemma_lrows_typed(ls@, len, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(b3, *cx));
                    assert(has_ty(Expr::Const(Value::Int(0)), tv, blt(b3, *cx), ETy::Int));
                    lemma_ge0_typed(i, tv, blt(b3, *cx));
                    lemma_lt_typed(i, len, tv, blt(b3, *cx));
                    lemma_and_typed(
                        Expr::Bin(BinOp::Ge, Box::new(i), Box::new(Expr::Const(Value::Int(0)))),
                        Expr::Bin(BinOp::Lt, Box::new(i), Box::new(len)),
                        tv,
                        blt(b3, *cx),
                    );
                }
            }
            let cond = and(bin(BinOp::Ge, copy_expr(&i), ci(0)), bin(BinOp::Lt, copy_expr(&i), len));
            let ghost cg = cond;
            check(blk, cond, FAIL_INDEX)?;
            proof {
                if tp {
                    lemma_check_typed(b3, *blk, cg, FAIL_INDEX, *cx);
                }
            }
            let dv = defaults(&t, enums);
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == rows@[0]@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                }
            }
            let slots = need(select(&rows, &i, &dv))?;
            proof {
                if pre {
                    if rows@.len() > 0 {
                        lemma_select_shape(rows_view(rows@), i, slots@, width(sty(t), enums@), b3.depth_s());
                    }
                    lemma_all_pure_mono(slots@, b3.depth_s(), blk.depth_s());
                }
                if tp {
                    let st = sty(t);
                    let ys = etys(slot_tys(st, cx.enums@));
                    lemma_xetys_of(st, cx.enums@);
                    if rows@.len() > 0 {
                        assert forall|q: int| 0 <= q < rows_view(rows@).len() implies #[trigger] typed(rows_view(rows@)[q], ys, tv, blt(b3, *cx)) by {
                        }
                        lemma_select_typed(rows_view(rows@), i, slots@, ys, tv, blt(b3, *cx));
                        lemma_select_shape(rows_view(rows@), i, slots@, width(sty(t), enums@), b3.depth_s());
                        lemma_typed_blk(slots@, ys, *cx, b3, *blk);
                    } else {
                        lemma_defaults_typed(st, tv, blt(*blk, *cx));
                    }
                }
            }
            proof {
                lemma_at(*e, *cx, sc@, b0, b1, b2, b3, *blk, sty(t), max, ls@, ig, i, lg, rows_view(rows@), cg, slots@);
            }
            Ok((to_xtype(&t), slots))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub(crate) fn low_first_last(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is First || e is Last,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::First(a) | TExpr::Last(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                }
            }
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            proof {
                if tp {
                    let st = sty(t);
                    let lt0 = STy::List(Box::new(st), max);
                    lemma_lim_small(st, cx.enums@);
                    lemma_xetys_of(lt0, cx.enums@);
                    assert(xty(tl) == to_xty(lt0));
                    crate::lower_types::lemma_slot_tys_len(st, cx.enums@);
                    lemma_lrows_typed(ls@, len, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(b1, *cx));
                    lemma_gt_typed(len, 0, tv, blt(b1, *cx));
                }
            }
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            let ghost b2 = *blk;
            proof {
                if tp {
                    lemma_check_typed(b1, b2, Expr::Bin(BinOp::Gt, Box::new(lg), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY, *cx);
                }
            }
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), b2.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, b2.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == rows@[0]@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                    if rows@.len() > 0 {
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                }
                if tp {
                    let st = sty(t);
                    let lt0 = STy::List(Box::new(st), max);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, b2);
                    lemma_lrows_typed(ls@, len, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(b2, *cx));
                    lemma_xetys_of(st, cx.enums@);
                    lemma_defaults_typed(st, tv, blt(b2, *cx));
                }
            }
            match e {
                TExpr::First(_) => {
                    let slots = if rows.len() > 0 {
                        copy_exprs(&rows[0])
                    } else {
                        defaults(&t, enums)
                    };
                    proof {
                        lemma_first(*e, *cx, sc@, b0, b1, b2, sty(t), max, ls@, lg, rows_view(rows@), slots@);
                    }
                    return Ok((to_xtype(&t), slots));
                },
                _ => {},
            }
            let ghost b2s = *blk;
            let i = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            proof {
                if tp {
                    let st = sty(t);
                    lemma_sub_typed(lg, 1, tv, blt(b2s, *cx));
                    lemma_bind_typed(b2s, *blk, Expr::Bin(BinOp::Sub, Box::new(lg), Box::new(Expr::Const(Value::Int(1)))), i, *cx, ETy::Int);
                    lemma_extends_trans(b1, b2s, *blk);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, *blk);
                    lemma_lrows_typed(ls@, lg, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(*blk, *cx));
                }
            }
            let dv = defaults(&t, enums);
            let slots = need(select(&rows, &i, &dv))?;
            proof {
                if pre {
                    lemma_all_pure_mono(ls@, b2.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, blk.depth_s());
                    if rows@.len() > 0 {
                        lemma_select_shape(rows_view(rows@), i, slots@, width(sty(t), enums@), blk.depth_s());
                    }
                }
                if tp {
                    let st = sty(t);
                    let ys = etys(slot_tys(st, cx.enums@));
                    if rows@.len() > 0 {
                        lemma_select_typed(rows_view(rows@), i, slots@, ys, tv, blt(*blk, *cx));
                    } else {
                        lemma_defaults_typed(st, tv, blt(*blk, *cx));
                    }
                }
            }
            proof {
                lemma_last(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rows_view(rows@), i, slots@);
            }
            Ok((to_xtype(&t), slots))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub(crate) fn low_list_update(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Push || e is Pop || e is Shift,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    match e {
        TExpr::Push(..) => low_push(e, cx, sc, blk),
        TExpr::Pop(..) | TExpr::Shift(..) => low_pop_shift(e, cx, sc, blk),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub(crate) fn low_push(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Push,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Push(t, n, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (u, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return Err(Fail::Type),
            };
            if max != *n || !stype_eq(&u, t) || max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(u), max, enums@);
                    lemma_xwidth_of(sty(u), enums@);
                    assert(lim_ok(**x, c, bt));
                }
                if tp {
                    lemma_lim_small(sty(u), cx.enums@);
                }
            }
            let xs = element(x, cx, sc, blk, &u)?;
            let ghost b2 = *blk;
            let (len, rows) = need(list_parts(&u, max, &ls, enums))?;
            let ghost lg = len;
            proof {
                if tp {
                    let st = sty(u);
                    let lt0 = STy::List(Box::new(st), max);
                    lemma_lim_small(st, cx.enums@);
                    lemma_xetys_of(lt0, cx.enums@);
                    assert(xty(tl) == to_xty(lt0));
                    crate::lower_types::lemma_slot_tys_len(st, cx.enums@);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, b2);
                    lemma_lrows_typed(ls@, len, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(b2, *cx));
                    assert(has_ty(Expr::Const(Value::Int(max as i64)), tv, blt(b2, *cx), ETy::Int));
                    lemma_lt_typed(len, Expr::Const(Value::Int(max as i64)), tv, blt(b2, *cx));
                    lemma_all_pure_mono(ls@, b1.depth_s(), b2.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(u), enums@), max as nat, b2.depth_s());
                }
            }
            check(blk, bin(BinOp::Lt, copy_expr(&len), ci(max as i64)), FAIL_FULL)?;
            let ghost b3 = *blk;
            proof {
                if tp {
                    lemma_check_typed(b2, b3, Expr::Bin(BinOp::Lt, Box::new(lg), Box::new(Expr::Const(Value::Int(max as i64)))), FAIL_FULL, *cx);
                    lemma_has_ty_blk(lg, ETy::Int, *cx, b2, b3);
                    lemma_add_typed(lg, 1, tv, blt(b3, *cx));
                }
            }
            let new_len = bind(blk, bin(BinOp::Add, copy_expr(&len), ci(1)))?;
            let ghost ng = new_len;
            proof {
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), blk.depth_s());
                    lemma_all_pure_mono(xs@, b2.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(u), enums@), max as nat, blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == xs@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let out = need(ite_rows(&rows, &len, &xs))?;
            let ghost og = rows_view(out@);
            let r = list_join(new_len, &out);
            proof {
                if tp {
                    let st = sty(u);
                    let ys = etys(slot_tys(st, cx.enums@));
                    let lt = blt(*blk, *cx);
                    lemma_bind_typed(b3, *blk, Expr::Bin(BinOp::Add, Box::new(lg), Box::new(Expr::Const(Value::Int(1)))), ng, *cx, ETy::Int);
                    lemma_extends_trans(b1, b2, b3);
                    lemma_extends_trans(b1, b3, *blk);
                    lemma_extends_trans(b2, b3, *blk);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, *blk);
                    lemma_lrows_typed(ls@, lg, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, lt);
                    lemma_typed_blk(xs@, ys, *cx, b2, *blk);
                    lemma_ite_rows_typed(rows_view(out@), rows_view(rows@), lg, xs@, ys, tv, lt);
                    lemma_list_join_typed(ng, rows_view(out@), slot_tys(st, cx.enums@), max as nat, tv, lt);
                }
                if pre {
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), len, xs@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), width(sty(u), enums@), blk.depth_s());
                    assert(all_pure(r@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(r@[j] == flat(rows_view(out@))[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                let rv = rows_view(rows@);
                lemma_push(*e, *cx, sc@, b0, b1, b2, b3, *blk, sty(u), max, ls@, xs@, lg, rv, ng, og, r@);
            }
            Ok((tl, r))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub(crate) fn low_pop_shift(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Pop || e is Shift,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Pop(a) | TExpr::Shift(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (t, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                }
            }
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            proof {
                if tp {
                    let st = sty(t);
                    let lt0 = STy::List(Box::new(st), max);
                    lemma_lim_small(st, cx.enums@);
                    lemma_xetys_of(lt0, cx.enums@);
                    assert(xty(tl) == to_xty(lt0));
                    crate::lower_types::lemma_slot_tys_len(st, cx.enums@);
                    lemma_lrows_typed(ls@, len, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, blt(b1, *cx));
                    lemma_gt_typed(len, 0, tv, blt(b1, *cx));
                }
            }
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            let ghost b2 = *blk;
            proof {
                if tp {
                    lemma_check_typed(b1, b2, Expr::Bin(BinOp::Gt, Box::new(lg), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY, *cx);
                    lemma_has_ty_blk(lg, ETy::Int, *cx, b1, b2);
                    lemma_sub_typed(lg, 1, tv, blt(b2, *cx));
                }
            }
            let new_len = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            let ghost ng = new_len;
            let defs = defaults(&t, enums);
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == defs@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
                if tp {
                    let st = sty(t);
                    let lt = blt(*blk, *cx);
                    lemma_bind_typed(b2, *blk, Expr::Bin(BinOp::Sub, Box::new(lg), Box::new(Expr::Const(Value::Int(1)))), ng, *cx, ETy::Int);
                    lemma_extends_trans(b1, b2, *blk);
                    lemma_typed_blk(ls@, xetys(xty(tl), cx.enums@), *cx, b1, *blk);
                    lemma_lrows_typed(ls@, lg, rows_view(rows@), slot_tys(st, cx.enums@), max as nat, tv, lt);
                    lemma_defaults_typed(st, tv, lt);
                    lemma_xetys_of(STy::List(Box::new(st), max), cx.enums@);
                }
            }
            match e {
                TExpr::Pop(_) => {
                    let out = need(ite_rows(&rows, &new_len, &defs))?;
                    let ghost og = rows_view(out@);
                    let r = list_join(new_len, &out);
            proof {
                if tp {
                    let st = sty(t);
                    let ys = etys(slot_tys(st, cx.enums@));
                    let lt = blt(*blk, *cx);
                    lemma_ite_rows_typed(rows_view(out@), rows_view(rows@), ng, defs@, ys, tv, lt);
                    lemma_list_join_typed(ng, rows_view(out@), slot_tys(st, cx.enums@), max as nat, tv, lt);
                }
                if pre {
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), new_len, defs@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), width(sty(t), enums@), blk.depth_s());
                    assert(all_pure(r@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(r@[j] == flat(rows_view(out@))[j - 1]);
                            }
                        }
                    }
                }
            }
                    proof {
                        let rv = rows_view(rows@);
                        lemma_pop(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rv, ng, defs@, og, r@);
                    }
                    Ok((tl, r))
                },
                _ => {
                    let mut out: Vec<Vec<Expr>> = Vec::new();
                    let mut p = 1;
                    while p < rows.len()
                        invariant
                            1 <= p,
                            p <= rows@.len() || rows@.len() == 0,
                            rows@.len() > 0 ==> out@.len() == p - 1,
                            rows@.len() == 0 ==> out@.len() == 0,
                            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q]@ == rows@[q + 1]@,
                        decreases rows.len() - p,
                    {
                        let ghost o1 = out@;
                        out.push(copy_exprs(&rows[p]));
                        proof {
                            assert forall|q: int| 0 <= q < out@.len() implies #[trigger] out@[q]@ == rows@[q + 1]@ by {
                                if q < o1.len() {
                                    assert(out@[q] == o1[q]);
                                }
                            }
                        }
                        p += 1;
                    }
                    let ghost o1 = out@;
                    if rows.len() > 0 {
                        out.push(defs);
                    }
                    let ghost og = rows_view(out@);
                    let r = list_join(new_len, &out);
                    proof {
                        if pre {
                            let rv = rows_view(rows@);
                            let w = width(sty(t), enums@);
                            assert forall|q: int| 0 <= q < og.len() implies (#[trigger] og[q]).len() == w && all_pure(
                                og[q],
                                blk.depth_s(),
                            ) by {
                                assert(og[q] == out@[q]@);
                                if q < o1.len() {
                                    assert(out@[q] == o1[q]);
                                    assert(o1[q]@ == rows@[q + 1]@);
                                    assert(rv[q + 1] == rows@[q + 1]@);
                                } else {
                                    assert(out@[q]@ == defs@);
                                }
                            }
                            lemma_flat_shape(og, w, blk.depth_s());
                            if tp {
                                let st = sty(t);
                                let ys = etys(slot_tys(st, cx.enums@));
                                let lt = blt(*blk, *cx);
                                assert forall|q: int| 0 <= q < og.len() implies #[trigger] typed(og[q], ys, tv, lt) by {
                                    assert(og[q] == out@[q]@);
                                    if q < o1.len() {
                                        assert(out@[q] == o1[q]);
                                        assert(o1[q]@ == rows@[q + 1]@);
                                        assert(rv[q + 1] == rows@[q + 1]@);
                                        assert(typed(rv[q + 1], ys, tv, lt));
                                    } else {
                                        assert(out@[q]@ == defs@);
                                    }
                                }
                                assert(og.len() == max) by {
                                    assert(rv.len() == max);
                                }
                                lemma_list_join_typed(ng, og, slot_tys(st, cx.enums@), max as nat, tv, lt);
                            }
                            assert(og.len() == max) by {
                                assert(rv.len() == max);
                            }
                            assert(all_pure(r@, blk.depth_s())) by {
                                assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                                    if j > 0 {
                                        assert(r@[j] == flat(og)[j - 1]);
                                    }
                                }
                            }
                        }
                    }
                    proof {
                        let rv = rows_view(rows@);
                        if rv.len() > 0 {
                            assert(og.len() == rv.len());
                            assert forall|q: int| 0 <= q < rv.len() - 1 implies #[trigger] og[q] == rv[q + 1] by {
                                assert(og[q] == out@[q]@);
                                assert(out@[q] == o1[q]);
                                assert(rv[q + 1] == rows@[q + 1]@);
                            }
                            assert(og[rv.len() - 1] == out@[rv.len() - 1]@);
                        }
                        lemma_shift(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rv, ng, defaults_s(sty(t), enums@), og, r@);
                    }
                    Ok((tl, r))
                },
            }
        },
        _ => Err(Fail::Type),
    }
}

} // verus!
