//! 葉（リテラル、変数、引数）、演算子、`let`、`all` と `any`、条件式の下ろし。意味の保存は `preserve_ops` にある。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{eval_l, lookup, Env, ErrKind};
use crate::kernel::expr_copy::copy_expr;
use crate::kernel::model::{BinOp, Expr, Value};
use crate::kernel::typing::ETy;
#[cfg(verus_keep_ghost)]
use crate::kernel::typing::{type_l, TyEnv};
#[cfg(verus_keep_ghost)]
use crate::lower::lowering::low_ok;
use crate::lower::lowering::{bool_in, layout_slots, lit_type, low, sub_scalar};
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_ops::pad_lets_seq;
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_ops::{ite_binds, lemma_bin, lemma_eq, lemma_fold, lemma_fold_empty};
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_ops::{lemma_implies, lemma_ite_binds_push, lemma_ite_bound, lemma_ite_out_pure};
#[cfg(verus_keep_ghost)]
use crate::preserve::preserve_ops::{lemma_ite_simple, lemma_let, lemma_not, lemma_pads_closed, pad_lets_s};
#[cfg(verus_keep_ghost)]
use crate::slot::block::lemma_extends_refl;
use crate::slot::block::{atom, atoms, bind, depth, need, new_block, wrap};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{all_pure, bool_lit, ite_s, kind_expr, lemma_all_pure_mono, lemma_pure_mono};
use crate::slot::expr_build::{bin, cb, defaults, extend, ite, pure_exec, tree, Join};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{lits, pure_below};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{extends, ok_x, sc_wf, shaped};
use crate::slot::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{all_ty, binds_typed, blt, has_ty, lemma_added_typed, lemma_bind_typed};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_binds_push, lemma_has_ty_blk, lemma_kind_typed, lemma_lits_typed};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_lts_len, lemma_pure_type, lemma_tok_ext, lemma_tree_typed};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_typed_blk, lemma_typed_concat, lemma_typed_ext, lemma_typed_sub};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{lemma_xetys_len, lemma_xetys_of, lenv, lts, sc_typed, tok, tok_in};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{ty_post, typed, xetys, xetys_seq};
#[cfg(verus_keep_ghost)]
use crate::slot::members::lemma_defaults_typed;
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{closed_lowers, closed_slots, ctx_ok, denotes, fresh, layout_ok, layouts_ok};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{lemma_extends_trans, lemma_fresh_refl, lemma_lits, lemma_models_len, lowers};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{result_ok, run, slot_vals, slots_result, wraps};
#[cfg(verus_keep_ghost)]
use crate::slot::slot_types::slot_tys;
use crate::slot::slots::{copy_exprs, eq_slots, not};
#[cfg(verus_keep_ghost)]
use crate::slot::total::{bound_tys, cx_wf, deep, here_ok, layout_wf, lemma_ite_tpre, lemma_lim_ok_seq_at};
#[cfg(verus_keep_ghost)]
use crate::slot::total::{lemma_sc_wf_mono, lim_ok, low_post, ok_s, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{default_val, enc, lemma_default_len, lemma_enc_len, lemma_models_enc};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_xtys, lemma_xwidth_of, lemma_xwidth_pos, member, sty, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{wf_xtypes, xty, xtys, xwidth, xwidth_sum, XTy};
use crate::value::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::value::infer::{ir_type_of, lemma_all_typed_bool, lemma_all_typed_iff};
#[cfg(verus_keep_ghost)]
use crate::value::limits::{lemma_lim_small, lemma_lim_xs_at, lim_xs};
use crate::value::source::TExpr;
#[cfg(verus_keep_ghost)]
use crate::value::source::{eval_src, SEnv};
use crate::value::stype_exec::{copy_stype, copy_xtype, to_xtype, xtype_eq};
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// 深さ `depth` で単独に評価できるように下ろす。スロットごとに、束縛を含む式を返す。
pub(crate) fn closed_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize, outer: Ghost<Seq<ETy>>) -> (r: Result<(XType, Vec<Expr>), Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, xs)) ==> closed_slots(*e, *cx, old(sc)@, depth as nat, xty(t), xs@),
        tpre(*e, *cx, old(sc)@, depth as nat) ==> deep(r) && (r matches Ok((t, xs)) ==> Some(xty(t)) == ir_type_of(
            *e,
            sctx(*cx),
            bound_tys(old(sc)@),
        ) && xs@.len() == xwidth(xty(t), cx.enums@)),
        tpre(*e, *cx, old(sc)@, depth as nat) && tok_in(*cx, old(sc)@, outer@, depth as nat) ==> (r matches Ok((t, xs))
            ==> typed(xs@, xetys(xty(t), cx.enums@), lenv(*cx), outer@)),
    decreases e, 5nat,
{
    let mut blk = new_block(depth, outer)?;
    let ghost b0 = blk;
    proof {
        assert(blt(b0, *cx) == outer@);
    }
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < slots.len()
        invariant
            i <= slots@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, slots@[j]),
            forall|j: int, t: TyEnv, o: Seq<ETy>|
                0 <= j < i && #[trigger] binds_typed(o, blk.binds@, t) ==> type_l(#[trigger] out@[j], t, o) == type_l(
                    slots@[j],
                    t,
                    lts(o, blk.binds@, t),
                ),
        decreases slots.len() - i,
    {
        let ghost o0 = out@;
        let x = wrap(&blk.binds, copy_expr(&slots[i]));
        out.push(x);
        proof {
            assert forall|j: int, t: TyEnv, o: Seq<ETy>|
                0 <= j < i + 1 && #[trigger] binds_typed(o, blk.binds@, t) implies type_l(#[trigger] out@[j], t, o) == type_l(
                slots@[j],
                t,
                lts(o, blk.binds@, t),
            ) by {
                if j < i {
                    assert(out@[j] == o0[j]);
                }
            }
        }
        proof {
            assert(wraps(out@[i as int], blk.binds@, slots@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        if tpre(*e, *cx, old(sc)@, depth as nat) && tok_in(*cx, old(sc)@, outer@, depth as nat) {
            assert(tok(*cx, old(sc)@, b0));
            assert(binds_typed(outer@, blk.binds@, lenv(*cx)));
            assert forall|j: int| 0 <= j < out@.len() implies #[trigger] has_ty(out@[j], lenv(*cx), outer@, xetys(xty(t), cx.enums@)[j]) by {
                assert(has_ty(slots@[j], lenv(*cx), blt(blk, *cx), xetys(xty(t), cx.enums@)[j]));
            }
        }
        {
            assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == depth as nat implies slots_result(
                eval_src(*e, se, sls),
                out@,
                env,
                ls,
                xty(t),
                se.enums,
            ) by {
                match eval_src(*e, se, sls) {
                    Ok(v) => {
                        let l = run(blk.binds@, env, ls)->Ok_0;
                        assert(denotes(slots@, env, l, v, xty(t), se.enums));
                        lemma_models_len(slot_vals(slots@, env, l), v, xty(t), se.enums);
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Ok::<
                            Value,
                            ErrKind,
                        >(slot_vals(slots@, env, l)[j]) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                        assert(slot_vals(out@, env, ls) =~= slot_vals(slots@, env, l));
                    },
                    Err(_) => {
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Err::<
                            Value,
                            ErrKind,
                        >(eval_src(*e, se, sls)->Err_0) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                    },
                }
            }
        }
    }
    Ok((t, out))
}

/// リテラルと参照。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_leaf(e: &TExpr, cx: &LowerCtx, sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const,
    ensures
        tpre(*e, *cx, sc@, _blk.depth_s()) ==> low_post(*e, *cx, sc@, _blk.depth_s(), r),
        tpre(*e, *cx, sc@, _blk.depth_s()) && tok(*cx, sc@, *_blk) ==> ty_post(*cx, *_blk, r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, sc@, *_blk, *_blk, xty(t), slots@),
{
    match e {
        TExpr::Lit(_) => low_lit(e, cx, sc, _blk),
        TExpr::Var(_) | TExpr::Next(_) => low_state(e, cx, sc, _blk),
        TExpr::Arg(_) | TExpr::Out => low_arg(e, cx, sc, _blk),
        TExpr::Local(_) | TExpr::Const(_) => low_named(e, cx, sc, _blk),
        _ => Err(Fail::Type),
    }
}

/// リテラルの下ろし（[`low_leaf`] の枝）。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_lit(e: &TExpr, cx: &LowerCtx, _sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Lit,
    ensures
        tpre(*e, *cx, _sc@, _blk.depth_s()) ==> low_post(*e, *cx, _sc@, _blk.depth_s(), r),
        tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk) ==> ty_post(*cx, *_blk, r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, _sc@, *_blk, *_blk, xty(t), slots@),
{
    let enums = &cx.enums;
    let ghost tp = tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk);
    let ghost tv = lenv(*cx);
    let ghost lt = blt(*_blk, *cx);
    match e {
        TExpr::Lit(v) => {
            match v {
                Value::Enum(id, k) => {
                    if !(*id < enums.len() && 0 <= *k && *k < enums[*id]) {
                        return Err(Fail::Type);
                    }
                },
                _ => {},
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Const(*v));
            let t = lit_type(v);
            proof {
                if tp {
                    assert(xetys(xty(t), enums@).len() == 1);
                    assert(has_ty(out@[0], tv, lt, xetys(xty(t), enums@)[0]));
                }
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, _sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(slot_vals(out@, env, ls) =~= seq![*v]);
                }
            }
            Ok((t, out))
        },
        _ => Err(Fail::Type),
    }
}

/// 状態変数の参照（遷移前と遷移後）の下ろし（[`low_leaf`] の枝）。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_state(e: &TExpr, cx: &LowerCtx, _sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Var || e is Next,
    ensures
        tpre(*e, *cx, _sc@, _blk.depth_s()) ==> low_post(*e, *cx, _sc@, _blk.depth_s(), r),
        tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk) ==> ty_post(*cx, *_blk, r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, _sc@, *_blk, *_blk, xty(t), slots@),
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, _sc@, _blk.depth_s());
    let ghost tp = tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk);
    let ghost tv = lenv(*cx);
    let ghost lt = blt(*_blk, *cx);
    match e {
        TExpr::Var(i) | TExpr::Next(i) => {
            let states = match &cx.states {
                Some(s) => s,
                None => return Err(Fail::Type),
            };
            let is_next = match e {
                TExpr::Next(_) => true,
                _ => false,
            };
            if is_next && !cx.next {
                return Err(Fail::Type);
            }
            if *i >= states.len() {
                return Err(Fail::Type);
            }
            let kind: u8 = if is_next {
                1
            } else {
                0
            };
            proof {
                if pre {
                    assert(layout_wf(states@[*i as int], enums@));
                }
                lemma_xwidth_of(sty(states@[*i as int].ty), enums@);
            }
            let (t, out) = need(layout_slots(&states[*i], kind, enums))?;
            proof {
                assert(all_pure(out@, _blk.depth_s()));
                if tp {
                    lemma_kind_typed(states@, *i as int, kind, out@, tv, lt);
                }
            }
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, _sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = states@[*i as int];
                    let xs = if is_next {
                        env.post
                    } else {
                        env.pre
                    };
                    let vs = if is_next {
                        se.post
                    } else {
                        se.pre
                    };
                    assert(layouts_ok(states@, vs, env.st_tys, xs, enums@));
                    let v = vs[*i as int];
                    assert(layout_ok(l, v, env.st_tys, xs, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(kind, (l.offset + j) as usize));
                        assert(lookup(env.st_tys, xs, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Ok((t, out))
        },
        _ => Err(Fail::Type),
    }
}

/// 引数と出力の参照の下ろし（[`low_leaf`] の枝）。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_arg(e: &TExpr, cx: &LowerCtx, _sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Arg || e is Out,
    ensures
        tpre(*e, *cx, _sc@, _blk.depth_s()) ==> low_post(*e, *cx, _sc@, _blk.depth_s(), r),
        tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk) ==> ty_post(*cx, *_blk, r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, _sc@, *_blk, *_blk, xty(t), slots@),
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, _sc@, _blk.depth_s());
    let ghost tp = tpre(*e, *cx, _sc@, _blk.depth_s()) && tok(*cx, _sc@, *_blk);
    let ghost tv = lenv(*cx);
    let ghost lt = blt(*_blk, *cx);
    match e {
        TExpr::Arg(i) => {
            if *i >= cx.args.len() {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(layout_wf(cx.args@[*i as int], enums@));
                }
                lemma_xwidth_of(sty(cx.args@[*i as int].ty), enums@);
            }
            let (t, out) = need(layout_slots(&cx.args[*i], 2, enums))?;
            proof {
                assert(all_pure(out@, _blk.depth_s()));
                if tp {
                    lemma_kind_typed(cx.args@, *i as int, 2, out@, tv, lt);
                }
            }
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, _sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = cx.args@[*i as int];
                    let v = se.args[*i as int];
                    assert(layout_ok(l, v, env.arg_tys, env.args, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(2, (l.offset + j) as usize));
                        assert(lookup(env.arg_tys, env.args, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Ok((t, out))
        },
        TExpr::Out => {
            let st = match &cx.out {
                Some(t) => t,
                None => return Err(Fail::Type),
            };
            if !cx.next {
                return Err(Fail::Type);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Out);
            let t = to_xtype(st);
            proof {
                if tp {
                    lemma_xetys_of(sty(*st), enums@);
                    crate::slot::slot_types::lemma_slot_tys_len(sty(*st), enums@);
                    assert(has_ty(out@[0], tv, lt, xetys(xty(t), enums@)[0]));
                }
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, _sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.out->Some_0;
                    lemma_enc_len(v, sty(*st), enums@);
                    lemma_models_enc(v, sty(*st), enums@);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Ok((t, out))
        },
        _ => Err(Fail::Type),
    }
}

/// 局所変数と名前付きの定数の参照の下ろし（[`low_leaf`] の枝）。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_named(e: &TExpr, cx: &LowerCtx, sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Local || e is Const,
    ensures
        tpre(*e, *cx, sc@, _blk.depth_s()) ==> low_post(*e, *cx, sc@, _blk.depth_s(), r),
        tpre(*e, *cx, sc@, _blk.depth_s()) && tok(*cx, sc@, *_blk) ==> ty_post(*cx, *_blk, r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, sc@, *_blk, *_blk, xty(t), slots@),
{
    let ghost enums = cx.enums@;
    let ghost pre = tpre(*e, *cx, sc@, _blk.depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(sc@);
    let ghost tp = tpre(*e, *cx, sc@, _blk.depth_s()) && tok(*cx, sc@, *_blk);
    let ghost tv = lenv(*cx);
    let ghost lt = blt(*_blk, *cx);
    match e {
        TExpr::Local(i) => {
            if *i >= sc.len() {
                return Err(Fail::Type);
            }
            let t = copy_xtype(&sc[*i].ty);
            proof {
                if pre {
                    assert(ok_x(xty(sc@[*i as int].ty), enums));
                    assert(bt[*i as int] == xty(sc@[*i as int].ty));
                }
            }
            let out = copy_exprs(&sc[*i].slots);
            proof {
                if tp {
                    assert(typed(sc@[*i as int].slots@, xetys(xty(sc@[*i as int].ty), enums), tv, lt));
                }
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(denotes(sc@[*i as int].slots@, env, ls, sls[*i as int], xty(sc@[*i as int].ty), se.enums));
                }
            }
            Ok((t, out))
        },
        TExpr::Const(i) => {
            if *i >= cx.consts.len() {
                return Err(Fail::Type);
            }
            let c = &cx.consts[*i];
            let mut out: Vec<Expr> = Vec::new();
            let mut j = 0;
            while j < c.slots.len()
                invariant
                    j <= c.slots@.len(),
                    out@ == lits(c.slots@.take(j as int)),
                decreases c.slots.len() - j,
            {
                out.push(Expr::Const(c.slots[j]));
                proof {
                    assert(out@ =~= lits(c.slots@.take(j + 1)));
                }
                j += 1;
            }
            let t = to_xtype(&c.ty);
            proof {
                lemma_lits(c.slots@, arbitrary(), Seq::empty());
                assert(c.slots@.take(c.slots@.len() as int) =~= c.slots@);
                assert(all_pure(out@, _blk.depth_s()));
                lemma_xwidth_of(sty(c.ty), enums);
                if pre {
                    assert(ok_s(sty(cx.consts@[*i as int].ty), enums));
                }
                if tp {
                    assert(crate::slot::slot_types::in_slots(c.slots@, slot_tys(sty(c.ty), enums), enums));
                    lemma_lits_typed(c.slots@, slot_tys(sty(c.ty), enums), tv, lt);
                    lemma_xetys_of(sty(c.ty), enums);
                }
            }
            proof {
                assert(c.slots@.take(c.slots@.len() as int) =~= c.slots@);
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.consts[*i as int];
                    assert(member(v, sty(c.ty), enums) && c.slots@ == enc(v, sty(c.ty), enums));
                    lemma_lits(c.slots@, env, ls);
                    lemma_models_enc(v, sty(c.ty), enums);
                }
            }
            Ok((t, out))
        },
        _ => Err(Fail::Type),
    }
}


/// リテラル、参照、スカラーの演算、短絡する演算、`let`。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_core(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const || e is Bin || e is Eq || e is Not || e is Fold || e is Implies || e is Ite || e is Let,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 2nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_) => {
            proof {
                lemma_extends_refl(*blk);
            }
            low_leaf(e, cx, sc, blk)
        },
        TExpr::Bin(op, a, b) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Int)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            proof {
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let y = sub_scalar(b, cx, sc, blk, &XType::Int)?;
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_pure_mono(x, b1.depth_s(), b2.depth_s());
                }
                if tp {
                    lemma_has_ty_blk(x, ETy::Int, *cx, b1, b2);
                    assert(has_ty(Expr::Bin(*op, Box::new(x), Box::new(y)), tv, blt(b2, *cx), if op is Add || op is Sub || op is Mul || op is Div || op is Mod { ETy::Int } else { ETy::Bool }));
                }
            }
            let ghost z = Expr::Bin(*op, Box::new(x), Box::new(y));
            let mut out: Vec<Expr> = Vec::new();
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    out.push(bind(blk, bin(*op, x, y))?);
                    proof {
                        if tp {
                            lemma_bind_typed(b2, *blk, z, out@[0], *cx, ETy::Int);
                        }
                        lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Int, out@);
                    }
                    Ok((XType::Int, out))
                },
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    out.push(bin(*op, x, y));
                    proof {
                        if pre {
                            assert(pure_below(out@[0], blk.depth_s()));
                        }
                    }
                    proof {
                        lemma_extends_refl(*blk);
                        lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Bool, out@);
                    }
                    Ok((XType::Bool, out))
                },
                _ => Err(Fail::Type),
            }
        },
        TExpr::Eq(positive, a, b) => {
            let ghost b0 = *blk;
            let (tx, x) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            proof {
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                }
            }
            let (ty, y) = low(b, cx, sc, blk)?;
            proof {
                if pre {
                    lemma_all_pure_mono(x@, b1.depth_s(), blk.depth_s());
                }
                if tp {
                    lemma_typed_blk(x@, xetys(xty(tx), cx.enums@), *cx, b1, *blk);
                }
            }
            if !xtype_eq(&ty, &tx) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, sctx(*cx), bound_tys(sc0)));
                    assert(here_ok(**a, sctx(*cx), bound_tys(sc0)));
                    assert(ok_x(xty(tx), cx.enums@));
                }
            }
            let c = need(eq_slots(&tx, &x, &y, enums))?;
            let ghost cg = c;
            let mut out: Vec<Expr> = Vec::new();
            out.push(
                if *positive {
                    c
                } else {
                    not(c)
                },
            );
            proof {
                lemma_eq(*e, *cx, sc@, b0, b1, *blk, xty(tx), x@, y@, cg, out@);
            }
            proof {
                if pre {
                    assert(all_pure(x@, blk.depth_s()) && all_pure(y@, blk.depth_s()));
                    assert(pure_below(cg, blk.depth_s()));
                    assert(pure_below(out@[0], blk.depth_s()));
                }
                if tp {
                    assert(xty(ty) == xty(tx));
                    assert(typed(y@, xetys(xty(tx), cx.enums@), tv, blt(*blk, *cx)));
                    assert(has_ty(cg, tv, blt(*blk, *cx), ETy::Bool));
                    assert(has_ty(out@[0], tv, blt(*blk, *cx), ETy::Bool));
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Not(a) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(not(x));
            proof {
                if pre {
                    assert(pure_below(out@[0], blk.depth_s()));
                }
            }
            proof {
                lemma_not(*e, *cx, sc@, b0, *blk, x);
            }
            Ok((XType::Bool, out))
        },
        TExpr::Fold(_, _) => low_fold(e, cx, sc, blk),
        TExpr::Implies(a, b) => {
            let ghost b0 = *blk;
            let p = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            proof {
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                    lemma_lts_len(b1.outer@, b1.binds@, tv);
                }
            }
            let q = bool_in(b, cx, sc, depth(blk), Ghost(blt(*blk, *cx)))?;
            let mut out: Vec<Expr> = Vec::new();
            let ghost z = Expr::Implies(Box::new(p), Box::new(q));
            out.push(bind(blk, Expr::Implies(Box::new(p), Box::new(q)))?);
            proof {
                if tp {
                    assert(has_ty(z, tv, blt(b1, *cx), ETy::Bool));
                    lemma_bind_typed(b1, *blk, z, out@[0], *cx, ETy::Bool);
                }
                lemma_implies(*e, *cx, sc@, b0, b1, *blk, p, q);
            }
            Ok((XType::Bool, out))
        },
        TExpr::Ite(_, _, _) => low_ite(e, cx, sc, blk),
        TExpr::Let(a, b) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let ghost s0 = slots@;
            let slots = atoms(slots, blk, Ghost(*cx), Ghost(xetys(xty(t), cx.enums@)))?;
            let ghost b2 = *blk;
            proof {
                if tp {
                    lemma_tok_ext(*cx, sc0, b0, b1);
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                    lemma_tok_ext(*cx, sc0, b1, b2);
                }
            }
            let ghost before = sc@;
            let ghost bound = Bound { ty: t, slots };
            sc.push(Bound { ty: t, slots });
            let ghost sc1 = sc@;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b2.depth_s(), cx.enums@);
                    assert(sc1 == sc0.push(bound));
                    assert(bound_tys(sc1) =~= bound_tys(sc0).push(xty(t)));
                    assert(sc_wf(sc1, b2.depth_s(), cx.enums@)) by {
                        assert forall|i: int| 0 <= i < sc1.len() implies ok_x(xty(#[trigger] sc1[i].ty), cx.enums@) && shaped(
                            sc1[i].slots@,
                            xty(sc1[i].ty),
                            b2.depth_s(),
                            cx.enums@,
                        ) by {
                            if i < sc0.len() {
                                assert(sc1[i] == sc0[i]);
                            } else {
                                assert(sc1[i] == bound);
                                assert(lim_ok(**a, sctx(*cx), bound_tys(sc0)));
                                assert(here_ok(**a, sctx(*cx), bound_tys(sc0)));
                            }
                        }
                    }
                }
            }
            proof {
                if tp {
                    assert(sc_typed(sc1, *cx, blt(b2, *cx))) by {
                        assert forall|i: int| 0 <= i < sc1.len() implies #[trigger] typed(
                            sc1[i].slots@,
                            xetys(xty(sc1[i].ty), cx.enums@),
                            tv,
                            blt(b2, *cx),
                        ) by {
                            if i < sc0.len() {
                                assert(sc1[i] == sc0[i]);
                            } else {
                                assert(sc1[i] == bound);
                            }
                        }
                    }
                    assert(tok(*cx, sc1, b2));
                }
            }
            let r = low(b, cx, sc, blk);
            if r.is_err() {
                return r;
            }
            sc.pop();
            proof {
                assert(sc@ =~= before);
                assert(sc1 == before.push(bound));
                {
                    let (tb, out) = r->Ok_0;
                    lemma_let(*e, *cx, before, b0, b1, b2, *blk, s0, bound, xty(tb), out@);
                }
            }
            r
        },
        _ => Err(Fail::Type),
    }
}

/// `all` と `any`。先頭の項はスロットにし、残りの項は単独に評価する式にして、短絡する木にたたむ。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn low_fold(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Fold,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let (all, es) = match e {
        TExpr::Fold(all, es) => (*all, es),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    proof {
        assert(decreases_to!(*e => *es));
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    proof {
        lemma_all_typed_bool(es@, c, bt);
        lemma_all_typed_iff(es@, XTy::Bool, c, bt);
        if pre {
            assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                lemma_lim_ok_seq_at(es@, c, bt, j);
            }
        }
    }
    let mut out: Vec<Expr> = Vec::new();
    if es.len() == 0 {
        proof {
            lemma_extends_refl(*blk);
        }
        out.push(cb(all));
        proof {
            lemma_fold_empty(*e, *cx, sc@, *blk, out@);
        }
        return Ok((XType::Bool, out));
    }
    proof {
        vstd::std_specs::vec::axiom_vec_index_decreases(*es, 0);
        if pre {
            assert(ir_type_of(es@[0], c, bt) == Some(XTy::Bool));
            assert(lim_ok(es@[0], c, bt));
        }
    }
    let x = sub_scalar(&es[0], cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let d = depth(blk);
    let mut terms: Vec<Expr> = Vec::new();
    terms.push(x);
    let ghost sc0 = sc@;
    proof {
        if pre {
            lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
        if tp {
            lemma_tok_ext(*cx, sc0, b0, b1);
            lemma_lts_len(b1.outer@, b1.binds@, tv);
            assert(all_ty(terms@, ETy::Bool, tv, blt(b1, *cx)));
        }
    }
    let mut i = 1;
    while i < es.len()
        invariant
            decreases_to!(*e => *es),
            *e == TExpr::Fold(all, *es),
            1 <= i <= es@.len(),
            sc@ == sc0,
            *blk == b1,
            b0 == *old(blk),
            extends(b0, b1),
            d == b1.depth_s(),
            lowers(es@[0], *cx, sc0, b0, b1, XTy::Bool, seq![x]),
            terms@.len() == i,
            terms@[0] == x,
            pre == tpre(*e, *cx, sc0, b0.depth_s()),
            sc0 == old(sc)@,
            c == sctx(*cx),
            bt == bound_tys(sc0),
            pre ==> sc_wf(sc0, d as nat, cx.enums@) && cx_wf(*cx),
            pre ==> forall|j: int| 0 <= j < es@.len() ==> ir_type_of(#[trigger] es@[j], c, bt) == Some(XTy::Bool) && lim_ok(
                es@[j],
                c,
                bt,
            ),
            forall|j: int|
                1 <= j < i ==> #[trigger] closed_lowers(es@[j], *cx, sc0, d as nat, XTy::Bool, terms@[j]),
            tp == (pre && tok(*cx, sc0, b0)),
            tv == lenv(*cx),
            tp ==> tok(*cx, sc0, b1) && blt(b1, *cx).len() == d && all_ty(terms@, ETy::Bool, tv, blt(b1, *cx)),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            if pre {
                assert(ir_type_of(es@[i as int], c, bt) == Some(XTy::Bool));
                assert(lim_ok(es@[i as int], c, bt));
                assert(sc_wf(sc@, d as nat, cx.enums@));
                assert(tpre(es@[i as int], *cx, sc@, d as nat));
            }
        }
        let q = bool_in(&es[i], cx, sc, d, Ghost(blt(*blk, *cx)))?;
        let ghost t0 = terms@;
        terms.push(q);
        proof {
            if tp {
                assert forall|j: int| 0 <= j < terms@.len() implies #[trigger] has_ty(terms@[j], tv, blt(b1, *cx), ETy::Bool) by {
                    if j < i {
                        assert(terms@[j] == t0[j]);
                        assert(has_ty(t0[j], tv, blt(b1, *cx), ETy::Bool));
                    }
                }
            }
            assert forall|j: int| 1 <= j < i + 1 implies #[trigger] closed_lowers(
                es@[j],
                *cx,
                sc0,
                d as nat,
                XTy::Bool,
                terms@[j],
            ) by {
                if j < i {
                    assert(terms@[j] == t0[j]);
                }
            }
        }
        i += 1;
    }
    let joined = tree(&terms, cb(all), if all { Join::RawAnd } else { Join::RawOr });
    let ghost jg = joined;
    proof {
        if tp {
            let jk = if all { Join::RawAnd } else { Join::RawOr };
            lemma_tree_typed(terms@, bool_lit(all), jk, tv, blt(b1, *cx), ETy::Bool);
        }
    }
    out.push(bind(blk, joined)?);
    proof {
        if tp {
            lemma_bind_typed(b1, *blk, jg, out@[0], *cx, ETy::Bool);
        }
        lemma_fold(*e, *cx, sc0, b0, b1, *blk, terms@);
    }
    Ok((XType::Bool, out))
}

/// 条件式のスロット。枝のスロットが局所変数 `n` 個のもとで純粋でなければ `None`。
pub(crate) fn ite_slots(c: &Expr, xs: &Vec<Expr>, ys: &Vec<Expr>, n: usize) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(out) ==> xs@.len() == ys@.len() && out@.len() == xs@.len() && (forall|i: int|
            0 <= i < out@.len() ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i])) && (forall|i: int|
            0 <= i < xs@.len() ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat)),
        xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat) ==> r is Some,
{
    let ghost pre = xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat);
    if xs.len() != ys.len() {
        return None;
    }
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < xs.len()
        invariant
            xs@.len() == ys@.len(),
            j <= xs@.len(),
            out@.len() == j,
            forall|i: int| 0 <= i < j ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i]),
            forall|i: int| 0 <= i < j ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat),
            pre == (xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat)),
        decreases xs.len() - j,
    {
        proof {
            if pre {
                assert(pure_below(xs@[j as int], n as nat));
                assert(pure_below(ys@[j as int], n as nat));
            }
        }
        if !pure_exec(&xs[j], n) || !pure_exec(&ys[j], n) {
            return None;
        }
        let ghost px = pure_below(xs@[j as int], n as nat) && pure_below(ys@[j as int], n as nat);
        out.push(ite(copy_expr(c), copy_expr(&xs[j]), copy_expr(&ys[j])));
        proof {
            assert(px);
            assert forall|i: int| 0 <= i < j + 1 implies pure_below(#[trigger] xs@[i], n as nat) && pure_below(
                ys@[i],
                n as nat,
            ) by {}
        }
        j += 1;
    }
    Some(out)
}

/// 束縛を持つ `ite` の枝を、最後のスロットを束縛する深さで一度だけ単独に評価する式に下ろす。
/// スロット `j` ごとに、足りない深さを空の `let` で埋めて、`j` 番目のスロットを選ぶ式を束縛する。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_ite_slots(
    _parent: &TExpr,
    a: &TExpr,
    b: &TExpr,
    c: &Expr,
    tx: &XType,
    w: usize,
    cx: &LowerCtx,
    sc: &mut Vec<Bound>,
    blk: &mut Block,
) -> (r: Result<(Vec<Expr>, Ghost<Seq<Seq<Expr>>>, Ghost<Seq<Seq<Expr>>>), Fail>)
    requires
        old(blk).wf(),
        w > 0,
        decreases_to!(*_parent => *a),
        decreases_to!(*_parent => *b),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((out, fa, fb)) ==> {
            let d = old(blk).depth_s();
            &&& final(blk).binds@ == old(blk).binds@ + ite_binds(*c, fa@, fb@, w as nat)
            &&& fa@.len() == w
            &&& fb@.len() == w
            &&& out@ == Seq::new(w as nat, |i: int| Expr::Local((d + i) as usize))
            &&& forall|i: int|
                0 <= i < w ==> #[trigger] closed_slots(*a, *cx, old(sc)@, (d + i) as nat, xty(*tx), fa@[i])
            &&& forall|i: int|
                0 <= i < w ==> #[trigger] closed_slots(*b, *cx, old(sc)@, (d + i) as nat, xty(*tx), fb@[i])
            &&& forall|i: int| 0 <= i < w ==> i < (#[trigger] fa@[i]).len() && i < fb@[i].len()
        },
        tpre(*a, *cx, old(sc)@, old(blk).depth_s()) && tpre(*b, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(
            *a,
            sctx(*cx),
            bound_tys(old(sc)@),
        ) == Some(xty(*tx)) && ir_type_of(*b, sctx(*cx), bound_tys(old(sc)@)) == Some(xty(*tx)) && w == xwidth(
            xty(*tx),
            cx.enums@,
        ) ==> deep(r),
        tpre(*a, *cx, old(sc)@, old(blk).depth_s()) && tpre(*b, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(
            *a,
            sctx(*cx),
            bound_tys(old(sc)@),
        ) == Some(xty(*tx)) && ir_type_of(*b, sctx(*cx), bound_tys(old(sc)@)) == Some(xty(*tx)) && w == xwidth(
            xty(*tx),
            cx.enums@,
        ) && ok_x(xty(*tx), cx.enums@) && tok(*cx, old(sc)@, *old(blk)) && has_ty(*c, lenv(*cx), blt(*old(blk), *cx), ETy::Bool)
            && pure_below(*c, old(blk).depth_s()) ==> binds_typed(final(blk).outer@, final(blk).binds@, lenv(*cx)) && (
        r matches Ok((out, _, _)) ==> typed(out@, xetys(xty(*tx), cx.enums@), lenv(*cx), blt(*final(blk), *cx))),
    decreases _parent, 0nat,
{
    let ghost b2 = *blk;
    let ghost sc0 = sc@;
    let d = depth(blk);
    let ghost pre = tpre(*a, *cx, sc0, d as nat) && tpre(*b, *cx, sc0, d as nat) && ir_type_of(*a, sctx(*cx), bound_tys(sc0))
        == Some(xty(*tx)) && ir_type_of(*b, sctx(*cx), bound_tys(sc0)) == Some(xty(*tx)) && w == xwidth(xty(*tx), cx.enums@);
    let ghost tv = lenv(*cx);
    let ghost ys = xetys(xty(*tx), cx.enums@);
    let ghost tq = pre && ok_x(xty(*tx), cx.enums@) && tok(*cx, sc0, b2) && has_ty(*c, tv, blt(b2, *cx), ETy::Bool)
        && pure_below(*c, d as nat);
    proof {
        lemma_extends_refl(*blk);
    }
    let ds = xdefaults(tx, &cx.enums);
    if ds.len() != w {
        proof {
            if tq {
                assert(typed(ds@, ys, tv, blt(b2, *cx)));
                lemma_xetys_len(xty(*tx), cx.enums@);
            }
        }
        return Err(Fail::Type);
    }
    if w - 1 >= usize::MAX - d {
        return Err(Fail::Depth);
    }
    let top = d + (w - 1);
    proof {
        if pre {
            lemma_sc_wf_mono(sc0, d as nat, top as nat, cx.enums@);
        }
    }
    // 各枝を、最後のスロットを束縛する深さ `top` で一度だけ下ろす。
    // スロット `j` は深さ `d + j` で束縛するので、足りない `w - 1 - j` 個の深さを空の `let` で埋めてから評価する。
    let ghost outer = blt(*blk, *cx) + xetys(xty(*tx), cx.enums@).take(w - 1);
    proof {
        if tq {
            lemma_xetys_len(xty(*tx), cx.enums@);
            lemma_lts_len(b2.outer@, b2.binds@, tv);
            assert(outer.len() == top);
            assert(outer.take(d as int) =~= blt(b2, *cx));
            assert(blt(b2, *cx).take(d as int) =~= blt(b2, *cx));
            assert forall|i: int| 0 <= i < sc0.len() implies #[trigger] typed(
                sc0[i].slots@,
                xetys(xty(sc0[i].ty), cx.enums@),
                tv,
                outer,
            ) by {
                assert(typed(sc0[i].slots@, xetys(xty(sc0[i].ty), cx.enums@), tv, blt(b2, *cx)));
                assert(shaped(sc0[i].slots@, xty(sc0[i].ty), d as nat, cx.enums@));
                lemma_typed_ext(sc0[i].slots@, xetys(xty(sc0[i].ty), cx.enums@), tv, blt(b2, *cx), outer, d as nat);
            }
            assert(tok_in(*cx, sc0, outer, top as nat));
        }
    }
    let (ta, xa) = closed_in(a, cx, sc, top, Ghost(outer))?;
    let (tb, yb) = closed_in(b, cx, sc, top, Ghost(outer))?;
    if !xtype_eq(&ta, tx) || !xtype_eq(&tb, tx) || xa.len() != w || yb.len() != w {
        return Err(Fail::Type);
    }
    let ghost mut fa: Seq<Seq<Expr>> = Seq::empty();
    let ghost mut fb: Seq<Seq<Expr>> = Seq::empty();
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < w
        invariant
            sc@ == sc0,
            j <= w,
            w == xa@.len(),
            w == yb@.len(),
            top == d + w - 1,
            b2.wf(),
            d == b2.depth_s(),
            b2 == *old(blk),
            extends(b2, *blk),
            blk.base == b2.base,
            blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, j as nat),
            fa.len() == j,
            fb.len() == j,
            out@ == Seq::new(j as nat, |i: int| Expr::Local((d + i) as usize)),
            closed_slots(*a, *cx, sc0, top as nat, xty(*tx), xa@),
            closed_slots(*b, *cx, sc0, top as nat, xty(*tx), yb@),
            forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*a, *cx, sc0, (d + i) as nat, xty(*tx), fa[i]),
            forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*b, *cx, sc0, (d + i) as nat, xty(*tx), fb[i]),
            forall|i: int| 0 <= i < fa.len() ==> i < (#[trigger] fa[i]).len(),
            forall|i: int| 0 <= i < fb.len() ==> i < (#[trigger] fb[i]).len(),
            sc0 == old(sc)@,
            ds@.len() == w,
            forall|i: int| 0 <= i < ds@.len() ==> #[trigger] ds@[i] is Const,
            tv == lenv(*cx),
            ys == xetys(xty(*tx), cx.enums@),
            outer == blt(b2, *cx) + ys.take(w - 1),
            pre == (tpre(*a, *cx, sc0, d as nat) && tpre(*b, *cx, sc0, d as nat) && ir_type_of(*a, sctx(*cx), bound_tys(sc0))
                == Some(xty(*tx)) && ir_type_of(*b, sctx(*cx), bound_tys(sc0)) == Some(xty(*tx)) && w == xwidth(xty(*tx), cx.enums@)),
            tq == (pre && ok_x(xty(*tx), cx.enums@) && tok(*cx, sc0, b2) && has_ty(*c, tv, blt(b2, *cx), ETy::Bool)
                && pure_below(*c, d as nat)),
            tq ==> ys.len() == w && blt(b2, *cx).len() == d && typed(xa@, ys, tv, outer) && typed(yb@, ys, tv, outer)
                && (forall|tv2: TyEnv, lt2: Seq<ETy>| tv2.enums == cx.enums@ ==> #[trigger] typed(ds@, ys, tv2, lt2)),
            tq ==> binds_typed(blk.outer@, blk.binds@, tv) && blt(*blk, *cx) == blt(b2, *cx) + ys.take(j as int),
        decreases w - j,
    {
        let ghost bj = *blk;
        let ghost dj = ds@.subrange(j as int, (w - 1) as int);
        let ghost ej = ite_s(*c, pad_lets_s(dj, xa@[j as int]), pad_lets_s(dj, yb@[j as int]));
        proof {
            if tq {
                let ltj = blt(bj, *cx);
                let yj = ys.subrange(j as int, (w - 1) as int);
                assert(ltj + yj =~= outer);
                assert forall|i: int| 0 <= i < dj.len() implies #[trigger] dj[i] is Const by {
                    assert(dj[i] == ds@[j + i]);
                }
                assert(typed(ds@, ys, tv, ltj));
                lemma_typed_sub(ds@, ys, tv, ltj, j as int, (w - 1) as int);
                lemma_pad_type(dj, yj, xa@[j as int], tv, ltj);
                lemma_pad_type(dj, yj, yb@[j as int], tv, ltj);
                assert(has_ty(xa@[j as int], tv, outer, ys[j as int]));
                assert(has_ty(yb@[j as int], tv, outer, ys[j as int]));
                assert(ltj.take(d as int) =~= blt(b2, *cx));
                assert(blt(b2, *cx).take(d as int) =~= blt(b2, *cx));
                lemma_pure_type(*c, tv, blt(b2, *cx), ltj, d as nat);
                assert(has_ty(ej, tv, ltj, ys[j as int]));
            }
        }
        let o = bind(blk, ite(copy_expr(c), pad_lets(&ds, j, w - 1, copy_expr(&xa[j])), pad_lets(&ds, j, w - 1, copy_expr(&yb[j]))))?;
        out.push(o);
        proof {
            if tq {
                lemma_bind_typed(bj, *blk, ej, o, *cx, ys[j as int]);
                lemma_binds_push(bj.outer@, bj.binds@, tv, ej);
                assert(blt(*blk, *cx) =~= blt(b2, *cx) + ys.take(j + 1));
            }
            lemma_extends_trans(b2, bj, *blk);
            let fa0 = fa;
            let fb0 = fb;
            let pa = pad_lets_seq(xa@, dj);
            let pb = pad_lets_seq(yb@, dj);
            assert(pa[j as int] == pad_lets_s(dj, xa@[j as int]));
            assert(pb[j as int] == pad_lets_s(dj, yb@[j as int]));
            fa = fa.push(pa);
            fb = fb.push(pb);
            lemma_ite_binds_push(*c, fa0, fb0, pa, pb, j as nat);
            assert(blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, (j + 1) as nat));
            assert(out@ =~= Seq::new((j + 1) as nat, |i: int| Expr::Local((d + i) as usize)));
            assert(fa[j as int] == pa && fb[j as int] == pb);
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fa[i]).len() by {
                if i < j {
                    assert(fa[i] == fa0[i]);
                } else {
                    assert(fa[i] == pa);
                }
            }
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fb[i]).len() by {
                if i < j {
                    assert(fb[i] == fb0[i]);
                } else {
                    assert(fb[i] == pb);
                }
            }
            lemma_pads_closed(*a, *cx, sc0, top as nat, (d + j) as nat, dj, xty(*tx), xa@);
            assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                *a,
                *cx,
                sc0,
                (d + i) as nat,
                xty(*tx),
                fa[i],
            ) by {
                if i < j {
                    assert(fa[i] == fa0[i]);
                }
            }
            lemma_pads_closed(*b, *cx, sc0, top as nat, (d + j) as nat, dj, xty(*tx), yb@);
            assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                *b,
                *cx,
                sc0,
                (d + i) as nat,
                xty(*tx),
                fb[i],
            ) by {
                if i < j {
                    assert(fb[i] == fb0[i]);
                }
            }
        }
        j += 1;
    }
    proof {
        assert forall|i: int| 0 <= i < w implies i < (#[trigger] fa[i]).len() && i < fb[i].len() by {}
        if tq {
            assert(ys.take(w as int) =~= ys);
            lemma_lts_len(b2.outer@, b2.binds@, tv);
            assert forall|i: int| 0 <= i < out@.len() implies #[trigger] has_ty(out@[i], tv, blt(*blk, *cx), ys[i]) by {
                assert(out@[i] == Expr::Local((d + i) as usize));
                assert(blt(*blk, *cx)[d + i] == ys[i]);
            }
        }
    }
    Ok((out, Ghost(fa), Ghost(fb)))
}

/// 条件式。条件を束縛する。枝が束縛を持たなければ、スロットごとに `ite` で選ぶ。
/// 束縛を持つなら、各枝を単独に評価する式に一度だけ下ろし、スロットごとに、その位置の深さで評価できるように
/// 空の `let` で深さを合わせて束縛する（[`low_ite_slots`]）。
/// 中核の `ite` は2つの枝が同じ型でなければならないので、枝の束縛を条件で守って並べることはしない。
#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
pub(crate) fn low_ite(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Ite,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    let (p, a, b) = match e {
        TExpr::Ite(p, a, b) => (p, a, b),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost scs = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    proof {
        if pre {
            lemma_ite_tpre(*e, *cx, scs, b0.depth_s(), b0.depth_s());
        }
    }
    let c0 = sub_scalar(p, cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let c = atom(blk, c0)?;
    let ghost b2 = *blk;
    proof {
        if pre {
            lemma_sc_wf_mono(scs, b0.depth_s(), b2.depth_s(), cx.enums@);
            lemma_pure_mono(c0, b1.depth_s(), b2.depth_s());
        }
        if tp {
            lemma_added_typed(b1, b2, c0, c, *cx, ETy::Bool);
            lemma_tok_ext(*cx, scs, b0, b1);
            lemma_sc_wf_mono(scs, b0.depth_s(), b1.depth_s(), cx.enums@);
            lemma_tok_ext(*cx, scs, b1, b2);
            lemma_lts_len(b2.outer@, b2.binds@, tv);
        }
    }
    let d = depth(blk);
    proof {
        lemma_extends_trans(b0, b1, b2);
        if pre {
            lemma_ite_tpre(*e, *cx, scs, b0.depth_s(), d as nat);
        }
    }
    let mut ba = new_block(d, Ghost(blt(*blk, *cx)))?;
    let ghost ba0 = ba;
    proof {
        if tp {
            assert(blt(ba0, *cx) == blt(b2, *cx));
            assert(tok(*cx, scs, ba0));
        }
    }
    let (tx, xs) = low(a, cx, sc, &mut ba)?;
    let mut bb = new_block(d, Ghost(blt(*blk, *cx)))?;
    let ghost bb0 = bb;
    proof {
        if tp {
            assert(blt(bb0, *cx) == blt(b2, *cx));
            assert(tok(*cx, scs, bb0));
        }
    }
    let (ty, ys) = low(b, cx, sc, &mut bb)?;
    if !xtype_eq(&ty, &tx) {
        return Err(Fail::Type);
    }
    proof {
        if pre {
            assert(here_ok(**a, sctx(*cx), bound_tys(scs)));
            assert(shaped(xs@, xty(tx), ba.depth_s(), cx.enums@));
            assert(shaped(ys@, xty(ty), bb.depth_s(), cx.enums@));
            lemma_xwidth_pos(xty(tx), cx.enums@);
        }
    }
    if ba.binds.len() == 0 && bb.binds.len() == 0 {
        proof {
            assert(ba.depth_s() == d && bb.depth_s() == d);
        }
        let out = need(ite_slots(&c, &xs, &ys, d))?;
        proof {
            if pre {
                assert(pure_below(c, d as nat));
                lemma_ite_out_pure(c, xs@, ys@, out@, d as nat);
            }
            if tp {
                assert(ba.binds@ =~= Seq::<Expr>::empty());
                assert(bb.binds@ =~= Seq::<Expr>::empty());
                assert(blt(ba, *cx) == blt(b2, *cx));
                assert(blt(bb, *cx) == blt(b2, *cx));
                assert(xty(ty) == xty(tx));
                let es = xetys(xty(tx), cx.enums@);
                assert forall|i: int| 0 <= i < out@.len() implies #[trigger] has_ty(out@[i], tv, blt(b2, *cx), es[i]) by {
                    assert(out@[i] == ite_s(c, xs@[i], ys@[i]));
                    assert(has_ty(xs@[i], tv, blt(ba, *cx), es[i]));
                    assert(has_ty(ys@[i], tv, blt(bb, *cx), es[i]));
                }
            }
        }
        proof {
            lemma_extends_refl(*blk);
            lemma_ite_simple(*e, *cx, sc@, b0, b1, b2, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, out@);
        }
        return Ok((tx, out));
    }
    if xs.len() == 0 || xs.len() != ys.len() {
        return Err(Fail::Type);
    }
    let w = xs.len();
    let ghost sc0 = sc@;
    proof {
        lemma_extends_trans(b0, b1, b2);
        assert(decreases_to!(*e => **a));
        assert(decreases_to!(*e => **b));
        if pre {
            assert(tpre(**a, *cx, scs, d as nat) && tpre(**b, *cx, scs, d as nat));
            assert(ir_type_of(**a, sctx(*cx), bound_tys(scs)) == Some(xty(tx)));
            assert(w == xwidth(xty(tx), cx.enums@));
        }
        if tp {
            assert(ok_x(xty(tx), cx.enums@));
            assert(pure_below(c, b2.depth_s()));
        }
    }
    let (out, Ghost(fa), Ghost(fb)) = low_ite_slots(e, a, b, &c, &tx, w, cx, sc, blk)?;
    proof {
        lemma_extends_trans(b0, b2, *blk);
    }
    proof {
        lemma_ite_bound(*e, *cx, sc0, b0, b1, b2, *blk, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, fa, fb, out@);
        if pre {
            assert(all_pure(out@, blk.depth_s())) by {
                assert forall|i: int| 0 <= i < out@.len() implies pure_below(#[trigger] out@[i], blk.depth_s()) by {
                    assert(out@[i] == Expr::Local((d + i) as usize));
                }
            }
        }
    }
    Ok((tx, out))
}

/// 式の型 `t` の各スロットの型の既定値の定数。
pub(crate) fn xdefaults(t: &XType, enums: &Vec<i64>) -> (r: Vec<Expr>)
    ensures
        forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] is Const,
        r@.len() == xwidth(xty(*t), enums@),
        ok_x(xty(*t), enums@) ==> forall|tv: TyEnv, lt: Seq<ETy>|
            tv.enums == enums@ ==> #[trigger] typed(r@, xetys(xty(*t), enums@), tv, lt),
    decreases t, 1nat,
{
    let mut out: Vec<Expr> = Vec::new();
    match t {
        XType::Bool => {
            out.push(Expr::Const(Value::Bool(false)));
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(has_ty(out@[0], tv, lt, ETy::Bool));
                }
            }
        },
        XType::Int => {
            out.push(Expr::Const(Value::Int(0)));
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(has_ty(out@[0], tv, lt, ETy::Int));
                }
            }
        },
        XType::Enum(id) => {
            out.push(Expr::Const(Value::Enum(*id, 0)));
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && ok_x(xty(*t), enums@) implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(has_ty(out@[0], tv, lt, ETy::Enum(*id)));
                }
            }
        },
        XType::Tuple(ts) | XType::Record(_, ts) => {
            proof {
                lemma_xtys(ts@);
                assert(decreases_to!(*t => *ts));
            }
            out = xdefaults_seq(t, ts, enums);
            proof {
                assert(xetys(xty(*t), enums@) == xetys_seq(xtys(ts@), enums@));
                if ok_x(xty(*t), enums@) {
                    assert(wf_xtypes(xtys(ts@), enums@) && lim_xs(xtys(ts@), enums@));
                }
            }
        },
        XType::Option(x) => {
            out.push(Expr::Const(Value::Bool(false)));
            let rest = xdefaults(x, enums);
            let ghost o0 = out@;
            extend(&mut out, &rest);
            proof {
                assert forall|i: int| 0 <= i < out@.len() implies #[trigger] out@[i] is Const by {
                    if i > 0 {
                        assert(out@[i] == rest@[i - 1]);
                    }
                }
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && ok_x(xty(*t), enums@) implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(typed(rest@, xetys(xty(**x), enums@), tv, lt));
                    assert(typed(o0, seq![ETy::Bool], tv, lt)) by {
                        assert(has_ty(o0[0], tv, lt, ETy::Bool));
                    }
                    lemma_typed_concat(o0, seq![ETy::Bool], rest@, xetys(xty(**x), enums@), tv, lt);
                }
            }
        },
        XType::Set(e) => {
            let st = SType::Set(Box::new(copy_stype(e)));
            out = defaults(&st, enums);
            proof {
                assert(sty(st) == STy::Set(Box::new(sty(**e))));
                lemma_default_len(sty(st), enums@);
                lemma_lits_const(enc(default_val(sty(st), enums@), sty(st), enums@));
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && ok_x(xty(*t), enums@) implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    lemma_lim_small(sty(**e), enums@);
                    lemma_defaults_typed(sty(st), tv, lt);
                }
            }
        },
        XType::Map(k, v) => {
            let st = SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v)));
            out = defaults(&st, enums);
            proof {
                assert(sty(st) == STy::Map(Box::new(sty(**k)), Box::new(sty(**v))));
                lemma_default_len(sty(st), enums@);
                lemma_lits_const(enc(default_val(sty(st), enums@), sty(st), enums@));
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && ok_x(xty(*t), enums@) implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    lemma_lim_small(sty(**v), enums@);
                    lemma_defaults_typed(sty(st), tv, lt);
                }
            }
        },
        XType::List(e, max) => {
            let st = SType::List(Box::new(copy_stype(e)), *max);
            out = defaults(&st, enums);
            proof {
                assert(sty(st) == STy::List(Box::new(sty(**e)), *max));
                lemma_default_len(sty(st), enums@);
                lemma_lits_const(enc(default_val(sty(st), enums@), sty(st), enums@));
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && ok_x(xty(*t), enums@) implies #[trigger] typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    lemma_lim_small(sty(**e), enums@);
                    lemma_defaults_typed(sty(st), tv, lt);
                }
            }
        },
    }
    out
}

pub(crate) fn xdefaults_seq(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: Vec<Expr>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i] is Const,
        r@.len() == xwidth_sum(xtys(ts@), enums@),
        wf_xtypes(xtys(ts@), enums@) && lim_xs(xtys(ts@), enums@) ==> forall|tv: TyEnv, lt: Seq<ETy>|
            tv.enums == enums@ ==> #[trigger] typed(r@, xetys_seq(xtys(ts@), enums@), tv, lt),
    decreases _parent, 0nat,
{
    proof {
        lemma_xtys(ts@);
        assert(xtys(ts@).take(0) =~= Seq::<XTy>::empty());
    }
    let ghost ok = wf_xtypes(xtys(ts@), enums@) && lim_xs(xtys(ts@), enums@);
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts@.len(),
            xtys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xtys(ts@)[j] == xty(ts@[j]),
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] is Const,
            ok == (wf_xtypes(xtys(ts@), enums@) && lim_xs(xtys(ts@), enums@)),
            out@.len() == xwidth_sum(xtys(ts@).take(i as int), enums@),
            ok ==> forall|tv: TyEnv, lt: Seq<ETy>|
                tv.enums == enums@ ==> #[trigger] typed(out@, xetys_seq(xtys(ts@).take(i as int), enums@), tv, lt),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let part = xdefaults(&ts[i], enums);
        let ghost o0 = out@;
        extend(&mut out, &part);
        proof {
            assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] is Const by {
                if j < o0.len() {
                    assert(out@[j] == o0[j]);
                } else {
                    assert(out@[j] == part@[j - o0.len()]);
                }
            }
            let xt = xtys(ts@);
            assert(xt.take(i + 1).drop_last() =~= xt.take(i as int));
            assert(xt.take(i + 1).last() == xty(ts@[i as int]));
            if ok {
                crate::value::encoding::lemma_wf_xtypes_at(xt, enums@, i as int);
                lemma_lim_xs_at(xt, enums@, i as int);
                assert(ok_x(xty(ts@[i as int]), enums@));
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ implies #[trigger] typed(
                    out@,
                    xetys_seq(xt.take(i + 1), enums@),
                    tv,
                    lt,
                ) by {
                    assert(typed(o0, xetys_seq(xt.take(i as int), enums@), tv, lt));
                    assert(typed(part@, xetys(xty(ts@[i as int]), enums@), tv, lt));
                    lemma_typed_concat(o0, xetys_seq(xt.take(i as int), enums@), part@, xetys(xty(ts@[i as int]), enums@), tv, lt);
                }
            }
        }
        i += 1;
    }
    proof {
        assert(xtys(ts@).take(ts@.len() as int) =~= xtys(ts@));
    }
    out
}

/// 定数の式の列の各式は、定数である。
pub(crate) proof fn lemma_lits_const(vs: Seq<Value>)
    ensures
        forall|i: int| 0 <= i < lits(vs).len() ==> #[trigger] lits(vs)[i] is Const,
{
}

/// `ds` の `lo..hi` を束縛として `x` にかぶせる。
pub(crate) fn pad_lets(ds: &Vec<Expr>, lo: usize, hi: usize, x: Expr) -> (r: Expr)
    requires
        lo <= hi <= ds@.len(),
    ensures
        r == pad_lets_s(ds@.subrange(lo as int, hi as int), x),
    decreases hi - lo,
{
    if lo == hi {
        proof {
            assert(ds@.subrange(lo as int, hi as int) =~= Seq::<Expr>::empty());
        }
        x
    } else {
        let inner = pad_lets(ds, lo + 1, hi, x);
        proof {
            assert(ds@.subrange(lo as int, hi as int).drop_first() =~= ds@.subrange(lo + 1, hi as int));
        }
        Expr::Let(Box::new(copy_expr(&ds[lo])), Box::new(inner))
    }
}

/// 定数の束縛をかぶせた式の型は、束縛の型を局所変数の型に加えた下での型である。
pub(crate) proof fn lemma_pad_type(ds: Seq<Expr>, ys: Seq<ETy>, x: Expr, t: TyEnv, lt: Seq<ETy>)
    requires
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] ds[i] is Const,
        typed(ds, ys, t, lt),
    ensures
        type_l(pad_lets_s(ds, x), t, lt) == type_l(x, t, lt + ys),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(lt + ys =~= lt);
    } else {
        let rest = ds.drop_first();
        let yr = ys.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i] is Const by {
            assert(rest[i] == ds[i + 1]);
        }
        assert(has_ty(ds[0], t, lt, ys[0]));
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] has_ty(rest[i], t, lt.push(ys[0]), yr[i]) by {
            assert(has_ty(ds[i + 1], t, lt, ys[i + 1]));
            assert(rest[i] == ds[i + 1]);
        }
        lemma_pad_type(rest, yr, x, t, lt.push(ys[0]));
        assert(lt.push(ys[0]) + yr =~= lt + ys);
    }
}

} // verus!
