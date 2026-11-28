//! 要素とキーの下ろし（`elem_lowers`、`elem_rank_lowers`）が意味を保存することの補題。SetとMapとListが共有する。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::kernel::model::{Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{bool_lit, ite_s, pure_below};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{added, extends, Block, Bound, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{atoms_ok, atoms_run, clean, ctx_ok, fresh, lemma_added, lemma_clean_pure};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{lemma_clean_weaken, lemma_ctx_weaken, lemma_denotes_weaken};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{lemma_extends_trans, lemma_fresh_refl, lemma_one, lemma_prefix_trans};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{lemma_run_fresh, lemma_run_fresh_ok, lemma_run_len, lemma_run_one, lowers};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{prefix, run, slot_vals};
#[cfg(verus_keep_ghost)]
use crate::slot::slot_store::{rank_spec, store_ok, store_spec};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{enc, keys, member, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::value::fits::fits_s;
#[cfg(verus_keep_ghost)]
use crate::value::keys::rank;
#[cfg(verus_keep_ghost)]
use crate::value::source::{eval_src, SEnv, TExpr, FAIL_NOT_IN_DOMAIN};
use vstd::prelude::*;

verus! {

/// 要素の下ろしの正しさ。値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
pub open spec fn elem_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, xs: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(e, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => if member(v, st, se.enums) {
                run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                    cx,
                    sc,
                    env,
                    se,
                    l,
                    sls,
                ) && clean(xs, env, l) && slot_vals(xs, env, l) == enc(v, st, se.enums)
            } else {
                run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
            },
        }
}

#[verifier::spinoff_prover]
pub proof fn lemma_element(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    t: XTy,
    slots: Seq<Expr>,
    st: STy,
    cond: Expr,
    out: Seq<Expr>,
    xs: Seq<Expr>,
)
    requires
        lowers(e, cx, sc, b0, b1, t, slots),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        fits_s(t, st),
        store_spec(t, slots, st, cx.enums@, cond, out),
        (cond == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN)),
        ),
        atoms_ok(out, xs, b2, b3),
    ensures
        elem_lowers(e, cx, sc, b0, b3, st, xs),
{
    let c = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN));
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(e, se, sls) {
        Err(k) => run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => if member(v, st, se.enums) {
            run(fresh(b0, b3), env, ls) matches Ok(l) && l.len() == b3.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && clean(xs, env, l) && slot_vals(xs, env, l) == enc(v, st, se.enums)
        } else {
            run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
        },
    } by {
        let enums = se.enums;
        lemma_one(e, cx, sc, b0, b1, t, slots, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(v) = eval_src(e, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(store_ok(cond, out, env, l1, v, st, enums));
            let m = member(v, st, enums);
            assert(eval_l(bool_lit(true), env, l1) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN), env, l1) == Err::<Value, ErrKind>(
                ErrKind::Failed(FAIL_NOT_IN_DOMAIN),
            ));
            let l2 = if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l1) == Ok::<Seq<Value>, ErrKind>(l1));
                assert(m);
                l1
            } else {
                lemma_run_one(b1, b2, c, env, l1);
                l1.push(Value::Bool(true))
            };
            if m {
                assert(run(fresh(b1, b2), env, l1) == Ok::<Seq<Value>, ErrKind>(l2));
                assert(prefix(l1, l2));
                lemma_run_len(fresh(b0, b1), env, ls);
                lemma_run_fresh_ok(b0, b2, env, ls);
                lemma_clean_weaken(out, env, l1, l2);
                assert(atoms_run(out, xs, b2, b3, env, l2));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_prefix_trans(ls, l2, l3);
                lemma_ctx_weaken(cx, sc, env, se, ls, l3, sls);
            }
        }
    }
}

pub proof fn lemma_elem_rank(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    t: XTy,
    slots: Seq<Expr>,
    st: STy,
    cond: Expr,
    out: Seq<Expr>,
    r: Expr,
    x: Expr,
)
    requires
        lowers(e, cx, sc, b0, b1, t, slots),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        fits_s(t, st),
        keys(st, cx.enums@) is Some,
        store_spec(t, slots, st, cx.enums@, cond, out),
        (cond == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN)),
        ),
        rank_spec(t, slots, st, cx.enums@, r),
        added(b2, b3, r, x),
    ensures
        elem_rank_lowers(e, cx, sc, b0, b3, st, x),
{
    let c = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN));
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(e, se, sls) {
        Err(k) => run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => if member(v, st, se.enums) {
            run(fresh(b0, b3), env, ls) matches Ok(l) && l.len() == b3.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && pure_below(x, l.len()) && eval_l(x, env, l) == Ok::<Value, ErrKind>(
                Value::Int(rank(v, st, se.enums) as i64),
            )
        } else {
            run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
        },
    } by {
        let enums = se.enums;
        lemma_one(e, cx, sc, b0, b1, t, slots, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(v) = eval_src(e, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(store_ok(cond, out, env, l1, v, st, enums));
            let m = member(v, st, enums);
            assert(eval_l(bool_lit(true), env, l1) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN), env, l1) == Err::<Value, ErrKind>(
                ErrKind::Failed(FAIL_NOT_IN_DOMAIN),
            ));
            let l2 = if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l1) == Ok::<Seq<Value>, ErrKind>(l1));
                assert(m);
                l1
            } else {
                lemma_run_one(b1, b2, c, env, l1);
                l1.push(Value::Bool(true))
            };
            if m {
                assert(run(fresh(b1, b2), env, l1) == Ok::<Seq<Value>, ErrKind>(l2));
                assert(prefix(l1, l2));
                lemma_denotes_weaken(slots, env, l1, l2, v, t, enums);
                lemma_clean_pure(slots, env, l2);
                assert(pure_below(r, l2.len()));
                lemma_run_len(fresh(b0, b1), env, ls);
                lemma_run_fresh_ok(b0, b2, env, ls);
                lemma_added(b2, b3, r, x, env, l2, Value::Int(rank(v, st, enums) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_prefix_trans(ls, l2, l3);
                lemma_ctx_weaken(cx, sc, env, se, ls, l3, sls);
            }
        }
    }
}

/// 要素の番号の下ろしの正しさ。値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
pub open spec fn elem_rank_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, x: Expr) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(e, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => if member(v, st, se.enums) {
                run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                    cx,
                    sc,
                    env,
                    se,
                    l,
                    sls,
                ) && pure_below(x, l.len()) && eval_l(x, env, l) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, st, se.enums) as i64),
                )
            } else {
                run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
            },
        }
}

} // verus!
