//! 演算子、`let`、`all` と `any`、`ite` の下ろしが意味を保存することの補題。
//!
//! 下ろしの実装は [`crate::lowering`] にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{models, xty, xwidth, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::equality::eq_ok;
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::infer::type_of;
#[cfg(verus_keep_ghost)]
use crate::lowering::*;
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_fold, eval_src, src_bool, SEnv, TExpr};
#[cfg(verus_keep_ghost)]
use crate::total::*;
use vstd::prelude::*;

verus! {

/// 純粋な条件とスロットから作った `ite` のスロットは純粋である。
pub proof fn lemma_ite_out_pure(c: Expr, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, n: nat)
    requires
        pure_below(c, n),
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == ite_s(c, xs[i], ys[i]),
        forall|i: int| 0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], n) && pure_below(ys[i], n),
    ensures
        all_pure(out, n),
{
    assert forall|i: int| 0 <= i < out.len() implies pure_below(#[trigger] out[i], n) by {
        assert(out[i] == ite_s(c, xs[i], ys[i]));
        assert(pure_below(xs[i], n) && pure_below(ys[i], n));
    }
}

/// 型の付く `ite` の条件と枝は、より深い位置でも前提を満たし、枝の型は `ite` の型である。
pub proof fn lemma_ite_tpre(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat, m: nat)
    requires
        e is Ite,
        tpre(e, cx, sc, n),
        n <= m,
    ensures
        tpre(*e->Ite_0, cx, sc, n),
        type_of(*e->Ite_0, sctx(cx), bound_tys(sc)) == Some(XTy::Bool),
        tpre(*e->Ite_1, cx, sc, m),
        tpre(*e->Ite_2, cx, sc, m),
        type_of(*e->Ite_1, sctx(cx), bound_tys(sc)) == type_of(e, sctx(cx), bound_tys(sc)),
        type_of(*e->Ite_2, sctx(cx), bound_tys(sc)) == type_of(e, sctx(cx), bound_tys(sc)),
{
    lemma_sc_wf_mono(sc, n, m, cx.enums@);
}

/// 空の `all` と `any` は、単位元になる。
pub proof fn lemma_fold_empty(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b: Block, out: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() == 0 && out == seq![bool_lit(all)],
    ensures
        lowers(e, cx, sc, b, b, XTy::Bool, out),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b, b), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        assert(fresh(b, b) =~= Seq::<Expr>::empty());
        assert(eval_fold(all, es@, se, sls) == Ok::<bool, ErrKind>(all));
        assert(eval_l(bool_lit(all), env, ls) == Ok::<Value, ErrKind>(Value::Bool(all)));
        lemma_one_denotes(bool_lit(all), env, ls, Value::Bool(all), XTy::Bool, se.enums);
    }
}

/// `let` の下ろし。束縛する値のスロットを局所変数の対応に加えて、本体を下ろす。
pub proof fn lemma_let(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    s0: Seq<Expr>,
    bound: Bound,
    tb: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Let(a, b) && lowers(*a, cx, sc, b0, b1, xty(bound.ty), s0) && lowers(
            *b,
            cx,
            sc.push(bound),
            b2,
            b3,
            tb,
            out,
        ),
        atoms_ok(s0, bound.slots@, b1, b2),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, tb, out),
{
    let a = e->Let_0;
    let b = e->Let_1;
    lemma_extends_trans(b1, b2, b3);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        tb,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, xty(bound.ty), s0, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b3, env, ls);
        lemma_run_fresh(b1, b2, b3, env, run(fresh(b0, b1), env, ls)->Ok_0);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(clean(s0, env, l1));
            assert(atoms_run(s0, bound.slots@, b1, b2, env, l1));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            let sc2 = sc.push(bound);
            let sls2 = sls.push(v);
            assert(denotes(bound.slots@, env, l2, v, xty(bound.ty), se.enums));
            assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(
                sc2[i].slots@,
                env,
                l2,
                sls2[i],
                xty(sc2[i].ty),
                se.enums,
            ) by {
                if i < sc.len() {
                    assert(sc2[i] == sc[i]);
                    assert(sls2[i] == sls[i]);
                }
            }
            assert(ctx_ok(cx, sc2, env, se, l2, sls2));
        }
    }
}

/// `all` と `any` の下ろし。先頭の項はスロットで、残りの項は単独に評価する式である。
pub proof fn lemma_fold(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, terms: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() >= 1 && terms.len() == es@.len() && lowers(
            es@[0],
            cx,
            sc,
            b0,
            b1,
            XTy::Bool,
            seq![terms[0]],
        ) && (forall|j: int|
            1 <= j < es@.len() ==> #[trigger] closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]))
            && b2.binds@ == b1.binds@.push(tree_s(terms, bool_lit(all), raw_join(all))),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    let joined = tree_s(terms, bool_lit(all), raw_join(all));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(es@[0], cx, sc, b0, b1, XTy::Bool, seq![terms[0]], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        match eval_src(es@[0], se, sls) {
            Err(k) => {
                lemma_fold_first_err(all, es@, se, sls, k);
            },
            Ok(v0) => {
                let l = run(fresh(b0, b1), env, ls)->Ok_0;
                lemma_denotes_one(terms[0], env, l, v0, XTy::Bool, se.enums);
                assert forall|j: int| 0 <= j < terms.len() implies #[trigger] as_bool(eval_l(terms[j], env, l)) == src_bool(
                    eval_src(es@[j], se, sls),
                ) && lift_bool(as_bool(eval_l(terms[j], env, l))) == eval_l(terms[j], env, l) by {
                    if j > 0 {
                        assert(closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]));
                        lemma_scalar_bool(eval_src(es@[j], se, sls), eval_l(terms[j], env, l), se.enums);
                    }
                }
                assert(bool_or_err(terms, env, l));
                lemma_fold_eq(all, es@, terms, se, sls, env, l);
                lemma_tree_sc(all, terms, env, l);
                lemma_run_one(b1, b2, joined, env, l);
                if let Ok(r) = eval_l(joined, env, l) {
                    lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
                }
            },
        }
    }
}

/// 条件式のスロットは、条件の真偽に応じて、片方の枝のスロットの値になる。
pub proof fn lemma_ite_slots(c: Expr, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, env: Env, l: Seq<Value>, pos: bool)
    requires
        pure_below(c, l.len()),
        eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(pos)),
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == ite_s(c, xs[j], ys[j]),
        forall|j: int| 0 <= j < xs.len() ==> pure_below(#[trigger] xs[j], l.len()) && pure_below(ys[j], l.len()),
        pos ==> clean(xs, env, l),
        !pos ==> clean(ys, env, l),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == if pos {
            slot_vals(xs, env, l)
        } else {
            slot_vals(ys, env, l)
        },
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == if pos {
        eval_l(xs[j], env, l)
    } else {
        eval_l(ys[j], env, l)
    } by {
        assert(pure_below(xs[j], l.len()));
    }
    if pos {
        assert(slot_vals(out, env, l) =~= slot_vals(xs, env, l));
    } else {
        assert(slot_vals(out, env, l) =~= slot_vals(ys, env, l));
    }
}

/// 条件式のスロットごとの束縛。`i` 番目は、条件で枝の `i` 番目のスロットを選ぶ。
pub open spec fn ite_binds(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, n: nat) -> Seq<Expr> {
    Seq::new(n, |i: int| ite_s(c, fa[i][i], fb[i][i]))
}

pub proof fn lemma_ite_binds_push(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, xa: Seq<Expr>, yb: Seq<Expr>, j: nat)
    requires
        fa.len() == j,
        fb.len() == j,
    ensures
        ite_binds(c, fa.push(xa), fb.push(yb), j + 1) =~= ite_binds(c, fa, fb, j).push(ite_s(c, xa[j as int], yb[j as int])),
{
    assert forall|i: int| 0 <= i < j implies #[trigger] fa.push(xa)[i] == fa[i] && fb.push(yb)[i] == fb[i] by {}
}

/// `k` 個の空の `let` の下で `x` を評価する。局所変数の数を `k` だけ増やす。
pub open spec fn pad_lets_s(k: nat, x: Expr) -> Expr
    decreases k,
{
    if k == 0 {
        x
    } else {
        Expr::Let(Box::new(bool_lit(true)), Box::new(pad_lets_s((k - 1) as nat, x)))
    }
}

pub open spec fn pad_lets_seq(xs: Seq<Expr>, k: nat) -> Seq<Expr> {
    xs.map_values(|x: Expr| pad_lets_s(k, x))
}

pub open spec fn trues(k: nat) -> Seq<Value> {
    Seq::new(k, |i: int| Value::Bool(true))
}

pub proof fn lemma_pad_eval(k: nat, x: Expr, env: Env, l: Seq<Value>)
    ensures
        eval_l(pad_lets_s(k, x), env, l) == eval_l(x, env, l + trues(k)),
    decreases k,
{
    if k == 0 {
        assert(l + trues(0) =~= l);
    } else {
        let inner = pad_lets_s((k - 1) as nat, x);
        assert(pad_lets_s(k, x) == Expr::Let(Box::new(bool_lit(true)), Box::new(inner)));
        assert(eval_l(bool_lit(true), env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
        lemma_pad_eval((k - 1) as nat, x, env, l.push(Value::Bool(true)));
        assert(l.push(Value::Bool(true)) + trues((k - 1) as nat) =~= l + trues(k));
    }
}

/// 深さ `n == d + k` で単独に評価する式は、空の `let` を `k` 個かぶせると、深さ `d` で単独に評価する式になる。
pub proof fn lemma_pads_closed(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat, d: nat, k: nat, t: XTy, xs: Seq<Expr>)
    requires
        n == d + k,
        closed_slots(e, cx, sc, n, t, xs),
    ensures
        closed_slots(e, cx, sc, d, t, pad_lets_seq(xs, k)),
{
    let ps = pad_lets_seq(xs, k);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == d implies slots_result(
        eval_src(e, se, sls),
        ps,
        env,
        ls,
        t,
        se.enums,
    ) by {
        let l2 = ls + trues(k);
        assert(prefix(ls, l2));
        lemma_ctx_weaken(cx, sc, env, se, ls, l2, sls);
        assert(ctx_ok(cx, sc, env, se, l2, sls) && l2.len() == n);
        assert forall|j: int| 0 <= j < ps.len() implies #[trigger] eval_l(ps[j], env, ls) == eval_l(xs[j], env, l2) by {
            lemma_pad_eval(k, xs[j], env, ls);
        }
        assert(slot_vals(ps, env, ls) =~= slot_vals(xs, env, l2));
    }
}

/// 枝が束縛を持たない条件式の下ろし。
pub proof fn lemma_ite_simple(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        ba1.binds@.len() == 0,
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        bb1.binds@.len() == 0,
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == ite_s(c, xs[i], ys[i]),
        forall|i: int|
            0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], b2.depth_s()) && pure_below(ys[i], b2.depth_s()),
    ensures
        lowers(e, cx, sc, b0, b2, t, out),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*p, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
            let bv = v->Bool_0;
            lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            assert(fresh(ba0, ba1) =~= Seq::<Expr>::empty());
            assert(fresh(bb0, bb1) =~= Seq::<Expr>::empty());
            assert(run(Seq::<Expr>::empty(), env, l2) == Ok::<Seq<Value>, ErrKind>(l2));
            if bv {
                lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
                if let Ok(va) = eval_src(*a, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, true);
                }
            } else {
                lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
                if let Ok(vb) = eval_src(*b, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, false);
                }
            }
        }
    }
}

/// スロットごとの束縛の、先頭 `k` 個の評価。
#[verifier::spinoff_prover]
pub proof fn lemma_ite_prefix(
    br: TExpr,
    f: Seq<Seq<Expr>>,
    c: Expr,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    bv: bool,
    d: nat,
    w: nat,
    k: nat,
    cx: LowerCtx,
    sc: Seq<Bound>,
    t: XTy,
    env: Env,
    se: SEnv,
    l2: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        ctx_ok(cx, sc, env, se, l2, sls),
        l2.len() == d,
        pure_below(c, d),
        eval_l(c, env, l2) == Ok::<Value, ErrKind>(Value::Bool(bv)),
        f == if bv {
            fa
        } else {
            fb
        },
        fa.len() == w,
        fb.len() == w,
        k <= w,
        forall|i: int| 0 <= i < w ==> #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]),
        forall|i: int| 0 <= i < w ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
    ensures
        match eval_src(br, se, sls) {
            Err(kk) => k > 0 ==> run(ite_binds(c, fa, fb, k), env, l2) == Err::<Seq<Value>, ErrKind>(kk),
            Ok(v) => run(ite_binds(c, fa, fb, k), env, l2) matches Ok(lk) && lk.len() == d + k && prefix(l2, lk)
                && forall|i: int|
                0 <= i < k ==> #[trigger] lk[d + i] == slot_vals(f[i], env, lk.take(d + i))[i] && models(
                    slot_vals(f[i], env, lk.take(d + i)),
                    v,
                    t,
                    se.enums,
                ),
        },
    decreases k,
{
    if k == 0 {
        assert(ite_binds(c, fa, fb, 0) =~= Seq::<Expr>::empty());
        lemma_prefix_refl(l2);
    } else {
        let j = (k - 1) as nat;
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, j, cx, sc, t, env, se, l2, sls);
        let x = ite_s(c, fa[j as int][j as int], fb[j as int][j as int]);
        assert(ite_binds(c, fa, fb, k) =~= ite_binds(c, fa, fb, j).push(x));
        lemma_run_push(ite_binds(c, fa, fb, j), x, env, l2);
        let r = run(ite_binds(c, fa, fb, j), env, l2);
        if r is Ok {
            let lj = r->Ok_0;
            lemma_run_len(ite_binds(c, fa, fb, j), env, l2);
            lemma_weaken(c, env, l2, lj);
            lemma_ctx_weaken(cx, sc, env, se, l2, lj, sls);
            assert(closed_slots(br, cx, sc, (d + j) as nat, t, f[j as int]));
            assert(ctx_ok(cx, sc, env, se, lj, sls));
            assert(j < f[j as int].len());
            let fj = f[j as int][j as int];
            assert(eval_l(c, env, lj) == Ok::<Value, ErrKind>(Value::Bool(bv)));
            assert(eval_l(x, env, lj) == eval_l(fj, env, lj));
            assert(slots_result(eval_src(br, se, sls), f[j as int], env, lj, t, se.enums));
            match eval_src(br, se, sls) {
                Ok(v) => {
                    assert(eval_l(f[j as int][j as int], env, lj) is Ok);
                    let val = eval_l(f[j as int][j as int], env, lj)->Ok_0;
                    let lk = lj.push(val);
                    assert(run(ite_binds(c, fa, fb, k), env, l2) == Ok::<Seq<Value>, ErrKind>(lk));
                    assert(slot_vals(f[j as int], env, lj)[j as int] == val);
                    assert(lk.take((d + j) as int) =~= lj);
                    assert forall|i: int| 0 <= i < k implies #[trigger] lk[d + i] == slot_vals(
                        f[i],
                        env,
                        lk.take(d + i),
                    )[i] && models(slot_vals(f[i], env, lk.take(d + i)), v, t, se.enums) by {
                        if i < j {
                            assert(lk.take((d + i) as int) =~= lj.take((d + i) as int));
                            assert(lk[d + i] == lj[d + i]);
                        }
                    }
                    lemma_prefix_trans(l2, lj, lk);
                },
                Err(_) => {},
            }
        }
    }
}

/// 枝が束縛を持つ条件式の、1つの環境での評価。
pub proof fn lemma_ite_bound_at(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        result_ok(eval_src(e, se, sls), run(fresh(b0, b3), env, ls), out, env, t, se.enums),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    let d = b2.depth_s();
    let w = xs.len();
    lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
    lemma_extends_trans(b1, b2, b3);
    lemma_run_fresh(b0, b1, b3, env, ls);
    if let Ok(v) = eval_src(*p, se, sls) {
        let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
        lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
        let bv = v->Bool_0;
        lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
        lemma_run_fresh(b1, b2, b3, env, l1);
        lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
        assert(fresh(b2, b3) =~= ite_binds(c, fa, fb, w));
        let br = if bv {
            *a
        } else {
            *b
        };
        let f = if bv {
            fa
        } else {
            fb
        };
        assert forall|i: int| 0 <= i < w implies #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]) by {
            if bv {
                assert(closed_slots(*a, cx, sc, (d + i) as nat, t, fa[i]));
            } else {
                assert(closed_slots(*b, cx, sc, (d + i) as nat, t, fb[i]));
            }
        }
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, w, cx, sc, t, env, se, l2, sls);
        if bv {
            lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
        } else {
            lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
        }
        if let Ok(vv) = eval_src(br, se, sls) {
            let lw = run(ite_binds(c, fa, fb, w), env, l2)->Ok_0;
            if bv {
                let la = run(fresh(ba0, ba1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(xs, env, la), vv, t, se.enums);
            } else {
                let lb = run(fresh(bb0, bb1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(ys, env, lb), vv, t, se.enums);
            }
            assert(b3.wf());
            lemma_ite_out(f, out, d, w, vv, t, env, lw, se.enums);
        }
    }
}

/// スロットごとの束縛を評価し終えたときの、条件式のスロットの値。
pub proof fn lemma_ite_out(
    f: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    d: nat,
    w: nat,
    vv: SVal,
    t: XTy,
    env: Env,
    lw: Seq<Value>,
    enums: Seq<i64>,
)
    requires
        w > 0,
        w == xwidth(t, enums),
        lw.len() == d + w,
        d + w < usize::MAX,
        out == Seq::new(w, |i: int| Expr::Local((d + i) as usize)),
        forall|i: int|
            0 <= i < w ==> #[trigger] lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i] && models(
                slot_vals(f[i], env, lw.take(d + i)),
                vv,
                t,
                enums,
            ),
    ensures
        denotes(out, env, lw, vv, t, enums),
{
    let vs = Seq::new(w, |i: int| slot_vals(f[i], env, lw.take(d + i)));
    let r = slot_vals(out, env, lw);
    assert forall|i: int| 0 <= i < w implies #[trigger] models(vs[i], vv, t, enums) && vs[i].len() == w by {
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
        lemma_models_len(vs[i], vv, t, enums);
    }
    assert forall|i: int| 0 <= i < w implies #[trigger] r[i] == vs[i][i] by {
        assert(out[i] == Expr::Local((d + i) as usize));
        assert(((d + i) as usize) as int == d + i);
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
    }
    lemma_models_diag(vs, r, vv, t, enums);
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], lw.len()) && eval_l(
        out[j],
        env,
        lw,
    ) is Ok by {
        assert(out[j] == Expr::Local((d + j) as usize));
    }
}

/// 枝が束縛を持つ条件式の下ろし。
pub proof fn lemma_ite_bound(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_ite_bound_at(e, cx, sc, b0, b1, b2, b3, c0, c, ba0, ba1, bb0, bb1, t, xs, ys, fa, fb, out, env, se, ls, sls);
    }
}

/// 整数の演算と比較の下ろし。算術は束縛し、比較はそのままスロットにする。
pub proof fn lemma_bin(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    x: Expr,
    y: Expr,
    t: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Bin(op, a, b) && lowers(*a, cx, sc, b0, b1, XTy::Int, seq![x]) && lowers(
            *b,
            cx,
            sc,
            b1,
            b2,
            XTy::Int,
            seq![y],
        ) && if op is Add || op is Sub || op is Mul || op is Div || op is Mod {
            t == XTy::Int && b3.binds@ == b2.binds@.push(Expr::Bin(op, Box::new(x), Box::new(y))) && out == seq![
                Expr::Local(b2.depth_s() as usize),
            ]
        } else {
            (op is Lt || op is Le || op is Gt || op is Ge) && t == XTy::Bool && b3 == b2 && out == seq![
                Expr::Bin(op, Box::new(x), Box::new(y)),
            ]
        },
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    let op = e->Bin_0;
    let a = e->Bin_1;
    let b = e->Bin_2;
    let z = Expr::Bin(op, Box::new(x), Box::new(y));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_pair(*a, *b, cx, sc, b0, b1, b2, XTy::Int, seq![x], XTy::Int, seq![y], env, se, ls, sls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(va) = eval_src(*a, se, sls) {
            if let Ok(vb) = eval_src(*b, se, sls) {
                let l = run(fresh(b0, b2), env, ls)->Ok_0;
                lemma_denotes_one(x, env, l, va, XTy::Int, se.enums);
                lemma_denotes_one(y, env, l, vb, XTy::Int, se.enums);
                if t == XTy::Bool {
                    lemma_fresh_refl(b2);
                    assert(fresh(b2, b3) =~= Seq::<Expr>::empty());
                    lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
                } else {
                    lemma_run_one(b2, b3, z, env, l);
                    if let Ok(r) = eval_l(z, env, l) {
                        lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Int, se.enums);
                    }
                }
            }
        }
    }
}

/// 否定の下ろし。
pub proof fn lemma_not(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, x: Expr)
    requires
        e matches TExpr::Not(a) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![x]),
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, seq![Expr::Not(Box::new(x))]),
{
    let a = e->Not_0;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        seq![Expr::Not(Box::new(x))],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![x], env, se, ls, sls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(x, env, l, v, XTy::Bool, se.enums);
            let z = Expr::Not(Box::new(x));
            lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
        }
    }
}

/// 含意の下ろし。前件はスロットにし、後件は単独に評価する式にして、全体を束縛する。
pub proof fn lemma_implies(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, p: Expr, q: Expr)
    requires
        e matches TExpr::Implies(a, b) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![p]) && closed_lowers(
            *b,
            cx,
            sc,
            b1.depth_s(),
            XTy::Bool,
            q,
        ),
        extends(b0, b1),
        extends(b1, b2),
        b2.binds@ == b1.binds@.push(Expr::Implies(Box::new(p), Box::new(q))),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let a = e->Implies_0;
    let b = e->Implies_1;
    let z = Expr::Implies(Box::new(p), Box::new(q));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![p], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(p, env, l, v, XTy::Bool, se.enums);
            lemma_run_one(b1, b2, z, env, l);
            assert(ctx_ok(cx, sc, env, se, l, sls));
            if let Ok(r) = eval_l(z, env, l) {
                lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
            }
        }
    }
}

/// 等しさの下ろし。
#[verifier::spinoff_prover]
pub proof fn lemma_eq(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    x: Seq<Expr>,
    y: Seq<Expr>,
    c: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Eq(positive, a, b) && lowers(*a, cx, sc, b0, b1, t, x) && lowers(*b, cx, sc, b1, b2, t, y)
            && out == seq![if positive { c } else { Expr::Not(Box::new(c)) }],
        extends(b0, b1),
        extends(b1, b2),
        eq_ok(t, x, y, c, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let positive = e->Eq_0;
    let a = e->Eq_1;
    let b = e->Eq_2;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_pair(*a, *b, cx, sc, b0, b1, b2, t, x, t, y, env, se, ls, sls);
        if let Ok(va) = eval_src(*a, se, sls) {
            if let Ok(vb) = eval_src(*b, se, sls) {
                let l = run(fresh(b0, b2), env, ls)->Ok_0;
                lemma_clean_pure(x, env, l);
                lemma_clean_pure(y, env, l);
                assert(pure_below(c, l.len()));
                assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(va == vb)));
                lemma_one_denotes(out[0], env, l, Value::Bool((va == vb) == positive), XTy::Bool, se.enums);
            }
        }
    }
}

} // verus!
