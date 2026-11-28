//! Tuple、Record、Optionの下ろしが意味を保存することの補題。
//!
//! 下ろしの実装は [`crate::lowering`] にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, lemma_default_len, lemma_xwidth_of, models_seq, STy, sty};
#[cfg(verus_keep_ghost)]
use crate::encoding::{SVal, to_xty, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{Env, ErrKind, eval_l};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{bool_lit, ite_s, lits, pure_below, split_ok};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{Block, Bound, extends, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_seq, eval_src, FAIL_NONE, SEnv, TExpr};
use vstd::prelude::*;

verus! {

/// 式の列を順に下ろすと、`b0` から `b1` までの束縛とスロットの列 `out` になり、値の列を表す。
pub open spec fn lowers_seq(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, out: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_seq(es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(vs) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && clean(out, env, l) && models_seq(slot_vals(out, env, l), vs, ts, se.enums),
        }
}

pub proof fn lemma_seq_base(cx: LowerCtx, sc: Seq<Bound>, b: Block)
    ensures
        lowers_seq(Seq::empty(), cx, sc, b, b, Seq::empty(), Seq::empty()),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_seq(Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(vs) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && clean(Seq::empty(), env, l) && models_seq(slot_vals(Seq::empty(), env, l), vs, Seq::empty(), se.enums),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        assert(slot_vals(Seq::empty(), env, ls) =~= Seq::<Value>::empty());
    }
}

/// 列の最後の式を下ろして、スロットの列の後ろに加える。
pub proof fn lemma_seq_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    ts: Seq<XTy>,
    out: Seq<Expr>,
    t: XTy,
    s: Seq<Expr>,
)
    requires
        es.len() > 0,
        lowers_seq(es.drop_last(), cx, sc, b0, b1, ts, out),
        lowers(es.last(), cx, sc, b1, b2, t, s),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers_seq(es, cx, sc, b0, b2, ts.push(t), out + s),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_seq(es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(vs) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && clean(out + s, env, l) && models_seq(slot_vals(out + s, env, l), vs, ts.push(t), se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(vs) = eval_seq(es.drop_last(), se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_one(es.last(), cx, sc, b1, b2, t, s, env, se, l1, sls);
            if let Ok(v) = eval_src(es.last(), se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_clean_weaken(out, env, l1, l2);
                lemma_clean_concat(out, s, env, l2);
                let a = slot_vals(out, env, l2);
                let c = slot_vals(s, env, l2);
                lemma_models_len(c, v, t, se.enums);
                let ts2 = ts.push(t);
                assert(ts2.drop_last() =~= ts);
                assert((a + c).take(a.len() as int) =~= a);
                assert((a + c).skip(a.len() as int) =~= c);
                assert(vs.push(v).drop_last() =~= vs);
                lemma_models_seq_len(a, vs, ts, se.enums);
            }
        }
    }
}

/// 組と構造体の下ろし。
pub proof fn lemma_tuple_done(e: TExpr, es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, out: Seq<Expr>)
    requires
        (e is Tuple && e->Tuple_0@ == es) || (e is Record && e->Record_1@ == es),
        lowers_seq(es, cx, sc, b0, b1, ts, out),
    ensures
        e is Tuple ==> lowers(e, cx, sc, b0, b1, XTy::Tuple(ts), out),
        e is Record ==> lowers(e, cx, sc, b0, b1, XTy::Record(e->Record_0@, ts), out),
{
}

/// 組の要素と構造体のフィールドの下ろし。
pub proof fn lemma_part(e: TExpr, a: TExpr, i: usize, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, slots: Seq<Expr>, x: Seq<Expr>)
    requires
        (e == TExpr::Nth(Box::new(a), i) && lowers(a, cx, sc, b0, b1, XTy::Tuple(ts), slots)) || (exists|nm: usize, names: Seq<usize>|
            e == TExpr::Field(Box::new(a), nm, i) && lowers(a, cx, sc, b0, b1, XTy::Record(names, ts), slots)),
        extends(b0, b1),
        i < ts.len(),
        split_ok(x, slots, ts, i as int, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b1, ts[i as int], x),
{
    let xt = if e is Nth {
        XTy::Tuple(ts)
    } else {
        let (nm, names) = choose|nm: usize, names: Seq<usize>| e == TExpr::Field(Box::new(a), nm, i) && lowers(a, cx, sc, b0, b1, XTy::Record(names, ts), slots);
        XTy::Record(names, ts)
    };
    assert(lowers(a, cx, sc, b0, b1, xt, slots));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        x,
        env,
        ts[i as int],
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, xt, slots, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_part(slots, env, l, v->Tuple_0, ts, i as int, se.enums);
        }
    }
}

/// 空のOptionの下ろし。
pub proof fn lemma_none(e: TExpr, st: STy, cx: LowerCtx, sc: Seq<Bound>, b: Block, out: Seq<Expr>)
    requires
        e is None && sty(e->None_0) == st,
        out == seq![bool_lit(false)] + lits(enc(default_val(st, cx.enums@), st, cx.enums@)),
    ensures
        lowers(e, cx, sc, b, b, XTy::Option(Box::new(to_xty(st))), out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b, b), env, ls),
        out,
        env,
        XTy::Option(Box::new(to_xty(st))),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        let dv = enc(default_val(st, enums), st, enums);
        lemma_lits(dv, env, ls);
        lemma_lits(seq![Value::Bool(false)], env, ls);
        assert(lits(seq![Value::Bool(false)]) =~= seq![bool_lit(false)]);
        lemma_clean_concat(seq![bool_lit(false)], lits(dv), env, ls);
        lemma_default_len(st, enums);
        lemma_xwidth_of(st, enums);
    }
}

/// 値のあるOptionの下ろし。
pub proof fn lemma_some(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, t: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        e == TExpr::Some(Box::new(a)),
        lowers(a, cx, sc, b0, b1, t, s),
        extends(b0, b1),
        out == seq![bool_lit(true)] + s,
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Option(Box::new(t)), out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        XTy::Option(Box::new(t)),
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, t, s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_lits(seq![Value::Bool(true)], env, l);
            assert(lits(seq![Value::Bool(true)]) =~= seq![bool_lit(true)]);
            lemma_clean_concat(seq![bool_lit(true)], s, env, l);
            lemma_models_len(slot_vals(s, env, l), v, t, se.enums);
            assert(slot_vals(out, env, l).drop_first() =~= slot_vals(s, env, l));
        }
    }
}

/// Optionの有無の下ろし。
pub proof fn lemma_is_some(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, t: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        (e == TExpr::IsSome(Box::new(a)) && out == seq![s[0]]) || (e == TExpr::IsNone(Box::new(a)) && out == seq![Expr::Not(Box::new(s[0]))]),
        lowers(a, cx, sc, b0, b1, t, s),
        t is Option,
        s.len() > 0,
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, t, s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let sv = slot_vals(s, env, l);
            assert(sv[0] == eval_l(s[0], env, l)->Ok_0);
            assert(pure_below(s[0], l.len()) && eval_l(s[0], env, l) is Ok);
            let b = v is Some;
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(b)));
            lemma_one_denotes(out[0], env, l, eval_l(out[0], env, l)->Ok_0, XTy::Bool, se.enums);
            assert(seq![out[0]] =~= out);
        }
    }
}

/// Optionの中身の取り出しの下ろし。空なら検査の束縛が失敗する。
pub proof fn lemma_unwrap(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, x: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        e == TExpr::Unwrap(Box::new(a)),
        lowers(a, cx, sc, b0, b1, XTy::Option(Box::new(x)), s),
        extends(b0, b1),
        extends(b1, b2),
        s.len() > 0,
        (s[0] == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(s[0], bool_lit(true), Expr::Fail(Type::Bool, FAIL_NONE)),
        ),
        out == s.subrange(1, s.len() as int),
    ensures
        lowers(e, cx, sc, b0, b2, x, out),
{
    let c = ite_s(s[0], bool_lit(true), Expr::Fail(Type::Bool, FAIL_NONE));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        x,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, XTy::Option(Box::new(x)), s, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let sv = slot_vals(s, env, l);
            assert(sv[0] == eval_l(s[0], env, l)->Ok_0);
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(v is Some)));
            lemma_clean_sub(s, env, l, 1, s.len() as int);
            assert(slot_vals(out, env, l) =~= sv.drop_first());
            assert(eval_l(bool_lit(true), env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NONE), env, l) == Err::<Value, ErrKind>(ErrKind::Failed(FAIL_NONE)));
            if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l) == Ok::<Seq<Value>, ErrKind>(l));
                assert(v is Some);
            } else {
                lemma_run_one(b1, b2, c, env, l);
                if v is Some {
                    assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
                    let l2 = l.push(Value::Bool(true));
                    assert(prefix(l, l2));
                    lemma_clean_weaken(out, env, l, l2);
                } else {
                    assert(eval_l(c, env, l) == Err::<Value, ErrKind>(ErrKind::Failed(FAIL_NONE)));
                }
            }
        }
    }
}

} // verus!
