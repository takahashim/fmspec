//! Setの演算と、SetとMapの大きさの下ろしが意味を保存することの補題。
//!
//! 下ろしの実装は [`crate::lowering`] にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, enc_rows, keys, keys_or_zero, member, sty, width, STy, SType, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, rank};
#[cfg(verus_keep_ghost)]
use crate::lowering::*;
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_map::*;
#[cfg(verus_keep_ghost)]
use crate::quant::{at_rank, lemma_bin_const, picks, vals_at};
#[cfg(verus_keep_ghost)]
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{count_some, count_true, eval_set_items, eval_src, SEnv, SetOp, TExpr};
use vstd::prelude::*;

verus! {

/// Setのリテラルの要素を順に下ろすと、`bits` は印の列を表す。
pub open spec fn setlit_ok(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, bits: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_set_items(st, es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(p) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && keys(st, se.enums) == Some(p.len()) && clean(bits, env, l) && slot_vals(bits, env, l) == Seq::new(
                p.len(),
                |j: int| Value::Bool(p[j]),
            ),
        }
}

pub proof fn lemma_setlit_base(cx: LowerCtx, sc: Seq<Bound>, b: Block, st: STy, bits: Seq<Expr>)
    requires
        keys(st, cx.enums@) is Some,
        bits == Seq::new(keys_or_zero(st, cx.enums@), |_j: int| bool_lit(false)),
    ensures
        setlit_ok(Seq::empty(), cx, sc, b, b, st, bits),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_set_items(st, Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(p) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && keys(st, se.enums) == Some(p.len()) && clean(bits, env, l) && slot_vals(bits, env, l) == Seq::new(
            p.len(),
            |j: int| Value::Bool(p[j]),
        ),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        let p = Seq::new(keys_or_zero(st, se.enums), |_i: int| false);
        assert forall|j: int| 0 <= j < bits.len() implies pure_below(#[trigger] bits[j], ls.len()) && eval_l(bits[j], env, ls) is Ok by {
            assert(bits[j] == bool_lit(false));
        }
        assert forall|j: int| 0 <= j < bits.len() implies #[trigger] slot_vals(bits, env, ls)[j] == Value::Bool(p[j]) by {
            assert(bits[j] == bool_lit(false));
        }
        assert(slot_vals(bits, env, ls) =~= Seq::new(p.len(), |j: int| Value::Bool(p[j])));
    }
}

/// Setのリテラルに要素を1つ加える。
pub proof fn lemma_setlit_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        es.len() > 0,
        setlit_ok(es.drop_last(), cx, sc, b0, b1, st, bits),
        elem_rank_lowers(es.last(), cx, sc, b1, b2, st, r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(true, bits[k], r, k as i64),
    ensures
        setlit_ok(es, cx, sc, b0, b2, st, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_set_items(st, es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(p) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && keys(st, se.enums) == Some(p.len()) && clean(out, env, l) && slot_vals(out, env, l) == Seq::new(
            p.len(),
            |j: int| Value::Bool(p[j]),
        ),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(p) = eval_set_items(st, es.drop_last(), se, sls) {
            let enums = se.enums;
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(v) = eval_src(es.last(), se, sls) {
                if member(v, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_run_fresh_ok(b1, b2, env, l1);
                    lemma_prefix_trans(ls, l1, l2);
                    lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
                    lemma_clean_weaken(bits, env, l1, l2);
                    let i = rank(v, st, enums);
                    lemma_rank_in_domain(v, st, enums);
                    lemma_mark(true, bits, r, out, p, i as i64, env, l2);
                    assert(Seq::new(p.len(), |j: int| Value::Bool(p[j] || i as i64 == j)) =~= Seq::new(
                        p.update(i, true).len(),
                        |j: int| Value::Bool(p.update(i, true)[j]),
                    ));
                }
            }
        }
    }
}

/// Setに要素が含まれるかの下ろし。番号が負なら、印を評価せずに偽になる。
#[verifier::spinoff_prover]
pub proof fn lemma_set_contains(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    cs: Seq<Expr>,
    r: Expr,
    hit: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::SetContains(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        cs.len() <= 0x7fff_ffff,
        picks(hit, cs, r),
        out == seq![and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let st = sty(t);
    let g = Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0))));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), cs, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(rank_result(eval_src(x, se, sls), run(fresh(b1, b2), env, l1), r, env, st, enums));
            if let Ok(y) = eval_src(x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                let bits = sv->Set_0;
                assert(slot_vals(cs, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                lemma_clean_weaken(cs, env, l1, l2);
                let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
                assert forall|j: int| 0 <= j < cs.len() implies pure_below(#[trigger] cs[j], l2.len()) && eval_l(cs[j], env, l2)
                    == Ok::<Value, ErrKind>(vals[j]) by {
                    assert(slot_vals(cs, env, l2)[j] == eval_l(cs[j], env, l2)->Ok_0);
                }
                assert(vals_at(cs, vals, env, l2));
                let m = member(y, st, enums);
                let i: i64 = if m { rank(y, st, enums) as i64 } else { -1i64 };
                assert(at_rank(r, env, l2, i));
                lemma_bin_const(BinOp::Ge, r, 0, env, l2, i);
                assert(all_pure(cs, l2.len()));
                assert(pure_below(hit, l2.len()));
                if m {
                    lemma_rank_in_domain(y, st, enums);
                    assert(eval_l(hit, env, l2) == Ok::<Value, ErrKind>(Value::Bool(bits[i as int])));
                    lemma_and(g, hit, env, l2, true, bits[i as int]);
                } else {
                    if hit == bool_lit(true) {
                        assert(and_s(g, hit) == g);
                    } else {
                        assert(and_s(g, hit) == Expr::And(Box::new(g), Box::new(hit)));
                    }
                }
                let z = and_s(g, hit);
                assert(pure_below(z, l2.len()));
                lemma_one_denotes(z, env, l2, eval_l(z, env, l2)->Ok_0, XTy::Bool, enums);
            }
        }
    }
}

/// Setに要素を加える下ろし。要素が型に属さなければ失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_insert(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Insert(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), bits),
        elem_rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(true, bits[k], r, k as i64),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Set(Box::new(sty(t))), out),
{
    let st = sty(t);
    let xt = XTy::Set(Box::new(st));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, xt, bits, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            if let Ok(y) = eval_src(x, se, sls) {
                if member(y, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_run_fresh_ok(b1, b2, env, l1);
                    let p = sv->Set_0;
                    assert(slot_vals(bits, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                    lemma_clean_weaken(bits, env, l1, l2);
                    let i = rank(y, st, enums);
                    lemma_rank_in_domain(y, st, enums);
                    lemma_mark(true, bits, r, out, p, i as i64, env, l2);
                    let q = p.update(i, true);
                    assert(slot_vals(out, env, l2) =~= Seq::new(q.len(), |j: int| Value::Bool(q[j])));
                }
            }
        }
    }
}

/// Setから要素を除く下ろし。要素が型に属さなければ、番号は -1 でSetは変わらない。
#[verifier::spinoff_prover]
pub proof fn lemma_remove(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Remove(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), bits),
        rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(false, bits[k], r, k as i64),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Set(Box::new(sty(t))), out),
{
    let st = sty(t);
    let xt = XTy::Set(Box::new(st));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, xt, bits, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(rank_result(eval_src(x, se, sls), run(fresh(b1, b2), env, l1), r, env, st, enums));
            if let Ok(y) = eval_src(x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                let p = sv->Set_0;
                assert(slot_vals(bits, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                lemma_clean_weaken(bits, env, l1, l2);
                let m = member(y, st, enums);
                let i: i64 = if m { rank(y, st, enums) as i64 } else { -1i64 };
                lemma_mark(false, bits, r, out, p, i, env, l2);
                let q = if m { p.update(i as int, false) } else { p };
                if m {
                    lemma_rank_in_domain(y, st, enums);
                }
                assert(slot_vals(out, env, l2) =~= Seq::new(q.len(), |j: int| Value::Bool(q[j])));
            }
        }
    }
}

/// Setの要素の有無か、Mapの行の有無。
pub open spec fn size_bits(v: SVal) -> Seq<bool> {
    match v {
        SVal::Set(bits) => bits,
        SVal::Map(rows) => Seq::new(rows.len(), |i: int| rows[i] is Some),
        _ => Seq::empty(),
    }
}

/// `fs` は、SetかMapの式 `a` の要素の有無を表すBoolの式の列である。
pub open spec fn flags_ok(a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, fs: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
                && vals_at(fs, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
        }
}

pub proof fn lemma_count_add(a: Seq<bool>, b: Seq<bool>)
    ensures
        count_true(a + b) == count_true(a) + count_true(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_count_add(a, b.drop_last());
    }
}

pub proof fn lemma_count_le(a: Seq<bool>)
    ensures
        count_true(a) <= a.len(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_count_le(a.drop_last());
    }
}

pub proof fn lemma_count_pos(a: Seq<bool>, j: int)
    requires
        0 <= j < a.len(),
        a[j],
    ensures
        count_true(a) > 0,
    decreases a.len(),
{
    if j < a.len() - 1 {
        assert(a.drop_last()[j] == a[j]);
        lemma_count_pos(a.drop_last(), j);
    }
}

pub proof fn lemma_count_none(a: Seq<bool>)
    requires
        forall|j: int| 0 <= j < a.len() ==> !#[trigger] a[j],
    ensures
        count_true(a) == 0,
    decreases a.len(),
{
    if a.len() > 0 {
        assert forall|j: int| 0 <= j < a.len() - 1 implies !#[trigger] a.drop_last()[j] by {
            assert(a.drop_last()[j] == a[j]);
        }
        lemma_count_none(a.drop_last());
    }
}

pub proof fn lemma_count_some(rows: Seq<Option<SVal>>)
    ensures
        count_some(rows) == count_true(Seq::new(rows.len(), |i: int| rows[i] is Some)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let b = Seq::new(rows.len(), |i: int| rows[i] is Some);
        assert(b.drop_last() =~= Seq::new(rows.drop_last().len(), |i: int| rows.drop_last()[i] is Some));
        lemma_count_some(rows.drop_last());
    }
}

/// 有無を0と1にした式の和は、真の数である。
pub proof fn lemma_sum_codes(codes: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        codes.len() == bits.len(),
        bits.len() <= 0x7fff_ffff,
        forall|j: int| 0 <= j < codes.len() ==> pure_below(#[trigger] codes[j], l.len()) && eval_l(codes[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if bits[j] { 1 } else { 0 })),
    ensures
        pure_below(tree_s(codes, int_lit(0), Join::Add), l.len()),
        eval_l(tree_s(codes, int_lit(0), Join::Add), env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(bits) as i64)),
    decreases codes.len(),
{
    if codes.len() > 1 {
        let m = codes.len() / 2;
        let lc = codes.take(m as int);
        let rc = codes.skip(m as int);
        let lb = bits.take(m as int);
        let rb = bits.skip(m as int);
        assert forall|j: int| 0 <= j < lc.len() implies pure_below(#[trigger] lc[j], l.len()) && eval_l(lc[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if lb[j] { 1 } else { 0 })) by {
            assert(lc[j] == codes[j] && lb[j] == bits[j]);
        }
        assert forall|j: int| 0 <= j < rc.len() implies pure_below(#[trigger] rc[j], l.len()) && eval_l(rc[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if rb[j] { 1 } else { 0 })) by {
            assert(rc[j] == codes[j + m] && rb[j] == bits[j + m]);
        }
        lemma_sum_codes(lc, lb, env, l);
        lemma_sum_codes(rc, rb, env, l);
        assert(bits =~= lb + rb);
        lemma_count_add(lb, rb);
        lemma_count_le(lb);
        lemma_count_le(rb);
        let x = tree_s(lc, int_lit(0), Join::Add);
        let y = tree_s(rc, int_lit(0), Join::Add);
        assert(tree_s(codes, int_lit(0), Join::Add) == Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)));
        assert(binop_spec(BinOp::Add, Value::Int(count_true(lb) as i64), Value::Int(count_true(rb) as i64))
            == Ok::<Value, ErrKind>(Value::Int(count_true(bits) as i64)));
        assert(eval_l(x, env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(lb) as i64)));
        assert(eval_l(y, env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(rb) as i64)));
    } else if codes.len() == 1 {
        assert(bits.drop_last() =~= Seq::<bool>::empty());
        assert(tree_s(codes, int_lit(0), Join::Add) == codes[0]);
        assert(count_true(bits.drop_last()) == 0);
        assert(bits.last() == bits[0]);
    } else {
        assert(count_true(bits) == 0);
    }
}

/// Setのスロットは要素の有無である。
pub proof fn lemma_flags_set(a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, s: Seq<Expr>)
    requires
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), s),
        extends(b0, b1),
    ensures
        flags_ok(a, cx, sc, b0, b1, s),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(a, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
            && vals_at(s, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
    } by {
        lemma_one(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = v->Set_0;
            assert(slot_vals(s, env, l) == enc(v, STy::Set(Box::new(st)), se.enums));
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], l.len()) && eval_l(s[j], env, l)
                == Ok::<Value, ErrKind>(vals[j]) by {
                assert(slot_vals(s, env, l)[j] == eval_l(s[j], env, l)->Ok_0);
            }
        }
    }
}

/// Mapのスロットの、各行の先頭は行の有無である。
#[verifier::spinoff_prover]
pub proof fn lemma_flags_map(
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sk: STy,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    n: nat,
)
    requires
        lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), cs),
        extends(b0, b1),
        keys(sk, cx.enums@) == Some(n),
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
    ensures
        flags_ok(a, cx, sc, b0, b1, fs),
{
    let xt = XTy::Map(Box::new(sk), Box::new(sv));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(a, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
            && vals_at(fs, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
    } by {
        lemma_one(a, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let rows = v->Map_0;
            let bits = Seq::new(rows.len(), |i: int| rows[i] is Some);
            assert(slot_vals(cs, env, l) == enc_rows(rows, sv, enums));
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert forall|q: int| 0 <= q < fs.len() implies pure_below(#[trigger] fs[q], l.len()) && eval_l(fs[q], env, l)
                == Ok::<Value, ErrKind>(vals[q]) by {
                lemma_enc_rows_index(rows, sv, enums, q, 0);
                let at = q * stride;
                assert(slot_vals(cs, env, l)[at] == eval_l(cs[at], env, l)->Ok_0);
                assert(row_slots(rows[q], sv, enums)[0] == Value::Bool(rows[q] is Some));
            }
            assert(vals_at(fs, vals, env, l));
        }
    }
}

/// SetかMapの大きさは、有無を0と1にした式の和である。
#[verifier::spinoff_prover]
pub proof fn lemma_size(
    e: TExpr,
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    fs: Seq<Expr>,
    codes: Seq<Expr>,
    x: Expr,
)
    requires
        e == TExpr::Size(Box::new(a)),
        flags_ok(a, cx, sc, b0, b1, fs),
        extends(b0, b1),
        extends(b1, b2),
        fs.len() <= 0x7fff_ffff,
        codes.len() == fs.len(),
        forall|q: int| 0 <= q < fs.len() ==> #[trigger] codes[q] == Expr::Code(Box::new(fs[q])),
        added(b1, b2, tree_s(codes, int_lit(0), Join::Add), x),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Int, seq![x]),
{
    let sm = tree_s(codes, int_lit(0), Join::Add);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![x],
        env,
        XTy::Int,
        se.enums,
    ) by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = size_bits(v);
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert(vals_at(fs, vals, env, l1));
            assert forall|j: int| 0 <= j < codes.len() implies pure_below(#[trigger] codes[j], l1.len()) && eval_l(
                codes[j],
                env,
                l1,
            ) == Ok::<Value, ErrKind>(Value::Int(if bits[j] { 1 } else { 0 })) by {
                assert(eval_l(fs[j], env, l1) == Ok::<Value, ErrKind>(vals[j]));
            }
            lemma_sum_codes(codes, bits, env, l1);
            lemma_count_le(bits);
            let c = Value::Int(count_true(bits) as i64);
            lemma_added(b1, b2, sm, x, env, l1, c);
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            if v is Map {
                lemma_count_some(v->Map_0);
            }
            lemma_one_denotes(x, env, l2, c, XTy::Int, se.enums);
        }
    }
}

/// SetかMapが空であることは、どの有無も真でないことである。
#[verifier::spinoff_prover]
pub proof fn lemma_is_empty(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, fs: Seq<Expr>)
    requires
        e == TExpr::IsEmpty(Box::new(a)),
        flags_ok(a, cx, sc, b0, b1, fs),
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, seq![Expr::Not(Box::new(tree_s(fs, bool_lit(false), Join::Or)))]),
{
    let t = tree_s(fs, bool_lit(false), Join::Or);
    let z = Expr::Not(Box::new(t));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        seq![z],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = size_bits(v);
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert(vals_at(fs, vals, env, l));
            assert forall|j: int| 0 <= j < fs.len() implies bool_val(#[trigger] eval_l(fs[j], env, l)) by {
                assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
            }
            assert(all_pure(fs, l.len()));
            lemma_any_of(fs, env, l);
            lemma_tree_pure(fs, bool_lit(false), Join::Or, l.len());
            if any_true(fs, env, l) {
                let j = choose|j: int| 0 <= j < fs.len() && #[trigger] eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(
                    Value::Bool(true),
                );
                assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
                lemma_count_pos(bits, j);
            } else {
                assert forall|j: int| 0 <= j < bits.len() implies !#[trigger] bits[j] by {
                    assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
                }
                lemma_count_none(bits);
            }
            if v is Map {
                lemma_count_some(v->Map_0);
            }
            lemma_one_denotes(z, env, l, Value::Bool(!any_true(fs, env, l)), XTy::Bool, se.enums);
        }
    }
}

/// Setの演算の、要素ごとのスロットの式。
pub open spec fn setop_s(op: SetOp, x: Expr, y: Expr) -> Expr {
    match op {
        SetOp::Union => or_s(x, y),
        SetOp::Intersection => and_s(x, y),
        SetOp::Difference => and_s(x, Expr::Not(Box::new(y))),
        SetOp::Subset => implies_s(x, y),
    }
}

pub open spec fn setop_b(op: SetOp, a: bool, b: bool) -> bool {
    match op {
        SetOp::Union => a || b,
        SetOp::Intersection => a && b,
        SetOp::Difference => a && !b,
        SetOp::Subset => a ==> b,
    }
}

pub proof fn lemma_setop_eval(op: SetOp, x: Expr, y: Expr, env: Env, l: Seq<Value>, a: bool, b: bool)
    requires
        pure_below(x, l.len()),
        pure_below(y, l.len()),
        eval_l(x, env, l) == Ok::<Value, ErrKind>(Value::Bool(a)),
        eval_l(y, env, l) == Ok::<Value, ErrKind>(Value::Bool(b)),
    ensures
        pure_below(setop_s(op, x, y), l.len()),
        eval_l(setop_s(op, x, y), env, l) == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, a, b))),
{
    let n = l.len();
    match op {
        SetOp::Union => {
            lemma_or(x, y, env, l, a, b);
            assert(pure_below(Expr::Or(Box::new(x), Box::new(y)), n));
        },
        SetOp::Intersection => {
            lemma_and(x, y, env, l, a, b);
            assert(pure_below(Expr::And(Box::new(x), Box::new(y)), n));
        },
        SetOp::Difference => {
            let ny = Expr::Not(Box::new(y));
            assert(pure_below(ny, n));
            assert(eval_l(ny, env, l) == Ok::<Value, ErrKind>(Value::Bool(!b)));
            lemma_and(x, ny, env, l, a, !b);
            assert(pure_below(Expr::And(Box::new(x), Box::new(ny)), n));
        },
        SetOp::Subset => {
            let z = Expr::Implies(Box::new(x), Box::new(y));
            assert(pure_below(z, n));
            if y != bool_lit(true) {
                assert(eval_l(z, env, l) == Ok::<Value, ErrKind>(Value::Bool(a ==> b)));
            } else {
                assert(b);
            }
        },
    }
}

/// Setの演算の要素ごとのスロットの値。
pub proof fn lemma_setbin_vals(op: SetOp, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, p: Seq<bool>, q: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        clean(xs, env, l),
        clean(ys, env, l),
        slot_vals(xs, env, l) == Seq::new(p.len(), |i: int| Value::Bool(p[i])),
        slot_vals(ys, env, l) == Seq::new(q.len(), |i: int| Value::Bool(q[i])),
        p.len() == q.len(),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == setop_s(op, xs[j], ys[j]),
    ensures
        out.len() == p.len(),
        forall|j: int| 0 <= j < out.len() ==> pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
            == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, p[j], q[j]))),
{
    assert(slot_vals(xs, env, l).len() == xs.len());
    assert(slot_vals(ys, env, l).len() == ys.len());
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, p[j], q[j]))) by {
        assert(out[j] == setop_s(op, xs[j], ys[j]));
        assert(slot_vals(xs, env, l)[j] == eval_l(xs[j], env, l)->Ok_0);
        assert(slot_vals(ys, env, l)[j] == eval_l(ys[j], env, l)->Ok_0);
        lemma_setop_eval(op, xs[j], ys[j], env, l, p[j], q[j]);
    }
}

/// 包含の判定は、すべての要素の含意である。
pub proof fn lemma_setbin_subset(out: Seq<Expr>, p: Seq<bool>, q: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        out.len() == p.len(),
        p.len() == q.len(),
        forall|j: int| 0 <= j < out.len() ==> pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
            == Ok::<Value, ErrKind>(Value::Bool(setop_b(SetOp::Subset, p[j], q[j]))),
    ensures
        denotes(
            seq![tree_s(out, bool_lit(true), Join::And)],
            env,
            l,
            SVal::Bool(forall|i: int| 0 <= i < p.len() ==> (p[i] ==> q[i])),
            XTy::Bool,
            enums,
        ),
{
    assert(all_bool(out, env, l));
    lemma_all_of(out, env, l);
    if all_true(out, env, l) {
        assert forall|i: int| 0 <= i < p.len() implies !p[i] || q[i] by {
            assert(eval_l(out[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
        }
    }
    if forall|i: int| 0 <= i < p.len() ==> (p[i] ==> q[i]) {
        assert forall|j: int| 0 <= j < out.len() implies #[trigger] eval_l(out[j], env, l) == Ok::<Value, ErrKind>(
            Value::Bool(true),
        ) by {
            assert(p[j] ==> q[j]);
        }
    }
    assert(all_pure(out, l.len()));
    lemma_tree_pure(out, bool_lit(true), Join::And, l.len());
    let z = tree_s(out, bool_lit(true), Join::And);
    lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, enums);
}

/// Setの和、積、差、包含の下ろし。
#[verifier::spinoff_prover]
pub proof fn lemma_setbin(
    e: TExpr,
    op: SetOp,
    a: TExpr,
    b: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e == TExpr::SetBin(op, Box::new(a), Box::new(b)),
        t is Set,
        lowers(a, cx, sc, b0, b1, t, xs),
        lowers(b, cx, sc, b1, b2, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|q: int| 0 <= q < out.len() ==> #[trigger] out[q] == setop_s(op, xs[q], ys[q]),
    ensures
        op is Subset ==> lowers(e, cx, sc, b0, b2, XTy::Bool, seq![tree_s(out, bool_lit(true), Join::And)]),
        !(op is Subset) ==> lowers(e, cx, sc, b0, b2, t, out),
{
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        if op is Subset { seq![tree_s(out, bool_lit(true), Join::And)] } else { out },
        env,
        if op is Subset { XTy::Bool } else { t },
        se.enums,
    ) by {
        lemma_setbin_at(e, op, a, b, cx, sc, b0, b1, b2, t, xs, ys, out, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_setbin_at(
    e: TExpr,
    op: SetOp,
    a: TExpr,
    b: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        e == TExpr::SetBin(op, Box::new(a), Box::new(b)),
        t is Set,
        lowers(a, cx, sc, b0, b1, t, xs),
        lowers(b, cx, sc, b1, b2, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|q: int| 0 <= q < out.len() ==> #[trigger] out[q] == setop_s(op, xs[q], ys[q]),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        result_ok(
            eval_src(e, se, sls),
            run(fresh(b0, b2), env, ls),
            if op is Subset { seq![tree_s(out, bool_lit(true), Join::And)] } else { out },
            env,
            if op is Subset { XTy::Bool } else { t },
            se.enums,
        ),
{
    let st = *t->Set_0;
    let stt = STy::Set(Box::new(st));
    lemma_pair(a, b, cx, sc, b0, b1, b2, t, xs, t, ys, env, se, ls, sls);
    if let Ok(va) = eval_src(a, se, sls) {
        if let Ok(vb) = eval_src(b, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b2), env, ls)->Ok_0;
            let p = va->Set_0;
            let q = vb->Set_0;
            assert(slot_vals(xs, env, l) == enc(va, stt, enums));
            assert(slot_vals(ys, env, l) == enc(vb, stt, enums));
            lemma_setbin_vals(op, xs, ys, out, p, q, env, l);
            if op is Subset {
                lemma_setbin_subset(out, p, q, env, l, enums);
            } else {
                let bits = Seq::new(p.len(), |i: int| setop_b(op, p[i], q[i]));
                assert(slot_vals(out, env, l) =~= Seq::new(bits.len(), |i: int| Value::Bool(bits[i])));
                assert(eval_src(e, se, sls) == Ok::<SVal, ErrKind>(SVal::Set(bits))) by {
                    match op {
                        SetOp::Union => assert(bits =~= Seq::new(p.len(), |i: int| p[i] || q[i])),
                        SetOp::Intersection => assert(bits =~= Seq::new(p.len(), |i: int| p[i] && q[i])),
                        SetOp::Difference => assert(bits =~= Seq::new(p.len(), |i: int| p[i] && !q[i])),
                        SetOp::Subset => {},
                    }
                }
            }
        }
    }
}

pub open spec fn mark_s(on: bool, bit: Expr, r: Expr, k: i64) -> Expr {
    if on {
        or_s(bit, Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    } else {
        and_s(bit, Expr::Bin(BinOp::Ne, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    }
}

/// 番号 `i` の位置を `on` にしたSetのスロットの値。
pub proof fn lemma_mark(on: bool, bits: Seq<Expr>, r: Expr, out: Seq<Expr>, p: Seq<bool>, i: i64, env: Env, l: Seq<Value>)
    requires
        clean(bits, env, l),
        slot_vals(bits, env, l) == Seq::new(p.len(), |j: int| Value::Bool(p[j])),
        p.len() <= 0x7fff_ffff,
        pure_below(r, l.len()),
        eval_l(r, env, l) == Ok::<Value, ErrKind>(Value::Int(i)),
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(on, bits[k], r, k as i64),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == Seq::new(p.len(), |j: int| Value::Bool(if on { p[j] || i == j } else { p[j] && i != j })),
{
    assert(slot_vals(bits, env, l).len() == bits.len());
    assert(at_rank(r, env, l, i));
    assert forall|k: int| 0 <= k < out.len() implies pure_below(#[trigger] out[k], l.len()) && eval_l(out[k], env, l)
        == Ok::<Value, ErrKind>(Value::Bool(if on { p[k] || i == k } else { p[k] && i != k })) by {
        assert(slot_vals(bits, env, l)[k] == eval_l(bits[k], env, l)->Ok_0);
        let c = if on { BinOp::Eq } else { BinOp::Ne };
        lemma_bin_const(c, r, k as i64, env, l, i);
        let y = Expr::Bin(c, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64))));
        if on {
            lemma_or(bits[k], y, env, l, p[k], i == k);
            assert(pure_below(Expr::Or(Box::new(bits[k]), Box::new(y)), l.len()));
        } else {
            lemma_and(bits[k], y, env, l, p[k], i != k);
            assert(pure_below(Expr::And(Box::new(bits[k]), Box::new(y)), l.len()));
        }
    }
    assert(slot_vals(out, env, l) =~= Seq::new(p.len(), |j: int| Value::Bool(if on { p[j] || i == j } else { p[j] && i != j })));
}

} // verus!
