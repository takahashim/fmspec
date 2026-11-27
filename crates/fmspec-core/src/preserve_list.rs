//! Listの演算の下ろしが意味を保存することの補題。
//!
//! 下ろしの実装は [`crate::lowering`] にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_items, enc_repeat, lemma_models_enc, list_items_member, member, sty};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, width, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::equality::eq_ok;
#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::lists::{flat, ite_rows_ok, lemma_ite_rows, lemma_list_join, lemma_list_parts, lemma_rows_weaken};
#[cfg(verus_keep_ghost)]
use crate::lists::{lemma_select, pad, pad_vals, parts_ok, rows_at, select_ok};
#[cfg(verus_keep_ghost)]
use crate::lowering::*;
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_map::*;
#[cfg(verus_keep_ghost)]
use crate::quant::{at_rank, lemma_bin_const, lemma_items_member};
#[cfg(verus_keep_ghost)]
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_elements, eval_src, SEnv, TExpr, FAIL_EMPTY, FAIL_FULL, FAIL_INDEX, FAIL_NOT_IN_DOMAIN};
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// 検査の束縛。条件が真なら真を加え、偽なら `code` で失敗する。
pub open spec fn checked(b0: Block, b1: Block, cond: Expr, code: i64) -> bool {
    ||| cond == bool_lit(true) && b1.binds@ == b0.binds@
    ||| b1.binds@ == b0.binds@.push(ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code)))
}

pub proof fn lemma_check(b0: Block, b1: Block, cond: Expr, code: i64, env: Env, l: Seq<Value>, c: bool)
    requires
        checked(b0, b1, cond, code),
        extends(b0, b1),
        l.len() == b0.depth_s(),
        eval_l(cond, env, l) == Ok::<Value, ErrKind>(Value::Bool(c)),
    ensures
        c ==> (run(fresh(b0, b1), env, l) matches Ok(l2) && l2.len() == b1.depth_s() && prefix(l, l2)),
        !c ==> run(fresh(b0, b1), env, l) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(code)),
{
    lemma_run_fresh_ok(b0, b1, env, l);
    let x = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code));
    assert(eval_l(bool_lit(true), env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
    assert(eval_l(Expr::Fail(Type::Bool, code), env, l) == Err::<Value, ErrKind>(ErrKind::Failed(code)));
    if cond == bool_lit(true) && b1.binds@ == b0.binds@ {
        lemma_fresh_refl(b0);
        assert(fresh(b0, b1) =~= Seq::<Expr>::empty());
        assert(run(Seq::<Expr>::empty(), env, l) == Ok::<Seq<Value>, ErrKind>(l));
    } else {
        lemma_run_one(b0, b1, x, env, l);
    }
}

/// Listの式を下ろした結果を、環境ごとに取り出す。
pub proof fn lemma_list_env(
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    env: Env,
    se: SEnv,
    l0: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        lowers(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        ctx_ok(cx, sc, env, se, l0, sls),
        l0.len() == b0.depth_s(),
    ensures
        match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b1), env, l0) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => v is List && (run(fresh(b0, b1), env, l0) matches Ok(l) && l.len() == b1.depth_s() && prefix(l0, l)
                && ctx_ok(cx, sc, env, se, l, sls) && v->List_0.len() <= max && list_items_member(v->List_0, st, se.enums)
                && pure_below(len, l.len()) && eval_l(len, env, l) == Ok::<Value, ErrKind>(
                Value::Int(v->List_0.len() as i64),
            ) && rows_at(rows, pad_vals(v->List_0, st, max as nat, se.enums), env, l)),
        },
{
    lemma_one(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls, env, se, l0, sls);
    if let Ok(v) = eval_src(a, se, sls) {
        let l = run(fresh(b0, b1), env, l0)->Ok_0;
        assert(member(v, STy::List(Box::new(st), max), se.enums));
        lemma_list_parts(ls, len, rows, env, l, v->List_0, st, max, se.enums);
    }
}

/// Listの添字の参照。添字が範囲外なら `FAIL_INDEX` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_at(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    x: Expr,
    y: Expr,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    cond: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::At(a, ix) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls) && lowers(
            *ix,
            cx,
            sc,
            b1,
            b2,
            XTy::Int,
            seq![x],
        ),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        added(b2, b3, x, y),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        cond == and_s(
            Expr::Bin(BinOp::Ge, Box::new(y), Box::new(Expr::Const(Value::Int(0)))),
            Expr::Bin(BinOp::Lt, Box::new(y), Box::new(len)),
        ),
        checked(b3, b4, cond, FAIL_INDEX),
        rows.len() > 0 ==> select_ok(rows, y, out),
    ensures
        lowers(e, cx, sc, b0, b4, to_xty(st), out),
{
    let a = e->At_0;
    let ix = e->At_1;
    let xt = XTy::List(Box::new(st), max);
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_run_fresh(b0, b3, b4, env, l0);
        lemma_extends_trans(b0, b1, b2);
        lemma_extends_trans(b0, b2, b3);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            lemma_one(*ix, cx, sc, b1, b2, XTy::Int, seq![x], env, se, l1, sls);
            if let Ok(vb) = eval_src(*ix, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                lemma_denotes_one(x, env, l2, vb, XTy::Int, enums);
                let n = vb->Int_0;
                lemma_added(b2, b3, x, y, env, l2, Value::Int(n));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_weaken(len, env, l1, l3);
                lemma_pure_mono(len, l1.len(), l3.len());
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                let g0 = Expr::Bin(BinOp::Ge, Box::new(y), Box::new(Expr::Const(Value::Int(0))));
                let g1 = Expr::Bin(BinOp::Lt, Box::new(y), Box::new(len));
                assert(eval_l(Expr::Const(Value::Int(0)), env, l3) == Ok::<Value, ErrKind>(Value::Int(0)));
                assert(eval_l(g0, env, l3) == Ok::<Value, ErrKind>(Value::Bool(n >= 0)));
                assert(eval_l(g1, env, l3) == Ok::<Value, ErrKind>(Value::Bool(n < items.len() as i64)));
                lemma_and(g0, g1, env, l3, n >= 0, n < items.len() as i64);
                let c = 0 <= n < items.len();
                lemma_check(b3, b4, cond, FAIL_INDEX, env, l3, c);
                if c {
                    let l4 = run(fresh(b3, b4), env, l3)->Ok_0;
                    lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l3, l4);
                    lemma_weaken(y, env, l3, l4);
                    lemma_pure_mono(y, l3.len(), l4.len());
                    assert(at_rank(y, env, l4, n));
                    lemma_select(rows, y, out, pad_vals(items, st, max as nat, enums), env, l4, n);
                    lemma_items_member(items, st, enums, n as int);
                    lemma_models_enc(items[n as int], st, enums);
                }
            }
        }
    }
}

/// Listの先頭。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_first(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::First(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        rows.len() > 0 ==> out == rows[0],
    ensures
        lowers(e, cx, sc, b0, b2, to_xty(st), out),
{
    let a = e->First_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(eval_l(Expr::Const(Value::Int(0)), env, l1) == Ok::<Value, ErrKind>(Value::Int(0)));
            assert(eval_l(cond, env, l1) == Ok::<Value, ErrKind>(Value::Bool(items.len() as i64 > 0)));
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l2);
                assert(clean(rows[0], env, l2));
                lemma_items_member(items, st, enums, 0);
                lemma_models_enc(items[0], st, enums);
            }
        }
    }
}

/// Listの末尾。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_last(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    i: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Last(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        i == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        rows.len() > 0 ==> select_ok(rows, i, out),
    ensures
        lowers(e, cx, sc, b0, b3, to_xty(st), out),
{
    let a = e->Last_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(eval_l(Expr::Const(Value::Int(0)), env, l1) == Ok::<Value, ErrKind>(Value::Int(0)));
            assert(eval_l(cond, env, l1) == Ok::<Value, ErrKind>(Value::Bool(items.len() as i64 > 0)));
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                let n = (items.len() - 1) as i64;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                assert(eval_l(Expr::Const(Value::Int(1)), env, l2) == Ok::<Value, ErrKind>(Value::Int(1)));
                assert(eval_l(d, env, l2) == Ok::<Value, ErrKind>(Value::Int(n)));
                assert(pure_below(Expr::Const(Value::Int(1)), l2.len()));
                assert(pure_below(d, l2.len()));
                lemma_added(b2, b3, d, i, env, l2, Value::Int(n));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                assert(at_rank(i, env, l3, n));
                lemma_select(rows, i, out, pad_vals(items, st, max as nat, enums), env, l3, n);
                lemma_items_member(items, st, enums, n as int);
                lemma_models_enc(items[n as int], st, enums);
            }
        }
    }
}

pub open spec fn defaults_s(st: STy, enums: Seq<i64>) -> Seq<Expr> {
    lits(enc(default_val(st, enums), st, enums))
}

/// 長さの式が整数 `n` を表すなら、`n` を足し引きした式も表す。
pub proof fn lemma_len_step(len: Expr, op: BinOp, k: i64, env: Env, l: Seq<Value>, n: i64)
    requires
        pure_below(len, l.len()),
        eval_l(len, env, l) == Ok::<Value, ErrKind>(Value::Int(n)),
        0 <= n <= 0x7fff_ffff,
        0 <= k <= 1,
        op is Add || op is Sub,
    ensures
        pure_below(Expr::Bin(op, Box::new(len), Box::new(Expr::Const(Value::Int(k)))), l.len()),
        eval_l(Expr::Bin(op, Box::new(len), Box::new(Expr::Const(Value::Int(k)))), env, l) == Ok::<Value, ErrKind>(
            Value::Int(if op is Add { (n + k) as i64 } else { (n - k) as i64 }),
        ),
{
    assert(at_rank(len, env, l, n));
    lemma_bin_const(op, len, k, env, l, n);
}

/// `contains` の `q` 番目の項。`q` が長さより小さく、`q` 番目の要素が値に等しい。
pub open spec fn hit_at(h: Expr, row: Seq<Expr>, xv: Seq<Expr>, len: Expr, c: Expr, q: int, t: XTy, enums: Seq<i64>) -> bool {
    &&& h == and_s(Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(q as i64)))), c)
    &&& eq_ok(t, row, xv, c, enums)
}

/// Listが値を含むかは、長さより前のどれかの要素が値に等しいことである。
#[verifier::spinoff_prover]
pub proof fn lemma_list_contains(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    t: XTy,
    xv: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    hits: Seq<Expr>,
    cs: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::ListContains(a, x) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls) && lowers(
            *x,
            cx,
            sc,
            b1,
            b2,
            t,
            xv,
        ),
        extends(b0, b1),
        extends(b1, b2),
        t == to_xty(st),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        hits.len() == rows.len(),
        cs.len() == rows.len(),
        forall|q: int| 0 <= q < rows.len() ==> #[trigger] hit_at(hits[q], rows[q], xv, len, cs[q], q, t, cx.enums@),
        out == seq![tree_s(hits, bool_lit(false), Join::Or)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let a = e->ListContains_0;
    let x = e->ListContains_1;
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, l0),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            lemma_one(*x, cx, sc, b1, b2, t, xv, env, se, l1, sls);
            if let Ok(y) = eval_src(*x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                let n = l2.len();
                let vals = pad_vals(items, st, max as nat, enums);
                lemma_rows_weaken(rows, vals, env, l1, l2);
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), n);
                lemma_clean_pure(xv, env, l2);
                assert(at_rank(len, env, l2, m));
                assert forall|q: int| 0 <= q < hits.len() implies pure_below(#[trigger] hits[q], n) && eval_l(
                    hits[q],
                    env,
                    l2,
                ) == Ok::<Value, ErrKind>(Value::Bool(q < items.len() && items[q] == y)) by {
                    assert(hit_at(hits[q], rows[q], xv, len, cs[q], q, t, enums));
                    lemma_clean_pure(rows[q], env, l2);
                    assert(pure_below(cs[q], n));
                    let g = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(q as i64))));
                    lemma_bin_const(BinOp::Gt, len, q as i64, env, l2, m);
                    if q < items.len() {
                        lemma_items_member(items, st, enums, q);
                        assert(pad(items, st, max as nat, enums)[q] == items[q]);
                        lemma_models_enc(items[q], st, enums);
                        assert(denotes(rows[q], env, l2, items[q], t, enums));
                        assert(eval_l(cs[q], env, l2) == Ok::<Value, ErrKind>(Value::Bool(items[q] == y)));
                        lemma_and(g, cs[q], env, l2, true, items[q] == y);
                    } else if cs[q] == bool_lit(true) {
                        assert(hits[q] == g);
                    } else {
                        assert(hits[q] == Expr::And(Box::new(g), Box::new(cs[q])));
                    }
                }
                assert(all_pure(hits, n));
                lemma_tree_pure(hits, bool_lit(false), Join::Or, n);
                lemma_any_of(hits, env, l2);
                if items.contains(y) {
                    let k = choose|k: int| 0 <= k < items.len() && items[k] == y;
                    assert(eval_l(hits[k], env, l2) == Ok::<Value, ErrKind>(Value::Bool(true)));
                }
                if any_true(hits, env, l2) {
                    let k = choose|k: int| 0 <= k < hits.len() && #[trigger] eval_l(hits[k], env, l2) == Ok::<Value, ErrKind>(
                        Value::Bool(true),
                    );
                    assert(items[k] == y);
                }
                lemma_one_denotes(out[0], env, l2, Value::Bool(items.contains(y)), XTy::Bool, enums);
                assert(out == seq![out[0]]);
            }
        }
    }
}

/// Listの末尾に要素を加える。要素が型に属さなければ `FAIL_NOT_IN_DOMAIN`、満杯なら `FAIL_FULL` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_push(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    xs: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Push(t, n, a, x) && sty(t) == st && n == max && lowers(
            *a,
            cx,
            sc,
            b0,
            b1,
            XTy::List(Box::new(st), max),
            ls,
        ) && elem_lowers(*x, cx, sc, b1, b2, st, xs),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b2, b3, Expr::Bin(BinOp::Lt, Box::new(len), Box::new(Expr::Const(Value::Int(max as i64)))), FAIL_FULL),
        new_len == Expr::Local(b3.depth_s() as usize),
        b4.binds@ == b3.binds@.push(Expr::Bin(BinOp::Add, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        ite_rows_ok(out, rows, len, xs),
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b4, XTy::List(Box::new(st), max), r),
{
    let a = e->Push_2;
    let x = e->Push_3;
    let cond = Expr::Bin(BinOp::Lt, Box::new(len), Box::new(Expr::Const(Value::Int(max as i64))));
    let d = Expr::Bin(BinOp::Add, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_run_fresh(b0, b3, b4, env, l0);
        lemma_extends_trans(b0, b1, b2);
        lemma_extends_trans(b0, b2, b3);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(y) = eval_src(*x, se, sls) {
                if member(y, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_weaken(len, env, l1, l2);
                    lemma_pure_mono(len, l1.len(), l2.len());
                    lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l2);
                    assert(at_rank(len, env, l2, m));
                    lemma_bin_const(BinOp::Lt, len, max as i64, env, l2, m);
                    lemma_check(b2, b3, cond, FAIL_FULL, env, l2, items.len() < max);
                    if items.len() < max {
                        let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                        lemma_weaken(len, env, l2, l3);
                        lemma_pure_mono(len, l2.len(), l3.len());
                        lemma_len_step(len, BinOp::Add, 1, env, l3, m);
                        lemma_added(b3, b4, d, new_len, env, l3, Value::Int((m + 1) as i64));
                        let l4 = run(fresh(b3, b4), env, l3)->Ok_0;
                        lemma_prefix_trans(l2, l3, l4);
                        lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l2, l4);
                        lemma_clean_weaken(xs, env, l2, l4);
                        lemma_weaken(len, env, l3, l4);
                        lemma_pure_mono(len, l3.len(), l4.len());
                        lemma_ite_rows(out, rows, len, xs, pad_vals(items, st, max as nat, enums), enc(y, st, enums), env, l4, m);
                        let items2 = items.push(y);
                        assert(items2.drop_last() =~= items);
                        assert(list_items_member(items2, st, enums));
                        assert(pad_vals(items2, st, max as nat, enums) =~= Seq::new(
                            rows.len(),
                            |p: int| if p == m { enc(y, st, enums) } else { pad_vals(items, st, max as nat, enums)[p] },
                        ));
                        lemma_list_join(new_len, out, env, l4, items2, st, max, enums);
                    }
                }
            }
        }
    }
}

/// Listの末尾を除く。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_pop(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    defs: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Pop(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        new_len == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        defs == defaults_s(st, cx.enums@),
        ite_rows_ok(out, rows, new_len, defs),
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b3, XTy::List(Box::new(st), max), r),
{
    let a = e->Pop_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(at_rank(len, env, l1, m));
            lemma_bin_const(BinOp::Gt, len, 0, env, l1, m);
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                lemma_len_step(len, BinOp::Sub, 1, env, l2, m);
                lemma_added(b2, b3, d, new_len, env, l2, Value::Int((m - 1) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                let dv = enc(default_val(st, enums), st, enums);
                lemma_lits(dv, env, l3);
                lemma_ite_rows(out, rows, new_len, defs, pad_vals(items, st, max as nat, enums), dv, env, l3, (m - 1) as i64);
                let items2 = items.drop_last();
                assert(list_items_member(items2, st, enums));
                assert(pad_vals(items2, st, max as nat, enums) =~= Seq::new(
                    rows.len(),
                    |p: int| if p == m - 1 { dv } else { pad_vals(items, st, max as nat, enums)[p] },
                ));
                lemma_list_join(new_len, out, env, l3, items2, st, max, enums);
            }
        }
    }
}

/// Listの先頭を除く。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
pub proof fn lemma_shift(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    defs: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Shift(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        new_len == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        defs == defaults_s(st, cx.enums@),
        rows.len() > 0 ==> out.len() == rows.len() && out[rows.len() - 1] == defs && forall|q: int|
            0 <= q < rows.len() - 1 ==> #[trigger] out[q] == rows[q + 1],
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b3, XTy::List(Box::new(st), max), r),
{
    let a = e->Shift_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(at_rank(len, env, l1, m));
            lemma_bin_const(BinOp::Gt, len, 0, env, l1, m);
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                lemma_len_step(len, BinOp::Sub, 1, env, l2, m);
                lemma_added(b2, b3, d, new_len, env, l2, Value::Int((m - 1) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                let vals = pad_vals(items, st, max as nat, enums);
                lemma_rows_weaken(rows, vals, env, l1, l3);
                let dv = enc(default_val(st, enums), st, enums);
                lemma_lits(dv, env, l3);
                let items2 = items.drop_first();
                let nv = pad_vals(items2, st, max as nat, enums);
                assert(nv =~= Seq::new(rows.len(), |p: int| if p < rows.len() - 1 { vals[p + 1] } else { dv }));
                assert forall|p: int| 0 <= p < out.len() implies clean(#[trigger] out[p], env, l3) && slot_vals(out[p], env, l3)
                    == nv[p] by {
                    if p < rows.len() - 1 {
                        assert(out[p] == rows[p + 1]);
                    }
                }
                assert(list_items_member(items2, st, enums)) by {
                    lemma_items_drop_first(items, st, enums);
                }
                lemma_list_join(new_len, out, env, l3, items2, st, max, enums);
            }
        }
    }
}

pub proof fn lemma_items_drop_first(items: Seq<SVal>, st: STy, enums: Seq<i64>)
    requires
        list_items_member(items, st, enums),
        items.len() > 0,
    ensures
        list_items_member(items.drop_first(), st, enums),
    decreases items.len(),
{
    if items.len() > 1 {
        lemma_items_drop_first(items.drop_last(), st, enums);
        assert(items.drop_first().drop_last() =~= items.drop_last().drop_first());
        assert(items.drop_first().last() == items.last());
    } else {
        assert(items.drop_first() =~= Seq::<SVal>::empty());
    }
}

/// Listのリテラルの要素を順に下ろすと、`out` は長さのスロットと要素のスロットの列を表す。
pub open spec fn listlit_ok(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, n: i64, out: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_elements(st, es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(items) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && items.len() == es.len() && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
                out,
                env,
                l,
            ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
        }
}

pub proof fn lemma_listlit_base(cx: LowerCtx, sc: Seq<Bound>, b: Block, st: STy, n: i64, out: Seq<Expr>)
    requires
        out == seq![Expr::Const(Value::Int(n))],
    ensures
        listlit_ok(Seq::empty(), cx, sc, b, b, st, n, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_elements(st, Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(items) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && items.len() == 0 && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
            out,
            env,
            l,
        ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        assert(out[0] == Expr::Const(Value::Int(n)));
        assert(slot_vals(out, env, ls) =~= seq![Value::Int(n)] + enc_items(Seq::empty(), st, se.enums));
    }
}

/// Listのリテラルに要素を1つ加える。
#[verifier::spinoff_prover]
pub proof fn lemma_listlit_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    n: i64,
    o1: Seq<Expr>,
    x: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        es.len() > 0,
        listlit_ok(es.drop_last(), cx, sc, b0, b1, st, n, o1),
        elem_lowers(es.last(), cx, sc, b1, b2, st, x),
        extends(b0, b1),
        extends(b1, b2),
        out == o1 + x,
    ensures
        listlit_ok(es, cx, sc, b0, b2, st, n, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_elements(st, es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(items) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && items.len() == es.len() && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
            out,
            env,
            l,
        ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(vs) = eval_elements(st, es.drop_last(), se, sls) {
            let enums = se.enums;
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(v) = eval_src(es.last(), se, sls) {
                if member(v, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_prefix_trans(ls, l1, l2);
                    lemma_clean_weaken(o1, env, l1, l2);
                    lemma_clean_concat(o1, x, env, l2);
                    let items = vs.push(v);
                    assert(items.drop_last() =~= vs);
                    assert(items.last() == v);
                    assert(enc_items(items, st, enums) == enc_items(vs, st, enums) + enc(v, st, enums));
                    assert(slot_vals(out, env, l2) =~= seq![Value::Int(n)] + enc_items(items, st, enums));
                }
            }
        }
    }
}

/// Listのリテラルの残りを既定値で埋める。
#[verifier::spinoff_prover]
pub proof fn lemma_listlit_done(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    o2: Seq<Expr>,
    dv: Seq<Value>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::ListLit(t, m, es) && sty(t) == st && m == max && es@.len() <= max && listlit_ok(
            es@,
            cx,
            sc,
            b0,
            b1,
            st,
            es@.len() as i64,
            o2,
        ) && out == o2 + lits(enc_repeat(dv, (max - es@.len()) as nat)),
        dv == enc(default_val(st, cx.enums@), st, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::List(Box::new(st), max), out),
{
    let es = e->ListLit_2@;
    let xt = XTy::List(Box::new(st), max);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        if let Ok(items) = eval_elements(st, es, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let tail = enc_repeat(dv, (max - es.len()) as nat);
            lemma_lits(tail, env, l);
            lemma_clean_concat(o2, lits(tail), env, l);
            let v = SVal::List(items);
            assert(member(v, STy::List(Box::new(st), max), enums));
            assert(slot_vals(out, env, l) == enc(v, STy::List(Box::new(st), max), enums));
        }
    }
}

/// Listの大きさは先頭のスロットである。
#[verifier::spinoff_prover]
pub proof fn lemma_list_size(
    e: TExpr,
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    s: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Size(Box::new(a)) || e == TExpr::IsEmpty(Box::new(a)),
        lowers(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), s),
        extends(b0, b1),
        s.len() > 0,
        max <= 0x7fff_ffff,
        out == if e is Size {
            seq![s[0]]
        } else {
            seq![Expr::Bin(BinOp::Eq, Box::new(s[0]), Box::new(Expr::Const(Value::Int(0))))]
        },
    ensures
        lowers(e, cx, sc, b0, b1, if e is Size { XTy::Int } else { XTy::Bool }, out),
{
    let xt = if e is Size { XTy::Int } else { XTy::Bool };
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let items = v->List_0;
            assert(slot_vals(s, env, l) == enc(v, STy::List(Box::new(st), max), se.enums));
            assert(slot_vals(s, env, l)[0] == eval_l(s[0], env, l)->Ok_0);
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Int(items.len() as i64)));
            assert(pure_below(s[0], l.len()));
            assert(items.len() <= max);
            if e is Size {
                lemma_one_denotes(out[0], env, l, Value::Int(items.len() as i64), XTy::Int, se.enums);
            } else {
                assert(binop_spec(BinOp::Eq, Value::Int(items.len() as i64), Value::Int(0)) == Ok::<Value, ErrKind>(
                    Value::Bool(items.len() == 0),
                ));
                let z = Expr::Bin(BinOp::Eq, Box::new(s[0]), Box::new(Expr::Const(Value::Int(0))));
                assert(out[0] == z);
                assert(pure_below(int_lit(0), l.len()));
                assert(eval_l(int_lit(0), env, l) == Ok::<Value, ErrKind>(Value::Int(0)));
                lemma_one_denotes(out[0], env, l, Value::Bool(items.len() == 0), XTy::Bool, se.enums);
            }
        }
    }
}

} // verus!
