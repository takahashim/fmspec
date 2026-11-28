//! 要素とキーの下ろしと、Mapの演算の下ろしが意味を保存することの補題。
//!
//! 下ろしの実装は [`crate::lowering`] にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_rows, keys, keys_or_zero, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_models_enc, member, sty, to_xty, width, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, and_s, bool_lit, lits, pure_below};
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, rank};
#[cfg(verus_keep_ghost)]
use crate::lists::{at_rank, lemma_ite_rows, lemma_rows_weaken, picks};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{added, extends, Block, Bound, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::map_lookup::{flat_slot, flat_slot_int, key_rank, MISSING_KEY};
#[cfg(verus_keep_ghost)]
use crate::maps::{lemma_map_join, lemma_map_parts, lemma_none_rows, lemma_rows_update, row_vals};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_elem::{elem_lowers, elem_rank_lowers};
#[cfg(verus_keep_ghost)]
use crate::preserve_set::*;
#[cfg(verus_keep_ghost)]
use crate::rows::{flat, head_at, heads_ok, ite_rows_ok, mparts_ok};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_map_items, eval_src, put_row, Item, SEnv, TExpr};
use vstd::prelude::*;

verus! {

/// Mapのスロット `ms` にキー `key` と値 `value` を置いた結果が `out` である。
pub open spec fn put_lowers(
    key: TExpr,
    value: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    out: Seq<Expr>,
) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>, rows: Seq<Option<SVal>>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() && #[trigger] denotes(
            ms,
            env,
            ls,
            SVal::Map(rows),
            XTy::Map(Box::new(kt), Box::new(vt)),
            se.enums,
        ) ==> match put_row(SVal::Map(rows), kt, vt, eval_src(key, se, sls), eval_src(value, se, sls), se.enums) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(rows2) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && denotes(out, env, l, SVal::Map(rows2), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
        }
}

/// キーの番号の行だけを、有無が真で値が `xs` の行に置き換える。
#[verifier::spinoff_prover]
pub proof fn lemma_put(
    key: TExpr,
    value: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    r: Expr,
    xs: Seq<Expr>,
    alt: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    res: Seq<Expr>,
)
    requires
        elem_rank_lowers(key, cx, sc, b0, b1, kt, r),
        elem_lowers(value, cx, sc, b1, b2, vt, xs),
        extends(b0, b1),
        extends(b1, b2),
        mparts_ok(ms, mrows, (1 + width(vt, cx.enums@)) as nat, keys_or_zero(kt, cx.enums@)),
        mrows.len() <= 0x7fff_ffff,
        alt == seq![bool_lit(true)] + xs,
        ite_rows_ok(out, mrows, r, alt),
        res == flat(out),
    ensures
        put_lowers(key, value, cx, sc, b0, b2, kt, vt, ms, res),
{
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>, rows: Seq<Option<SVal>>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() && #[trigger] denotes(
            ms,
            env,
            ls,
            SVal::Map(rows),
            mt,
            se.enums,
        ) implies match put_row(SVal::Map(rows), kt, vt, eval_src(key, se, sls), eval_src(value, se, sls), se.enums) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows2) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(res, env, l, SVal::Map(rows2), mt, se.enums),
    } by {
        let enums = se.enums;
        lemma_map_parts(ms, mrows, env, ls, rows, kt, vt, enums);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(kv) = eval_src(key, se, sls) {
            if member(kv, kt, enums) {
                let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                assert(ctx_ok(cx, sc, env, se, l1, sls));
                if let Ok(vv) = eval_src(value, se, sls) {
                    if member(vv, vt, enums) {
                        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                        lemma_prefix_trans(ls, l1, l2);
                        lemma_rows_weaken(mrows, row_vals(rows, vt, enums), env, ls, l2);
                        lemma_weaken(r, env, l1, l2);
                        lemma_pure_mono(r, l1.len(), l2.len());
                        let rk = rank(kv, kt, enums);
                        lemma_rank_in_domain(kv, kt, enums);
                        assert(at_rank(r, env, l2, rk as i64));
                        let av = row_slots(Some(vv), vt, enums);
                        lemma_lits(seq![Value::Bool(true)], env, l2);
                        assert(lits(seq![Value::Bool(true)]) =~= seq![bool_lit(true)]);
                        lemma_clean_concat(seq![bool_lit(true)], xs, env, l2);
                        lemma_ite_rows(out, mrows, r, alt, row_vals(rows, vt, enums), av, env, l2, rk as i64);
                        lemma_rows_update(rows, vt, enums, rk as int, Some(vv));
                        let rows2 = rows.update(rk as int, Some(vv));
                        assert(row_vals(rows2, vt, enums) =~= Seq::new(
                            mrows.len(),
                            |p: int| if p == rk as i64 { av } else { row_vals(rows, vt, enums)[p] },
                        ));
                        lemma_map_join(out, env, l2, rows2, kt, vt, enums);
                    }
                }
            }
        }
    }
}

/// Mapの更新の下ろし。
#[verifier::spinoff_prover]
pub proof fn lemma_put_expr(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    slots: Seq<Expr>,
)
    requires
        e matches TExpr::Put(skt, svt, a, x, y) && sty(skt) == kt && sty(svt) == vt && lowers(
            *a,
            cx,
            sc,
            b0,
            b1,
            XTy::Map(Box::new(kt), Box::new(vt)),
            ms,
        ) && put_lowers(*x, *y, cx, sc, b1, b2, kt, vt, ms, slots),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Map(Box::new(kt), Box::new(vt)), slots),
{
    let a = e->Put_2;
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        slots,
        env,
        mt,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), se.enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            assert(denotes(ms, env, l1, SVal::Map(rows), mt, se.enums));
            assert(ctx_ok(cx, sc, env, se, l1, sls));
        }
    }
}

/// Mapのリテラルの要素を順に置くと、`slots` は置いた結果のMapを表す。
pub open spec fn maplit_ok(
    items: Seq<Item>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    slots: Seq<Expr>,
) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_map_items(
            kt,
            vt,
            items,
            se,
            sls,
        ) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(rows) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && denotes(slots, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
        }
}

pub proof fn lemma_maplit_base(cx: LowerCtx, sc: Seq<Bound>, b0: Block, kt: STy, vt: STy, slots: Seq<Expr>)
    requires
        keys(kt, cx.enums@) is Some,
        slots == lits(
            enc(default_val(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@), STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
        ),
    ensures
        maplit_ok(Seq::empty(), cx, sc, b0, b0, kt, vt, slots),
{
    let mst = STy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_map_items(
        kt,
        vt,
        Seq::<Item>::empty(),
        se,
        sls,
    ) {
        Err(k) => run(fresh(b0, b0), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows) => run(fresh(b0, b0), env, ls) matches Ok(l) && l.len() == b0.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(slots, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
    } by {
        let enums = se.enums;
        let rows = eval_map_items(kt, vt, Seq::<Item>::empty(), se, sls)->Ok_0;
        lemma_fresh_refl(b0);
        assert(fresh(b0, b0) =~= Seq::<Expr>::empty());
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        assert(prefix(ls, ls));
        lemma_none_rows(keys_or_zero(kt, enums), vt, enums);
        assert(rows =~= Seq::new(keys_or_zero(kt, enums), |_i: int| None::<SVal>));
        assert(default_val(mst, enums)->Map_0 =~= rows);
        lemma_lits(enc(default_val(mst, enums), mst, enums), env, ls);
    }
}

pub proof fn lemma_maplit_step(
    items: Seq<Item>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    s1: Seq<Expr>,
    s2: Seq<Expr>,
)
    requires
        items.len() > 0,
        maplit_ok(items.drop_last(), cx, sc, b0, b1, kt, vt, s1),
        put_lowers(items.last().key, items.last().value, cx, sc, b1, b2, kt, vt, s1, s2),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        maplit_ok(items, cx, sc, b0, b2, kt, vt, s2),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_map_items(
        kt,
        vt,
        items,
        se,
        sls,
    ) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(s2, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(rows) = eval_map_items(kt, vt, items.drop_last(), se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            assert(denotes(s1, env, l1, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums));
            if let Ok(rows2) = eval_map_items(kt, vt, items, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
            }
        }
    }
}

/// Mapのキーの集合は、各行の有無のスロットである。
#[verifier::spinoff_prover]
pub proof fn lemma_keys(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    h: Seq<Expr>,
)
    requires
        e matches TExpr::Keys(a) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(kt), Box::new(vt)), ms),
        extends(b0, b1),
        mparts_ok(ms, mrows, (1 + width(vt, cx.enums@)) as nat, keys_or_zero(kt, cx.enums@)),
        heads_ok(h, mrows),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Set(Box::new(kt)), h),
{
    let a = e->Keys_0;
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        h,
        env,
        XTy::Set(Box::new(kt)),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            lemma_map_parts(ms, mrows, env, l1, rows, kt, vt, enums);
            let bits = eval_src(e, se, sls)->Ok_0->Set_0;
            assert(bits.len() == rows.len());
            let vals = row_vals(rows, vt, enums);
            assert forall|j: int| 0 <= j < h.len() implies pure_below(#[trigger] h[j], l1.len()) && eval_l(h[j], env, l1)
                == Ok::<Value, ErrKind>(Value::Bool(bits[j])) by {
                assert(head_at(h[j], mrows[j]));
                assert(clean(mrows[j], env, l1) && slot_vals(mrows[j], env, l1) == vals[j]);
                assert(pure_below(mrows[j][0], l1.len()) && eval_l(mrows[j][0], env, l1) is Ok);
                assert(slot_vals(mrows[j], env, l1)[0] == eval_l(mrows[j][0], env, l1)->Ok_0);
                assert(vals[j] == row_slots(rows[j], vt, enums));
            }
            assert(slot_vals(h, env, l1) =~= enc(SVal::Set(bits), STy::Set(Box::new(kt)), enums));
        }
    }
}

/// Mapがキーを持つかは、キーの集合がキーを含むかである。
#[verifier::spinoff_prover]
pub proof fn lemma_has_key(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    present: Seq<Expr>,
    r: Expr,
    hit: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::HasKey(t, a, x) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(vt)), ms)
            && rank_lowers(*x, cx, sc, b1, b2, sty(t), r) && mparts_ok(
            ms,
            mrows,
            (1 + width(vt, cx.enums@)) as nat,
            keys_or_zero(sty(t), cx.enums@),
        ),
        extends(b0, b1),
        extends(b1, b2),
        heads_ok(present, mrows),
        present.len() <= 0x7fff_ffff,
        picks(hit, present, r),
        out == seq![and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let t = e->HasKey_0;
    let a = e->HasKey_1;
    let x = e->HasKey_2;
    let kt = sty(t);
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    let ek = TExpr::Keys(a);
    lemma_keys(ek, cx, sc, b0, b1, kt, vt, ms, mrows, present);
    let es = TExpr::SetContains(t, Box::new(ek), x);
    lemma_set_contains(es, t, ek, *x, cx, sc, b0, b1, b2, present, r, hit, out);
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
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        if let Ok(m) = eval_src(*a, se, sls) {
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            if let Ok(y) = eval_src(*x, se, sls) {
                if member(y, kt, enums) {
                    lemma_rank_in_domain(y, kt, enums);
                }
            }
        }
        assert(eval_src(e, se, sls) == eval_src(es, se, sls));
    }
}

/// Mapからキーを除く。キーの番号の行だけを、有無が偽で値が既定値の行に置き換える。
#[verifier::spinoff_prover]
pub proof fn lemma_delete(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    r: Expr,
    alt: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    res: Seq<Expr>,
)
    requires
        e matches TExpr::Delete(t, a, x) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(vt)), ms)
            && rank_lowers(*x, cx, sc, b1, b2, sty(t), r) && mparts_ok(
            ms,
            mrows,
            (1 + width(vt, cx.enums@)) as nat,
            keys_or_zero(sty(t), cx.enums@),
        ),
        extends(b0, b1),
        extends(b1, b2),
        mrows.len() <= 0x7fff_ffff,
        alt == seq![bool_lit(false)] + lits(enc(default_val(vt, cx.enums@), vt, cx.enums@)),
        ite_rows_ok(out, mrows, r, alt),
        res == flat(out),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Map(Box::new(sty(e->Delete_0)), Box::new(vt)), res),
{
    let t = e->Delete_0;
    let a = e->Delete_1;
    let x = e->Delete_2;
    let kt = sty(t);
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        res,
        env,
        mt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            lemma_map_parts(ms, mrows, env, l1, rows, kt, vt, enums);
            assert(rank_result(eval_src(*x, se, sls), run(fresh(b1, b2), env, l1), r, env, kt, enums));
            if let Ok(y) = eval_src(*x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                lemma_rows_weaken(mrows, row_vals(rows, vt, enums), env, l1, l2);
                let mem = member(y, kt, enums);
                let rk: i64 = if mem {
                    rank(y, kt, enums) as i64
                } else {
                    -1i64
                };
                assert(at_rank(r, env, l2, rk));
                let av = row_slots(None, vt, enums);
                assert(lits(av) =~= alt);
                lemma_lits(av, env, l2);
                let vals = row_vals(rows, vt, enums);
                lemma_ite_rows(out, mrows, r, alt, vals, av, env, l2, rk);
                if mem {
                    lemma_rank_in_domain(y, kt, enums);
                    let rkk = rank(y, kt, enums) as int;
                    lemma_rows_update(rows, vt, enums, rkk, None);
                    let rows2 = rows.update(rkk, None);
                    assert(row_vals(rows2, vt, enums) =~= Seq::new(
                        mrows.len(),
                        |p: int| if p == rk { av } else { vals[p] },
                    ));
                    lemma_map_join(out, env, l2, rows2, kt, vt, enums);
                } else {
                    assert(vals =~= Seq::new(mrows.len(), |p: int| if p == rk { av } else { vals[p] }));
                    lemma_map_join(out, env, l2, rows, kt, vt, enums);
                }
            }
        }
    }
}

/// `Map#get` の下ろしの正しさ（[`crate::lower_map::low_get`]）。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn lemma_get(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    a: TExpr,
    x: TExpr,
    ms: Seq<Expr>,
    sk: STy,
    sv: STy,
    rr: Expr,
    rank_local: usize,
    c: Expr,
    slots: Seq<Expr>,
    fallback: Seq<Expr>,
    rows: usize,
    wd: usize,
)
    requires
        e matches TExpr::Get(t, ea, ex) && *ea == a && *ex == x && sty(t) == sk,
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), ms),
        rank_lowers(x, cx, sc, b1, b2, sk, rr),
        added(b2, b3, rr, Expr::Local(rank_local)),
        fresh(b3, b4) == seq![c],
        rows == keys_or_zero(sk, cx.enums@),
        wd == width(sv, cx.enums@),
        fallback == lits(enc(default_val(sv, cx.enums@), sv, cx.enums@)),
        slots.len() == wd,
        forall|n: nat| #[trigger] all_pure(ms, n) && rank_local < n && all_pure(fallback, n) ==> all_pure(slots, n),
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int && (key_rank(locals, rank_local) < 0
                || key_rank(locals, rank_local) < rows <= i64::MAX) ==> #[trigger] eval_l(c, env, locals) == if key_rank(
                locals,
                rank_local,
            ) < 0 {
                Err(ErrKind::Failed(MISSING_KEY))
            } else {
                match as_bool(flat_slot(ms, wd, 0, key_rank(locals, rank_local), env, locals)) {
                    Ok(true) => Ok(Value::Bool(true)),
                    Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                    Err(error) => Err(error),
                }
            },
        forall|i: int, env: Env, locals: Seq<Value>|
            0 <= i < wd && rank_local < locals.len() && locals[rank_local as int] is Int && 0 <= key_rank(
                locals,
                rank_local,
            ) < rows <= i64::MAX ==> #[trigger] eval_l(slots[i], env, locals) == flat_slot_int(
                ms,
                wd,
                i + 1,
                key_rank(locals, rank_local),
                env,
                locals,
            ),
    ensures
        lowers(e, cx, sc, b0, b4, to_xty(sv), slots),
{
    let enums = cx.enums@;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, ls),
        slots,
        env,
        to_xty(sv),
        se.enums,
    ) by {
        lemma_run_fresh(b0, b1, b4, env, ls);
        lemma_run_len(fresh(b0, b1), env, ls);
        match eval_src(a, se, sls) {
            Err(_) => {},
            Ok(m) => {
                let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                assert(denotes(ms, env, l1, m, XTy::Map(Box::new(sk), Box::new(sv)), enums));
                lemma_ctx_weaken(cx, sc, env, se, ls, l1, sls);
                assert(ctx_ok(cx, sc, env, se, l1, sls));
                lemma_run_fresh(b1, b2, b4, env, l1);
                lemma_run_len(fresh(b1, b2), env, l1);
                match eval_src(x, se, sls) {
                    Err(_) => {},
                    Ok(y) => {
                        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                        let rows_v = m->Map_0;
                        let mem = member(y, sk, enums);
                        let rk: i64 = if mem {
                            rank(y, sk, enums) as i64
                        } else {
                            -1i64
                        };
                        assert(eval_l(rr, env, l2) == Ok::<Value, ErrKind>(Value::Int(rk)));
                        lemma_added(b2, b3, rr, Expr::Local(rank_local), env, l2, Value::Int(rk));
                        lemma_run_fresh(b2, b3, b4, env, l2);
                        let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                        assert(rank_local < l3.len() && l3[rank_local as int] == Value::Int(rk));
                        assert(key_rank(l3, rank_local) == rk as int);
                        lemma_run_push(Seq::empty(), c, env, l3);
                        assert(seq![c] =~= Seq::<Expr>::empty().push(c));
                        lemma_prefix_trans(ls, l1, l2);
                        lemma_prefix_trans(l1, l2, l3);
                        assert(keys(sk, enums) == Some(rows_v.len()));
                        if mem {
                            lemma_rank_in_domain(y, sk, enums);
                            let rkk = rank(y, sk, enums);
                            assert(0 <= rkk < rows);
                            let w1 = 1 + wd;
                            lemma_enc_rows_index(rows_v, sv, enums, rkk, 0);
                            let pos = rkk * w1;
                            assert(clean(ms, env, l1));
                            lemma_weaken(ms[pos], env, l1, l3);
                            assert(eval_l(ms[pos], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[pos]));
                            assert(slot_vals(ms, env, l1) == enc_rows(rows_v, sv, enums));
                            assert(flat_slot(ms, wd, 0, rkk, env, l3) == Ok::<Value, ErrKind>(
                                Value::Bool(rows_v[rkk] is Some),
                            ));
                            match rows_v[rkk] {
                                None => {},
                                Some(val) => {
                                    let l4 = l3.push(Value::Bool(true));
                                    lemma_prefix_trans(l3, l3, l4);
                                    lemma_prefix_trans(l1, l3, l4);
                                    assert(key_rank(l4, rank_local) == rkk);
                                    lemma_map_rows_member_index(rows_v, sv, enums, rkk);
                                    lemma_enc_len(val, sv, enums);
                                    lemma_models_enc(val, sv, enums);
                                    lemma_clean_pure(ms, env, l1);
                                    assert(all_pure(ms, l4.len())) by {
                                        assert forall|j: int| 0 <= j < ms.len() implies pure_below(#[trigger] ms[j], l4.len()) by {
                                            lemma_pure_mono(ms[j], l1.len(), l4.len());
                                        }
                                    }
                                    lemma_lits(enc(default_val(sv, enums), sv, enums), env, l4);
                                    assert(all_pure(fallback, l4.len()));
                                    assert(all_pure(slots, l4.len()));
                                    assert forall|i: int| 0 <= i < slots.len() implies pure_below(#[trigger] slots[i], l4.len())
                                        && eval_l(slots[i], env, l4) == Ok::<Value, ErrKind>(enc(val, sv, enums)[i]) by {
                                        lemma_enc_rows_index(rows_v, sv, enums, rkk, i + 1);
                                        let q = rkk * w1 + i + 1;
                                        lemma_weaken(ms[q], env, l1, l4);
                                        assert(eval_l(ms[q], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[q]));
                                        assert(eval_l(slots[i], env, l4) == flat_slot_int(ms, wd, i + 1, rkk, env, l4));
                                    }
                                    assert(slot_vals(slots, env, l4) =~= enc(val, sv, enums));
                                },
                            }
                        }
                    },
                }
            },
        }
    }
}

} // verus!
