//! 量化の下ろしの部品。
//!
//! キーの型の値は、正規順での番号 `0..keys` と1対1に対応する（[`crate::keys`]）。
//! 量化は番号を1つの整数の局所変数でたどり、番号から正規形のスロットの式を作る（[`unrank`]）。
//! そのため、たどる順は値の正規順になる。

#[cfg(verus_keep_ghost)]
use crate::canon::{slot_tys, slot_tys_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_items, enc_seq, keys, keys_product, sty, stys, STy, SVal};
use crate::encoding::{keys_exec, SType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_default_len, lemma_keys_pos, lemma_stys, wf_stype, wf_stypes, width_sum};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_items_len, lemma_enc_len, list_items_member, member, width};
#[cfg(verus_keep_ghost)]
use crate::equality::{small, smalls};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, decode, quant_l};
#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, eval_l, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::keys::{domain, lemma_domain_len, lemma_product_len, product};
#[cfg(verus_keep_ghost)]
use crate::lower_types::*;
#[cfg(verus_keep_ghost)]
use crate::model::Type;
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
use crate::slots::{bin, cb, ci, defaults, eq, ite};
#[cfg(verus_keep_ghost)]
use crate::slots::{ite_s, lits};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_qstate, eval_src, qresult, select_bits, src_bool, QState, SEnv, TExpr};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// 式 `r` が、局所変数 `l` のもとで整数 `i` になる。
pub open spec fn at_rank(r: Expr, env: Env, l: Seq<Value>, i: i64) -> bool {
    pure_below(r, l.len()) && eval_l(r, env, l) == Ok::<Value, ErrKind>(Value::Int(i))
}

/// `r` が番号 `i` になるなら、`xs` は型 `t` の正規順で `i` 番目の値の符号化になる。
pub open spec fn unrank_ok(t: STy, r: Expr, xs: Seq<Expr>, enums: Seq<i64>) -> bool {
    &&& forall|n: nat| pure_below(r, n) ==> #[trigger] all_pure(xs, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        wf_stype(t, enums) && small(t) && tv.enums == enums && #[trigger] has_ty(r, tv, lt, ETy::Int) ==> typed(
            xs,
            etys(slot_tys(t, enums)),
            tv,
            lt,
        )
    &&& forall|env: Env, l: Seq<Value>, i: i64|
        #[trigger] at_rank(r, env, l, i) && keys(t, enums) is Some && 0 <= i < keys(t, enums)->0 ==> clean(xs, env, l)
            && slot_vals(xs, env, l) == enc(domain(t, enums)[i as int], t, enums)
}

/// [`unrank_ok`] の、要素の型の列についての形。値の組は辞書順の列 [`product`] の `i` 番目である。
pub open spec fn unrank_seq_ok(ts: Seq<STy>, r: Expr, xs: Seq<Expr>, enums: Seq<i64>) -> bool {
    &&& forall|n: nat| pure_below(r, n) ==> #[trigger] all_pure(xs, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        wf_stypes(ts, enums) && smalls(ts) && tv.enums == enums && #[trigger] has_ty(r, tv, lt, ETy::Int) ==> typed(
            xs,
            etys(slot_tys_seq(ts, enums)),
            tv,
            lt,
        )
    &&& forall|env: Env, l: Seq<Value>, i: i64|
        #[trigger] at_rank(r, env, l, i) && keys_product(ts, enums) is Some && 0 <= i < keys_product(ts, enums)->0
            ==> clean(xs, env, l) && slot_vals(xs, env, l) == enc_seq(product(ts, enums)[i as int], ts, enums)
}

/// 整数の定数との二項演算は、`r` と同じく純粋である。
pub proof fn lemma_bin_const_pure(op: BinOp, r: Expr, k: i64, n: nat)
    requires
        pure_below(r, n),
    ensures
        pure_below(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), n),
{
    assert(pure_below(Expr::Const(Value::Int(k)), n));
}

/// 整数の定数との二項演算の値。
pub proof fn lemma_bin_const(op: BinOp, r: Expr, k: i64, env: Env, l: Seq<Value>, i: i64)
    requires
        at_rank(r, env, l, i),
    ensures
        pure_below(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), l.len()),
        eval_l(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), env, l) == binop_spec(
            op,
            Value::Int(i),
            Value::Int(k),
        ),
{
    lemma_bin_const_pure(op, r, k, l.len());
    assert(eval_l(Expr::Const(Value::Int(k)), env, l) == Ok::<Value, ErrKind>(Value::Int(k)));
}

/// 整数の比較の値。
proof fn lemma_cmp_eval(op: BinOp, r: Expr, k: i64, env: Env, l: Seq<Value>, i: i64)
    requires
        at_rank(r, env, l, i),
        op is Eq || op is Gt,
    ensures
        pure_below(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), l.len()),
        eval_l(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), env, l) == Ok::<Value, ErrKind>(
            Value::Bool(
                if op is Eq {
                    i == k
                } else {
                    i > k
                },
            ),
        ),
{
    lemma_bin_const(op, r, k, env, l, i);
}

/// 番号 `r` の列挙型のラベル。
fn unrank_enum(id: usize, n: i64, r: &Expr) -> (x: Expr)
    ensures
        forall|m: nat| pure_below(*r, m) ==> #[trigger] pure_below(x, m),
        forall|tv: TyEnv, lt: Seq<ETy>|
            id < tv.enums.len() && n == tv.enums[id as int] && n >= 1 && #[trigger] has_ty(*r, tv, lt, ETy::Int) ==> has_ty(
                x,
                tv,
                lt,
                ETy::Enum(id),
            ),
        forall|env: Env, l: Seq<Value>, i: i64|
            #[trigger] at_rank(*r, env, l, i) && 0 <= i < n ==> eval_l(x, env, l) == Ok::<Value, ErrKind>(
                Value::Enum(id, i),
            ),
{
    if n <= 0 {
        return Expr::Const(Value::Enum(id, 0));
    }
    let mut acc = Expr::Const(Value::Enum(id, n - 1));
    let mut k = n - 1;
    while k > 0
        invariant
            0 <= k < n,
            forall|m: nat| pure_below(*r, m) ==> #[trigger] pure_below(acc, m),
            forall|env: Env, l: Seq<Value>, i: i64|
                #[trigger] at_rank(*r, env, l, i) && k <= i < n ==> eval_l(acc, env, l) == Ok::<Value, ErrKind>(
                    Value::Enum(id, i),
                ),
            forall|tv: TyEnv, lt: Seq<ETy>|
                id < tv.enums.len() && n == tv.enums[id as int] && #[trigger] has_ty(*r, tv, lt, ETy::Int) ==> has_ty(
                    acc,
                    tv,
                    lt,
                    ETy::Enum(id),
                ),
        decreases k,
    {
        k -= 1;
        let ghost prev = acc;
        acc = ite(eq(copy_expr(r), ci(k)), Expr::Const(Value::Enum(id, k)), acc);
        proof {
            assert forall|tv: TyEnv, lt: Seq<ETy>|
                id < tv.enums.len() && n == tv.enums[id as int] && #[trigger] has_ty(*r, tv, lt, ETy::Int) implies has_ty(
                acc,
                tv,
                lt,
                ETy::Enum(id),
            ) by {
                assert(has_ty(prev, tv, lt, ETy::Enum(id)));
                assert(has_ty(Expr::Const(Value::Int(k)), tv, lt, ETy::Int));
                assert(has_ty(Expr::Const(Value::Enum(id, k)), tv, lt, ETy::Enum(id)));
                assert(has_ty(eq_s(*r, k), tv, lt, ETy::Bool));
            }
            assert forall|m: nat| pure_below(*r, m) implies #[trigger] pure_below(acc, m) by {
                lemma_bin_const_pure(BinOp::Eq, *r, k, m);
                assert(pure_below(prev, m));
                assert(pure_below(Expr::Const(Value::Enum(id, k)), m));
            }
            assert forall|env: Env, l: Seq<Value>, i: i64| #[trigger] at_rank(*r, env, l, i) && k <= i < n implies eval_l(
                acc,
                env,
                l,
            ) == Ok::<Value, ErrKind>(Value::Enum(id, i)) by {
                lemma_cmp_eval(BinOp::Eq, *r, k, env, l, i);
                assert(eval_l(Expr::Const(Value::Enum(id, k)), env, l) == Ok::<Value, ErrKind>(Value::Enum(id, k)));
            }
        }
    }
    acc
}

/// 番号 `r` の、型 `t` の値の正規形のスロット。キーの型でなければ `None`。
pub fn unrank(t: &SType, r: &Expr, enums: &Vec<i64>) -> (out: Option<Vec<Expr>>)
    ensures
        out matches Some(xs) ==> unrank_ok(sty(*t), *r, xs@, enums@),
        wf_stype(sty(*t), enums@) && keys(sty(*t), enums@) is Some ==> (out is Some && out->Some_0@.len() == width(
            sty(*t),
            enums@,
        )),
    decreases t, 1nat, 0nat,
{
    let mut out: Vec<Expr> = Vec::new();
    match t {
        SType::Bool => {
            out.push(bin(BinOp::Gt, copy_expr(r), ci(0)));
            proof {
                assert forall|env: Env, l: Seq<Value>, i: i64|
                    #[trigger] at_rank(*r, env, l, i) && keys(sty(*t), enums@) is Some && 0 <= i < keys(
                        sty(*t),
                        enums@,
                    )->0 implies clean(out@, env, l) && slot_vals(out@, env, l) == enc(
                    domain(sty(*t), enums@)[i as int],
                    sty(*t),
                    enums@,
                ) by {
                    lemma_cmp_eval(BinOp::Gt, *r, 0, env, l, i);
                    assert(slot_vals(out@, env, l) =~= seq![Value::Bool(i > 0)]);
                }
                assert forall|n: nat| pure_below(*r, n) implies #[trigger] all_pure(out@, n) by {
                    lemma_bin_const_pure(BinOp::Gt, *r, 0, n);
                }
                assert forall|tv: TyEnv, lt: Seq<ETy>|
                    wf_stype(sty(*t), enums@) && small(sty(*t)) && tv.enums == enums@ && #[trigger] has_ty(*r, tv, lt, ETy::Int) implies typed(out@, etys(slot_tys(sty(*t), enums@)), tv, lt) by {
                    assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
                    assert(has_ty(Expr::Const(Value::Int(0)), tv, lt, ETy::Int));
                    assert(has_ty(out@[0], tv, lt, ETy::Bool));
                }
            }
            Some(out)
        },
        SType::Int(lo, _) => {
            out.push(bin(BinOp::Add, copy_expr(r), ci(*lo)));
            proof {
                assert forall|env: Env, l: Seq<Value>, i: i64|
                    #[trigger] at_rank(*r, env, l, i) && keys(sty(*t), enums@) is Some && 0 <= i < keys(
                        sty(*t),
                        enums@,
                    )->0 implies clean(out@, env, l) && slot_vals(out@, env, l) == enc(
                    domain(sty(*t), enums@)[i as int],
                    sty(*t),
                    enums@,
                ) by {
                    lemma_bin_const(BinOp::Add, *r, *lo, env, l, i);
                    assert(slot_vals(out@, env, l) =~= seq![Value::Int((*lo + i) as i64)]);
                }
                assert forall|n: nat| pure_below(*r, n) implies #[trigger] all_pure(out@, n) by {
                    lemma_bin_const_pure(BinOp::Add, *r, *lo, n);
                }
                assert forall|tv: TyEnv, lt: Seq<ETy>|
                    wf_stype(sty(*t), enums@) && small(sty(*t)) && tv.enums == enums@ && #[trigger] has_ty(*r, tv, lt, ETy::Int) implies typed(out@, etys(slot_tys(sty(*t), enums@)), tv, lt) by {
                    let hi = sty(*t)->Int_1;
                    assert(etys(seq![Type::Int(*lo, hi)]) =~= seq![ETy::Int]);
                    assert(has_ty(Expr::Const(Value::Int(*lo)), tv, lt, ETy::Int));
                    assert(has_ty(out@[0], tv, lt, ETy::Int));
                }

            }
            Some(out)
        },
        SType::Enum(id) => {
            if *id >= enums.len() {
                return None;
            }
            out.push(unrank_enum(*id, enums[*id], r));
            proof {
                assert forall|env: Env, l: Seq<Value>, i: i64|
                    #[trigger] at_rank(*r, env, l, i) && keys(sty(*t), enums@) is Some && 0 <= i < keys(
                        sty(*t),
                        enums@,
                    )->0 implies clean(out@, env, l) && slot_vals(out@, env, l) == enc(
                    domain(sty(*t), enums@)[i as int],
                    sty(*t),
                    enums@,
                ) by {
                    assert(slot_vals(out@, env, l) =~= seq![Value::Enum(*id, i)]);
                }
                assert forall|n: nat| pure_below(*r, n) implies #[trigger] all_pure(out@, n) by {
                    assert(pure_below(out@[0], n));
                }
                assert forall|tv: TyEnv, lt: Seq<ETy>|
                    wf_stype(sty(*t), enums@) && small(sty(*t)) && tv.enums == enums@ && #[trigger] has_ty(*r, tv, lt, ETy::Int) implies typed(out@, etys(slot_tys(sty(*t), enums@)), tv, lt) by {
                    assert(etys(seq![Type::Enum(*id)]) =~= seq![ETy::Enum(*id)]);
                    assert(has_ty(out@[0], tv, lt, ETy::Enum(*id)));
                }

            }
            Some(out)
        },
        SType::Tuple(ts) | SType::Record(_, ts) => {
            proof {
                lemma_stys(ts@);
                assert(stys(ts@).take(ts.len() as int) =~= stys(ts@));
            }
            let xs = unrank_seq(t, ts, ts.len(), r, enums)?;
            proof {
                lemma_unrank_tuple(sty(*t), stys(ts@), *r, xs@, enums@);
            }
            Some(xs)
        },
        SType::Option(x) => {
            proof {
                lemma_default_len(sty(**x), enums@);
            }
            let ds = defaults(x, enums);
            let us = unrank(x, &bin(BinOp::Sub, copy_expr(r), ci(1)), enums)?;
            if ds.len() != us.len() {
                return None;
            }
            out.push(bin(BinOp::Gt, copy_expr(r), ci(0)));
            let ghost tag = out@;
            let mut payload: Vec<Expr> = Vec::new();
            let mut j = 0;
            while j < ds.len()
                invariant
                    ds@.len() == us@.len(),
                    j <= ds@.len(),
                    payload@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] payload@[q] == ite_s(eq_s(*r, 0), ds@[q], us@[q]),
                decreases ds.len() - j,
            {
                payload.push(ite(eq(copy_expr(r), ci(0)), copy_expr(&ds[j]), copy_expr(&us[j])));
                j += 1;
            }
            let ghost pv = payload@;
            let mut k = 0;
            while k < payload.len()
                invariant
                    k <= pv.len(),
                    out@ == tag + pv.take(k as int),
                    payload@ == pv,
                decreases payload.len() - k,
            {
                out.push(copy_expr(&payload[k]));
                proof {
                    assert(tag + pv.take(k + 1) =~= (tag + pv.take(k as int)).push(pv[k as int]));
                }
                k += 1;
            }
            proof {
                assert(pv.take(pv.len() as int) =~= pv);
                lemma_unrank_option(sty(**x), *r, ds@, us@, tag, pv, enums@);
            }
            Some(out)
        },
        _ => None,
    }
}

/// 組と構造体の番号の逆写像は、要素の型の列の逆写像そのものである。
proof fn lemma_unrank_tuple(t: STy, ts: Seq<STy>, r: Expr, xs: Seq<Expr>, enums: Seq<i64>)
    requires
        t == STy::Tuple(ts) || exists|nm| t == STy::Record(nm, ts),
        unrank_seq_ok(ts, r, xs, enums),
    ensures
        unrank_ok(t, r, xs, enums),
{
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        wf_stype(t, enums) && small(t) && tv.enums == enums && #[trigger] has_ty(r, tv, lt, ETy::Int) implies typed(
        xs,
        etys(slot_tys(t, enums)),
        tv,
        lt,
    ) by {
        assert(slot_tys(t, enums) == slot_tys_seq(ts, enums));
    }
    assert forall|env: Env, l: Seq<Value>, i: i64|
        #[trigger] at_rank(r, env, l, i) && keys(t, enums) is Some && 0 <= i < keys(t, enums)->0 implies clean(
        xs,
        env,
        l,
    ) && slot_vals(xs, env, l) == enc(domain(t, enums)[i as int], t, enums) by {
        assert(keys(t, enums) == keys_product(ts, enums));
        lemma_product_len(ts, enums);
        assert(domain(t, enums)[i as int] == SVal::Tuple(product(ts, enums)[i as int]));
    }
}

pub open spec fn eq_s(r: Expr, k: i64) -> Expr {
    Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k))))
}

/// Optionの番号の逆写像。0なら空で、そうでなければ中身の番号は1を引いた値である。
proof fn lemma_unrank_option(x: STy, r: Expr, ds: Seq<Expr>, us: Seq<Expr>, tag: Seq<Expr>, pv: Seq<Expr>, enums: Seq<i64>)
    requires
        ds == lits(enc(default_val(x, enums), x, enums)),
        unrank_ok(x, Expr::Bin(BinOp::Sub, Box::new(r), Box::new(Expr::Const(Value::Int(1)))), us, enums),
        ds.len() == us.len(),
        tag == seq![Expr::Bin(BinOp::Gt, Box::new(r), Box::new(Expr::Const(Value::Int(0))))],
        pv.len() == ds.len(),
        forall|q: int| 0 <= q < pv.len() ==> #[trigger] pv[q] == ite_s(eq_s(r, 0), ds[q], us[q]),
    ensures
        unrank_ok(STy::Option(Box::new(x)), r, tag + pv, enums),
{
    let t = STy::Option(Box::new(x));
    let r1 = Expr::Bin(BinOp::Sub, Box::new(r), Box::new(Expr::Const(Value::Int(1))));
    let xs = tag + pv;
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        wf_stype(t, enums) && small(t) && tv.enums == enums && #[trigger] has_ty(r, tv, lt, ETy::Int) implies typed(
        xs,
        etys(slot_tys(t, enums)),
        tv,
        lt,
    ) by {
        let ys = etys(slot_tys(x, enums));
        lemma_etys_concat(seq![Type::Bool], slot_tys(x, enums));
        assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
        assert(has_ty(Expr::Const(Value::Int(1)), tv, lt, ETy::Int));
        assert(has_ty(Expr::Const(Value::Int(0)), tv, lt, ETy::Int));
        assert(has_ty(r1, tv, lt, ETy::Int));
        assert(typed(us, ys, tv, lt));
        lemma_defaults_typed(x, tv, lt);
        assert(typed(ds, ys, tv, lt));
        assert(has_ty(eq_s(r, 0), tv, lt, ETy::Bool));
        assert forall|q: int| 0 <= q < xs.len() implies #[trigger] has_ty(xs[q], tv, lt, (seq![ETy::Bool] + ys)[q]) by {
            if q >= 1 {
                assert(xs[q] == pv[q - 1]);
                assert(has_ty(ds[q - 1], tv, lt, ys[q - 1]) && has_ty(us[q - 1], tv, lt, ys[q - 1]));
            } else {
                assert(xs[0] == tag[0]);
            }
        }
    }
    assert forall|n: nat| pure_below(r, n) implies #[trigger] all_pure(xs, n) by {
        lemma_bin_const_pure(BinOp::Sub, r, 1, n);
        lemma_bin_const_pure(BinOp::Eq, r, 0, n);
        assert(all_pure(us, n));
        lemma_lits(enc(default_val(x, enums), x, enums), arbitrary(), Seq::empty());
        assert(all_pure(ds, n));
        assert forall|q: int| 0 <= q < xs.len() implies pure_below(#[trigger] xs[q], n) by {
            if q >= 1 {
                assert(xs[q] == pv[q - 1]);
                assert(pure_below(ds[q - 1], n) && pure_below(us[q - 1], n));
            }
        }
    }
    assert forall|env: Env, l: Seq<Value>, i: i64|
        #[trigger] at_rank(r, env, l, i) && keys(t, enums) is Some && 0 <= i < keys(t, enums)->0 implies clean(
        xs,
        env,
        l,
    ) && slot_vals(xs, env, l) == enc(domain(t, enums)[i as int], t, enums) by {
        lemma_domain_len(x, enums);
        lemma_cmp_eval(BinOp::Gt, r, 0, env, l, i);
        lemma_cmp_eval(BinOp::Eq, r, 0, env, l, i);
        let dv = enc(default_val(x, enums), x, enums);
        lemma_lits(dv, env, l);
        assert(pure_below(eq_s(r, 0), l.len()));
        let dom = domain(t, enums);
        assert(dom =~= seq![SVal::None] + domain(x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))));
        if i == 0 {
            assert(dom[0] == SVal::None);
            assert forall|q: int| 0 <= q < pv.len() implies pure_below(#[trigger] pv[q], l.len()) && eval_l(pv[q], env, l)
                == Ok::<Value, ErrKind>(dv[q]) by {
                assert(ds[q] == Expr::Const(dv[q]));
                lemma_bin_const_pure(BinOp::Sub, r, 1, l.len());
                assert(all_pure(us, l.len()));
                assert(pure_below(us[q], l.len()));
            }
            assert(slot_vals(xs, env, l) =~= seq![Value::Bool(false)] + dv);
        } else {
            let j = (i - 1) as i64;
            lemma_bin_const(BinOp::Sub, r, 1, env, l, i);
            assert(at_rank(r1, env, l, j));
            let w = domain(x, enums)[j as int];
            assert(dom[i as int] == SVal::Some(Box::new(w)));
            let uv = enc(w, x, enums);
            assert(clean(us, env, l) && slot_vals(us, env, l) == uv);
            assert forall|q: int| 0 <= q < pv.len() implies pure_below(#[trigger] pv[q], l.len()) && eval_l(pv[q], env, l)
                == Ok::<Value, ErrKind>(uv[q]) by {
                assert(ds[q] == Expr::Const(dv[q]));
                assert(eval_l(us[q], env, l) == Ok::<Value, ErrKind>(slot_vals(us, env, l)[q]));
            }
            assert(slot_vals(xs, env, l) =~= seq![Value::Bool(true)] + uv);
        }
    }
}

/// 要素の型の列 `ts` の先頭 `n` 個の値の組の、番号 `r` の正規形のスロット。
fn unrank_seq(_parent: &SType, ts: &Vec<SType>, n: usize, r: &Expr, enums: &Vec<i64>) -> (out: Option<Vec<Expr>>)
    requires
        decreases_to!(*_parent => *ts),
        n <= ts@.len(),
    ensures
        out matches Some(xs) ==> unrank_seq_ok(stys(ts@).take(n as int), *r, xs@, enums@),
        wf_stypes(stys(ts@).take(n as int), enums@) && keys_product(stys(ts@).take(n as int), enums@) is Some ==> (
        out is Some && out->Some_0@.len() == width_sum(stys(ts@).take(n as int), enums@)),
    decreases _parent, 0nat, n,
{
    proof {
        lemma_stys(ts@);
    }
    let ghost tn = stys(ts@).take(n as int);
    if n == 0 {
        let out: Vec<Expr> = Vec::new();
        proof {
            assert forall|env: Env, l: Seq<Value>, i: i64|
                #[trigger] at_rank(*r, env, l, i) && keys_product(tn, enums@) is Some && 0 <= i < keys_product(
                    tn,
                    enums@,
                )->0 implies clean(out@, env, l) && slot_vals(out@, env, l) == enc_seq(
                product(tn, enums@)[i as int],
                tn,
                enums@,
            ) by {
                assert(slot_vals(out@, env, l) =~= Seq::<Value>::empty());
            }
        }
        return Some(out);
    }
    let ghost ok = wf_stypes(tn, enums@) && keys_product(tn, enums@) is Some;
    proof {
        let tp = stys(ts@).take(n - 1);
        assert(tn.drop_last() =~= tp);
        assert(tn.last() == sty(ts@[n - 1]));
        if ok {
            lemma_keys_pos(sty(ts@[n - 1]), enums@);
        }
    }
    let k = match keys_exec(&ts[n - 1], enums) {
        Some(k) => k,
        None => return None,
    };
    if k == 0 || k > 0x7fff_ffff {
        return None;
    }
    let kk = k as i64;
    let q = bin(BinOp::Div, copy_expr(r), ci(kk));
    let m = bin(BinOp::Mod, copy_expr(r), ci(kk));
    let pre = unrank_seq(_parent, ts, n - 1, &q, enums)?;
    proof {
        vstd::std_specs::vec::axiom_vec_index_decreases(*ts, (n - 1) as int);
    }
    let last = unrank(&ts[n - 1], &m, enums)?;
    let mut out = pre;
    let ghost pv = out@;
    let mut j = 0;
    while j < last.len()
        invariant
            j <= last@.len(),
            out@ == pv + last@.take(j as int),
        decreases last.len() - j,
    {
        out.push(copy_expr(&last[j]));
        proof {
            assert(pv + last@.take(j + 1) =~= (pv + last@.take(j as int)).push(last@[j as int]));
        }
        j += 1;
    }
    proof {
        assert(last@.take(last@.len() as int) =~= last@);
        assert(tn.drop_last() =~= stys(ts@).take(n - 1));
        assert(tn.last() == sty(ts@[n - 1]));
        lemma_unrank_seq_step(tn, *r, kk, pv, last@, enums@);
    }
    Some(out)
}

/// 混合基数の最後の桁は `r mod k`、残りの桁は `r div k` の番号である。
proof fn lemma_unrank_seq_step(tn: Seq<STy>, r: Expr, k: i64, pv: Seq<Expr>, lv: Seq<Expr>, enums: Seq<i64>)
    requires
        tn.len() > 0,
        k > 0,
        keys(tn.last(), enums) == Some(k as nat),
        unrank_seq_ok(tn.drop_last(), Expr::Bin(BinOp::Div, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), pv, enums),
        unrank_ok(tn.last(), Expr::Bin(BinOp::Mod, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), lv, enums),
    ensures
        unrank_seq_ok(tn, r, pv + lv, enums),
{
    let q = Expr::Bin(BinOp::Div, Box::new(r), Box::new(Expr::Const(Value::Int(k))));
    let m = Expr::Bin(BinOp::Mod, Box::new(r), Box::new(Expr::Const(Value::Int(k))));
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        wf_stypes(tn, enums) && smalls(tn) && tv.enums == enums && #[trigger] has_ty(r, tv, lt, ETy::Int) implies typed(
        pv + lv,
        etys(slot_tys_seq(tn, enums)),
        tv,
        lt,
    ) by {
        assert(has_ty(Expr::Const(Value::Int(k)), tv, lt, ETy::Int));
        assert(has_ty(q, tv, lt, ETy::Int));
        assert(has_ty(m, tv, lt, ETy::Int));
        assert(wf_stypes(tn.drop_last(), enums) && wf_stype(tn.last(), enums));
        assert(smalls(tn.drop_last()) && small(tn.last()));
        assert(typed(pv, etys(slot_tys_seq(tn.drop_last(), enums)), tv, lt));
        assert(typed(lv, etys(slot_tys(tn.last(), enums)), tv, lt));
        lemma_etys_concat(slot_tys_seq(tn.drop_last(), enums), slot_tys(tn.last(), enums));
        lemma_typed_concat(pv, etys(slot_tys_seq(tn.drop_last(), enums)), lv, etys(slot_tys(tn.last(), enums)), tv, lt);
    }
    assert forall|n: nat| pure_below(r, n) implies #[trigger] all_pure(pv + lv, n) by {
        lemma_bin_const_pure(BinOp::Div, r, k, n);
        lemma_bin_const_pure(BinOp::Mod, r, k, n);
        assert(all_pure(pv, n) && all_pure(lv, n));
        assert forall|j: int| 0 <= j < (pv + lv).len() implies pure_below(#[trigger] (pv + lv)[j], n) by {
            if j < pv.len() {
                assert((pv + lv)[j] == pv[j]);
            } else {
                assert((pv + lv)[j] == lv[j - pv.len()]);
            }
        }
    }
    assert forall|env: Env, l: Seq<Value>, i: i64|
        #[trigger] at_rank(r, env, l, i) && keys_product(tn, enums) is Some && 0 <= i < keys_product(tn, enums)->0
        implies clean(pv + lv, env, l) && slot_vals(pv + lv, env, l) == enc_seq(product(tn, enums)[i as int], tn, enums)
        by {
        let p = keys_product(tn.drop_last(), enums)->0;
        assert(keys_product(tn, enums)->0 == p * k);
        let iq: int = (i as int) / (k as int);
        let im: int = (i as int) % (k as int);
        assert(0 <= iq < p && 0 <= im < k) by (nonlinear_arith)
            requires
                0 <= i < p * k,
                k > 0,
                iq == (i as int) / (k as int),
                im == (i as int) % (k as int),
        ;
        lemma_bin_const(BinOp::Div, r, k, env, l, i);
        lemma_bin_const(BinOp::Mod, r, k, env, l, i);
        assert(at_rank(q, env, l, iq as i64));
        assert(at_rank(m, env, l, im as i64)) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, k as int);
        }
        lemma_product_len(tn.drop_last(), enums);
        lemma_domain_len(tn.last(), enums);
        let pp = product(tn.drop_last(), enums);
        let dd = domain(tn.last(), enums);
        let vs = product(tn, enums)[i as int];
        assert(vs == pp[iq].push(dd[im]));
        assert(vs.drop_last() =~= pp[iq]);
        assert(vs.last() == dd[im]);
        lemma_clean_concat(pv, lv, env, l);
    }
}


// ---- 番号の位置の式を選ぶ ----

/// 式の列 `fs` の各式は、局所変数 `l` のもとで純粋で、値は `vals` になる。
pub open spec fn vals_at(fs: Seq<Expr>, vals: Seq<Value>, env: Env, l: Seq<Value>) -> bool {
    &&& fs.len() == vals.len()
    &&& forall|j: int|
        0 <= j < fs.len() ==> pure_below(#[trigger] fs[j], l.len()) && eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(
            vals[j],
        )
}

/// 局所変数を後ろに加えても、式の値は変わらない。
pub proof fn lemma_vals_weaken(fs: Seq<Expr>, vals: Seq<Value>, env: Env, l: Seq<Value>, l2: Seq<Value>)
    requires
        vals_at(fs, vals, env, l),
        prefix(l, l2),
    ensures
        vals_at(fs, vals, env, l2),
{
    assert forall|j: int| 0 <= j < fs.len() implies pure_below(#[trigger] fs[j], l2.len()) && eval_l(fs[j], env, l2)
        == Ok::<Value, ErrKind>(vals[j]) by {
        lemma_weaken(fs[j], env, l, l2);
        lemma_pure_mono(fs[j], l.len(), l2.len());
    }
}

/// `x` は、番号 `r` が `lo..hi` にあれば、その位置の式 `fs[r]` と同じ値になる。
pub open spec fn picks_in(x: Expr, fs: Seq<Expr>, r: Expr, lo: int, hi: int) -> bool {
    &&& forall|m: nat| pure_below(r, m) && all_pure(fs, m) ==> #[trigger] pure_below(x, m)
    &&& forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
        lo < hi && has_ty(r, tv, lt, ETy::Int) && #[trigger] all_ty(fs, y, tv, lt) ==> has_ty(x, tv, lt, y)
    &&& forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
        #[trigger] at_rank(r, env, l, i) && #[trigger] vals_at(fs, vals, env, l) && lo <= i < hi ==> eval_l(x, env, l)
            == Ok::<Value, ErrKind>(vals[i as int])
}

pub open spec fn picks(x: Expr, fs: Seq<Expr>, r: Expr) -> bool {
    picks_in(x, fs, r, 0, fs.len() as int)
}

/// 番号 `r` が範囲内で、その位置のスロットが真であるという式は純粋である。
pub proof fn lemma_hit_pure(r: Expr, fs: Seq<Expr>, hit: Expr, n: nat)
    requires
        picks(hit, fs, r),
        pure_below(r, n),
        all_pure(fs, n),
    ensures
        pure_below(
            crate::slots::and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit),
            n,
        ),
{
    assert(pure_below(hit, n));
    lemma_bin_const_pure(BinOp::Ge, r, 0, n);
}

/// 番号 `r` の位置の式を選ぶ式。
pub(crate) fn pick_slot(fs: &Vec<Expr>, r: &Expr) -> (x: Expr)
    requires
        fs@.len() <= 0x7fff_ffff,
    ensures
        picks(x, fs@, *r),
        fs@.len() == 0 ==> x == crate::slots::bool_lit(false),
{
    if fs.len() == 0 {
        return cb(false);
    }
    pick_range(fs, 0, fs.len(), r)
}

/// 番号 `r` の `lo..hi` の位置の式を、二分木の `ite` で選ぶ。
fn pick_range(fs: &Vec<Expr>, lo: usize, hi: usize, r: &Expr) -> (x: Expr)
    requires
        lo < hi <= fs@.len() <= 0x7fff_ffff,
    ensures
        picks_in(x, fs@, *r, lo as int, hi as int),
    decreases hi - lo,
{
    if hi - lo == 1 {
        let x = copy_expr(&fs[lo]);
        proof {
            assert forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
                #[trigger] at_rank(*r, env, l, i) && #[trigger] vals_at(fs@, vals, env, l) && lo <= i < hi implies eval_l(
                x,
                env,
                l,
            ) == Ok::<Value, ErrKind>(vals[i as int]) by {
                assert(i == lo);
            }
            assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
                lo < hi && has_ty(*r, tv, lt, ETy::Int) && #[trigger] all_ty(fs@, y, tv, lt) implies has_ty(x, tv, lt, y) by {
                assert(has_ty(fs@[lo as int], tv, lt, y));
            }
        }
        return x;
    }
    let mid = lo + (hi - lo) / 2;
    let a = pick_range(fs, lo, mid, r);
    let b = pick_range(fs, mid, hi, r);
    let c = bin(BinOp::Lt, copy_expr(r), ci(mid as i64));
    let x = ite(c, a, b);
    proof {
        assert forall|m: nat| pure_below(*r, m) && all_pure(fs@, m) implies #[trigger] pure_below(x, m) by {
            lemma_bin_const_pure(BinOp::Lt, *r, mid as i64, m);
            assert(pure_below(a, m) && pure_below(b, m));
        }
        assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            lo < hi && has_ty(*r, tv, lt, ETy::Int) && #[trigger] all_ty(fs@, y, tv, lt) implies has_ty(x, tv, lt, y) by {
            assert(has_ty(Expr::Const(Value::Int(mid as i64)), tv, lt, ETy::Int));
            assert(has_ty(c, tv, lt, ETy::Bool));
            assert(has_ty(a, tv, lt, y) && has_ty(b, tv, lt, y));
        }
        assert forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
            #[trigger] at_rank(*r, env, l, i) && #[trigger] vals_at(fs@, vals, env, l) && lo <= i < hi implies eval_l(
            x,
            env,
            l,
        ) == Ok::<Value, ErrKind>(vals[i as int]) by {
            lemma_bin_const(BinOp::Lt, *r, mid as i64, env, l, i);
            assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(i < mid)));
        }
    }
    x
}

/// Listの要素は、要素の型に属する。
pub proof fn lemma_items_member(items: Seq<SVal>, t: STy, enums: Seq<i64>, k: int)
    requires
        list_items_member(items, t, enums),
        0 <= k < items.len(),
    ensures
        member(items[k], t, enums),
    decreases items.len(),
{
    if k < items.len() - 1 {
        lemma_items_member(items.drop_last(), t, enums, k);
        assert(items.drop_last()[k] == items[k]);
    }
}

/// Listの要素の符号化の、`k` 番目の要素の `j` 番目のスロット。
pub proof fn lemma_items_index(items: Seq<SVal>, t: STy, enums: Seq<i64>, k: int, j: int)
    requires
        list_items_member(items, t, enums),
        0 <= k < items.len(),
        0 <= j < width(t, enums),
    ensures
        member(items[k], t, enums),
        enc_items(items, t, enums).len() == items.len() * width(t, enums),
        0 <= k * width(t, enums) + j < items.len() * width(t, enums),
        enc_items(items, t, enums)[k * width(t, enums) + j] == enc(items[k], t, enums)[j],
    decreases items.len(),
{
    let n = items.len() as int;
    let w = width(t, enums) as int;
    lemma_enc_items_len(items, t, enums);
    lemma_enc_items_len(items.drop_last(), t, enums);
    assert(k * w + j < n * w) by (nonlinear_arith)
        requires
            0 <= k < n,
            0 <= j < w,
    ;
    assert(0 <= k * w) by (nonlinear_arith)
        requires
            0 <= k,
            0 <= w,
    ;
    lemma_enc_len(items.last(), t, enums);
    if k == n - 1 {
        assert((n - 1) * w + j - (n - 1) * w == j);
    } else {
        lemma_items_index(items.drop_last(), t, enums, k, j);
        assert(items.drop_last()[k] == items[k]);
    }
}

/// 先頭の `len` 個の位置を選ぶと、列の先頭になる。
pub proof fn lemma_select_prefix(dom: Seq<SVal>, m: nat, len: nat)
    requires
        m <= dom.len(),
    ensures
        select_bits(dom, Seq::new(m, |i: int| i < len)) == dom.take(if m <= len { m as int } else { len as int }),
    decreases m,
{
    if m > 0 {
        let bits = Seq::new(m, |i: int| i < len);
        assert(bits.drop_last() =~= Seq::new((m - 1) as nat, |i: int| i < len));
        lemma_select_prefix(dom, (m - 1) as nat, len);
        if m <= len {
            assert(dom.take(m - 1).push(dom[m - 1]) =~= dom.take(m as int));
        }
    } else {
        assert(dom.take(0) =~= Seq::<SVal>::empty());
    }
}

// ---- 番号を順にたどる量化と、値を順にたどる量化 ----

/// 正規順の列 `dom` のうち、`bits` の先頭 `n` 個で選んだ値をたどった量化の状態。
pub open spec fn qprefix(all: bool, dom: Seq<SVal>, bits: Seq<bool>, n: int, body: TExpr, se: SEnv, sls: Seq<SVal>) -> QState {
    eval_qstate(all, select_bits(dom, bits.take(n)), body, se, sls)
}

/// 状態に、本体を1つ評価した結果を加える。
pub open spec fn qstep(all: bool, st: QState, r: Result<bool, ErrKind>) -> QState {
    match st {
        QState::Decided(b) => QState::Decided(b),
        _ => match r {
            Ok(b) => if b != all {
                QState::Decided(b)
            } else {
                st
            },
            Err(k) => match st {
                QState::Open => QState::Pending(k),
                _ => st,
            },
        },
    }
}

/// 値の決まっていない状態が保留している失敗。
pub open spec fn qpend(st: QState) -> Option<ErrKind> {
    match st {
        QState::Pending(k) => Some(k),
        _ => None,
    }
}

/// 1つ先の位置までの量化の状態。選ばない位置では変わらず、選ぶ位置ではその値で本体を評価した結果を加える。
proof fn lemma_qprefix_next(all: bool, dom: Seq<SVal>, bits: Seq<bool>, n: int, body: TExpr, se: SEnv, sls: Seq<SVal>)
    requires
        0 <= n < bits.len(),
    ensures
        qprefix(all, dom, bits, n + 1, body, se, sls) == if bits[n] {
            qstep(all, qprefix(all, dom, bits, n, body, se, sls), src_bool(eval_src(body, se, sls.push(dom[n]))))
        } else {
            qprefix(all, dom, bits, n, body, se, sls)
        },
{
    let t = bits.take(n + 1);
    assert(t.drop_last() =~= bits.take(n));
    assert(t.last() == bits[n]);
    let pre = select_bits(dom, bits.take(n));
    if bits[n] {
        assert(select_bits(dom, t) == pre.push(dom[n]));
        assert(pre.push(dom[n]).drop_last() =~= pre);
    } else {
        assert(select_bits(dom, t) == pre);
    }
}

/// 量化の値が決まったら、先をたどっても変わらない。
proof fn lemma_qprefix_stuck(
    all: bool,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    n: int,
    m: int,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
)
    requires
        0 <= n <= m <= bits.len(),
        qprefix(all, dom, bits, n, body, se, sls) is Decided,
    ensures
        qprefix(all, dom, bits, m, body, se, sls) == qprefix(all, dom, bits, n, body, se, sls),
    decreases m - n,
{
    if m > n {
        lemma_qprefix_stuck(all, dom, bits, n, m - 1, body, se, sls);
        lemma_qprefix_next(all, dom, bits, m - 1, body, se, sls);
    }
}

/// 番号 `x` で本体を評価した真偽は、選ぶ位置では値の意味論の本体の真偽になり、選ばない位置では `all` になる。
pub open spec fn q_step_ok(
    all: bool,
    qb: Expr,
    env: Env,
    l: Seq<Value>,
    bits: Seq<bool>,
    dom: Seq<SVal>,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
) -> bool {
    forall|x: int|
        0 <= x < bits.len() ==> #[trigger] as_bool(eval_l(qb, env, l.push(Value::Int(x as i64)))) == if bits[x] {
            src_bool(eval_src(body, se, sls.push(dom[x])))
        } else {
            Ok::<bool, ErrKind>(all)
        }
}

/// 番号 `n..` をたどる量化の値は、先頭から選んだ値をたどる量化の値になる。
/// 番号の量化が保留している失敗は、値の量化の状態が保留している失敗と同じである。
pub proof fn lemma_qscan(
    all: bool,
    ty: Type,
    qb: Expr,
    env: Env,
    l: Seq<Value>,
    bits: Seq<bool>,
    dom: Seq<SVal>,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
    n: int,
)
    requires
        ty is Int,
        0 <= n <= bits.len() <= 0x7fff_ffff,
        q_step_ok(all, qb, env, l, bits, dom, body, se, sls),
        !(qprefix(all, dom, bits, n, body, se, sls) is Decided),
    ensures
        quant_l(all, ty, qb, env, l, n, bits.len() - 1, qpend(qprefix(all, dom, bits, n, body, se, sls)))
            == lift_bool(qresult(all, qprefix(all, dom, bits, bits.len() as int, body, se, sls))),
    decreases bits.len() - n,
{
    let st = qprefix(all, dom, bits, n, body, se, sls);
    if n < bits.len() {
        assert(decode(ty, n as i64) == Value::Int(n as i64));
        let s = as_bool(eval_l(qb, env, l.push(Value::Int(n as i64))));
        assert(s == if bits[n] {
            src_bool(eval_src(body, se, sls.push(dom[n])))
        } else {
            Ok::<bool, ErrKind>(all)
        });
        lemma_qprefix_next(all, dom, bits, n, body, se, sls);
        assert(qprefix(all, dom, bits, n + 1, body, se, sls) == qstep(all, st, s));
        if s == Ok::<bool, ErrKind>(all) {
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, n + 1);
        } else if s is Err {
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, n + 1);
        } else {
            lemma_qprefix_stuck(all, dom, bits, n + 1, bits.len() as int, body, se, sls);
        }
    } else {
        assert(bits.take(n) =~= bits.take(bits.len() as int));
    }
}

/// すべての位置を選ぶと、列そのものになる。
pub proof fn lemma_select_all(dom: Seq<SVal>, n: nat)
    requires
        n <= dom.len(),
    ensures
        select_bits(dom, Seq::new(n, |i: int| true)) == dom.take(n as int),
    decreases n,
{
    if n > 0 {
        let bits = Seq::new(n, |i: int| true);
        assert(bits.drop_last() =~= Seq::new((n - 1) as nat, |i: int| true));
        lemma_select_all(dom, (n - 1) as nat);
        assert(dom.take(n - 1).push(dom[n - 1]) =~= dom.take(n as int));
    } else {
        assert(dom.take(0) =~= Seq::<SVal>::empty());
    }
}

} // verus!
