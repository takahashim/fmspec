//! 量化の下ろしの部品。
//!
//! キーの型の値は、正規順での番号 `0..keys` と1対1に対応する（[`crate::value::keys`]）。
//! 量化は番号を1つの整数の局所変数でたどり、番号から正規形のスロットの式を作る（[`unrank`]）。
//! そのため、たどる順は値の正規順になる。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{eval_l, Env, ErrKind};
use crate::kernel::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::kernel::model::Type;
use crate::kernel::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::kernel::typing::{ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{all_pure, ite_s, lits, pure_below};
use crate::slot::expr_build::{bin, ci, defaults, eq, ite};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::*;
#[cfg(verus_keep_ghost)]
use crate::slot::members::lemma_defaults_typed;
#[cfg(verus_keep_ghost)]
use crate::slot::pick::{at_rank, lemma_bin_const, lemma_bin_const_pure};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::slot::slot_types::{slot_tys, slot_tys_seq};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::width_sum;
use crate::value::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{default_val, enc, enc_seq, keys, keys_product, lemma_default_len};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_keys_pos, lemma_stys, sty, stys, wf_stype, wf_stypes, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::keys::{domain, lemma_domain_len, lemma_product_len, product};
#[cfg(verus_keep_ghost)]
use crate::value::limits::{small, smalls};
use crate::value::stype_exec::keys_exec;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

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


} // verus!
