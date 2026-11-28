//! 格納の型の値を、正規形のスロットの列に置く式（`store`）と、キーの番号の式（`rank_expr`）。その契約（`store_spec`、`rank_spec` など）も置く。

#[cfg(verus_keep_ghost)]
use crate::canon::lemma_defaults_typed;
use crate::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_seq, keys, keys_product, lemma_default_len, lemma_stys};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_xtys, member, members, models_seq, STy, sty, stys, SVal, wf_stype};
#[cfg(verus_keep_ghost)]
use crate::encoding::{wf_stypes, width, width_sum, XTy, xty, xtys, xwidth, xwidth_sum};
#[cfg(verus_keep_ghost)]
use crate::eval::{Env, ErrKind, eval_l};
use crate::expr_build::{all_of, and, bin, cb, ci, defaults, extend, implies, is_bool_lit, ite};
use crate::expr_build::{split, sub_exprs};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, and_s, bool_lit, concat, int_lit, ite_s, Join, pure_below};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{split_ok, xoff};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::fits::{fits_all_s, fits_s, lemma_fits_all};
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, radix, rank, rank_seq};
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_fits_width, lemma_lim_xs_at, lim, lim_x, lim_xs, small, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{has_ty, lemma_concat_typed, lemma_econcat_xetys, lemma_fits_etys};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_smalls_at, lemma_tree_typed, lemma_typed_sub, lemma_xetys_part};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{typed, xetys, xetys_seq};
use crate::model::{BinOp, Expr};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
#[cfg(verus_keep_ghost)]
use crate::preserve::{all_true, bool_val, clean, denotes, lemma_all_of, lemma_and};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_clean_pure, lemma_clean_sub, lemma_concat_enc, lemma_concat_pure};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_concat_push, lemma_denotes_part, lemma_join_pure, lemma_lits};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_members, lemma_models_seq_parts, lemma_option_out_pure, lemma_sub_pure};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_tree_pure, mixed_rank_eval, ranks_pure, slot_vals};
use crate::ranking::{mixed_rank_expr, offset_rank, option_rank};
use crate::slots::copy_exprs;
use crate::stype_exec::keys_exec;
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

/// 値を型 `st` の場所に置く。値が型に属する条件と、正規形にしたスロットを返す。
/// `t` は `st` に合うものとする。
pub fn store(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<(Expr, Vec<Expr>)>)
    ensures
        r matches Some((c, out)) ==> store_spec(xty(*t), slots@, sty(*st), enums@, c, out@),
        fits_s(xty(*t), sty(*st)) && slots@.len() == xwidth(xty(*t), enums@) && lim_x(xty(*t), enums@) ==> (r is Some && r->Some_0.1@.len() == width(sty(*st), enums@)),
    decreases t, 1nat,
{
    proof {
        if fits_s(xty(*t), sty(*st)) {
            lemma_fits_width(xty(*t), sty(*st), enums@);
        }
    }
    match (t, st) {
        (XType::Int, SType::Int(lo, hi)) => {
            if slots.len() == 0 {
                return None;
            }
            let x = bin(BinOp::Le, ci(*lo), copy_expr(&slots[0]));
            let y = bin(BinOp::Le, copy_expr(&slots[0]), ci(*hi));
            let c = and(copy_expr(&x), copy_expr(&y));
            let out = copy_exprs(slots);
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(c, tv, lt, ETy::Bool) && typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(xty(*t) == XTy::Int);
                    assert(xetys(XTy::Int, enums@) =~= seq![ETy::Int]);
                    assert(has_ty(slots@[0], tv, lt, xetys(XTy::Int, enums@)[0]));
                    assert(has_ty(slots@[0], tv, lt, ETy::Int));
                    assert(has_ty(Expr::Const(Value::Int(*lo)), tv, lt, ETy::Int));
                    assert(has_ty(Expr::Const(Value::Int(*hi)), tv, lt, ETy::Int));
                    assert(has_ty(x, tv, lt, ETy::Bool));
                    assert(has_ty(y, tv, lt, ETy::Bool));
                    assert(c == and_s(x, y));
                    assert(out@ == slots@);
                }
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(c, n) && all_pure(out@, n) by {
                    assert(pure_below(slots@[0], n));
                    assert(pure_below(Expr::Const(Value::Int(*lo)), n));
                    assert(pure_below(Expr::Const(Value::Int(*hi)), n));
                    assert(pure_below(x, n));
                    assert(pure_below(y, n));
                    lemma_join_pure(Join::And, x, y, n);
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    let k = v->Int_0;
                    assert(sv[0] == Value::Int(k));
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(Value::Int(k)));
                    assert(eval_l(Expr::Const(Value::Int(*lo)), env, ls) == Ok::<Value, ErrKind>(Value::Int(*lo)));
                    assert(eval_l(Expr::Const(Value::Int(*hi)), env, ls) == Ok::<Value, ErrKind>(Value::Int(*hi)));
                    assert(eval_l(x, env, ls) == Ok::<Value, ErrKind>(Value::Bool(*lo <= k)));
                    assert(eval_l(y, env, ls) == Ok::<Value, ErrKind>(Value::Bool(k <= *hi)));
                    lemma_and(x, y, env, ls, *lo <= k, k <= *hi);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let (c, out) = store_parts(t, xs, ts, slots, enums)?;
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(c, tv, lt, ETy::Bool) && typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let (c, out) = store_parts(t, xs, ts, slots, enums)?;
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(c, tv, lt, ETy::Bool) && typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                    assert(typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Option(x), SType::Option(inner)) => {
            proof {
                assert(decreases_to!(*t => **x));
            }
            store_option(t, x, slots, st, inner, enums)
        },
        _ => {
            let c = cb(true);
            let out = copy_exprs(slots);
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(c, tv, lt, ETy::Bool) && typed(out@, xetys(xty(*t), enums@), tv, lt) by {
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Some((c, out))
        },
    }
}

pub(crate) fn store_option(_parent: &XType, x: &XType, slots: &Vec<Expr>, _st: &SType, inner: &SType, enums: &Vec<i64>) -> (r:
    Option<(Expr, Vec<Expr>)>)
    requires
        decreases_to!(*_parent => *x),
        *_parent == XType::Option(Box::new(*x)),
        *_st == SType::Option(Box::new(*inner)),
    ensures
        r matches Some((c, out)) ==> store_spec(xty(*_parent), slots@, sty(*_st), enums@, c, out@),
        fits_s(xty(*_parent), sty(*_st)) && slots@.len() == xwidth(xty(*_parent), enums@) && lim_x(xty(*_parent), enums@)
            ==> (r is Some && r->Some_0.1@.len() == width(sty(*_st), enums@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_default_len(sty(*inner), enums@);
    }
    if slots.len() == 0 {
        return None;
    }
    let rest = sub_exprs(slots, 1, slots.len());
    let (c, payload) = store(x, &rest, inner, enums)?;
    let defs = defaults(inner, enums);
    if payload.len() != defs.len() {
        return None;
    }
    let tag = copy_expr(&slots[0]);
    let mut out: Vec<Expr> = Vec::new();
    out.push(copy_expr(&tag));
    let n = defs.len();
    let mut i = 0;
    while i < n
        invariant
            n == payload@.len(),
            n == defs@.len(),
            i <= n,
            out@.len() == 1 + i,
            out@[0] == tag,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[1 + j] == ite_s(tag, payload@[j], defs@[j]),
        decreases n - i,
    {
        out.push(ite(copy_expr(&tag), copy_expr(&payload[i]), copy_expr(&defs[i])));
        i += 1;
    }
    let cond = implies(copy_expr(&tag), copy_expr(&c));
    proof {
        let dv = enc(default_val(sty(*inner), enums@), sty(*inner), enums@);
        lemma_default_len(sty(*inner), enums@);
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(cond, m) && all_pure(out@, m) by {
            assert(pure_below(slots@[0], m));
            lemma_sub_pure(slots@, 1, slots@.len() as int, m);
            assert(all_pure(rest@, m));
            assert(all_pure(payload@, m));
            lemma_lits(dv, arbitrary(), arbitrary());
            assert(all_pure(defs@, m));
            lemma_option_out_pure(tag, payload@, defs@, out@, m);
        }
        assert forall|env: Env, ls: Seq<Value>, v: SVal|
            fits_s(xty(*_parent), sty(*_st)) && #[trigger] denotes(slots@, env, ls, v, xty(*_parent), enums@) implies store_ok(
            cond,
            out@,
            env,
            ls,
            v,
            sty(*_st),
            enums@,
        ) by {
            let sv = slot_vals(slots@, env, ls);
            lemma_clean_pure(slots@, env, ls);
            let m = ls.len();
            lemma_sub_pure(slots@, 1, slots@.len() as int, m);
            assert(all_pure(rest@, m));
            lemma_lits(dv, env, ls);
            assert(eval_l(tag, env, ls) == Ok::<Value, ErrKind>(sv[0]));
            assert(pure_below(tag, m));
            match v {
                SVal::Some(w) => {
                    lemma_clean_sub(slots@, env, ls, 1, slots@.len() as int);
                    assert(sv.subrange(1, sv.len() as int) =~= sv.drop_first());
                    assert(denotes(rest@, env, ls, *w, xty(*x), enums@));
                    assert(store_ok(c, payload@, env, ls, *w, sty(*inner), enums@));
                    lemma_option_out(tag, payload@, defs@, out@, env, ls, true);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*_st), enums@));
                },
                _ => {
                    assert(all_pure(payload@, m));
                    lemma_option_out(tag, payload@, defs@, out@, env, ls, false);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*_st), enums@));
                },
            }
        }
    }
    proof {
        assert forall|tv: TyEnv, lt: Seq<ETy>|
            fits_s(xty(*_parent), sty(*_st)) && wf_stype(sty(*_st), enums@) && small(sty(*_st)) && tv.enums == enums@
                && #[trigger] typed(slots@, xetys(xty(*_parent), enums@), tv, lt) implies has_ty(cond, tv, lt, ETy::Bool)
            && typed(out@, xetys(xty(*_parent), enums@), tv, lt) by {
            let ys = xetys(xty(*x), enums@);
            assert(xty(*_parent) == XTy::Option(Box::new(xty(*x))));
            assert(sty(*_st) == STy::Option(Box::new(sty(*inner))));
            assert(fits_s(xty(*x), sty(*inner)));
            assert(wf_stype(sty(*inner), enums@) && small(sty(*inner)));
            assert(xetys(xty(*_parent), enums@) == seq![ETy::Bool] + ys);
            assert((seq![ETy::Bool] + ys)[0] == ETy::Bool);
            assert(has_ty(slots@[0], tv, lt, (seq![ETy::Bool] + ys)[0]));
            lemma_typed_sub(slots@, seq![ETy::Bool] + ys, tv, lt, 1, slots@.len() as int);
            assert((seq![ETy::Bool] + ys).subrange(1, slots@.len() as int) =~= ys);
            assert(rest@ =~= slots@.subrange(1, slots@.len() as int));
            assert(typed(rest@, ys, tv, lt));
            assert(has_ty(c, tv, lt, ETy::Bool) && typed(payload@, ys, tv, lt));
            lemma_defaults_typed(sty(*inner), tv, lt);
            lemma_fits_etys(xty(*x), sty(*inner), enums@);
            assert(typed(defs@, ys, tv, lt));
            assert forall|j: int| 0 <= j < out@.len() implies #[trigger] has_ty(out@[j], tv, lt, (seq![ETy::Bool] + ys)[j]) by {
                if j > 0 {
                    assert(out@[1 + (j - 1)] == ite_s(tag, payload@[j - 1], defs@[j - 1]));
                    assert(j - 1 < payload@.len());
                    assert(has_ty(payload@[j - 1], tv, lt, ys[j - 1]));
                    assert(has_ty(defs@[j - 1], tv, lt, ys[j - 1]));
                }
            }
        }
    }
    Some((cond, out))
}

#[verifier::spinoff_prover]
pub(crate) fn store_parts(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r:
    Option<(Expr, Vec<Expr>)>)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r matches Some((c, out)) ==> store_parts_spec(xtys(xs@), slots@, stys(ts@), enums@, c, out@),
        fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(xtys(xs@), enums@)
            && xwidth_sum(xtys(xs@), enums@) <= lim() ==> (r is Some && r->Some_0.1@.len() == width_sum(stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let ghost pre = fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(
        xtys(xs@),
        enums@,
    ) && xwidth_sum(xtys(xs@), enums@) <= lim();
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_fits_all(xtys(xs@), stys(ts@));
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
    }
    let parts = split(xs, slots, enums)?;
    if xs.len() != ts.len() {
        return None;
    }
    let n = xs.len();
    let mut conds: Vec<Expr> = Vec::new();
    let mut out: Vec<Expr> = Vec::new();
    let ghost mut outs: Seq<Seq<Expr>> = Seq::empty();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n == xs@.len(),
            n == ts@.len(),
            n == parts@.len(),
            i <= n,
            conds@.len() == i,
            outs.len() == i,
            out@ == concat(outs),
            forall|k: int|
                0 <= k < i ==> #[trigger] store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]),
            forall|k: int| 0 <= k < xs@.len() ==> #[trigger] split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@),
            xtys(xs@).len() == n,
            stys(ts@).len() == n,
            forall|k: int| 0 <= k < n ==> #[trigger] xtys(xs@)[k] == xty(xs@[k]),
            forall|k: int| 0 <= k < n ==> #[trigger] stys(ts@)[k] == sty(ts@[k]),
            pre == (fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(
                xtys(xs@),
                enums@,
            ) && xwidth_sum(xtys(xs@), enums@) <= lim()),
            pre ==> out@.len() == width_sum(stys(ts@).take(i as int), enums@),
            pre ==> forall|k: int| 0 <= k < n ==> #[trigger] fits_s(xtys(xs@)[k], stys(ts@)[k]),
            pre ==> lim_xs(xtys(xs@), enums@),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
            assert(split_ok(parts@[i as int]@, slots@, xtys(xs@), i as int, enums@));
            if pre {
                lemma_lim_xs_at(xtys(xs@), enums@, i as int);
                assert(fits_s(xtys(xs@)[i as int], stys(ts@)[i as int]));
                assert(fits_s(xty(xs@[i as int]), sty(ts@[i as int])));
                assert(lim_x(xty(xs@[i as int]), enums@));
                assert(parts@[i as int]@.len() == xwidth(xty(xs@[i as int]), enums@));
            }
            let w = stys(ts@);
            assert(w.take(i + 1).drop_last() =~= w.take(i as int));
            assert(w.take(i + 1).last() == w[i as int]);
        }
        let (c, s) = store(&xs[i], &parts[i], &ts[i], enums)?;
        conds.push(c);
        extend(&mut out, &s);
        proof {
            lemma_concat_push(outs, s@);
            outs = outs.push(s@);
            assert forall|k: int|
                0 <= k < i + 1 implies #[trigger] store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]) by {
                if k < i {
                }
            }
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(n as int) =~= stys(ts@));
    }
    let c = all_of(&conds);
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(c, m) && all_pure(out@, m) by {
            assert forall|k: int| 0 <= k < n implies #[trigger] all_pure(outs[k], m) && pure_below(conds@[k], m) by {
                assert(split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@));
                lemma_sub_pure(slots@, xoff(xtys(xs@), k, enums@), xoff(xtys(xs@), k, enums@) + xwidth(xtys(xs@)[k], enums@), m);
                assert(all_pure(parts@[k]@, m));
                assert(store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]));
            }
            assert forall|k: int| 0 <= k < conds@.len() implies pure_below(#[trigger] conds@[k], m) by {
                assert(all_pure(outs[k], m) && pure_below(conds@[k], m));
            }
            lemma_tree_pure(conds@, bool_lit(true), Join::And, m);
            assert forall|k: int| 0 <= k < outs.len() implies #[trigger] all_pure(outs[k], m) by {
                assert(all_pure(outs[k], m) && pure_below(conds@[k], m));
            }
            lemma_concat_pure(outs, m);
        }
        assert forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
            fits_all_s(xtys(xs@), stys(ts@)) && clean(slots@, env, ls) && #[trigger] models_seq(
                slot_vals(slots@, env, ls),
                vs,
                xtys(xs@),
                enums@,
            ) implies {
            &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(members(vs, stys(ts@), enums@)))
            &&& clean(out@, env, ls)
            &&& slot_vals(out@, env, ls) == enc_seq(vs, stys(ts@), enums@)
        } by {
            let xt = xtys(xs@);
            let st = stys(ts@);
            lemma_fits_all(xt, st);
            assert forall|k: int| 0 <= k < n implies #[trigger] store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@) by {
                lemma_denotes_part(slots@, env, ls, vs, xt, k, enums@);
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                assert(fits_s(xt[k], st[k]));
                assert(store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]));
            }
            assert forall|k: int| 0 <= k < conds@.len() implies bool_val(#[trigger] eval_l(conds@[k], env, ls)) by {
                assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
            }
            lemma_all_of(conds@, env, ls);
            lemma_members(vs, st, enums@);
            lemma_models_seq_parts(slot_vals(slots@, env, ls), vs, xt, enums@);
            if all_true(conds@, env, ls) {
                assert forall|k: int| 0 <= k < st.len() implies #[trigger] member(vs[k], st[k], enums@) by {
                    assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
                    assert(eval_l(conds@[k], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
                }
            }
            if members(vs, st, enums@) {
                assert forall|k: int| 0 <= k < conds@.len() implies #[trigger] eval_l(conds@[k], env, ls) == Ok::<
                    Value,
                    ErrKind,
                >(Value::Bool(true)) by {
                    assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
                    assert(member(vs[k], st[k], enums@));
                }
            }
            assert forall|k: int| 0 <= k < outs.len() implies #[trigger] clean(outs[k], env, ls) && slot_vals(outs[k], env, ls)
                == enc(vs[k], st[k], enums@) by {
                assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
            }
            lemma_concat_enc(outs, vs, st, env, ls, enums@);
        }
        assert forall|tv: TyEnv, lt: Seq<ETy>|
            fits_all_s(xtys(xs@), stys(ts@)) && wf_stypes(stys(ts@), enums@) && smalls(stys(ts@)) && tv.enums == enums@
                && #[trigger] typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt) implies has_ty(c, tv, lt, ETy::Bool)
            && typed(out@, xetys_seq(xtys(xs@), enums@), tv, lt) by {
            let xt = xtys(xs@);
            let st = stys(ts@);
            lemma_fits_all(xt, st);
            let yss = Seq::new(n as nat, |k: int| xetys(xt[k], enums@));
            assert forall|k: int| 0 <= k < n implies #[trigger] typed(outs[k], yss[k], tv, lt) && has_ty(conds@[k], tv, lt, ETy::Bool) by {
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                crate::encoding::lemma_wf_stypes_at(st, enums@, k);
                lemma_smalls_at(st, k);
                lemma_xetys_part(xt, k, enums@);
                lemma_typed_sub(slots@, xetys_seq(xt, enums@), tv, lt, xoff(xt, k, enums@), xoff(xt, k, enums@) + xwidth(xt[k], enums@));
                assert(typed(parts@[k]@, xetys(xt[k], enums@), tv, lt));
                assert(fits_s(xt[k], st[k]));
                assert(store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]));
            }
            assert forall|k: int| 0 <= k < conds@.len() implies #[trigger] has_ty(conds@[k], tv, lt, ETy::Bool) by {
                assert(typed(outs[k], yss[k], tv, lt) && has_ty(conds@[k], tv, lt, ETy::Bool));
            }
            lemma_tree_typed(conds@, bool_lit(true), Join::And, tv, lt, ETy::Bool);
            assert forall|k: int| 0 <= k < outs.len() implies #[trigger] typed(outs[k], yss[k], tv, lt) by {
                assert(typed(outs[k], yss[k], tv, lt) && has_ty(conds@[k], tv, lt, ETy::Bool));
            }
            lemma_concat_typed(outs, yss, tv, lt);
            lemma_econcat_xetys(xt, enums@);
            assert(yss =~= Seq::new(xt.len(), |k: int| xetys(xt[k], enums@)));
        }
    }
    Some((c, out))
}

/// 要素の型 `st` での番号。値が型に属するときに限って評価する。
pub fn rank_expr(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(e) ==> rank_spec(xty(*t), slots@, sty(*st), enums@, e),
        fits_s(xty(*t), sty(*st)) && slots@.len() == xwidth(xty(*t), enums@) && lim_x(xty(*t), enums@) && keys(
            sty(*st),
            enums@,
        ) is Some ==> r is Some,
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Int, SType::Int(lo, _)) => {
            if slots.len() == 0 {
                return None;
            }
            let e = offset_rank(copy_expr(&slots[0]), *lo);
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                    assert(xty(*t) == XTy::Int);
                    assert(xetys(XTy::Int, enums@) =~= seq![ETy::Int]);
                    assert(has_ty(slots@[0], tv, lt, xetys(XTy::Int, enums@)[0]));
                    assert(has_ty(Expr::Const(Value::Int(*lo)), tv, lt, ETy::Int));
                }
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                    assert(pure_below(int_lit(*lo), n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(sv[0]));
                }
            }
            Some(e)
        },
        (XType::Bool, _) | (XType::Enum(_), _) => {
            if slots.len() == 0 {
                return None;
            }
            let e = Expr::Code(Box::new(copy_expr(&slots[0])));
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                    assert(xetys(xty(*t), enums@).len() == 1);
                    assert(has_ty(slots@[0], tv, lt, xetys(xty(*t), enums@)[0]));
                }
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(sv[0]));
                }
            }
            Some(e)
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let e = mixed(t, xs, ts, slots, enums)?;
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                    assert(typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some(e)
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let e = mixed(t, xs, ts, slots, enums)?;
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                    assert(typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some(e)
        },
        (XType::Option(x), SType::Option(inner)) => {
            if slots.len() == 0 {
                return None;
            }
            let rest = sub_exprs(slots, 1, slots.len());
            let payload = rank_expr(x, &rest, inner, enums)?;
            let tag = copy_expr(&slots[0]);
            let e = option_rank(copy_expr(&tag), copy_expr(&payload));
            proof {
                assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                    let ys = xetys(xty(**x), enums@);
                    assert(xty(*t) == XTy::Option(Box::new(xty(**x))));
                    assert(xetys(xty(*t), enums@) == seq![ETy::Bool] + ys);
                    assert((seq![ETy::Bool] + ys)[0] == ETy::Bool);
                    assert(has_ty(slots@[0], tv, lt, (seq![ETy::Bool] + ys)[0]));
                    lemma_typed_sub(slots@, seq![ETy::Bool] + ys, tv, lt, 1, slots@.len() as int);
                    assert((seq![ETy::Bool] + ys).subrange(1, slots@.len() as int) =~= ys);
                    assert(rest@ =~= slots@.subrange(1, slots@.len() as int));
                    assert(typed(rest@, ys, tv, lt));
                    assert(has_ty(payload, tv, lt, ETy::Int));
                    assert(has_ty(Expr::Const(Value::Int(1)), tv, lt, ETy::Int));
                    assert(has_ty(Expr::Const(Value::Int(0)), tv, lt, ETy::Int));
                    assert(has_ty(Expr::Bin(BinOp::Add, Box::new(Expr::Const(Value::Int(1))), Box::new(payload)), tv, lt, ETy::Int));
                }
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                    lemma_sub_pure(slots@, 1, slots@.len() as int, n);
                    assert(all_pure(rest@, n));
                    assert(pure_below(payload, n));
                    assert(pure_below(int_lit(1), n));
                    assert(pure_below(int_lit(0), n));
                    assert(pure_below(Expr::Bin(BinOp::Add, Box::new(int_lit(1)), Box::new(payload)), n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(tag, env, ls) == Ok::<Value, ErrKind>(sv[0]));
                    match v {
                        SVal::Some(w) => {
                            lemma_clean_sub(slots@, env, ls, 1, slots@.len() as int);
                            assert(sv.subrange(1, sv.len() as int) =~= sv.drop_first());
                            assert(denotes(rest@, env, ls, *w, xty(**x), enums@));
                            assert(keys(sty(**inner), enums@) is Some);
                            lemma_rank_in_domain(*w, sty(**inner), enums@);
                            assert(eval_l(payload, env, ls) == Ok::<Value, ErrKind>(
                                Value::Int(rank(*w, sty(**inner), enums@) as i64),
                            ));
                        },
                        _ => {},
                    }
                }
            }
            Some(e)
        },
        _ => {
            let e = ci(0);
            proof {
                assert(has_ty(e, arbitrary(), arbitrary(), ETy::Int));
            }
            Some(e)
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) fn mixed(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<
    Expr,
>)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r matches Some(e) ==> mixed_spec(xtys(xs@), slots@, stys(ts@), enums@, e),
        fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(xtys(xs@), enums@)
            && xwidth_sum(xtys(xs@), enums@) <= lim() && keys_product(stys(ts@), enums@) is Some ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(
        xtys(xs@),
        enums@,
    ) && xwidth_sum(xtys(xs@), enums@) <= lim() && keys_product(stys(ts@), enums@) is Some;
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_fits_all(xtys(xs@), stys(ts@));
    }
    let parts = split(xs, slots, enums)?;
    if xs.len() != ts.len() {
        return None;
    }
    let n = xs.len();
    let mut ranks: Vec<(Expr, i64)> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n == xs@.len(),
            n == ts@.len(),
            n == parts@.len(),
            i <= n,
            ranks@.len() == i,
            forall|k: int|
                0 <= k < i ==> #[trigger] rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0) && keys(
                    sty(ts@[k]),
                    enums@,
                ) is Some && ranks@[k].1 as int == radix(sty(ts@[k]), enums@),
            forall|k: int| 0 <= k < xs@.len() ==> #[trigger] split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@),
            xtys(xs@).len() == n,
            stys(ts@).len() == n,
            forall|k: int| 0 <= k < n ==> #[trigger] xtys(xs@)[k] == xty(xs@[k]),
            forall|k: int| 0 <= k < n ==> #[trigger] stys(ts@)[k] == sty(ts@[k]),
            pre == (fits_all_s(xtys(xs@), stys(ts@)) && slots@.len() == xwidth_sum(xtys(xs@), enums@) && lim_xs(
                xtys(xs@),
                enums@,
            ) && xwidth_sum(xtys(xs@), enums@) <= lim() && keys_product(stys(ts@), enums@) is Some),
            pre ==> forall|k: int| 0 <= k < n ==> #[trigger] fits_s(xtys(xs@)[k], stys(ts@)[k]),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
            assert(split_ok(parts@[i as int]@, slots@, xtys(xs@), i as int, enums@));
            if pre {
                lemma_lim_xs_at(xtys(xs@), enums@, i as int);
                lemma_keys_product_prefix(stys(ts@), i as int, enums@);
                assert(fits_s(xtys(xs@)[i as int], stys(ts@)[i as int]));
                assert(keys(stys(ts@)[i as int], enums@) is Some);
            }
        }
        let k = rank_expr(&xs[i], &parts[i], &ts[i], enums)?;
        let base = match keys_exec(&ts[i], enums) {
            Some(k) => k as i64,
            None => return None,
        };
        let ghost r0 = ranks@;
        ranks.push((k, base));
        proof {
            assert(ranks@[i as int] == (k, base));
            assert(rank_spec(xty(xs@[i as int]), parts@[i as int]@, sty(ts@[i as int]), enums@, k));
            assert forall|j: int|
                0 <= j < i + 1 implies #[trigger] rank_spec(xty(xs@[j]), parts@[j]@, sty(ts@[j]), enums@, ranks@[j].0)
                && keys(sty(ts@[j]), enums@) is Some && ranks@[j].1 as int == radix(sty(ts@[j]), enums@) by {
                if j < i {
                    assert(ranks@[j] == r0[j]);
                }
            }
        }
        i += 1;
    }
    let e = mixed_rank_expr(&ranks);
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        assert forall|tv: TyEnv, lt: Seq<ETy>| tv.enums == enums@ && #[trigger] typed(slots@, xetys_seq(xtys(xs@), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
            let xt = xtys(xs@);
            assert forall|k: int| 0 <= k < ranks@.len() implies #[trigger] has_ty(ranks@[k].0, tv, lt, ETy::Int) by {
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                lemma_xetys_part(xt, k, enums@);
                lemma_typed_sub(slots@, xetys_seq(xt, enums@), tv, lt, xoff(xt, k, enums@), xoff(xt, k, enums@) + xwidth(xt[k], enums@));
                assert(typed(parts@[k]@, xetys(xt[k], enums@), tv, lt));
                assert(rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0));
            }
            assert(crate::ranking::ranks_int(ranks@, tv, lt));
        }
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(e, m) by {
            assert forall|k: int| 0 <= k < ranks@.len() implies pure_below(#[trigger] ranks@[k].0, m) by {
                assert(split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@));
                lemma_sub_pure(slots@, xoff(xtys(xs@), k, enums@), xoff(xtys(xs@), k, enums@) + xwidth(xtys(xs@)[k], enums@), m);
                assert(all_pure(parts@[k]@, m));
                assert(rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0));
            }
            assert(ranks_pure(ranks@, m));
        }
        assert forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
            fits_all_s(xtys(xs@), stys(ts@)) && clean(slots@, env, ls) && #[trigger] models_seq(
                slot_vals(slots@, env, ls),
                vs,
                xtys(xs@),
                enums@,
            ) && members(vs, stys(ts@), enums@) && keys_product(stys(ts@), enums@) is Some implies eval_l(e, env, ls)
            == Ok::<Value, ErrKind>(Value::Int(rank_seq(vs, stys(ts@), enums@) as i64)) by {
            let xt = xtys(xs@);
            let st = stys(ts@);
            lemma_fits_all(xt, st);
            lemma_members(vs, st, enums@);
            lemma_models_seq_parts(slot_vals(slots@, env, ls), vs, xt, enums@);
            assert forall|k: int|
                0 <= k < st.len() implies #[trigger] eval_l(ranks@[k].0, env, ls) == Ok::<Value, ErrKind>(
                Value::Int(rank(vs[k], st[k], enums@) as i64),
            ) && ranks@[k].1 as int == radix(st[k], enums@) by {
                lemma_denotes_part(slots@, env, ls, vs, xt, k, enums@);
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                assert(fits_s(xt[k], st[k]));
                assert(member(vs[k], st[k], enums@));
                assert(rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0));
            }
            lemma_mixed_eval(ranks@, vs, st, env, ls, n as nat, enums@);
            assert(vs.take(n as int) =~= vs);
            assert(st.take(n as int) =~= st);
        }
    }
    Some(e)
}

/// 値が要素の型に属すれば、その番号。属さなければ -1。
pub fn rank_or_neg(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(e) ==> rank_neg_spec(xty(*t), slots@, sty(*st), enums@, e),
        fits_s(xty(*t), sty(*st)) && slots@.len() == xwidth(xty(*t), enums@) && lim_x(xty(*t), enums@) && keys(
            sty(*st),
            enums@,
        ) is Some ==> r is Some,
{
    let (in_dom, _) = store(t, slots, st, enums)?;
    let r = rank_expr(t, slots, st, enums)?;
    if is_bool_lit(&in_dom, true) {
        proof {
            assert forall|tv: TyEnv, lt: Seq<ETy>|
                fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(r, tv, lt, ETy::Int) by {
            }
            assert forall|env: Env, ls: Seq<Value>, v: SVal|
                fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && keys(
                    sty(*st),
                    enums@,
                ) is Some implies eval_l(r, env, ls) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums@) {
                rank(v, sty(*st), enums@) as i64
            } else {
                -1i64
            })) by {
                assert(eval_l(in_dom, env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
        }
        Some(r)
    } else {
        let e = ite(copy_expr(&in_dom), copy_expr(&r), ci(-1));
        proof {
            assert forall|tv: TyEnv, lt: Seq<ETy>|
                fits_s(xty(*t), sty(*st)) && wf_stype(sty(*st), enums@) && small(sty(*st)) && tv.enums == enums@ && #[trigger] typed(slots@, xetys(xty(*t), enums@), tv, lt) implies has_ty(e, tv, lt, ETy::Int) by {
                assert(has_ty(in_dom, tv, lt, ETy::Bool));
                assert(has_ty(r, tv, lt, ETy::Int));
                assert(has_ty(int_lit(-1i64), tv, lt, ETy::Int));
            }
            assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(e, m) by {
                assert(pure_below(in_dom, m));
                assert(pure_below(r, m));
                assert(pure_below(int_lit(-1i64), m));
            }
            assert forall|env: Env, ls: Seq<Value>, v: SVal|
                fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && keys(
                    sty(*st),
                    enums@,
                ) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums@) {
                rank(v, sty(*st), enums@) as i64
            } else {
                -1i64
            })) by {
                assert(eval_l(in_dom, env, ls) == Ok::<Value, ErrKind>(Value::Bool(member(v, sty(*st), enums@))));
                assert(eval_l(int_lit(-1i64), env, ls) == Ok::<Value, ErrKind>(Value::Int(-1i64)));
            }
        }
        Some(e)
    }
}

/// Optionの正規形のスロットの値。`tag` が `on` のとき、真なら値のスロット、偽なら既定値のスロットを選ぶ。
pub proof fn lemma_option_out(tag: Expr, payload: Seq<Expr>, defs: Seq<Expr>, out: Seq<Expr>, env: Env, ls: Seq<Value>, on: bool)
    requires
        eval_l(tag, env, ls) == Ok::<Value, ErrKind>(Value::Bool(on)),
        pure_below(tag, ls.len()),
        on ==> clean(payload, env, ls),
        all_pure(payload, ls.len()),
        clean(defs, env, ls),
        payload.len() == defs.len(),
        out.len() == 1 + defs.len(),
        out[0] == tag,
        forall|j: int| 0 <= j < defs.len() ==> #[trigger] out[1 + j] == ite_s(tag, payload[j], defs[j]),
    ensures
        clean(out, env, ls),
        slot_vals(out, env, ls) == seq![Value::Bool(on)] + if on {
            slot_vals(payload, env, ls)
        } else {
            slot_vals(defs, env, ls)
        },
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], ls.len()) && eval_l(out[j], env, ls)
        == Ok::<Value, ErrKind>((seq![Value::Bool(on)] + if on {
        slot_vals(payload, env, ls)
    } else {
        slot_vals(defs, env, ls)
    })[j]) by {
        if j > 0 {
            assert(out[1 + (j - 1)] == ite_s(tag, payload[j - 1], defs[j - 1]));
            assert(pure_below(payload[j - 1], ls.len()));
            assert(pure_below(defs[j - 1], ls.len()));
            assert(eval_l(defs[j - 1], env, ls) is Ok);
            if on {
                assert(eval_l(payload[j - 1], env, ls) is Ok);
            }
        }
    }
    assert(slot_vals(out, env, ls) =~= seq![Value::Bool(on)] + if on {
        slot_vals(payload, env, ls)
    } else {
        slot_vals(defs, env, ls)
    });
}

/// 値を格納の型の場所に置く条件とスロットの意味。
pub open spec fn store_ok(c: Expr, out: Seq<Expr>, env: Env, ls: Seq<Value>, v: SVal, st: STy, enums: Seq<i64>) -> bool {
    &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(member(v, st, enums)))
    &&& clean(out, env, ls)
    &&& slot_vals(out, env, ls) == enc(v, st, enums)
}

/// [`crate::slot_store::store`] の結果 `(c, out)` の性質。
pub open spec fn store_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, c: Expr, out: Seq<Expr>) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(c, n) && all_pure(out, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        fits_s(t, st) && wf_stype(st, enums) && small(st) && tv.enums == enums && #[trigger] typed(
            slots,
            xetys(t, enums),
            tv,
            lt,
        ) ==> has_ty(c, tv, lt, ETy::Bool) && typed(out, xetys(t, enums), tv, lt)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) ==> store_ok(c, out, env, ls, v, st, enums)
}

/// [`crate::slot_store::store`] の、TupleとRecordの要素の列についての性質。
pub open spec fn store_parts_spec(xs: Seq<XTy>, slots: Seq<Expr>, ts: Seq<STy>, enums: Seq<i64>, c: Expr, out: Seq<Expr>) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(c, n) && all_pure(out, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        fits_all_s(xs, ts) && wf_stypes(ts, enums) && smalls(ts) && tv.enums == enums && #[trigger] typed(
            slots,
            xetys_seq(xs, enums),
            tv,
            lt,
        ) ==> has_ty(c, tv, lt, ETy::Bool) && typed(out, xetys_seq(xs, enums), tv, lt)
    &&& forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
        fits_all_s(xs, ts) && clean(slots, env, ls) && #[trigger] models_seq(slot_vals(slots, env, ls), vs, xs, enums)
            ==> {
            &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(members(vs, ts, enums)))
            &&& clean(out, env, ls)
            &&& slot_vals(out, env, ls) == enc_seq(vs, ts, enums)
        }
}

/// [`crate::slot_store::rank_expr`] の結果 `r` の性質。値が型に属し、型がキーの型なら、番号を表す。
pub open spec fn rank_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && #[trigger] typed(slots, xetys(t, enums), tv, lt) ==> has_ty(r, tv, lt, ETy::Int)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) && member(v, st, enums) && keys(st, enums) is Some
            ==> eval_l(r, env, ls) == Ok::<Value, ErrKind>(Value::Int(rank(v, st, enums) as i64))
}

/// TupleとRecordの要素の列についての、番号の性質。
pub open spec fn mixed_spec(xs: Seq<XTy>, slots: Seq<Expr>, ts: Seq<STy>, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && #[trigger] typed(slots, xetys_seq(xs, enums), tv, lt) ==> has_ty(r, tv, lt, ETy::Int)
    &&& forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
        fits_all_s(xs, ts) && clean(slots, env, ls) && #[trigger] models_seq(slot_vals(slots, env, ls), vs, xs, enums)
            && members(vs, ts, enums) && keys_product(ts, enums) is Some ==> eval_l(r, env, ls) == Ok::<Value, ErrKind>(
            Value::Int(rank_seq(vs, ts, enums) as i64),
        )
}

/// [`crate::slot_store::rank_or_neg`] の結果 `r` の性質。型に属さなければ -1。
pub open spec fn rank_neg_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        fits_s(t, st) && wf_stype(st, enums) && small(st) && tv.enums == enums && #[trigger] typed(
            slots,
            xetys(t, enums),
            tv,
            lt,
        ) ==> has_ty(r, tv, lt, ETy::Int)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) && keys(st, enums) is Some ==> eval_l(r, env, ls)
            == Ok::<Value, ErrKind>(Value::Int(if member(v, st, enums) {
            rank(v, st, enums) as i64
        } else {
            -1i64
        }))
}

/// 値の数の積が `MAX_KEYS` に収まれば、先頭部分の積も収まる。
pub proof fn lemma_keys_product_prefix(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        keys_product(ts, enums) is Some,
        0 <= i <= ts.len(),
    ensures
        keys_product(ts.take(i), enums) is Some,
        i < ts.len() ==> keys(ts[i], enums) is Some,
    decreases ts.len(),
{
    if i == ts.len() {
        assert(ts.take(i) =~= ts);
    } else {
        lemma_keys_product_prefix(ts.drop_last(), i, enums);
        assert(ts.drop_last().take(i) =~= ts.take(i));
        if i < ts.len() - 1 {
            assert(ts.drop_last()[i] == ts[i]);
        }
    }
}

/// 要素の番号の式を混合基数の桁として左から順にたたむと、組の番号になる。
pub proof fn lemma_mixed_eval(
    parts: Seq<(Expr, i64)>,
    vs: Seq<SVal>,
    ts: Seq<STy>,
    env: Env,
    ls: Seq<Value>,
    i: nat,
    enums: Seq<i64>,
)
    requires
        parts.len() == vs.len(),
        vs.len() == ts.len(),
        i <= ts.len(),
        keys_product(ts, enums) is Some,
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] member(vs[k], ts[k], enums),
        forall|k: int|
            0 <= k < ts.len() ==> #[trigger] eval_l(parts[k].0, env, ls) == Ok::<Value, ErrKind>(
                Value::Int(rank(vs[k], ts[k], enums) as i64),
            ) && parts[k].1 as int == radix(ts[k], enums),
    ensures
        0 <= rank_seq(vs.take(i as int), ts.take(i as int), enums) < keys_product(ts.take(i as int), enums)->0,
        mixed_rank_eval(parts, i, env, ls) == Ok::<Value, ErrKind>(
            Value::Int(rank_seq(vs.take(i as int), ts.take(i as int), enums) as i64),
        ),
    decreases i,
{
    lemma_keys_product_prefix(ts, i as int, enums);
    if i == 0 {
        assert(ts.take(0) =~= Seq::<STy>::empty());
    } else {
        let j = i - 1;
        lemma_mixed_eval(parts, vs, ts, env, ls, j as nat, enums);
        lemma_keys_product_prefix(ts, j, enums);
        let v0 = vs.take(j);
        let t0 = ts.take(j);
        let v1 = vs.take(i as int);
        let t1 = ts.take(i as int);
        assert(v1.drop_last() =~= v0);
        assert(t1.drop_last() =~= t0);
        assert(v1.last() == vs[j]);
        assert(t1.last() == ts[j]);
        assert(member(vs[j], ts[j], enums));
        lemma_rank_in_domain(vs[j], ts[j], enums);
        let rs0 = rank_seq(v0, t0, enums);
        let kp0 = keys_product(t0, enums)->0 as int;
        let k = keys(ts[j], enums)->0 as int;
        let r = rank(vs[j], ts[j], enums);
        assert(rank_seq(v1, t1, enums) == rs0 * radix(ts[j], enums) + r);
        assert(radix(ts[j], enums) == k);
        assert(keys_product(t1, enums) == Some((kp0 * k) as nat));
        assert(kp0 * k <= 4096);
        assert(0 <= rs0 * k) by (nonlinear_arith)
            requires
                0 <= rs0,
                0 <= k,
        ;
        assert(rs0 * k + r < kp0 * k) by (nonlinear_arith)
            requires
                0 <= rs0 < kp0,
                0 <= r < k,
        ;
        if i == 1 {
            assert(v0 =~= Seq::<SVal>::empty());
            assert(rs0 == 0);
            assert(0 * k == 0);
        } else {
            assert(rs0 * k <= kp0 * k) by (nonlinear_arith)
                requires
                    0 <= rs0 < kp0,
                    0 <= k,
            ;
        }
    }
}

} // verus!
