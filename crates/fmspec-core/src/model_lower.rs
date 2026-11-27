//! モデル全体の下ろし。
//!
//! [`lower_model`] は、名前を解決したIRのモデル（[`SModel`]）を中核のモデルに下ろす。
//! 定数と初期値の候補は、下ろした式を評価して値にする。
//! 初期状態は、状態変数ごとの候補の符号を整列して重複を除き、その直積から初期条件を満たすものを残す。
//! 下ろしが成功すれば、中核のモデルの安全性は値の上のモデルの安全性と一致する（[`lowers_model`]）。

use crate::canon::{slot_types, slot_types_list};
use crate::encoding::{copy_stype, wf_stype_exec, SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, enc_seq, lemma_stys, lemma_width_pos, member, members, sty, stys, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, wf_stype, wf_stypes, width_sum, XTy};
use crate::equality::small_stype;
#[cfg(verus_keep_ghost)]
use crate::eval::{code_of, eval_l, eval_spec, prop_spec, Env, ErrKind};
use crate::eval::{eval, eval_prop, Ctx};
use crate::expr_build::stype_width;
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_small, lemma_width_sum_prefix, small, smalls};
use crate::lower_ctx::{Constant, Fail, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{layout_at, layouts_at, lemma_slot_tys_len, slot_tys, slot_tys_seq};
use crate::lowering::{lower_prop, lower_stored};
use crate::model::{Action, Contract, Expr, RawModel, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::model_safe::*;
#[cfg(verus_keep_ghost)]
use crate::model_total::{action_typed, const_ctx, consts_match, lemma_const_ctx, lemma_sa_typed};
use crate::model_total::{check_model, lower_action};
#[cfg(verus_keep_ghost)]
use crate::model_total::{lemma_state_ctx, model_typed, out_sty, st_ctx, tys_ok};
#[cfg(verus_keep_ghost)]
use crate::model_wf::{action_at, contract_at, lemma_model_frame, sm_wf, wf_frame};
#[cfg(verus_keep_ghost)]
use crate::preserve::{layouts_ok, lemma_members, stored_result, top_ok};
#[cfg(verus_keep_ghost)]
use crate::semantics::{inv_env, safe, Conditions};
#[cfg(verus_keep_ghost)]
use crate::smodel::user_err;
#[cfg(verus_keep_ghost)]
use crate::smodel::{codes, consts_ok, lemma_code_in, lemma_encode_in, lemma_rel_codes, rel, s_cand};
#[cfg(verus_keep_ghost)]
use crate::smodel::{s_env, s_init, s_init_var, s_prop, s_safe, s_state_tys, styped, type_err};
use crate::smodel::{Fault, LowerError, SModel};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, SEnv};
#[cfg(verus_keep_ghost)]
use crate::step::encode_spec;
use crate::step::{copy_vec, encode, vec_eq};
#[cfg(verus_keep_ghost)]
use crate::total::{cx_wf, ok_s, sctx};
use vstd::prelude::*;

verus! {

/// 初期値の候補の組み合わせのうち、調べる数の上限。
pub const MAX_INITIAL_CANDIDATES: usize = 1 << 20;

/// 写像の1つの式と、置く場所の型（詳細化の検査で、抽象モデルの状態変数の型）。
/// 式は、このモデルの状態だけを参照する文脈（不変条件と同じ文脈）で下ろす。
pub struct SMap {
    pub expr: crate::source::TExpr,
    pub ty: SType,
}

/// 中核のモデル `m` の安全性は、定数の値が `cv` のモデル `sm` の安全性と一致する。
pub open spec fn lowers_model(sm: SModel, m: RawModel) -> bool {
    exists|cv: Seq<SVal>| consts_ok(sm, cv) && forall|c: Conditions| #[trigger] safe(m, c) <==> s_safe(sm, cv, c)
}

// ---- 型の検査と位置 ----

proof fn lemma_wf_all(ts: Seq<STy>, enums: Seq<i64>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> wf_stype(#[trigger] ts[i], enums) && small(ts[i]),
    ensures
        wf_stypes(ts, enums),
        smalls(ts),
    decreases ts.len(),
{
    if ts.len() > 0 {
        let a = ts.drop_last();
        assert forall|i: int| 0 <= i < a.len() implies wf_stype(#[trigger] a[i], enums) && small(a[i]) by {
            assert(a[i] == ts[i]);
        }
        lemma_wf_all(a, enums);
        assert(ts.last() == ts[ts.len() - 1]);
    }
}

/// 型の列が整形式で、Listの長さの上限が小さいことを確かめる。失敗した位置を返す。
fn check_types(ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Result<(), usize>)
    ensures
        r is Ok ==> wf_stypes(stys(ts@), enums@) && smalls(stys(ts@)),
        tys_ok(stys(ts@), enums@) ==> r is Ok,
{
    proof {
        lemma_stys(ts@);
    }
    let ghost ok = tys_ok(stys(ts@), enums@);
    let mut i = 0;
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            forall|j: int| 0 <= j < i ==> wf_stype(#[trigger] stys(ts@)[j], enums@) && small(stys(ts@)[j]),
            ok == tys_ok(stys(ts@), enums@),
        decreases ts.len() - i,
    {
        proof {
            if ok {
                assert(ok_s(stys(ts@)[i as int], enums@));
                lemma_lim_small(stys(ts@)[i as int], enums@);
            }
        }
        if !(wf_stype_exec(&ts[i], enums) && small_stype(&ts[i])) {
            return Err(i);
        }
        i += 1;
    }
    proof {
        lemma_wf_all(stys(ts@), enums@);
    }
    Ok(())
}

/// 型の列の各型の位置。位置は、それより前の型の幅の和である。幅が `usize` に収まらない位置を返す。
fn layouts_of(ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Result<Vec<Layout>, usize>)
    ensures
        r matches Ok(ls) ==> layouts_at(ls@, stys(ts@), enums@),
        tys_ok(stys(ts@), enums@) ==> r is Ok,
{
    let ghost ok = tys_ok(stys(ts@), enums@);
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
    }
    let mut ls: Vec<Layout> = Vec::new();
    let mut off: usize = 0;
    let mut i = 0;
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            ls@.len() == i,
            off == width_sum(stys(ts@).take(i as int), enums@),
            forall|j: int| 0 <= j < i ==> #[trigger] layout_at(ls@[j], stys(ts@), j, enums@),
            ok == tys_ok(stys(ts@), enums@),
        decreases ts.len() - i,
    {
        proof {
            if ok {
                let xs = stys(ts@);
                assert(ok_s(xs[i as int], enums@));
                assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
                assert(xs.take(i + 1).last() == xs[i as int]);
                lemma_width_sum_prefix(xs, enums@, i + 1);
            }
        }
        let w = match stype_width(&ts[i], enums) {
            Some(w) => w,
            None => return Err(i),
        };
        ls.push(Layout { ty: copy_stype(&ts[i]), offset: off });
        let next = match off.checked_add(w) {
            Some(n) => n,
            None => return Err(i),
        };
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        off = next;
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    Ok(ls)
}

// ---- 定数の式の評価 ----

/// 状態も引数もない環境。
pub open spec fn empty_env() -> Env {
    Env {
        st_tys: Seq::empty(),
        arg_tys: Seq::empty(),
        pre: Seq::empty(),
        args: Seq::empty(),
        post: Seq::empty(),
        out: None,
    }
}

/// スロットの式 `out` の値は `vals` で、スロットの型 `tys` の符号は `cs` である。
pub open spec fn slots_eval(out: Seq<Expr>, tys: Seq<Type>, enums: Seq<i64>, vals: Seq<Value>, cs: Seq<i64>) -> bool {
    &&& out.len() == tys.len()
    &&& vals.len() == out.len()
    &&& cs.len() == out.len()
    &&& forall|j: int|
        0 <= j < out.len() ==> #[trigger] eval_spec(out[j], empty_env()) == Ok::<Value, ErrKind>(vals[j]) && encode_spec(
            enums,
            tys[j],
            vals[j],
        ) == Ok::<i64, ErrKind>(cs[j])
}

/// スロットの式を空の環境で評価し、スロットの型の符号にする。
fn eval_slots(out: &Vec<Expr>, tys: &Vec<Type>, enums: &Vec<i64>) -> (r: Result<(Vec<Value>, Vec<i64>), Fault>)
    ensures
        r matches Ok((vals, cs)) ==> slots_eval(out@, tys@, enums@, vals@, cs@),
        out@.len() == tys@.len() ==> !(r matches Err(Fault::Lower)),
{
    if out.len() != tys.len() {
        return Err(Fault::Lower);
    }
    let none_t: Vec<Type> = Vec::new();
    let none_v: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &none_t, arg_tys: &none_t, pre: &none_v, args: &none_v, post: &none_v, out: None };
    proof {
        assert(ctx@ =~= empty_env());
    }
    let mut vals: Vec<Value> = Vec::new();
    let mut cs: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < out.len()
        invariant
            j <= out@.len(),
            out@.len() == tys@.len(),
            ctx@ == empty_env(),
            vals@.len() == j,
            cs@.len() == j,
            forall|k: int|
                0 <= k < j ==> #[trigger] eval_spec(out@[k], empty_env()) == Ok::<Value, ErrKind>(vals@[k]) && encode_spec(
                    enums@,
                    tys@[k],
                    vals@[k],
                ) == Ok::<i64, ErrKind>(cs@[k]),
        decreases out@.len() - j,
    {
        let v = match eval(&out[j], &ctx) {
            Ok(v) => v,
            Err(k) => return Err(Fault::Eval(k)),
        };
        let c = match encode(enums, &tys[j], &v) {
            Ok(c) => c,
            Err(k) => return Err(Fault::Eval(k)),
        };
        vals.push(v);
        cs.push(c);
        j += 1;
    }
    Ok((vals, cs))
}

/// 評価したスロットがどれもスロットの型の値なら、値の上の評価は型に属する値で、スロットはその符号化である。
proof fn lemma_stored_val(
    src: Result<SVal, ErrKind>,
    out: Seq<Expr>,
    t: STy,
    enums: Seq<i64>,
    vals: Seq<Value>,
    cs: Seq<i64>,
)
    requires
        stored_result(src, out, empty_env(), Seq::empty(), t, enums),
        slots_eval(out, slot_tys(t, enums), enums, vals, cs),
        out.len() >= 1,
    ensures
        src is Ok,
        member(src->Ok_0, t, enums),
        enc(src->Ok_0, t, enums) == vals,
        cs == codes(vals),
{
    match src {
        Err(k) => {
            assert(eval_l(out[0], empty_env(), Seq::empty()) == Err::<Value, ErrKind>(k));
            assert(eval_spec(out[0], empty_env()) == Ok::<Value, ErrKind>(vals[0]));
        },
        Ok(v) => {
            let e = enc(v, t, enums);
            let tys = slot_tys(t, enums);
            lemma_slot_tys_len(t, enums);
            assert forall|j: int| 0 <= j < out.len() implies #[trigger] e[j] == vals[j] && in_slot_at(tys, vals, j, enums)
                && cs[j] == code_of(vals[j]) by {
                assert(eval_l(out[j], empty_env(), Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                assert(eval_spec(out[j], empty_env()) == Ok::<Value, ErrKind>(vals[j]));
                lemma_encode_in(tys[j], vals[j], enums);
                lemma_code_in(tys[j], vals[j], enums);
            }
            assert(e =~= vals);
            assert(cs =~= codes(vals));
            assert(crate::lower_types::in_slots(e, tys, enums));
        },
    }
}

spec fn in_slot_at(tys: Seq<Type>, vals: Seq<Value>, j: int, enums: Seq<i64>) -> bool {
    crate::lower_types::in_slot(tys[j], vals[j], enums)
}

/// 型 `t` の式を空の環境で評価する。値を `(slots, codes)` で返す。
fn eval_stored(e: &crate::source::TExpr, cx: &LowerCtx, t: &SType) -> (r: Result<(Vec<Value>, Vec<i64>), Fault>)
    ensures
        r matches Ok((vals, cs)) ==> forall|se: SEnv| #[trigger]
            top_ok(*cx, empty_env(), se, Seq::empty(), 0) ==> {
                let src = eval_src(*e, se, Seq::empty());
                &&& src is Ok
                &&& member(src->Ok_0, sty(*t), cx.enums@)
                &&& enc(src->Ok_0, sty(*t), cx.enums@) == vals@
                &&& cs@ == codes(vals@)
            },
        cx_wf(*cx) && styped(*e, sctx(*cx), to_xty(sty(*t))) && ok_s(sty(*t), cx.enums@) ==> !(r matches Err(
            Fault::Lower,
        )),
{
    let ghost pre = cx_wf(*cx) && styped(*e, sctx(*cx), to_xty(sty(*t))) && ok_s(sty(*t), cx.enums@);
    let out = match lower_stored(e, cx, t, 0) {
        Ok(o) => o,
        Err(Fail::Depth) => return Err(Fault::Depth),
        Err(Fail::Type) => return Err(Fault::Lower),
    };
    proof {
        if pre {
            lemma_width_pos(sty(*t), cx.enums@);
            lemma_slot_tys_len(sty(*t), cx.enums@);
        }
    }
    if out.len() == 0 {
        return Err(Fault::Lower);
    }
    let mut tys: Vec<Type> = Vec::new();
    slot_types(t, &cx.enums, &mut tys);
    proof {
        assert(tys@ =~= slot_tys(sty(*t), cx.enums@));
    }
    let (vals, cs) = eval_slots(&out, &tys, &cx.enums)?;
    proof {
        assert forall|se: SEnv| #[trigger] top_ok(*cx, empty_env(), se, Seq::empty(), 0) implies {
            let src = eval_src(*e, se, Seq::empty());
            &&& src is Ok
            &&& member(src->Ok_0, sty(*t), cx.enums@)
            &&& enc(src->Ok_0, sty(*t), cx.enums@) == vals@
            &&& cs@ == codes(vals@)
        } by {
            assert(se.enums == cx.enums@);
            lemma_stored_val(eval_src(*e, se, Seq::empty()), out@, sty(*t), cx.enums@, vals@, cs@);
        }
    }
    Ok((vals, cs))
}

// ---- 符号の列の集合 ----

/// 列 `vs` は符号の列 `x` を含む。
pub open spec fn has(vs: Seq<Vec<i64>>, x: Seq<i64>) -> bool {
    exists|q: int| 0 <= q < vs.len() && #[trigger] vs[q]@ == x
}

/// 辞書順で `a < b`。
fn lex_lt(a: &Vec<i64>, b: &Vec<i64>) -> bool {
    let mut i = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a.len(),
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
        i += 1;
    }
    a.len() < b.len()
}

/// 辞書順に整列した列 `out` に `x` を加える。同じ列がすでにあれば加えない。
fn insert_sorted(out: &mut Vec<Vec<i64>>, x: Vec<i64>)
    ensures
        forall|y: Seq<i64>| #[trigger] has(final(out)@, y) <==> (has(old(out)@, y) || y == x@),
{
    let ghost o = out@;
    let mut k = 0;
    loop
        invariant
            k <= out@.len(),
            out@ == o,
        decreases out@.len() - k,
    {
        if k >= out.len() || !lex_lt(&out[k], &x) {
            break;
        }
        k += 1;
    }
    if k < out.len() && vec_eq(&out[k], &x) {
        proof {
            assert forall|y: Seq<i64>| #[trigger] has(out@, y) <==> (has(o, y) || y == x@) by {
                if y == x@ {
                    assert(out@[k as int]@ == y);
                }
            }
        }
        return;
    }
    let ghost xv = x@;
    out.insert(k, x);
    proof {
        assert(out@ == o.insert(k as int, out@[k as int]));
        assert(out@[k as int]@ == xv);
        assert forall|y: Seq<i64>| #[trigger] has(out@, y) <==> (has(o, y) || y == xv) by {
            if has(out@, y) {
                let q = choose|q: int| 0 <= q < out@.len() && #[trigger] out@[q]@ == y;
                if q < k {
                    assert(o[q]@ == y);
                } else if q > k {
                    assert(o[q - 1]@ == y);
                }
            }
            if has(o, y) {
                let q = choose|q: int| 0 <= q < o.len() && #[trigger] o[q]@ == y;
                if q < k {
                    assert(out@[q]@ == y);
                } else {
                    assert(out@[q + 1]@ == y);
                }
            }
            if y == xv {
                assert(out@[k as int]@ == y);
            }
        }
    }
}

// ---- 初期値の候補 ----

/// 定数と初期値の候補を下ろす文脈。状態と引数を参照できない。
pub open spec fn init_cx(sm: SModel, cv: Seq<SVal>, cx: LowerCtx) -> bool {
    &&& cx.enums@ == sm.enums@
    &&& cx.states is None
    &&& cx.args@ == Seq::<Layout>::empty()
    &&& !cx.next
    &&& cx.out is None
    &&& consts_rel(cx.consts@, cv, sm.enums@)
}

proof fn lemma_init_top(sm: SModel, cv: Seq<SVal>, cx: LowerCtx)
    requires
        init_cx(sm, cv, cx),
    ensures
        top_ok(cx, empty_env(), s_env(sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None), Seq::empty(), 0),
{
    assert(layouts_ok(cx.args@, Seq::<SVal>::empty(), Seq::<Type>::empty(), Seq::<i64>::empty(), sm.enums@));
}

/// `y` は、状態変数 `i` の初期値の候補の値 `w` の符号である。
pub open spec fn cand_codes(sm: SModel, cv: Seq<SVal>, i: int, w: SVal, y: Seq<i64>) -> bool {
    let t = s_state_tys(sm)[i];
    s_init_var(sm, cv, i, w) && member(w, t, sm.enums@) && y == codes(enc(w, t, sm.enums@))
}

/// 列 `cs` は、状態変数 `i` の初期値の候補の値の符号を過不足なく含む。
pub open spec fn cands_ok(sm: SModel, cv: Seq<SVal>, i: int, cs: Seq<Vec<i64>>) -> bool {
    let t = s_state_tys(sm)[i];
    &&& forall|y: Seq<i64>| #[trigger] has(cs, y) ==> exists|w: SVal| #[trigger] cand_codes(sm, cv, i, w, y)
    &&& forall|w: SVal|
        #[trigger] s_init_var(sm, cv, i, w) ==> member(w, t, sm.enums@) && has(cs, codes(enc(w, t, sm.enums@)))
}

/// 状態変数 `i` の初期値の候補の符号を、辞書順に整列して重複を除いた列。
fn var_cands(sm: &SModel, cx: &LowerCtx, i: usize, Ghost(cv): Ghost<Seq<SVal>>) -> (r: Result<Vec<Vec<i64>>, LowerError>)
    requires
        i < sm.states@.len(),
        i < sm.inits@.len(),
        init_cx(*sm, cv, *cx),
    ensures
        r matches Ok(cs) ==> cands_ok(*sm, cv, i as int, cs@),
        model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len() ==> (r matches Err(
            e,
        ) ==> user_err(e)),
{
    let ghost se = s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None);
    let ghost t = s_state_tys(*sm)[i as int];
    let ghost pre = model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len();
    proof {
        lemma_stys(sm.states@);
        lemma_init_top(*sm, cv, *cx);
        if pre {
            lemma_const_ctx(*sm, cv, *cx);
            assert(ok_s(stys(sm.states@)[i as int], sm.enums@));
        }
    }
    let es = &sm.inits[i];
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut j = 0;
    while j < es.len()
        invariant
            j <= es@.len(),
            i < sm.states@.len(),
            i < sm.inits@.len(),
            *es == sm.inits@[i as int],
            t == sty(sm.states@[i as int]),
            t == s_state_tys(*sm)[i as int],
            top_ok(*cx, empty_env(), se, Seq::empty(), 0),
            se == s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None),
            cx.enums@ == sm.enums@,
            forall|y: Seq<i64>| #[trigger] has(out@, y) ==> exists|w: SVal| #[trigger] cand_codes(*sm, cv, i as int, w, y),
            forall|q: int|
                0 <= q < j ==> {
                    let r = #[trigger] s_cand(*sm, cv, es@[q]);
                    &&& r is Ok
                    &&& member(r->Ok_0, t, sm.enums@)
                    &&& has(out@, codes(enc(r->Ok_0, t, sm.enums@)))
                },
            pre ==> cx_wf(*cx) && sctx(*cx) == const_ctx(*sm, sm.consts@.len() as int) && ok_s(t, sm.enums@),
            pre == (model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len()),
        decreases es@.len() - j,
    {
        proof {
            if pre {
                assert(styped(sm.inits@[i as int]@[j as int], const_ctx(*sm, sm.consts@.len() as int), to_xty(t)));
            }
        }
        let (_vals, cs) = match eval_stored(&es[j], cx, &sm.states[i]) {
            Ok(r) => r,
            Err(f) => return Err(LowerError::Init(i, j, f)),
        };
        let ghost w = s_cand(*sm, cv, es@[j as int])->Ok_0;
        proof {
            assert(s_cand(*sm, cv, es@[j as int]) == eval_src(es@[j as int], se, Seq::empty()));
            assert(s_init_var(*sm, cv, i as int, w));
            assert(cand_codes(*sm, cv, i as int, w, cs@));
        }
        let ghost cv0 = cs@;
        let ghost o = out@;
        insert_sorted(&mut out, cs);
        proof {
            assert(has(out@, cv0));
            assert forall|q: int| 0 <= q < j + 1 implies {
                let r = #[trigger] s_cand(*sm, cv, es@[q]);
                &&& r is Ok
                &&& member(r->Ok_0, t, sm.enums@)
                &&& has(out@, codes(enc(r->Ok_0, t, sm.enums@)))
            } by {
                if q < j {
                    assert(has(o, codes(enc(s_cand(*sm, cv, es@[q])->Ok_0, t, sm.enums@))));
                }
            }
            assert forall|y: Seq<i64>| #[trigger] has(out@, y) implies exists|w: SVal| #[trigger] cand_codes(
                *sm,
                cv,
                i as int,
                w,
                y,
            ) by {
                if has(o, y) {
                } else {
                    assert(cand_codes(*sm, cv, i as int, w, y));
                }
            }
        }
        j += 1;
    }
    proof {
        assert forall|w: SVal| #[trigger] s_init_var(*sm, cv, i as int, w) implies member(w, t, sm.enums@) && has(
            out@,
            codes(enc(w, t, sm.enums@)),
        ) by {
            let q = choose|q: int| 0 <= q < sm.inits@[i as int].len() && #[trigger] s_cand(*sm, cv, sm.inits@[i as int][q])
                == Ok::<SVal, ErrKind>(w);
            assert(s_cand(*sm, cv, es@[q]) is Ok);
        }
    }
    Ok(out)
}

// ---- 候補の直積 ----

/// `ws` は、先頭の `k` 個の状態変数の初期値の候補の値の組である。
pub open spec fn combo(sm: SModel, cv: Seq<SVal>, k: int, ws: Seq<SVal>) -> bool {
    &&& ws.len() == k
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] s_init_var(sm, cv, i, ws[i]) && member(ws[i], s_state_tys(sm)[i], sm.enums@)
}

/// 列 `ps` は、先頭の `k` 個の状態変数の初期値の候補の組の符号を過不足なく含む。
pub open spec fn prod_ok(sm: SModel, cv: Seq<SVal>, k: int, ps: Seq<Vec<i64>>) -> bool {
    let ts = s_state_tys(sm).take(k);
    &&& forall|y: Seq<i64>|
        #[trigger] has(ps, y) ==> exists|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) && y == codes(enc_seq(ws, ts, sm.enums@))
    &&& forall|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) ==> has(ps, codes(enc_seq(ws, ts, sm.enums@)))
}

/// 2つの符号の列をつなげる。
pub open spec fn cat(ps: Seq<Vec<i64>>, cs: Seq<Vec<i64>>, p: int, q: int) -> Seq<i64> {
    ps[p]@ + cs[q]@
}

fn concat(a: &Vec<i64>, b: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        r@ == a@ + b@,
{
    let mut r = copy_vec(a);
    let mut j = 0;
    while j < b.len()
        invariant
            j <= b@.len(),
            r@ == a@ + b@.take(j as int),
        decreases b@.len() - j,
    {
        r.push(b[j]);
        j += 1;
        proof {
            assert(r@ =~= a@ + b@.take(j as int));
        }
    }
    proof {
        assert(b@.take(j as int) =~= b@);
    }
    r
}

/// `ps` の各列と `cs` の各列をつなげた列を、`ps` の順、`cs` の順に並べる。
fn product_step(ps: &Vec<Vec<i64>>, cs: &Vec<Vec<i64>>) -> (r: Vec<Vec<i64>>)
    ensures
        forall|y: Seq<i64>|
            #[trigger] has(r@, y) ==> exists|p: int, q: int|
                0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
        forall|p: int, q: int| 0 <= p < ps@.len() && 0 <= q < cs@.len() ==> has(r@, #[trigger] cat(ps@, cs@, p, q)),
{
    let mut r: Vec<Vec<i64>> = Vec::new();
    let mut p = 0;
    while p < ps.len()
        invariant
            p <= ps@.len(),
            forall|y: Seq<i64>|
                #[trigger] has(r@, y) ==> exists|p: int, q: int|
                    0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
            forall|p0: int, q: int| 0 <= p0 < p && 0 <= q < cs@.len() ==> has(r@, #[trigger] cat(ps@, cs@, p0, q)),
        decreases ps@.len() - p,
    {
        let mut q = 0;
        while q < cs.len()
            invariant
                p < ps@.len(),
                q <= cs@.len(),
                forall|y: Seq<i64>|
                    #[trigger] has(r@, y) ==> exists|p: int, q: int|
                        0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
                forall|p0: int, q0: int|
                    0 <= p0 < p && 0 <= q0 < cs@.len() ==> has(r@, #[trigger] cat(ps@, cs@, p0, q0)),
                forall|q0: int| 0 <= q0 < q ==> has(r@, #[trigger] cat(ps@, cs@, p as int, q0)),
            decreases cs@.len() - q,
        {
            let x = concat(&ps[p], &cs[q]);
            let ghost o = r@;
            r.push(x);
            proof {
                assert(r@[o.len() as int]@ == cat(ps@, cs@, p as int, q as int));
                assert forall|y: Seq<i64>| has(o, y) implies #[trigger] has(r@, y) by {
                    let k = choose|k: int| 0 <= k < o.len() && #[trigger] o[k]@ == y;
                    assert(r@[k]@ == y);
                }
                assert forall|y: Seq<i64>| #[trigger] has(r@, y) implies exists|p: int, q: int|
                    0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q) by {
                    let k = choose|k: int| 0 <= k < r@.len() && #[trigger] r@[k]@ == y;
                    if k < o.len() {
                        assert(o[k]@ == y);
                        assert(has(o, y));
                    }
                }
            }
            q += 1;
        }
        p += 1;
    }
    r
}

pub proof fn lemma_codes_concat(a: Seq<Value>, b: Seq<Value>)
    ensures
        codes(a + b) == codes(a) + codes(b),
{
    assert(codes(a + b) =~= codes(a) + codes(b));
}

/// 候補の組の直積を1つの状態変数だけ延ばす。
proof fn lemma_prod_step(
    sm: SModel,
    cv: Seq<SVal>,
    k: int,
    ps: Seq<Vec<i64>>,
    cs: Seq<Vec<i64>>,
    r: Seq<Vec<i64>>,
)
    requires
        0 <= k < s_state_tys(sm).len(),
        prod_ok(sm, cv, k, ps),
        cands_ok(sm, cv, k, cs),
        forall|y: Seq<i64>|
            #[trigger] has(r, y) ==> exists|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() && y == #[trigger] cat(ps, cs, p, q),
        forall|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() ==> has(r, #[trigger] cat(ps, cs, p, q)),
    ensures
        prod_ok(sm, cv, k + 1, r),
{
    let enums = sm.enums@;
    let all = s_state_tys(sm);
    let ts = all.take(k);
    let ts1 = all.take(k + 1);
    assert(ts1.drop_last() =~= ts);
    assert(ts1.last() == all[k]);
    assert forall|ws: Seq<SVal>| ws.len() == k + 1 implies #[trigger] enc_seq(ws, ts1, enums) == enc_seq(
        ws.drop_last(),
        ts,
        enums,
    ) + enc(ws[k], all[k], enums) by {
        assert(ws.last() == ws[k]);
    }
    assert forall|y: Seq<i64>| #[trigger] has(r, y) implies exists|ws: Seq<SVal>| #[trigger] combo(sm, cv, k + 1, ws) && y
        == codes(enc_seq(ws, ts1, enums)) by {
        let (p, q) = choose|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() && y == #[trigger] cat(ps, cs, p, q);
        assert(has(ps, ps[p]@));
        let ws0 = choose|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) && ps[p]@ == codes(enc_seq(ws, ts, enums));
        assert(has(cs, cs[q]@));
        let w = choose|w: SVal| #[trigger] cand_codes(sm, cv, k, w, cs[q]@);
        let ws = ws0.push(w);
        assert(ws.drop_last() =~= ws0);
        assert forall|i: int| 0 <= i < k + 1 implies #[trigger] s_init_var(sm, cv, i, ws[i]) && member(
            ws[i],
            all[i],
            enums,
        ) by {
            if i < k {
                assert(ws[i] == ws0[i]);
                assert(s_init_var(sm, cv, i, ws0[i]));
            }
        }
        assert(combo(sm, cv, k + 1, ws));
        lemma_codes_concat(enc_seq(ws0, ts, enums), enc(w, all[k], enums));
    }
    assert forall|ws: Seq<SVal>| #[trigger] combo(sm, cv, k + 1, ws) implies has(r, codes(enc_seq(ws, ts1, enums))) by {
        let ws0 = ws.drop_last();
        assert forall|i: int| 0 <= i < k implies #[trigger] s_init_var(sm, cv, i, ws0[i]) && member(ws0[i], all[i], enums) by {
            assert(ws0[i] == ws[i]);
            assert(s_init_var(sm, cv, i, ws[i]));
        }
        assert(combo(sm, cv, k, ws0));
        let p = choose|p: int| 0 <= p < ps.len() && #[trigger] ps[p]@ == codes(enc_seq(ws0, ts, enums));
        assert(s_init_var(sm, cv, k, ws[k]));
        let q = choose|q: int| 0 <= q < cs.len() && #[trigger] cs[q]@ == codes(enc(ws[k], all[k], enums));
        lemma_codes_concat(enc_seq(ws0, ts, enums), enc(ws[k], all[k], enums));
        assert(cat(ps, cs, p, q) == codes(enc_seq(ws, ts1, enums)));
    }
}

// ---- 初期条件 ----

/// 状態 `y` の環境。
pub open spec fn st_env(tys: Seq<Type>, y: Seq<i64>) -> Env {
    Env { st_tys: tys, arg_tys: Seq::empty(), pre: y, args: Seq::empty(), post: Seq::empty(), out: None }
}

/// 状態 `y` は初期条件 `cc` を満たす。
pub open spec fn keep(cc: Option<Expr>, tys: Seq<Type>, y: Seq<i64>) -> bool {
    match cc {
        None => true,
        Some(c) => prop_spec(c, st_env(tys, y)) == Ok::<bool, ErrKind>(true),
    }
}

/// 初期条件を満たす状態だけを、順に残す。評価に失敗すれば、その理由を返す。
fn filter_inits(ps: Vec<Vec<i64>>, cc: &Option<Expr>, tys: &Vec<Type>) -> (r: Result<Vec<Vec<i64>>, Fault>)
    ensures
        r matches Ok(f) ==> forall|y: Seq<i64>| #[trigger] has(f@, y) <==> has(ps@, y) && keep(*cc, tys@, y),
        r matches Err(f) ==> f is Eval,
{
    let c = match cc {
        None => {
            proof {
                assert forall|y: Seq<i64>| #[trigger] has(ps@, y) <==> has(ps@, y) && keep(*cc, tys@, y) by {}
            }
            return Ok(ps);
        },
        Some(c) => c,
    };
    let none_t: Vec<Type> = Vec::new();
    let none_v: Vec<i64> = Vec::new();
    let mut f: Vec<Vec<i64>> = Vec::new();
    let mut p = 0;
    while p < ps.len()
        invariant
            p <= ps@.len(),
            *cc == Some(*c),
            none_t@ == Seq::<Type>::empty(),
            none_v@ == Seq::<i64>::empty(),
            forall|y: Seq<i64>| #[trigger] has(f@, y) ==> has(ps@, y) && keep(*cc, tys@, y),
            forall|p0: int| 0 <= p0 < p && keep(*cc, tys@, ps@[p0]@) ==> has(f@, #[trigger] ps@[p0]@),
        decreases ps@.len() - p,
    {
        let ctx = Ctx { st_tys: tys, arg_tys: &none_t, pre: &ps[p], args: &none_v, post: &none_v, out: None };
        proof {
            assert(ctx@ =~= st_env(tys@, ps@[p as int]@));
        }
        match eval_prop(c, &ctx) {
            Err(k) => return Err(Fault::Eval(k)),
            Ok(false) => {},
            Ok(true) => {
                let ghost o = f@;
                f.push(copy_vec(&ps[p]));
                proof {
                    assert(f@[o.len() as int]@ == ps@[p as int]@);
                    assert(has(ps@, ps@[p as int]@));
                    assert forall|y: Seq<i64>| has(o, y) implies #[trigger] has(f@, y) by {
                        let k = choose|k: int| 0 <= k < o.len() && #[trigger] o[k]@ == y;
                        assert(f@[k]@ == y);
                    }
                    assert forall|y: Seq<i64>| #[trigger] has(f@, y) implies has(ps@, y) && keep(*cc, tys@, y) by {
                        let k = choose|k: int| 0 <= k < f@.len() && #[trigger] f@[k]@ == y;
                        if k < o.len() {
                            assert(o[k]@ == y);
                            assert(has(o, y));
                        }
                    }
                }
            },
        }
        p += 1;
    }
    proof {
        assert forall|y: Seq<i64>| #[trigger] has(f@, y) <==> has(ps@, y) && keep(*cc, tys@, y) by {
            if has(ps@, y) && keep(*cc, tys@, y) {
                let k = choose|k: int| 0 <= k < ps@.len() && #[trigger] ps@[k]@ == y;
            }
        }
    }
    Ok(f)
}

/// 初期条件の下ろし。
pub open spec fn constraint_low(sm: SModel, sx: LowerCtx, cc: Option<Expr>) -> bool {
    match (sm.constraint, cc) {
        (None, None) => true,
        (Some(e), Some(c)) => prop_low(e, sx, c),
        _ => false,
    }
}

/// 候補の組の直積から初期条件で選んだ中核の初期状態は、値の上の初期状態と対応する。
proof fn lemma_init_ok(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    sx: LowerCtx,
    ps: Seq<Vec<i64>>,
    cc: Option<Expr>,
)
    requires
        sm.inits@.len() == sm.states@.len(),
        prod_ok(sm, cv, sm.states@.len() as int, ps),
        forall|y: Seq<i64>| #[trigger] has(m.inits@, y) <==> has(ps, y) && keep(cc, m.state_types@, y),
        constraint_low(sm, sx, cc),
        ctx_is(sx, sm.enums@, cv, st, Seq::empty(), false, None),
        layouts_at(st, s_state_tys(sm), sm.enums@),
        wf_stypes(s_state_tys(sm), sm.enums@),
        smalls(s_state_tys(sm)),
        m.state_types@ == slot_tys_seq(s_state_tys(sm), sm.enums@),
        m.enums@ == sm.enums@,
    ensures
        init_ok(sm, cv, m, st),
{
    let enums = sm.enums@;
    let ts = s_state_tys(sm);
    let n = sm.states@.len() as int;
    lemma_stys(sm.states@);
    assert(ts.take(n) =~= ts);
    assert forall|s: Seq<SVal>, y: Seq<i64>| combo(sm, cv, n, s) && y == codes(enc_seq(s, ts, enums)) implies {
        &&& #[trigger] rel(st, s, m.state_types@, y, enums)
        &&& members(s, ts, enums)
        &&& (keep(cc, m.state_types@, y) <==> match sm.constraint {
            None => true,
            Some(e) => s_prop(sm, cv, e, s) == Ok::<bool, ErrKind>(true),
        })
    } by {
        assert forall|i: int| 0 <= i < ts.len() implies member(#[trigger] s[i], ts[i], enums) by {
            assert(s_init_var(sm, cv, i, s[i]));
        }
        lemma_members(s, ts, enums);
        lemma_rel_codes(st, s, ts, enums);
        match (sm.constraint, cc) {
            (Some(e), Some(c)) => {
                lemma_prop(sm, cv, m, st, sx, e, c, s, y);
                assert(inv_env(m, y) == st_env(m.state_types@, y));
            },
            _ => {},
        }
    }
    assert forall|k: int| 0 <= k < m.inits@.len() implies #[trigger] init_src(sm, cv, st, m.state_types@, m.inits@[k]@) by {
        let y = m.inits@[k]@;
        assert(has(m.inits@, y));
        let ws = choose|ws: Seq<SVal>| #[trigger] combo(sm, cv, n, ws) && y == codes(enc_seq(ws, ts.take(n), enums));
        assert(rel(st, ws, m.state_types@, y, enums));
        assert forall|i: int| 0 <= i < ws.len() implies #[trigger] s_init_var(sm, cv, i, ws[i]) by {}
        assert(s_init(sm, cv, ws));
    }
    assert forall|s: Seq<SVal>| #[trigger] s_init(sm, cv, s) implies exists|k: int|
        0 <= k < m.inits@.len() && #[trigger] rel(st, s, m.state_types@, m.inits@[k]@, enums) by {
        lemma_members(s, ts, enums);
        assert forall|i: int| 0 <= i < n implies #[trigger] s_init_var(sm, cv, i, s[i]) && member(s[i], ts[i], enums) by {
            assert(s_init_var(sm, cv, i, s[i]));
        }
        assert(combo(sm, cv, n, s));
        let y = codes(enc_seq(s, ts, enums));
        assert(rel(st, s, m.state_types@, y, enums));
        assert(has(ps, y));
        assert(has(m.inits@, y));
        let k = choose|k: int| 0 <= k < m.inits@.len() && #[trigger] m.inits@[k]@ == y;
    }
}

// ---- モデル全体の下ろし ----

/// 定数 `q` の値は `cv[q]` である。
pub open spec fn const_at(sm: SModel, cv: Seq<SVal>, q: int) -> bool {
    &&& eval_src(sm.consts@[q].expr, s_env(sm, cv.take(q), Seq::empty(), Seq::empty(), Seq::empty(), None), Seq::empty())
        == Ok::<SVal, ErrKind>(cv[q])
    &&& member(cv[q], sty(sm.consts@[q].ty), sm.enums@)
}

/// 下ろした式は、中核のモデルの文脈で型を持つ。
proof fn lemma_model_types(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    stg: Seq<Layout>,
    sx: LowerCtx,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
)
    requires
        wf_frame(m),
        m.enums@ == sm.enums@,
        m.state_types@ == slot_tys_seq(stys(sm.states@), sm.enums@),
        layouts_at(stg, stys(sm.states@), sm.enums@),
        ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
        cs.len() == m.actions@.len(),
        m.actions@.len() == sm.actions@.len(),
        ks.len() == m.contracts@.len(),
        m.contracts@.len() == sm.contracts@.len(),
        forall|q: int| 0 <= q < m.actions@.len() ==> #[trigger] action_at(sm, cv, stg, cs[q], q, m.actions@[q]),
        forall|q: int| 0 <= q < m.contracts@.len() ==> #[trigger] contract_at(sm, cv, stg, ks[q], q, m.contracts@[q]),
        forall|q: int| 0 <= q < m.actions@.len() ==> #[trigger] crate::smodel::act_typed(m.actions@[q], crate::lower_types::lenv(cs[q])),
        forall|q: int| 0 <= q < m.invariants@.len() ==> #[trigger] crate::lower_types::has_ty(m.invariants@[q], crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool),
        forall|q: int| 0 <= q < m.contracts@.len() ==> #[trigger] crate::lower_types::has_ty(m.contracts@[q].expr, crate::lower_types::lenv(ks[q]), Seq::empty(), crate::typing::ETy::Bool),
        m.terminal matches Some(e) ==> crate::lower_types::has_ty(e, crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool),
    ensures
        crate::typing::wf(m),
{
    crate::model_wf::lemma_inv_env(sm, cv, stg, sx, m);
    assert forall|a: int| 0 <= a < m.actions@.len() implies #[trigger] crate::smodel::act_typed(m.actions@[a], crate::typing::act_tyenv(m, a)) by {
        assert(action_at(sm, cv, stg, cs[a], a, m.actions@[a]));
        crate::model_wf::lemma_act_env(sm, cv, stg, cs[a], a, m);
        assert(crate::smodel::act_typed(m.actions@[a], crate::lower_types::lenv(cs[a])));
    }
    assert forall|c: int| 0 <= c < m.contracts@.len() implies #[trigger] crate::lower_types::has_ty(
        m.contracts@[c].expr,
        crate::typing::con_tyenv(m, m.contracts@[c].action as int),
        Seq::empty(),
        crate::typing::ETy::Bool,
    ) by {
        assert(contract_at(sm, cv, stg, ks[c], c, m.contracts@[c]));
        let a = sm.contracts@[c].action as int;
        assert(action_at(sm, cv, stg, cs[a], a, m.actions@[a]));
        crate::model_wf::lemma_con_env(sm, cv, stg, cs[a], ks[c], c, m);
        assert(crate::lower_types::has_ty(m.contracts@[c].expr, crate::lower_types::lenv(ks[c]), Seq::empty(), crate::typing::ETy::Bool));
    }
    assert forall|i: int| 0 <= i < m.invariants@.len() implies #[trigger] crate::lower_types::has_ty(
        m.invariants@[i],
        crate::typing::inv_tyenv(m),
        Seq::empty(),
        crate::typing::ETy::Bool,
    ) by {
        assert(crate::lower_types::has_ty(m.invariants@[i], crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool));
    }
    crate::model_wf::lemma_model_wf(m);
}

/// モデル全体を中核のモデルに下ろす。
pub fn lower_model(sm: &SModel) -> (r: Result<RawModel, LowerError>)
    ensures
        r matches Ok(m) ==> lowers_model(*sm, m),
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)),
        r matches Ok(m) ==> sm_wf(*sm) ==> wf_frame(m),
        r matches Ok(m) ==> sm_wf(*sm) ==> crate::typing::wf(m),
{
    let none: Vec<SMap> = Vec::new();
    match lower_model_map(sm, &none) {
        Ok((m, _)) => Ok(m),
        Err(e) => Err(e),
    }
}

/// モデル全体を中核のモデルに下ろし、写像 `maps` の各式をスロットごとの式に下ろして、つないだ列を返す。
/// 写像の式の意味保存は、ここでは述べない。判定ゲートの定理は、下ろした中核の式について述べる。
pub fn lower_model_map(sm: &SModel, maps: &Vec<SMap>) -> (r: Result<(RawModel, Vec<Expr>), LowerError>)
    ensures
        r matches Ok((m, _)) ==> lowers_model(*sm, m),
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)) || (e is Mapping && maps@.len() > 0),
        r matches Ok((m, _)) ==> sm_wf(*sm) ==> wf_frame(m),
        r matches Ok((m, _)) ==> sm_wf(*sm) ==> crate::typing::wf(m),
{
    // 状態変数と引数の型の誤りは、その位置を報告する。
    match check_types(&sm.states, &sm.enums) {
        Ok(()) => {},
        Err(i) => return Err(LowerError::State(i)),
    }
    let mut a = 0;
    while a < sm.actions.len()
        invariant
            a <= sm.actions@.len(),
        decreases sm.actions@.len() - a,
    {
        match check_types(&sm.actions[a].args, &sm.enums) {
            Ok(()) => {},
            Err(i) => {
                proof {
                    assert(!action_typed(*sm, a as int));
                }
                return Err(LowerError::Args(a, i));
            },
        }
        a += 1;
    }
    if !check_model(sm) {
        return Err(LowerError::Type);
    }
    let enums = copy_vec(&sm.enums);
    match check_types(&sm.states, &enums) {
        Ok(()) => {},
        Err(i) => return Err(LowerError::State(i)),
    }
    let st = match layouts_of(&sm.states, &enums) {
        Ok(ls) => ls,
        Err(i) => return Err(LowerError::State(i)),
    };
    let ghost stg = st@;
    let st_tys = slot_types_list(&sm.states, &enums);
    let mut cx = LowerCtx {
        enums: copy_vec(&enums),
        states: None,
        args: Vec::new(),
        next: false,
        out: None,
        consts: Vec::new(),
    };
    // 定数
    let ghost mut cv: Seq<SVal> = Seq::empty();
    let mut i = 0;
    while i < sm.consts.len()
        invariant
            i <= sm.consts@.len(),
            enums@ == sm.enums@,
            init_cx(*sm, cv, cx),
            cv.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] const_at(*sm, cv, q),
            model_typed(*sm),
            consts_match(*sm, cx.consts@),
        decreases sm.consts@.len() - i,
    {
        let c = &sm.consts[i];
        proof {
            lemma_const_ctx(*sm, cv, cx);
            assert(cx.consts@.len() == i);
            assert(ok_s(sty(sm.consts@[i as int].ty), sm.enums@));
        }
        let (vals, _cs) = match eval_stored(&c.expr, &cx, &c.ty) {
            Ok(r) => r,
            Err(f) => return Err(LowerError::Const(i, f)),
        };
        let ghost cv0 = cv;
        proof {
            let se = s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None);
            lemma_init_top(*sm, cv, cx);
            let v = eval_src(c.expr, se, Seq::empty())->Ok_0;
            cv = cv.push(v);
            assert(cv.take(i as int) =~= cv0);
            assert forall|q: int| 0 <= q < i + 1 implies #[trigger] const_at(*sm, cv, q) by {
                if q < i {
                    assert(cv.take(q) =~= cv0.take(q));
                    assert(const_at(*sm, cv0, q));
                }
            }
        }
        let ghost cs0 = cx.consts@;
        cx.consts.push(Constant { ty: copy_stype(&c.ty), slots: vals });
        proof {
            assert forall|q: int| 0 <= q < cx.consts@.len() implies sty(#[trigger] cx.consts@[q].ty) == sty(
                sm.consts@[q].ty,
            ) by {
                if q < i {
                    assert(cx.consts@[q] == cs0[q]);
                }
            }
            assert forall|q: int| 0 <= q < cx.consts@.len() implies member(#[trigger] cv[q], sty(cx.consts@[q].ty), sm.enums@)
                && cx.consts@[q].slots@ == enc(cv[q], sty(cx.consts@[q].ty), sm.enums@) by {
                if q < i {
                    assert(cx.consts@[q] == cs0[q]);
                    assert(cv[q] == cv0[q]);
                }
            }
        }
        i += 1;
    }
    // 初期値の候補
    if sm.inits.len() != sm.states.len() {
        return Err(LowerError::InitCount);
    }
    let mut cands: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut total: usize = 1;
    let mut i = 0;
    while i < sm.states.len()
        invariant
            i <= sm.states@.len(),
            sm.inits@.len() == sm.states@.len(),
            init_cx(*sm, cv, cx),
            cands@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] cands_ok(*sm, cv, q, cands@[q]@),
            model_typed(*sm),
            consts_match(*sm, cx.consts@),
            cx.consts@.len() == sm.consts@.len(),
        decreases sm.states@.len() - i,
    {
        let c = var_cands(sm, &cx, i, Ghost(cv))?;
        total = match total.checked_mul(c.len()) {
            Some(t) => t,
            None => return Err(LowerError::InitCount),
        };
        if total > MAX_INITIAL_CANDIDATES {
            return Err(LowerError::InitCount);
        }
        cands.push(c);
        i += 1;
    }
    // 候補の直積
    let mut ps: Vec<Vec<i64>> = Vec::new();
    ps.push(Vec::new());
    proof {
        let enums = sm.enums@;
        let ts0 = s_state_tys(*sm).take(0);
        assert(ts0 =~= Seq::<STy>::empty());
        assert forall|y: Seq<i64>| #[trigger] has(ps@, y) implies exists|ws: Seq<SVal>| #[trigger] combo(*sm, cv, 0, ws) && y
            == codes(enc_seq(ws, ts0, enums)) by {
            assert(combo(*sm, cv, 0, Seq::<SVal>::empty()));
            assert(codes(enc_seq(Seq::<SVal>::empty(), ts0, enums)) =~= Seq::<i64>::empty());
        }
        assert forall|ws: Seq<SVal>| #[trigger] combo(*sm, cv, 0, ws) implies has(ps@, codes(enc_seq(ws, ts0, enums))) by {
            assert(codes(enc_seq(ws, ts0, enums)) =~= Seq::<i64>::empty());
            assert(ps@[0]@ =~= Seq::<i64>::empty());
        }
        lemma_stys(sm.states@);
    }
    let mut k = 0;
    while k < cands.len()
        invariant
            k <= cands@.len(),
            cands@.len() == sm.states@.len(),
            s_state_tys(*sm).len() == sm.states@.len(),
            forall|q: int| 0 <= q < cands@.len() ==> #[trigger] cands_ok(*sm, cv, q, cands@[q]@),
            prod_ok(*sm, cv, k as int, ps@),
        decreases cands@.len() - k,
    {
        let next = product_step(&ps, &cands[k]);
        proof {
            assert(cands_ok(*sm, cv, k as int, cands@[k as int]@));
            lemma_prod_step(*sm, cv, k as int, ps@, cands@[k as int]@, next@);
        }
        ps = next;
        k += 1;
    }
    // 状態を参照できる文脈
    proof {
        assert(consts_rel(cx.consts@, cv, sm.enums@));
        assert(cx.consts@.len() == sm.consts@.len());
    }
    cx.states = Some(st);
    let ghost sx = cx;
    proof {
        assert(ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None));
        assert(layouts_at(cx.args@, Seq::<STy>::empty(), sm.enums@));
        assert(tys_ok(Seq::<STy>::empty(), sm.enums@));
        lemma_state_ctx(*sm, cv, cx, Seq::empty());
        crate::model_wf::lemma_cx_tok(cx, cv, stys(sm.states@), Seq::empty());
    }
    let ghost sc0 = st_ctx(*sm, Seq::empty(), false, None);
    let cc: Option<Expr> = match &sm.constraint {
        None => None,
        Some(e) => match lower_prop(e, &cx) {
            Ok(c) => Some(c),
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Constraint(Fault::Lower)),
        },
    };
    let ghost psg = ps@;
    let inits = match filter_inits(ps, &cc, &st_tys) {
        Ok(f) => f,
        Err(f) => return Err(LowerError::Constraint(f)),
    };
    if inits.len() == 0 {
        return Err(LowerError::NoInit);
    }
    // 不変条件と終端条件
    let mut invariants: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < sm.invariants.len()
        invariant
            i <= sm.invariants@.len(),
            cx == sx,
            invariants@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] prop_low(sm.invariants@[q], sx, invariants@[q]),
            model_typed(*sm),
            cx_wf(sx),
            sctx(sx) == sc0,
            sc0 == st_ctx(*sm, Seq::empty(), false, None),
            crate::lower_types::cx_tok(sx),
            forall|q: int| 0 <= q < i ==> #[trigger] crate::lower_types::has_ty(invariants@[q], crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool),
        decreases sm.invariants@.len() - i,
    {
        proof {
            assert(styped(sm.invariants@[i as int], sc0, XTy::Bool));
        }
        match lower_prop(&sm.invariants[i], &cx) {
            Ok(e) => {
                let ghost i0 = invariants@;
                invariants.push(e);
                proof {
                    assert forall|q: int| 0 <= q < i + 1 implies #[trigger] crate::lower_types::has_ty(invariants@[q], crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool) by {
                        if q < i {
                            assert(invariants@[q] == i0[q]);
                        }
                    }
                }
            },
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Invariant(i)),
        }
        i += 1;
    }
    let terminal: Option<Expr> = match &sm.terminal {
        None => None,
        Some(e) => match lower_prop(e, &cx) {
            Ok(c) => Some(c),
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Terminal),
        },
    };
    proof {
        if terminal is Some {
            assert(styped(sm.terminal->Some_0, sc0, XTy::Bool));
            assert(crate::lower_types::has_ty(terminal->Some_0, crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool));
        }
    }
    // 操作
    let mut actions: Vec<Action> = Vec::new();
    let ghost mut cs: Seq<LowerCtx> = Seq::empty();
    let mut a = 0;
    while a < sm.actions.len()
        invariant
            a <= sm.actions@.len(),
            cx.enums == sx.enums,
            cx.states == sx.states,
            cx.consts == sx.consts,
            !cx.next,
            cx.out is None,
            ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
            enums@ == sm.enums@,
            actions@.len() == a,
            forall|q: int| 0 <= q < a ==> #[trigger] crate::smodel::act_typed(actions@[q], crate::lower_types::lenv(cs[q])),
            cs.len() == a,
            forall|q: int| 0 <= q < a ==> #[trigger] action_at(*sm, cv, stg, cs[q], q, actions@[q]),
            model_typed(*sm),
            cx.consts@.len() == sm.consts@.len(),
            consts_match(*sm, cx.consts@),
            layouts_at(stg, stys(sm.states@), sm.enums@),
        decreases sm.actions@.len() - a,
    {
        let sa = &sm.actions[a];
        proof {
            assert(action_typed(*sm, a as int));
            lemma_sa_typed(*sm, a as int);
        }
        match check_types(&sa.args, &enums) {
            Ok(()) => {},
            Err(i) => return Err(LowerError::Args(a, i)),
        }
        let la = match layouts_of(&sa.args, &enums) {
            Ok(l) => l,
            Err(i) => return Err(LowerError::Args(a, i)),
        };
        cx.args = la;
        proof {
            lemma_state_ctx(*sm, cv, cx, stys(sa.args@));
            crate::model_wf::lemma_cx_tok(cx, cv, stys(sm.states@), stys(sa.args@));
        }
        let act = lower_action(sa, &cx, a)?;
        let ghost a0 = actions@;
        let ghost cs0 = cs;
        proof {
            cs = cs.push(cx);
            assert(action_at(*sm, cv, stg, cs[a as int], a as int, act));
        }
        actions.push(act);
        proof {
            assert forall|q: int| 0 <= q < a + 1 implies #[trigger] crate::smodel::act_typed(actions@[q], crate::lower_types::lenv(cs[q])) by {
                if q < a {
                    assert(actions@[q] == a0[q]);
                    assert(cs[q] == cs0[q]);
                }
            }
        }
        a += 1;
    }
    // 遷移契約
    cx.next = true;
    let mut contracts: Vec<Contract> = Vec::new();
    let ghost mut ks: Seq<LowerCtx> = Seq::empty();
    let mut k = 0;
    while k < sm.contracts.len()
        invariant
            k <= sm.contracts@.len(),
            cx.enums == sx.enums,
            cx.states == sx.states,
            cx.consts == sx.consts,
            cx.next,
            ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
            enums@ == sm.enums@,
            contracts@.len() == k,
            ks.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] crate::lower_types::has_ty(contracts@[q].expr, crate::lower_types::lenv(ks[q]), Seq::empty(), crate::typing::ETy::Bool),
            forall|q: int| 0 <= q < k ==> #[trigger] contract_at(*sm, cv, stg, ks[q], q, contracts@[q]),
            model_typed(*sm),
            cx.consts@.len() == sm.consts@.len(),
            consts_match(*sm, cx.consts@),
            layouts_at(stg, stys(sm.states@), sm.enums@),
        decreases sm.contracts@.len() - k,
    {
        let con = &sm.contracts[k];
        proof {
            assert(sm.contracts@[k as int] == *con);
        }
        if con.action >= sm.actions.len() {
            return Err(LowerError::Contract(k));
        }
        let sa = &sm.actions[con.action];
        proof {
            assert(action_typed(*sm, con.action as int));
        }
        let la = match layouts_of(&sa.args, &enums) {
            Ok(l) => l,
            Err(_) => return Err(LowerError::Contract(k)),
        };
        cx.args = la;
        cx.out = match &sa.output {
            None => None,
            Some(o) => Some(copy_stype(&o.ty)),
        };
        proof {
            lemma_state_ctx(*sm, cv, cx, stys(sa.args@));
            crate::model_wf::lemma_cx_tok(cx, cv, stys(sm.states@), stys(sa.args@));
            assert(out_sty(*sa) == match cx.out {
                Some(t) => Some(sty(t)),
                None => None,
            });
        }
        let e = match lower_prop(&con.expr, &cx) {
            Ok(e) => e,
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Contract(k)),
        };
        let c = Contract { action: con.action, expr: e };
        let ghost k0 = contracts@;
        let ghost ks0 = ks;
        proof {
            ks = ks.push(cx);
            assert(contract_at(*sm, cv, stg, ks[k as int], k as int, c));
        }
        contracts.push(c);
        proof {
            assert forall|q: int| 0 <= q < k + 1 implies #[trigger] crate::lower_types::has_ty(contracts@[q].expr, crate::lower_types::lenv(ks[q]), Seq::empty(), crate::typing::ETy::Bool) by {
                if q < k {
                    assert(contracts@[q] == k0[q]);
                    assert(ks[q] == ks0[q]);
                }
            }
        }
        k += 1;
    }
    let m = RawModel { enums, state_types: st_tys, inits, actions, invariants, contracts, terminal };
    proof {
        lemma_stys(sm.states@);
        lemma_init_ok(*sm, cv, m, stg, sx, psg, cc);
        assert forall|a: int| 0 <= a < cs.len() implies #[trigger] action_low(*sm, cv, m, stg, cs[a], a) by {
            assert(action_at(*sm, cv, stg, cs[a], a, actions@[a]));
        }
        assert forall|q: int| 0 <= q < ks.len() implies #[trigger] contract_low(*sm, cv, m, stg, cs, ks[q], q) by {
            assert(contract_at(*sm, cv, stg, ks[q], q, contracts@[q]));
        }
        assert(model_ok(*sm, cv, m, stg, cs, ks, sx));
        if sm_wf(*sm) {
            lemma_model_frame(*sm, cv, m, stg, cs, ks);
            lemma_model_types(*sm, cv, m, stg, sx, cs, ks);
        }
        assert forall|i: int| 0 <= i < cv.len() implies #[trigger] sm.consts@[i] == sm.consts@[i] && eval_src(
            sm.consts@[i].expr,
            s_env(*sm, cv.take(i), Seq::empty(), Seq::empty(), Seq::empty(), None),
            Seq::empty(),
        ) == Ok::<SVal, ErrKind>(cv[i]) && member(cv[i], sty(sm.consts@[i].ty), sm.enums@) by {
            assert(const_at(*sm, cv, i));
        }
        assert(consts_ok(*sm, cv));
        assert forall|c: Conditions| #[trigger] safe(m, c) <==> s_safe(*sm, cv, c) by {
            lemma_safe(*sm, cv, m, stg, cs, ks, sx, c);
        }
    }
    assert(lowers_model(*sm, m));
    // 写像。状態だけを参照する文脈で下ろす。
    cx.args = Vec::new();
    cx.next = false;
    cx.out = None;
    let mut slots: Vec<Expr> = Vec::new();
    let mut q: usize = 0;
    while q < maps.len()
        invariant
            q <= maps@.len(),
            lowers_model(*sm, m),
            sm_wf(*sm) ==> wf_frame(m) && crate::typing::wf(m),
        decreases maps@.len() - q,
    {
        match lower_stored(&maps[q].expr, &cx, &maps[q].ty, 0) {
            Ok(out) => {
                let mut j: usize = 0;
                while j < out.len()
                    invariant
                        j <= out@.len(),
                    decreases out@.len() - j,
                {
                    slots.push(copy_expr(&out[j]));
                    j += 1;
                }
            },
            Err(Fail::Depth) => {
                return Err(LowerError::Depth);
            },
            Err(Fail::Type) => {
                return Err(LowerError::Mapping(q));
            },
        }
        q += 1;
    }
    Ok((m, slots))
}

} // verus!
