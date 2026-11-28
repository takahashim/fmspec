//! モデル全体の下ろし。
//!
//! [`lower_model`] は、名前を解決したIRのモデル（[`SModel`]）を中核のモデルに下ろす。
//! 定数と初期値の候補は、下ろした式を評価して値にする。
//! 初期状態は、状態変数ごとの候補の符号を整列して重複を除き、その直積から初期条件を満たすものを残す。
//! 下ろしが成功すれば、中核のモデルの安全性は値の上のモデルの安全性と一致する（[`lowers_model`]）。

use crate::action_lower::lower_action;
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, lemma_stys, member, sty, stys, wf_stype, wf_stypes, width_sum, STy, XTy};
use crate::encoding::{SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::eval::ErrKind;
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_small, lemma_width_sum_prefix, small, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layout_at, layouts_at};
use crate::lower_ctx::{Constant, Fail, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_error::{type_err, user_err};
use crate::lower_error::{Fault, LowerError};
#[cfg(verus_keep_ghost)]
use crate::lower_spec::prop_low;
#[cfg(verus_keep_ghost)]
use crate::lower_spec::{action_at, action_low, contract_at, contract_low, ctx_is, model_ok};
use crate::lowering::{lower_prop, lower_stored};
use crate::model::{Action, Contract, Expr, RawModel};
use crate::model_init::{eval_stored, filter_inits, init_products};
#[cfg(verus_keep_ghost)]
use crate::model_init::{init_cx, lemma_init_ok, lemma_init_top};
#[cfg(verus_keep_ghost)]
use crate::model_safe::lemma_safe;
use crate::model_total::check_model;
#[cfg(verus_keep_ghost)]
use crate::model_total::{action_typed, consts_match, lemma_const_ctx, lemma_sa_typed};
#[cfg(verus_keep_ghost)]
use crate::model_total::{lemma_state_ctx, model_typed, out_sty, st_ctx, styped, tys_ok};
#[cfg(verus_keep_ghost)]
use crate::model_wf::{lemma_model_frame, sm_wf, wf_frame};
#[cfg(verus_keep_ghost)]
use crate::semantics::{safe, Conditions};
use crate::slot_types::slot_types_list;
#[cfg(verus_keep_ghost)]
use crate::slot_types::slot_tys_seq;
use crate::smodel::SModel;
#[cfg(verus_keep_ghost)]
use crate::smodel::{consts_ok, s_env, s_safe};
#[cfg(verus_keep_ghost)]
use crate::source::eval_src;
#[cfg(verus_keep_ghost)]
use crate::srel::consts_rel;
use crate::state_enc::copy_vec;
use crate::stype_exec::{copy_stype, stype_width, wf_stype_exec};
#[cfg(verus_keep_ghost)]
use crate::total::{cx_wf, ok_s, sctx};
use crate::total_check::small_stype;
use vstd::prelude::*;

verus! {

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
        forall|q: int| 0 <= q < m.actions@.len() ==> #[trigger] crate::action_lower::act_typed(m.actions@[q], crate::lower_types::lenv(cs[q])),
        forall|q: int| 0 <= q < m.invariants@.len() ==> #[trigger] crate::lower_types::has_ty(m.invariants@[q], crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool),
        forall|q: int| 0 <= q < m.contracts@.len() ==> #[trigger] crate::lower_types::has_ty(m.contracts@[q].expr, crate::lower_types::lenv(ks[q]), Seq::empty(), crate::typing::ETy::Bool),
        m.terminal matches Some(e) ==> crate::lower_types::has_ty(e, crate::lower_types::lenv(sx), Seq::empty(), crate::typing::ETy::Bool),
    ensures
        crate::typing::wf(m),
{
    crate::model_wf::lemma_inv_env(sm, cv, stg, sx, m);
    assert forall|a: int| 0 <= a < m.actions@.len() implies #[trigger] crate::action_lower::act_typed(m.actions@[a], crate::typing::act_tyenv(m, a)) by {
        assert(action_at(sm, cv, stg, cs[a], a, m.actions@[a]));
        crate::model_wf::lemma_act_env(sm, cv, stg, cs[a], a, m);
        assert(crate::action_lower::act_typed(m.actions@[a], crate::lower_types::lenv(cs[a])));
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

/// 定数を宣言の順に評価して、文脈 `cx` の定数に加える。値の上の定数の値の列を ghost で返す。
fn lower_consts(sm: &SModel, cx: &mut LowerCtx) -> (r: Result<Ghost<Seq<SVal>>, LowerError>)
    requires
        init_cx(*sm, Seq::empty(), *old(cx)),
        model_typed(*sm),
        consts_match(*sm, old(cx).consts@),
    ensures
        r matches Ok(cv) ==> {
            &&& init_cx(*sm, cv@, *final(cx))
            &&& cv@.len() == sm.consts@.len()
            &&& forall|q: int| 0 <= q < sm.consts@.len() ==> #[trigger] const_at(*sm, cv@, q)
            &&& consts_match(*sm, final(cx).consts@)
        },
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)),
{
    let ghost mut cv: Seq<SVal> = Seq::empty();
    let mut i = 0;
    while i < sm.consts.len()
        invariant
            i <= sm.consts@.len(),
            init_cx(*sm, cv, *cx),
            cv.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] const_at(*sm, cv, q),
            model_typed(*sm),
            consts_match(*sm, cx.consts@),
        decreases sm.consts@.len() - i,
    {
        let c = &sm.consts[i];
        proof {
            lemma_const_ctx(*sm, cv, *cx);
            assert(cx.consts@.len() == i);
            assert(ok_s(sty(sm.consts@[i as int].ty), sm.enums@));
        }
        let (vals, _cs) = match eval_stored(&c.expr, cx, &c.ty) {
            Ok(r) => r,
            Err(f) => return Err(LowerError::Const(i, f)),
        };
        let ghost cv0 = cv;
        proof {
            let se = s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None);
            lemma_init_top(*sm, cv, *cx);
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
    Ok(Ghost(cv))
}

/// 操作を下ろす。文脈 `cx` の引数のレイアウトを、操作ごとに置き換える。
fn lower_actions(
    sm: &SModel,
    cx: &mut LowerCtx,
    enums: &Vec<i64>,
    Ghost(cv): Ghost<Seq<SVal>>,
    Ghost(stg): Ghost<Seq<Layout>>,
    Ghost(sx): Ghost<LowerCtx>,
) -> (r: Result<(Vec<Action>, Ghost<Seq<LowerCtx>>), LowerError>)
    requires
        old(cx).enums == sx.enums,
        old(cx).states == sx.states,
        old(cx).consts == sx.consts,
        !old(cx).next,
        old(cx).out is None,
        ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
        enums@ == sm.enums@,
        model_typed(*sm),
        old(cx).consts@.len() == sm.consts@.len(),
        consts_match(*sm, old(cx).consts@),
        layouts_at(stg, stys(sm.states@), sm.enums@),
    ensures
        final(cx).enums == sx.enums,
        final(cx).states == sx.states,
        final(cx).consts == sx.consts,
        !final(cx).next,
        final(cx).out is None,
        r matches Ok((actions, cs)) ==> {
            &&& actions@.len() == sm.actions@.len()
            &&& cs@.len() == sm.actions@.len()
            &&& forall|q: int|
                0 <= q < actions@.len() ==> #[trigger] crate::action_lower::act_typed(actions@[q], crate::lower_types::lenv(cs@[q]))
            &&& forall|q: int| 0 <= q < actions@.len() ==> #[trigger] action_at(*sm, cv, stg, cs@[q], q, actions@[q])
        },
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)),
{
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
            forall|q: int| 0 <= q < a ==> #[trigger] crate::action_lower::act_typed(actions@[q], crate::lower_types::lenv(cs[q])),
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
        match check_types(&sa.args, enums) {
            Ok(()) => {},
            Err(i) => return Err(LowerError::Args(a, i)),
        }
        let la = match layouts_of(&sa.args, enums) {
            Ok(l) => l,
            Err(i) => return Err(LowerError::Args(a, i)),
        };
        cx.args = la;
        proof {
            lemma_state_ctx(*sm, cv, *cx, stys(sa.args@));
            crate::model_wf::lemma_cx_tok(*cx, cv, stys(sm.states@), stys(sa.args@));
        }
        let act = lower_action(sa, cx, a)?;
        let ghost a0 = actions@;
        let ghost cs0 = cs;
        proof {
            cs = cs.push(*cx);
            assert(action_at(*sm, cv, stg, cs[a as int], a as int, act));
        }
        actions.push(act);
        proof {
            assert forall|q: int| 0 <= q < a + 1 implies #[trigger] crate::action_lower::act_typed(actions@[q], crate::lower_types::lenv(cs[q])) by {
                if q < a {
                    assert(actions@[q] == a0[q]);
                    assert(cs[q] == cs0[q]);
                }
            }
        }
        a += 1;
    }
    Ok((actions, Ghost(cs)))
}

/// 遷移契約を下ろす。文脈 `cx` の引数のレイアウトと出力の型を、契約の操作ごとに置き換える。
fn lower_contracts(
    sm: &SModel,
    cx: &mut LowerCtx,
    enums: &Vec<i64>,
    Ghost(cv): Ghost<Seq<SVal>>,
    Ghost(stg): Ghost<Seq<Layout>>,
    Ghost(sx): Ghost<LowerCtx>,
) -> (r: Result<(Vec<Contract>, Ghost<Seq<LowerCtx>>), LowerError>)
    requires
        old(cx).enums == sx.enums,
        old(cx).states == sx.states,
        old(cx).consts == sx.consts,
        old(cx).next,
        ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
        enums@ == sm.enums@,
        model_typed(*sm),
        old(cx).consts@.len() == sm.consts@.len(),
        consts_match(*sm, old(cx).consts@),
        layouts_at(stg, stys(sm.states@), sm.enums@),
    ensures
        final(cx).enums == sx.enums,
        final(cx).states == sx.states,
        final(cx).consts == sx.consts,
        r matches Ok((contracts, ks)) ==> {
            &&& contracts@.len() == sm.contracts@.len()
            &&& ks@.len() == sm.contracts@.len()
            &&& forall|q: int|
                0 <= q < contracts@.len() ==> #[trigger] crate::lower_types::has_ty(contracts@[q].expr, crate::lower_types::lenv(ks@[q]), Seq::empty(), crate::typing::ETy::Bool)
            &&& forall|q: int| 0 <= q < contracts@.len() ==> #[trigger] contract_at(*sm, cv, stg, ks@[q], q, contracts@[q])
        },
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)),
{
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
        let la = match layouts_of(&sa.args, enums) {
            Ok(l) => l,
            Err(_) => return Err(LowerError::Contract(k)),
        };
        cx.args = la;
        cx.out = match &sa.output {
            None => None,
            Some(o) => Some(copy_stype(&o.ty)),
        };
        proof {
            lemma_state_ctx(*sm, cv, *cx, stys(sa.args@));
            crate::model_wf::lemma_cx_tok(*cx, cv, stys(sm.states@), stys(sa.args@));
            assert(out_sty(*sa) == match cx.out {
                Some(t) => Some(sty(t)),
                None => None,
            });
        }
        let e = match lower_prop(&con.expr, cx) {
            Ok(e) => e,
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Contract(k)),
        };
        let c = Contract { action: con.action, expr: e };
        let ghost k0 = contracts@;
        let ghost ks0 = ks;
        proof {
            ks = ks.push(*cx);
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
    Ok((contracts, Ghost(ks)))
}

/// 不変条件と終端条件を、状態を参照できる文脈 `cx` で下ろす。
fn lower_props(sm: &SModel, cx: &LowerCtx) -> (r: Result<(Vec<Expr>, Option<Expr>), LowerError>)
    requires
        model_typed(*sm),
        cx_wf(*cx),
        sctx(*cx) == st_ctx(*sm, Seq::empty(), false, None),
        crate::lower_types::cx_tok(*cx),
    ensures
        r matches Ok((invariants, terminal)) ==> {
            &&& invariants@.len() == sm.invariants@.len()
            &&& forall|q: int|
                0 <= q < invariants@.len() ==> #[trigger] prop_low(sm.invariants@[q], *cx, invariants@[q])
            &&& forall|q: int|
                0 <= q < invariants@.len() ==> #[trigger] crate::lower_types::has_ty(invariants@[q], crate::lower_types::lenv(*cx), Seq::empty(), crate::typing::ETy::Bool)
            &&& match (sm.terminal, terminal) {
                (None, None) => true,
                (Some(e), Some(x)) => prop_low(e, *cx, x) && crate::lower_types::has_ty(x, crate::lower_types::lenv(*cx), Seq::empty(), crate::typing::ETy::Bool),
                _ => false,
            }
        },
        r matches Err(e) ==> e is Depth,
{
    let mut invariants: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < sm.invariants.len()
        invariant
            i <= sm.invariants@.len(),
            invariants@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] prop_low(sm.invariants@[q], *cx, invariants@[q]),
            model_typed(*sm),
            cx_wf(*cx),
            sctx(*cx) == st_ctx(*sm, Seq::empty(), false, None),
            crate::lower_types::cx_tok(*cx),
            forall|q: int| 0 <= q < i ==> #[trigger] crate::lower_types::has_ty(invariants@[q], crate::lower_types::lenv(*cx), Seq::empty(), crate::typing::ETy::Bool),
        decreases sm.invariants@.len() - i,
    {
        proof {
            assert(styped(sm.invariants@[i as int], st_ctx(*sm, Seq::empty(), false, None), XTy::Bool));
        }
        match lower_prop(&sm.invariants[i], cx) {
            Ok(e) => {
                let ghost i0 = invariants@;
                invariants.push(e);
                proof {
                    assert forall|q: int| 0 <= q < i + 1 implies #[trigger] crate::lower_types::has_ty(invariants@[q], crate::lower_types::lenv(*cx), Seq::empty(), crate::typing::ETy::Bool) by {
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
        Some(e) => match lower_prop(e, cx) {
            Ok(c) => Some(c),
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Terminal),
        },
    };
    proof {
        if terminal is Some {
            assert(styped(sm.terminal->Some_0, st_ctx(*sm, Seq::empty(), false, None), XTy::Bool));
            assert(crate::lower_types::has_ty(terminal->Some_0, crate::lower_types::lenv(*cx), Seq::empty(), crate::typing::ETy::Bool));
        }
    }
    Ok((invariants, terminal))
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
    proof {
        assert(consts_rel(cx.consts@, Seq::empty(), sm.enums@));
    }
    let _cv = lower_consts(sm, &mut cx)?;
    let ghost cv = _cv@;
    // 初期値の候補の直積
    let ps = init_products(sm, &cx, Ghost(cv))?;
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
    proof {
        assert(sctx(sx) == st_ctx(*sm, Seq::empty(), false, None));
    }
    let (invariants, terminal) = lower_props(sm, &cx)?;
    // 操作
    let (actions, _cs) = lower_actions(sm, &mut cx, &enums, Ghost(cv), Ghost(stg), Ghost(sx))?;
    let ghost cs = _cs@;
    // 遷移契約
    cx.next = true;
    let (contracts, _ks) = lower_contracts(sm, &mut cx, &enums, Ghost(cv), Ghost(stg), Ghost(sx))?;
    let ghost ks = _ks@;
    let m = RawModel { enums, state_types: st_tys, inits, actions, invariants, contracts, terminal };
    proof {
        lemma_stys(sm.states@);
        lemma_init_ok(*sm, cv, m, stg, sx, psg, cc);
        assert forall|a: int| 0 <= a < cs.len() implies #[trigger] action_low(*sm, cv, m, stg, cs[a], a) by {
            assert(action_at(*sm, cv, stg, cs[a], a, actions@[a]));
        }
        assert forall|q: int| 0 <= q < ks.len() implies #[trigger] contract_low(*sm, cv, m, stg, ks[q], q) by {
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
