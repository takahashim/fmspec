//! モデル全体の型付けと大きさの条件（計画書 docs/plans/lowering_totality.md の手順5と手順7）。
//!
//! [`model_typed`] は、モデルの各式が、下ろしで使う文脈で型を持ち、大きさの条件を満たすことを表す。
//! [`check_model`] はそれを実行時に確かめる。

use crate::kernel::state_enc::copy_vec;
#[cfg(verus_keep_ghost)]
use crate::model::srel::consts_rel;
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::LowerCtx;
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{layout_at, layout_tys, layouts_at, lemma_layout_end, Constant, Layout};
#[cfg(verus_keep_ghost)]
use crate::slot::total::{const_tys, cx_wf, layout_wf, lim_ok, ok_s, sctx};
use crate::slot::total_check::{cap_s, check_lim, lim_s_exec};
#[cfg(verus_keep_ghost)]
use crate::slot::total_check::{capped, lemma_capped_add};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_enc_len, lemma_stys, member, sty, stys, to_xty, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{width_sum, xty, xtys, XTy};
use crate::value::encoding::{SType, XType};
use crate::value::infer::{check, Scope};
#[cfg(verus_keep_ghost)]
use crate::value::infer::{ir_type_of, scope_view, SCtx};
#[cfg(verus_keep_ghost)]
use crate::value::limits::lim;
#[cfg(verus_keep_ghost)]
use crate::value::smodel::SAction;
use crate::value::smodel::SModel;
use crate::value::source::TExpr;
use crate::value::stype_exec::{copy_stype, wf_stype_exec, xtype_eq};
use vstd::prelude::*;

verus! {

/// 型の列の各型が整形式で大きさの条件を満たし、幅の和も上限以下である。
pub open spec fn tys_ok(ts: Seq<STy>, enums: Seq<i64>) -> bool {
    (forall|i: int| 0 <= i < ts.len() ==> ok_s(#[trigger] ts[i], enums)) && width_sum(ts, enums) <= lim()
}

pub open spec fn const_tys_s(sm: SModel, n: int) -> Seq<STy> {
    Seq::new(n as nat, |j: int| sty(sm.consts@[j].ty))
}

/// 定数 `n` 個までを参照できる、状態のない文脈（定数と初期値）。
pub open spec fn const_ctx(sm: SModel, n: int) -> SCtx {
    SCtx {
        enums: sm.enums@,
        states: None,
        args: Seq::empty(),
        next: false,
        out: None,
        consts: const_tys_s(sm, n),
    }
}

/// 状態を参照できる文脈。
pub open spec fn st_ctx(sm: SModel, args: Seq<STy>, next: bool, out: Option<STy>) -> SCtx {
    SCtx {
        enums: sm.enums@,
        states: Some(stys(sm.states@)),
        args,
        next,
        out,
        consts: const_tys_s(sm, sm.consts@.len() as int),
    }
}

pub open spec fn out_sty(sa: SAction) -> Option<STy> {
    match sa.output {
        Some(o) => Some(sty(o.ty)),
        None => None,
    }
}

pub open spec fn scalar_s(t: STy) -> bool {
    t is Bool || t is Int || t is Enum
}

/// 操作 `a` の式が型を持ち、大きさの条件を満たす。
pub open spec fn action_typed(sm: SModel, a: int) -> bool {
    let sa = sm.actions@[a];
    let c = st_ctx(sm, stys(sa.args@), false, None);
    &&& tys_ok(stys(sa.args@), sm.enums@)
    &&& styped(sa.guard, c, XTy::Bool)
    &&& forall|u: int|
        0 <= u < sa.updates@.len() ==> (#[trigger] sa.updates@[u]).var < sm.states@.len() && styped(
            sa.updates@[u].expr,
            c,
            to_xty(sty(sm.states@[sa.updates@[u].var as int])),
        )
    &&& sa.output matches Some(o) ==> scalar_s(sty(o.ty)) && ok_s(sty(o.ty), sm.enums@) && styped(
        o.expr,
        c,
        to_xty(sty(o.ty)),
    )
}

/// モデルの各式が、下ろしで使う文脈で型を持ち、大きさの条件を満たす。
pub open spec fn model_typed(sm: SModel) -> bool {
    let enums = sm.enums@;
    let sc = st_ctx(sm, Seq::empty(), false, None);
    &&& forall|i: int|
        0 <= i < sm.consts@.len() ==> ok_s(sty((#[trigger] sm.consts@[i]).ty), enums) && styped(
            sm.consts@[i].expr,
            const_ctx(sm, i),
            to_xty(sty(sm.consts@[i].ty)),
        )
    &&& tys_ok(stys(sm.states@), enums)
    &&& sm.inits@.len() == sm.states@.len()
    &&& forall|i: int, j: int|
        0 <= i < sm.inits@.len() && 0 <= j < sm.inits@[i]@.len() ==> styped(
            #[trigger] sm.inits@[i]@[j],
            const_ctx(sm, sm.consts@.len() as int),
            to_xty(sty(sm.states@[i])),
        )
    &&& sm.constraint matches Some(c) ==> styped(c, sc, XTy::Bool)
    &&& forall|i: int| 0 <= i < sm.invariants@.len() ==> styped(#[trigger] sm.invariants@[i], sc, XTy::Bool)
    &&& sm.terminal matches Some(t) ==> styped(t, sc, XTy::Bool)
    &&& forall|a: int| 0 <= a < sm.actions@.len() ==> #[trigger] action_typed(sm, a)
    &&& forall|k: int|
        0 <= k < sm.contracts@.len() ==> (#[trigger] sm.contracts@[k]).action < sm.actions@.len() && styped(
            sm.contracts@[k].expr,
            st_ctx(
                sm,
                stys(sm.actions@[sm.contracts@[k].action as int].args@),
                true,
                out_sty(sm.actions@[sm.contracts@[k].action as int]),
            ),
            XTy::Bool,
        )
}

/// 局所変数のない文脈で、式が型 `want` を持ち、大きさの条件を満たすか。
fn check_expr(e: &TExpr, s: &Scope, want: &XType) -> (r: bool)
    ensures
        r == styped(*e, scope_view(s), xty(*want)),
{
    let mut lt: Vec<XType> = Vec::new();
    proof {
        assert(xtys(lt@) =~= Seq::<XTy>::empty());
    }
    let ok = match check(e, s, &mut lt) {
        Some(x) => xtype_eq(&x, want),
        None => false,
    };
    ok && check_lim(e, s, &mut lt)
}

/// 型の列が [`tys_ok`] を満たすか。
fn tys_ok_exec(ts: &Vec<SType>, enums: &Vec<i64>) -> (r: bool)
    ensures
        r == tys_ok(stys(ts@), enums@),
{
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
    }
    let mut acc: u128 = 0;
    let mut i = 0;
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            forall|j: int| 0 <= j < i ==> ok_s(#[trigger] stys(ts@)[j], enums@),
            acc == capped(width_sum(stys(ts@).take(i as int), enums@)),
        decreases ts.len() - i,
    {
        if !(wf_stype_exec(&ts[i], enums) && lim_s_exec(&ts[i], enums)) {
            proof {
                assert(!ok_s(stys(ts@)[i as int], enums@));
            }
            return false;
        }
        let w = cap_s(&ts[i], enums);
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
            lemma_capped_add(width_sum(xs.take(i as int), enums@), width(sty(ts@[i as int]), enums@));
        }
        acc = if acc + w > 0x7fff_ffff {
            0x8000_0000
        } else {
            acc + w
        };
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    acc <= 0x7fff_ffff
}

fn copy_stypes(ts: &Vec<SType>) -> (r: Vec<SType>)
    ensures
        stys(r@) == stys(ts@),
{
    let mut out: Vec<SType> = Vec::new();
    let mut i = 0;
    proof {
        lemma_stys(ts@);
    }
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> sty(#[trigger] out@[j]) == sty(ts@[j]),
        decreases ts.len() - i,
    {
        out.push(copy_stype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_stys(out@);
        assert(stys(out@) =~= stys(ts@));
    }
    out
}

/// モデルの各式が型を持ち、大きさの条件を満たすか（[`model_typed`] と一致する）。
pub fn check_model(sm: &SModel) -> (r: bool)
    ensures
        r == model_typed(*sm),
{
    let enums = &sm.enums;
    // 定数
    let mut ctys: Vec<SType> = Vec::new();
    let mut i = 0;
    while i < sm.consts.len()
        invariant
            i <= sm.consts@.len(),
            enums@ == sm.enums@,
            stys(ctys@) == const_tys_s(*sm, i as int),
            forall|j: int|
                0 <= j < i ==> ok_s(sty((#[trigger] sm.consts@[j]).ty), sm.enums@) && styped(
                    sm.consts@[j].expr,
                    const_ctx(*sm, j),
                    to_xty(sty(sm.consts@[j].ty)),
                ),
        decreases sm.consts.len() - i,
    {
        if !check_const(sm, i, &ctys) {
            return false;
        }
        push_const_ty(sm, i, &mut ctys);
        i += 1;
    }
    // 状態変数と初期値
    if !tys_ok_exec(&sm.states, enums) {
        return false;
    }
    if sm.inits.len() != sm.states.len() {
        return false;
    }
    let is = Scope {
        enums: copy_vec(enums),
        states: None,
        args: Vec::new(),
        next: false,
        out: None,
        consts: copy_stypes(&ctys),
    };
    proof {
        assert(stys(Seq::<SType>::empty()) =~= Seq::<STy>::empty());
        assert(scope_view(&is) == const_ctx(*sm, sm.consts@.len() as int));
        lemma_stys(sm.states@);
    }
    let mut i = 0;
    while i < sm.inits.len()
        invariant
            i <= sm.inits@.len(),
            sm.inits@.len() == sm.states@.len(),
            enums@ == sm.enums@,
            scope_view(&is) == const_ctx(*sm, sm.consts@.len() as int),
            forall|p: int, j: int|
                0 <= p < i && 0 <= j < sm.inits@[p]@.len() ==> styped(
                    #[trigger] sm.inits@[p]@[j],
                    const_ctx(*sm, sm.consts@.len() as int),
                    to_xty(sty(sm.states@[p])),
                ),
        decreases sm.inits.len() - i,
    {
        let want = crate::value::stype_exec::to_xtype(&sm.states[i]);
        if !check_all_exprs(&sm.inits[i], &is, &want) {
            return false;
        }
        i += 1;
    }
    // 状態を参照する式
    let st = copy_stypes(&sm.states);
    let ss = Scope {
        enums: copy_vec(enums),
        states: Some(copy_stypes(&sm.states)),
        args: Vec::new(),
        next: false,
        out: None,
        consts: copy_stypes(&ctys),
    };
    proof {
        assert(scope_view(&ss) == st_ctx(*sm, Seq::empty(), false, None));
    }
    match &sm.constraint {
        Some(c) => if !check_expr(c, &ss, &XType::Bool) {
            return false;
        },
        None => {},
    }
    let mut i = 0;
    while i < sm.invariants.len()
        invariant
            i <= sm.invariants@.len(),
            scope_view(&ss) == st_ctx(*sm, Seq::empty(), false, None),
            forall|p: int| 0 <= p < i ==> styped(#[trigger] sm.invariants@[p], st_ctx(*sm, Seq::empty(), false, None), XTy::Bool),
        decreases sm.invariants.len() - i,
    {
        if !check_expr(&sm.invariants[i], &ss, &XType::Bool) {
            return false;
        }
        i += 1;
    }
    match &sm.terminal {
        Some(t) => if !check_expr(t, &ss, &XType::Bool) {
            return false;
        },
        None => {},
    }
    // 操作
    let mut a = 0;
    while a < sm.actions.len()
        invariant
            a <= sm.actions@.len(),
            enums@ == sm.enums@,
            stys(ctys@) == const_tys_s(*sm, sm.consts@.len() as int),
            stys(st@) == stys(sm.states@),
            forall|b: int| 0 <= b < a ==> #[trigger] action_typed(*sm, b),
        decreases sm.actions.len() - a,
    {
        if !check_action(sm, a, &ctys, &st) {
            return false;
        }
        a += 1;
    }
    // 遷移契約
    let mut k = 0;
    while k < sm.contracts.len()
        invariant
            k <= sm.contracts@.len(),
            enums@ == sm.enums@,
            stys(ctys@) == const_tys_s(*sm, sm.consts@.len() as int),
            stys(st@) == stys(sm.states@),
            forall|q: int|
                0 <= q < k ==> (#[trigger] sm.contracts@[q]).action < sm.actions@.len() && styped(
                    sm.contracts@[q].expr,
                    st_ctx(
                        *sm,
                        stys(sm.actions@[sm.contracts@[q].action as int].args@),
                        true,
                        out_sty(sm.actions@[sm.contracts@[q].action as int]),
                    ),
                    XTy::Bool,
                ),
        decreases sm.contracts.len() - k,
    {
        let con = &sm.contracts[k];
        if con.action >= sm.actions.len() {
            return false;
        }
        let sa = &sm.actions[con.action];
        let cs = Scope {
            enums: copy_vec(enums),
            states: Some(copy_stypes(&st)),
            args: copy_stypes(&sa.args),
            next: true,
            out: match &sa.output {
                Some(o) => Some(copy_stype(&o.ty)),
                None => None,
            },
            consts: copy_stypes(&ctys),
        };
        proof {
            assert(scope_view(&cs) == st_ctx(*sm, stys(sa.args@), true, out_sty(*sa)));
        }
        if !check_expr(&con.expr, &cs, &XType::Bool) {
            return false;
        }
        k += 1;
    }
    true
}

/// 定数 `i` の式が型を持ち、大きさの条件を満たすか。
fn check_const(sm: &SModel, i: usize, ctys: &Vec<SType>) -> (r: bool)
    requires
        i < sm.consts@.len(),
        stys(ctys@) == const_tys_s(*sm, i as int),
    ensures
        r == (ok_s(sty(sm.consts@[i as int].ty), sm.enums@) && styped(
            sm.consts@[i as int].expr,
            const_ctx(*sm, i as int),
            to_xty(sty(sm.consts@[i as int].ty)),
        )),
{
    let c = &sm.consts[i];
    let s = Scope {
        enums: copy_vec(&sm.enums),
        states: None,
        args: Vec::new(),
        next: false,
        out: None,
        consts: copy_stypes(ctys),
    };
    proof {
        assert(stys(Seq::<SType>::empty()) =~= Seq::<STy>::empty());
        assert(scope_view(&s) == const_ctx(*sm, i as int));
    }
    wf_stype_exec(&c.ty, &sm.enums) && lim_s_exec(&c.ty, &sm.enums) && check_expr(
        &c.expr,
        &s,
        &crate::value::stype_exec::to_xtype(&c.ty),
    )
}

fn push_const_ty(sm: &SModel, i: usize, ctys: &mut Vec<SType>)
    requires
        i < sm.consts@.len(),
        stys(old(ctys)@) == const_tys_s(*sm, i as int),
    ensures
        stys(final(ctys)@) == const_tys_s(*sm, i + 1),
{
    let ghost before = ctys@;
    let x = copy_stype(&sm.consts[i].ty);
    ctys.push(x);
    proof {
        lemma_stys(ctys@);
        lemma_stys(before);
        assert(ctys@ == before.push(x));
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] stys(ctys@)[j] == const_tys_s(*sm, i + 1)[j] by {
            if j < i {
                assert(ctys@[j] == before[j]);
                assert(stys(before)[j] == const_tys_s(*sm, i as int)[j]);
            }
        }
        assert(stys(ctys@) =~= const_tys_s(*sm, i + 1));
    }
}

/// 式の列のすべてが、型 `want` を持ち大きさの条件を満たすか。
fn check_all_exprs(es: &Vec<TExpr>, s: &Scope, want: &XType) -> (r: bool)
    ensures
        r == forall|q: int| 0 <= q < es@.len() ==> styped(#[trigger] es@[q], scope_view(s), xty(*want)),
{
    let mut j = 0;
    while j < es.len()
        invariant
            j <= es@.len(),
            forall|q: int| 0 <= q < j ==> styped(#[trigger] es@[q], scope_view(s), xty(*want)),
        decreases es.len() - j,
    {
        if !check_expr(&es[j], s, want) {
            return false;
        }
        j += 1;
    }
    true
}

/// 操作 `a` が [`action_typed`] を満たすか。
fn check_action(sm: &SModel, a: usize, ctys: &Vec<SType>, st: &Vec<SType>) -> (r: bool)
    requires
        a < sm.actions@.len(),
        stys(ctys@) == const_tys_s(*sm, sm.consts@.len() as int),
        stys(st@) == stys(sm.states@),
    ensures
        r == action_typed(*sm, a as int),
{
    let sa = &sm.actions[a];
    let enums = &sm.enums;
    if !tys_ok_exec(&sa.args, enums) {
        return false;
    }
    let s = Scope {
        enums: copy_vec(enums),
        states: Some(copy_stypes(st)),
        args: copy_stypes(&sa.args),
        next: false,
        out: None,
        consts: copy_stypes(ctys),
    };
    proof {
        assert(scope_view(&s) == st_ctx(*sm, stys(sa.args@), false, None));
        lemma_stys(sm.states@);
    }
    if !check_expr(&sa.guard, &s, &XType::Bool) {
        return false;
    }
    let mut u = 0;
    while u < sa.updates.len()
        invariant
            u <= sa.updates@.len(),
            *sa == sm.actions@[a as int],
            scope_view(&s) == st_ctx(*sm, stys(sa.args@), false, None),
            stys(sm.states@).len() == sm.states@.len(),
            forall|j: int| 0 <= j < sm.states@.len() ==> #[trigger] stys(sm.states@)[j] == sty(sm.states@[j]),
            forall|q: int|
                0 <= q < u ==> (#[trigger] sa.updates@[q]).var < sm.states@.len() && styped(
                    sa.updates@[q].expr,
                    st_ctx(*sm, stys(sa.args@), false, None),
                    to_xty(sty(sm.states@[sa.updates@[q].var as int])),
                ),
        decreases sa.updates.len() - u,
    {
        let up = &sa.updates[u];
        if up.var >= sm.states.len() {
            return false;
        }
        if !check_expr(&up.expr, &s, &crate::value::stype_exec::to_xtype(&sm.states[up.var])) {
            return false;
        }
        u += 1;
    }
    match &sa.output {
        Some(o) => {
            let scalar = match &o.ty {
                SType::Bool | SType::Int(_, _) | SType::Enum(_) => true,
                _ => false,
            };
            scalar && wf_stype_exec(&o.ty, enums) && lim_s_exec(&o.ty, enums) && check_expr(
                &o.expr,
                &s,
                &crate::value::stype_exec::to_xtype(&o.ty),
            )
        },
        None => true,
    }
}


// ---- 下ろしの文脈との対応（手順5） ----

/// 操作 `sa` の式が、状態を参照できる文脈 `c` で型を持ち、大きさの条件を満たす。
pub open spec fn sa_typed(sa: SAction, c: SCtx) -> bool {
    let sts = c.states->Some_0;
    &&& c.states is Some
    &&& tys_ok(stys(sa.args@), c.enums)
    &&& styped(sa.guard, c, XTy::Bool)
    &&& forall|u: int|
        0 <= u < sa.updates@.len() ==> (#[trigger] sa.updates@[u]).var < sts.len() && styped(
            sa.updates@[u].expr,
            c,
            to_xty(sts[sa.updates@[u].var as int]),
        )
    &&& sa.output matches Some(o) ==> scalar_s(sty(o.ty)) && ok_s(sty(o.ty), c.enums) && styped(
        o.expr,
        c,
        to_xty(sty(o.ty)),
    )
}

pub proof fn lemma_sa_typed(sm: SModel, a: int)
    requires
        0 <= a < sm.actions@.len(),
        action_typed(sm, a),
    ensures
        sa_typed(sm.actions@[a], st_ctx(sm, stys(sm.actions@[a].args@), false, None)),
{
    lemma_stys(sm.states@);
}

/// 型が条件を満たせば、位置は整形式である。
pub proof fn lemma_layouts_wf(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(ls, ts, enums),
        tys_ok(ts, enums),
    ensures
        layout_tys(ls) == ts,
        forall|i: int| 0 <= i < ls.len() ==> #[trigger] layout_wf(ls[i], enums),
{
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] layout_wf(ls[i], enums) by {
        lemma_layout_end(ls, ts, enums, i);
        assert(layout_at(ls[i], ts, i, enums));
        assert(ok_s(ts[i], enums));
    }
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] layout_tys(ls)[i] == ts[i] by {
        assert(layout_at(ls[i], ts, i, enums));
    }
    assert(layout_tys(ls) =~= ts);
}

/// 下ろしの文脈の定数の型は、モデルの先頭の定数の型である。
pub open spec fn consts_match(sm: SModel, cs: Seq<Constant>) -> bool {
    &&& cs.len() <= sm.consts@.len()
    &&& forall|q: int| 0 <= q < cs.len() ==> sty(#[trigger] cs[q].ty) == sty(sm.consts@[q].ty)
}

/// 定数の型は条件を満たし、定数のスロットは型の幅だけある。
pub proof fn lemma_consts_wf(sm: SModel, cv: Seq<SVal>, cs: Seq<Constant>)
    requires
        model_typed(sm),
        consts_match(sm, cs),
        consts_rel(cs, cv, sm.enums@),
    ensures
        forall|q: int|
            0 <= q < cs.len() ==> ok_s(sty(#[trigger] cs[q].ty), sm.enums@) && cs[q].slots@.len() == width(
                sty(cs[q].ty),
                sm.enums@,
            ),
        const_tys(cs) == const_tys_s(sm, cs.len() as int),
{
    assert forall|q: int| 0 <= q < cs.len() implies ok_s(sty(#[trigger] cs[q].ty), sm.enums@) && cs[q].slots@.len()
        == width(sty(cs[q].ty), sm.enums@) by {
        assert(sty(cs[q].ty) == sty(sm.consts@[q].ty));
        assert(ok_s(sty(sm.consts@[q].ty), sm.enums@));
        assert(member(cv[q], sty(cs[q].ty), sm.enums@));
        lemma_enc_len(cv[q], sty(cs[q].ty), sm.enums@);
    }
    assert(const_tys(cs) =~= const_tys_s(sm, cs.len() as int));
}

/// 定数と初期値を下ろす文脈は整形式で、型付けの文脈は [`const_ctx`] である。
pub proof fn lemma_const_ctx(sm: SModel, cv: Seq<SVal>, cx: LowerCtx)
    requires
        model_typed(sm),
        cx.enums@ == sm.enums@,
        cx.states is None,
        cx.args@ == Seq::<Layout>::empty(),
        !cx.next,
        cx.out is None,
        consts_rel(cx.consts@, cv, sm.enums@),
        consts_match(sm, cx.consts@),
    ensures
        cx_wf(cx),
        sctx(cx) == const_ctx(sm, cx.consts@.len() as int),
{
    lemma_consts_wf(sm, cv, cx.consts@);
    assert(layout_tys(cx.args@) =~= Seq::<STy>::empty());
}

/// 状態を参照できる文脈は整形式で、型付けの文脈は [`st_ctx`] である。
pub proof fn lemma_state_ctx(sm: SModel, cv: Seq<SVal>, cx: LowerCtx, ats: Seq<STy>)
    requires
        model_typed(sm),
        cx.enums@ == sm.enums@,
        cx.states is Some,
        layouts_at(cx.states->Some_0@, stys(sm.states@), sm.enums@),
        layouts_at(cx.args@, ats, sm.enums@),
        tys_ok(ats, sm.enums@),
        consts_rel(cx.consts@, cv, sm.enums@),
        consts_match(sm, cx.consts@),
        cx.consts@.len() == sm.consts@.len(),
        cx.out matches Some(t) ==> scalar_s(sty(t)) && ok_s(sty(t), sm.enums@),
    ensures
        cx_wf(cx),
        sctx(cx) == st_ctx(
            sm,
            ats,
            cx.next,
            match cx.out {
                Some(t) => Some(sty(t)),
                None => None,
            },
        ),
{
    lemma_consts_wf(sm, cv, cx.consts@);
    lemma_layouts_wf(cx.states->Some_0@, stys(sm.states@), sm.enums@);
    lemma_layouts_wf(cx.args@, ats, sm.enums@);
}

/// 局所変数のない文脈で、式が型 `x` を持ち、大きさの条件を満たす。
pub open spec fn styped(e: TExpr, c: SCtx, x: XTy) -> bool {
    ir_type_of(e, c, Seq::empty()) == Some(x) && lim_ok(e, c, Seq::empty())
}

} // verus!
