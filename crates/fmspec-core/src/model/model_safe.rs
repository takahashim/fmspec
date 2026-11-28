//! モデル全体の下ろしが安全性を保存することの証明。
//!
//! [`model_ok`] は、中核のモデルが値の上のモデルを下ろしたものであることで、下ろしが保証する性質をまとめる。
//! [`lemma_safe`] は、そのとき中核の安全性と値の上の安全性が一致することである。
//! 中核の到達可能な状態は、到達可能な値の状態を表し（[`lemma_reach_core`]）、
//! 到達可能な値の状態は、到達可能な中核の状態に表される（[`lemma_reach_src`]）。
//! 値を表す状態どうしでは、不変条件、遷移、遷移契約、終端条件の評価が一致する（[`lemma_state_safe`]）。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{decode, eval_l, prop_spec};
#[cfg(verus_keep_ghost)]
use crate::kernel::model::{Expr, RawModel, Type};
#[cfg(verus_keep_ghost)]
use crate::kernel::semantics::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::state_enc::{args_ok, vals_ok};
#[cfg(verus_keep_ghost)]
use crate::kernel::step::{act_env, all_disabled, step_spec, Step};
#[cfg(verus_keep_ghost)]
use crate::model::action_lower::{lemma_step, lemma_step_off, out_ok, out_rel, step_rel};
#[cfg(verus_keep_ghost)]
use crate::model::lower_spec::{action_low, contract_low, ctx_is, init_src, model_ok, prop_low};
#[cfg(verus_keep_ghost)]
use crate::model::srel::{arg_vals, canon_from, codes, consts_rel, lemma_canon_rel, lemma_code_in};
#[cfg(verus_keep_ghost)]
use crate::model::srel::{lemma_rel_codes, rel};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{layout_at, layouts_at, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{env_rel, layout_ok, layouts_ok, lemma_members, prop_result};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{enc, enc_seq, member, sty, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::smodel::*;
#[cfg(verus_keep_ghost)]
use crate::value::source::{eval_src, TExpr};
use vstd::prelude::*;

verus! {

// ---- 環境の対応 ----

/// 同じ型の列の位置どうしは、値の列を同じように表す。
proof fn lemma_layouts_same(
    l1: Seq<Layout>,
    l2: Seq<Layout>,
    ts: Seq<STy>,
    vs: Seq<SVal>,
    tys: Seq<Type>,
    xs: Seq<i64>,
    enums: Seq<i64>,
)
    requires
        layouts_at(l1, ts, enums),
        layouts_at(l2, ts, enums),
        layouts_ok(l1, vs, tys, xs, enums),
    ensures
        layouts_ok(l2, vs, tys, xs, enums),
{
    assert forall|i: int| 0 <= i < l2.len() implies #[trigger] layout_ok(l2[i], vs[i], tys, xs, enums) by {
        assert(layout_at(l1[i], ts, i, enums));
        assert(layout_at(l2[i], ts, i, enums));
        assert(layout_ok(l1[i], vs[i], tys, xs, enums));
    }
}

proof fn lemma_consts_env(cx: LowerCtx, cv: Seq<SVal>, enums: Seq<i64>)
    requires
        consts_rel(cx.consts@, cv, enums),
    ensures
        cv.len() == cx.consts@.len(),
        forall|i: int|
            0 <= i < cx.consts@.len() ==> member(#[trigger] cv[i], sty(cx.consts@[i].ty), enums)
                && cx.consts@[i].slots@ == enc(cv[i], sty(cx.consts@[i].ty), enums),
{
}

/// 操作の環境の対応。
proof fn lemma_env_act(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cx: LowerCtx,
    a: int,
    p: Seq<SVal>,
    ps: Seq<i64>,
    vs: Seq<SVal>,
    xs: Seq<i64>,
)
    requires
        ctx_is(cx, sm.enums@, cv, st, cx.args@, false, None),
        0 <= a < m.actions@.len(),
        rel(st, p, m.state_types@, ps, sm.enums@),
        layouts_ok(cx.args@, vs, m.actions@[a].domains@, xs, sm.enums@),
    ensures
        env_rel(cx, act_env(m, a, xs, ps), s_env(sm, cv, p, vs, Seq::empty(), None)),
{
    lemma_consts_env(cx, cv, sm.enums@);
}

/// 状態の性質の環境の対応。
proof fn lemma_env_inv(sm: SModel, cv: Seq<SVal>, m: RawModel, st: Seq<Layout>, sx: LowerCtx, s: Seq<SVal>, y: Seq<i64>)
    requires
        ctx_is(sx, sm.enums@, cv, st, Seq::empty(), false, None),
        rel(st, s, m.state_types@, y, sm.enums@),
    ensures
        env_rel(sx, inv_env(m, y), s_env(sm, cv, s, Seq::empty(), Seq::empty(), None)),
{
    lemma_consts_env(sx, cv, sm.enums@);
    assert(layouts_ok(sx.args@, Seq::<SVal>::empty(), Seq::<Type>::empty(), Seq::<i64>::empty(), sm.enums@));
}

/// 状態の性質の評価の対応。
pub proof fn lemma_prop(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    sx: LowerCtx,
    e: TExpr,
    c: Expr,
    s: Seq<SVal>,
    y: Seq<i64>,
)
    requires
        ctx_is(sx, sm.enums@, cv, st, Seq::empty(), false, None),
        rel(st, s, m.state_types@, y, sm.enums@),
        prop_low(e, sx, c),
    ensures
        prop_spec(c, inv_env(m, y)) == s_prop(sm, cv, e, s),
{
    lemma_env_inv(sm, cv, m, st, sx, s, y);
    assert(prop_result(
        eval_src(e, s_env(sm, cv, s, Seq::empty(), Seq::empty(), None), Seq::empty()),
        eval_l(c, inv_env(m, y), Seq::empty()),
    ));
}

/// 遷移契約の評価の対応。
proof fn lemma_con(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    k: int,
    p: Seq<SVal>,
    ps: Seq<i64>,
    vs: Seq<SVal>,
    xs: Seq<i64>,
    t: Seq<SVal>,
    ts: Seq<i64>,
    o: Option<SVal>,
    x: Option<i64>,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        0 <= k < sm.contracts@.len(),
        rel(st, p, m.state_types@, ps, sm.enums@),
        rel(st, t, m.state_types@, ts, sm.enums@),
        layouts_ok(cs[sm.contracts@[k].action as int].args@, vs, m.actions@[sm.contracts@[k].action as int].domains@, xs, sm.enums@),
        out_rel(sm.actions@[sm.contracts@[k].action as int].output, o, x, sm.enums@),
    ensures
        con_spec(m, k, ps, xs, ts, x) == s_con(sm, cv, k, p, vs, t, o),
{
    let enums = sm.enums@;
    let a = sm.contracts@[k].action as int;
    let kx = ks[k];
    assert(contract_low(sm, cv, m, st, kx, k));
    assert(action_low(sm, cv, m, st, cs[a], a));
    let env = con_env(m, a, ps, xs, ts, x);
    let se = s_env(sm, cv, p, vs, t, o);
    lemma_layouts_same(cs[a].args@, kx.args@, s_arg_tys(sm, a), vs, m.actions@[a].domains@, xs, enums);
    lemma_consts_env(kx, cv, enums);
    let so = sm.actions@[a].output;
    let mo = m.actions@[a].output;
    assert(out_ok(so, cs[a], mo));
    match (o, x) {
        (Some(v), Some(c)) => {
            let s = so->Some_0;
            let ot = sty(s.ty);
            let oo = mo->Some_0;
            assert(oo.ty == crate::slot::slot_types::slot_tys(ot, enums)[0]);
            assert(width(ot, enums) == 1);
            assert(crate::value::encoding::wf_stype(ot, enums)) by {
                crate::value::encoding::lemma_enc_len(v, ot, enums);
            }
            crate::slot::members::lemma_member_in(v, ot, enums);
            lemma_code_in(oo.ty, enc(v, ot, enums)[0], enums);
            assert(env.out == Some(decode(oo.ty, c)));
        },
        _ => {},
    }
    assert(env_rel(kx, env, se));
    assert(prop_result(eval_src(sm.contracts@[k].expr, se, Seq::empty()), eval_l(m.contracts@[k].expr, env, Seq::empty())));
}

// ---- 引数の対応 ----

/// 値の引数の符号。
pub open spec fn arg_codes(sm: SModel, a: int, vs: Seq<SVal>) -> Seq<i64> {
    codes(enc_seq(vs, s_arg_tys(sm, a), sm.enums@))
}

/// 値の引数の符号は、引数の値を表し、ドメインに従う。
proof fn lemma_arg_codes(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    a: int,
    vs: Seq<SVal>,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        0 <= a < sm.actions@.len(),
        s_args_ok(sm, a, vs),
    ensures
        layouts_ok(cs[a].args@, vs, m.actions@[a].domains@, arg_codes(sm, a, vs), sm.enums@),
        args_ok(m, a, arg_codes(sm, a, vs)),
{
    assert(action_low(sm, cv, m, st, cs[a], a));
    lemma_rel_codes(cs[a].args@, vs, s_arg_tys(sm, a), sm.enums@);
}

/// 正規形の中核の引数は、値の引数を表す。
proof fn lemma_core_args(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    a: int,
    xs: Seq<i64>,
    ps: Seq<i64>,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        0 <= a < sm.actions@.len(),
        args_ok(m, a, xs),
        canon_from(cs[a].args@, 0, act_env(m, a, xs, ps), sm.enums@),
    ensures
        layouts_ok(cs[a].args@, arg_vals(cs[a].args@, act_env(m, a, xs, ps), sm.enums@), m.actions@[a].domains@, xs, sm.enums@),
        s_args_ok(sm, a, arg_vals(cs[a].args@, act_env(m, a, xs, ps), sm.enums@)),
{
    let enums = sm.enums@;
    let la = cs[a].args@;
    let ts = s_arg_tys(sm, a);
    let env = act_env(m, a, xs, ps);
    assert(action_low(sm, cv, m, st, cs[a], a));
    lemma_canon_rel(la, env, ts, enums);
    let vs = arg_vals(la, env, enums);
    assert forall|i: int| 0 <= i < ts.len() implies member(#[trigger] vs[i], ts[i], enums) by {
        assert(layout_ok(la[i], vs[i], env.arg_tys, env.args, enums));
        assert(layout_at(la[i], ts, i, enums));
    }
    lemma_members(vs, ts, enums);
}

// ---- 遷移と状態の対応 ----

/// 値を表す状態と引数での遷移は対応し、安全性も一致する。
proof fn lemma_trans(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    a: int,
    p: Seq<SVal>,
    ps: Seq<i64>,
    vs: Seq<SVal>,
    xs: Seq<i64>,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        0 <= a < sm.actions@.len(),
        rel(st, p, m.state_types@, ps, sm.enums@),
        layouts_ok(cs[a].args@, vs, m.actions@[a].domains@, xs, sm.enums@),
        vals_ok(sm.enums@, m.actions@[a].domains@, xs),
    ensures
        step_rel(s_step(sm, cv, a, vs, p), step_spec(m, a, xs, ps), st, m.state_types@, sm.actions@[a].output, sm.enums@),
        forall|c: Conditions| trans_safe(m, c, a, xs, ps) <==> #[trigger] s_trans_safe(sm, cv, c, a, vs, p),
{
    let enums = sm.enums@;
    assert(action_low(sm, cv, m, st, cs[a], a));
    lemma_env_act(sm, cv, m, st, cs[a], a, p, ps, vs, xs);
    lemma_step(sm, cv, m, a, cs[a], p, ps, vs, xs);
    assert forall|c: Conditions| trans_safe(m, c, a, xs, ps) <==> #[trigger] s_trans_safe(sm, cv, c, a, vs, p) by {
        match (s_step(sm, cv, a, vs, p), step_spec(m, a, xs, ps)) {
            (SStep::To(t, o), Step::To(y, x)) => {
                assert forall|k: int|
                    #![trigger con_on(m, c, k)]
                    #![trigger s_con_on(sm, c, k)]
                    (con_on(m, c, k) && m.contracts@[k].action == a) == (s_con_on(sm, c, k) && sm.contracts@[k].action
                        == a) && (con_on(m, c, k) && m.contracts@[k].action == a ==> con_spec(m, k, ps, xs, y, x) == s_con(
                        sm,
                        cv,
                        k,
                        p,
                        vs,
                        t,
                        o,
                    )) by {
                    if 0 <= k < sm.contracts@.len() {
                        assert(contract_low(sm, cv, m, st, ks[k], k));
                        if m.contracts@[k].action == a {
                            lemma_con(sm, cv, m, st, cs, ks, sx, k, p, ps, vs, xs, t, y, o, x);
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

/// 値を表す状態では、状態の安全性が一致する。
proof fn lemma_state_safe(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    c: Conditions,
    s: Seq<SVal>,
    y: Seq<i64>,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        rel(st, s, m.state_types@, y, sm.enums@),
    ensures
        state_safe(m, c, y) <==> s_state_safe(sm, cv, c, s),
{
    let enums = sm.enums@;
    assert forall|i: int|
        #![trigger inv_on(m, c, i)]
        #![trigger s_inv_on(sm, c, i)]
        inv_on(m, c, i) == s_inv_on(sm, c, i) && (inv_on(m, c, i) ==> inv_spec(m, i, y) == s_prop(
            sm,
            cv,
            sm.invariants@[i],
            s,
        )) by {
        if inv_on(m, c, i) {
            lemma_prop(sm, cv, m, st, sx, sm.invariants@[i], m.invariants@[i], s, y);
        }
    }
    assert(invs_hold(m, c, y) == s_invs_hold(sm, cv, c, s));
    // 遷移
    assert forall|a: int, vs: Seq<SVal>| #[trigger] s_act_on(sm, c, a) && #[trigger] s_args_ok(sm, a, vs) implies act_on(
        m,
        c,
        a,
    ) && args_ok(m, a, arg_codes(sm, a, vs)) && (trans_safe(m, c, a, arg_codes(sm, a, vs), y) <==> s_trans_safe(
        sm,
        cv,
        c,
        a,
        vs,
        s,
    )) && (step_spec(m, a, arg_codes(sm, a, vs), y) is Disabled <==> s_step(sm, cv, a, vs, s) is Disabled) by {
        lemma_arg_codes(sm, cv, m, st, cs, ks, sx, a, vs);
        lemma_trans(sm, cv, m, st, cs, ks, sx, a, s, y, vs, arg_codes(sm, a, vs));
        assert(s_trans_safe(sm, cv, c, a, vs, s) == s_trans_safe(sm, cv, c, a, vs, s));
    }
    assert forall|a: int, xs: Seq<i64>| #[trigger] act_on(m, c, a) && #[trigger] args_ok(m, a, xs) implies s_act_on(
        sm,
        c,
        a,
    ) && ((step_spec(m, a, xs, y) is Disabled && trans_safe(m, c, a, xs, y)) || (s_args_ok(
        sm,
        a,
        arg_vals(cs[a].args@, act_env(m, a, xs, y), enums),
    ) && (trans_safe(m, c, a, xs, y) <==> s_trans_safe(
        sm,
        cv,
        c,
        a,
        arg_vals(cs[a].args@, act_env(m, a, xs, y), enums),
        s,
    )) && (step_spec(m, a, xs, y) is Disabled <==> s_step(
        sm,
        cv,
        a,
        arg_vals(cs[a].args@, act_env(m, a, xs, y), enums),
        s,
    ) is Disabled))) by {
        assert(action_low(sm, cv, m, st, cs[a], a));
        if canon_from(cs[a].args@, 0, act_env(m, a, xs, y), enums) {
            let vs = arg_vals(cs[a].args@, act_env(m, a, xs, y), enums);
            lemma_core_args(sm, cv, m, st, cs, ks, sx, a, xs, y);
            lemma_trans(sm, cv, m, st, cs, ks, sx, a, s, y, vs, xs);
            assert(s_trans_safe(sm, cv, c, a, vs, s) == s_trans_safe(sm, cv, c, a, vs, s));
        } else {
            lemma_step_off(sm.actions@[a], m, a, cs[a], y, xs);
        }
    }
    // 終端
    match (sm.terminal, m.terminal) {
        (Some(e), Some(x)) => {
            lemma_prop(sm, cv, m, st, sx, e, x, s, y);
        },
        _ => {},
    }
    assert(terminal_spec(m, y) == s_terminal(sm, cv, s));
    assert(stuck(m, c, y) == s_stuck(sm, cv, c, s)) by {
        if stuck(m, c, y) {
            assert forall|a: int, vs: Seq<SVal>| #[trigger] s_act_on(sm, c, a) && #[trigger] s_args_ok(sm, a, vs) implies s_step(
                sm,
                cv,
                a,
                vs,
                s,
            ) is Disabled by {
                assert(all_disabled(m, a, y));
                assert(args_ok(m, a, arg_codes(sm, a, vs)));
            }
        }
        if s_stuck(sm, cv, c, s) {
            assert forall|a: int| #[trigger] act_on(m, c, a) implies all_disabled(m, a, y) by {
                assert forall|xs: Seq<i64>| #[trigger] args_ok(m, a, xs) implies step_spec(m, a, xs, y) is Disabled by {
                    assert(act_on(m, c, a) && args_ok(m, a, xs));
                }
            }
        }
    }
    if state_safe(m, c, y) {
        assert forall|a: int, vs: Seq<SVal>| #[trigger] s_act_on(sm, c, a) && #[trigger] s_args_ok(sm, a, vs) implies s_trans_safe(
            sm,
            cv,
            c,
            a,
            vs,
            s,
        ) by {
            assert(act_on(m, c, a) && args_ok(m, a, arg_codes(sm, a, vs)));
        }
    }
    if s_state_safe(sm, cv, c, s) {
        assert forall|a: int, xs: Seq<i64>| #[trigger] act_on(m, c, a) && #[trigger] args_ok(m, a, xs) implies trans_safe(
            m,
            c,
            a,
            xs,
            y,
        ) by {
            assert(act_on(m, c, a) && args_ok(m, a, xs));
        }
    }
}

// ---- 到達可能性の対応 ----

/// 中核の到達可能な状態は、到達可能な値の状態を表す。
proof fn lemma_reach_core(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    c: Conditions,
    y: Seq<i64>,
    n: nat,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        reach(m, c, y, n),
    ensures
        exists|s: Seq<SVal>| s_reach(sm, cv, c, s, n) && #[trigger] rel(st, s, m.state_types@, y, sm.enums@),
    decreases n,
{
    let enums = sm.enums@;
    if n == 0 {
        let i = choose|i: int| 0 <= i < m.inits@.len() && (#[trigger] m.inits@[i])@ == y;
        assert(init_src(sm, cv, st, m.state_types@, m.inits@[i]@));
    } else {
        let (q, a, xs, x) = choose|q: Seq<i64>, a: int, xs: Seq<i64>, x: Option<i64>|
            reach(m, c, q, (n - 1) as nat) && #[trigger] is_edge(m, c, q, a, xs, x, y);
        lemma_reach_core(sm, cv, m, st, cs, ks, sx, c, q, (n - 1) as nat);
        let p = choose|p: Seq<SVal>| s_reach(sm, cv, c, p, (n - 1) as nat) && #[trigger] rel(st, p, m.state_types@, q, enums);
        assert(action_low(sm, cv, m, st, cs[a], a));
        if !canon_from(cs[a].args@, 0, act_env(m, a, xs, q), enums) {
            lemma_step_off(sm.actions@[a], m, a, cs[a], q, xs);
        }
        let vs = arg_vals(cs[a].args@, act_env(m, a, xs, q), enums);
        lemma_core_args(sm, cv, m, st, cs, ks, sx, a, xs, q);
        lemma_trans(sm, cv, m, st, cs, ks, sx, a, p, q, vs, xs);
        let (t, o) = match s_step(sm, cv, a, vs, p) {
            SStep::To(t, o) => (t, o),
            _ => (p, None),
        };
        assert(s_edge(sm, cv, c, p, a, vs, o, t));
        assert(s_reach(sm, cv, c, t, n));
        assert(rel(st, t, m.state_types@, y, enums));
    }
}

/// 到達可能な値の状態は、到達可能な中核の状態に表される。
proof fn lemma_reach_src(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    c: Conditions,
    s: Seq<SVal>,
    n: nat,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
        s_reach(sm, cv, c, s, n),
    ensures
        exists|y: Seq<i64>| reach(m, c, y, n) && #[trigger] rel(st, s, m.state_types@, y, sm.enums@),
    decreases n,
{
    let enums = sm.enums@;
    if n == 0 {
        let k = choose|k: int| 0 <= k < m.inits@.len() && #[trigger] rel(st, s, m.state_types@, m.inits@[k]@, enums);
        assert(is_init(m, m.inits@[k]@));
        assert(reach(m, c, m.inits@[k]@, 0));
    } else {
        let (p, a, vs, o) = choose|p: Seq<SVal>, a: int, vs: Seq<SVal>, o: Option<SVal>|
            s_reach(sm, cv, c, p, (n - 1) as nat) && #[trigger] s_edge(sm, cv, c, p, a, vs, o, s);
        lemma_reach_src(sm, cv, m, st, cs, ks, sx, c, p, (n - 1) as nat);
        let q = choose|q: Seq<i64>| reach(m, c, q, (n - 1) as nat) && #[trigger] rel(st, p, m.state_types@, q, enums);
        let xs = arg_codes(sm, a, vs);
        lemma_arg_codes(sm, cv, m, st, cs, ks, sx, a, vs);
        lemma_trans(sm, cv, m, st, cs, ks, sx, a, p, q, vs, xs);
        let (y, x) = match step_spec(m, a, xs, q) {
            Step::To(y, x) => (y, x),
            _ => (q, None),
        };
        assert(is_edge(m, c, q, a, xs, x, y));
        assert(reach(m, c, y, n));
        assert(rel(st, s, m.state_types@, y, enums));
    }
}

/// 下ろしは安全性を保存する。中核のモデルが安全であることと、値の上のモデルが安全であることは同値である。
pub proof fn lemma_safe(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
    c: Conditions,
)
    requires
        model_ok(sm, cv, m, st, cs, ks, sx),
    ensures
        safe(m, c) <==> s_safe(sm, cv, c),
{
    if safe(m, c) {
        assert forall|s: Seq<SVal>, n: nat| #[trigger] s_reach(sm, cv, c, s, n) implies s_state_safe(sm, cv, c, s) by {
            lemma_reach_src(sm, cv, m, st, cs, ks, sx, c, s, n);
            let y = choose|y: Seq<i64>| reach(m, c, y, n) && #[trigger] rel(st, s, m.state_types@, y, sm.enums@);
            lemma_state_safe(sm, cv, m, st, cs, ks, sx, c, s, y);
        }
    }
    if s_safe(sm, cv, c) {
        assert forall|y: Seq<i64>, n: nat| #[trigger] reach(m, c, y, n) implies state_safe(m, c, y) by {
            lemma_reach_core(sm, cv, m, st, cs, ks, sx, c, y, n);
            let s = choose|s: Seq<SVal>| s_reach(sm, cv, c, s, n) && #[trigger] rel(st, s, m.state_types@, y, sm.enums@);
            lemma_state_safe(sm, cv, m, st, cs, ks, sx, c, s, y);
        }
    }
}

} // verus!
