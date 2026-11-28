//! モデルの下ろしの結果の性質（仕様）。下ろした中核のモデルが、名前を解決したモデルのどの部分をどの文脈で下ろしたものか（`model_ok`、`action_at`、`contract_at` など）。証明は `model_safe` と `model_wf` にある。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{eval_l, Env};
#[cfg(verus_keep_ghost)]
use crate::kernel::model::{Action, Contract, Expr, RawModel, Type};
#[cfg(verus_keep_ghost)]
use crate::model::action_lower::act_ok;
#[cfg(verus_keep_ghost)]
use crate::model::srel::{consts_rel, rel};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_ctx::{layouts_at, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{env_rel, prop_result};
#[cfg(verus_keep_ghost)]
use crate::slot::slot_types::slot_tys_seq;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{sty, wf_stypes, SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::value::limits::smalls;
#[cfg(verus_keep_ghost)]
use crate::value::smodel::{s_arg_tys, s_init, s_state_tys, SModel, SOutput};
#[cfg(verus_keep_ghost)]
use crate::value::source::{eval_src, SEnv, TExpr};
use vstd::prelude::*;

verus! {

/// 文脈の出力の型は、操作の出力の型である。
pub open spec fn out_ty(t: Option<SType>, so: Option<SOutput>) -> bool {
    match (t, so) {
        (None, None) => true,
        (Some(t), Some(s)) => sty(t) == sty(s.ty),
        _ => false,
    }
}

/// 下ろしの文脈 `cx` の中身。
pub open spec fn ctx_is(
    cx: LowerCtx,
    enums: Seq<i64>,
    cv: Seq<SVal>,
    st: Seq<Layout>,
    la: Seq<Layout>,
    next: bool,
    so: Option<SOutput>,
) -> bool {
    &&& cx.enums@ == enums
    &&& cx.states matches Some(s) && s@ == st
    &&& cx.args@ == la
    &&& cx.next == next
    &&& out_ty(cx.out, so)
    &&& consts_rel(cx.consts@, cv, enums)
}

/// 中核の式 `c` は、値の上の式 `e` を文脈 `cx` で下ろしたものである。
pub open spec fn prop_low(e: TExpr, cx: LowerCtx, c: Expr) -> bool {
    forall|env: Env, se: SEnv|
        #[trigger] env_rel(cx, env, se) ==> prop_result(eval_src(e, se, Seq::empty()), eval_l(c, env, Seq::empty()))
}

/// 符号の列 `y` は、値の上のある初期状態を表す。
pub open spec fn init_src(sm: SModel, cv: Seq<SVal>, st: Seq<Layout>, tys: Seq<Type>, y: Seq<i64>) -> bool {
    exists|s: Seq<SVal>| s_init(sm, cv, s) && #[trigger] rel(st, s, tys, y, sm.enums@)
}

/// 中核の初期状態は、値の上の初期状態を表し、値の上の初期状態は、どれかの中核の初期状態に表される。
pub open spec fn init_ok(sm: SModel, cv: Seq<SVal>, m: RawModel, st: Seq<Layout>) -> bool {
    &&& forall|k: int| 0 <= k < m.inits@.len() ==> #[trigger] init_src(sm, cv, st, m.state_types@, m.inits@[k]@)
    &&& forall|s: Seq<SVal>|
        #[trigger] s_init(sm, cv, s) ==> exists|k: int|
            0 <= k < m.inits@.len() && #[trigger] rel(st, s, m.state_types@, m.inits@[k]@, sm.enums@)
}

/// 操作 `a` の下ろし。文脈 `cx` は、状態 `st` と操作の引数の文脈である。
pub open spec fn action_low(sm: SModel, cv: Seq<SVal>, m: RawModel, st: Seq<Layout>, cx: LowerCtx, a: int) -> bool {
    action_at(sm, cv, st, cx, a, m.actions@[a])
}

/// 遷移契約 `k` の下ろし。文脈 `kx` は、遷移後の状態と出力も参照できる、操作の文脈である。
/// 引数の位置は、操作の下ろしの文脈と同じである。
pub open spec fn contract_low(sm: SModel, cv: Seq<SVal>, m: RawModel, st: Seq<Layout>, kx: LowerCtx, k: int) -> bool {
    contract_at(sm, cv, st, kx, k, m.contracts@[k])
}

/// 中核のモデル `m` は、定数の値が `cv` のモデル `sm` を下ろしたものである。
/// `st` は状態変数の位置、`cs` は操作ごとの文脈、`ks` は遷移契約ごとの文脈、`sx` は状態だけの文脈。
pub open spec fn model_ok(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
    sx: LowerCtx,
) -> bool {
    let enums = sm.enums@;
    let ts = s_state_tys(sm);
    &&& m.enums@ == enums
    &&& layouts_at(st, ts, enums)
    &&& wf_stypes(ts, enums)
    &&& smalls(ts)
    &&& m.state_types@ == slot_tys_seq(ts, enums)
    &&& init_ok(sm, cv, m, st)
    &&& m.actions@.len() == sm.actions@.len()
    &&& cs.len() == sm.actions@.len()
    &&& forall|a: int| 0 <= a < cs.len() ==> #[trigger] action_low(sm, cv, m, st, cs[a], a)
    &&& ctx_is(sx, enums, cv, st, Seq::empty(), false, None)
    &&& m.invariants@.len() == sm.invariants@.len()
    &&& forall|i: int|
        0 <= i < sm.invariants@.len() ==> #[trigger] prop_low(sm.invariants@[i], sx, m.invariants@[i])
    &&& match (sm.terminal, m.terminal) {
        (None, None) => true,
        (Some(e), Some(x)) => prop_low(e, sx, x),
        _ => false,
    }
    &&& m.contracts@.len() == sm.contracts@.len()
    &&& ks.len() == sm.contracts@.len()
    &&& forall|k: int| 0 <= k < ks.len() ==> #[trigger] contract_low(sm, cv, m, st, ks[k], k)
}

/// 操作 `a` を文脈 `cx` で下ろした結果 `act` の性質。
pub open spec fn action_at(sm: SModel, cv: Seq<SVal>, st: Seq<Layout>, cx: LowerCtx, a: int, act: Action) -> bool {
    let ts = s_arg_tys(sm, a);
    &&& ctx_is(cx, sm.enums@, cv, st, cx.args@, false, None)
    &&& layouts_at(cx.args@, ts, sm.enums@)
    &&& wf_stypes(ts, sm.enums@)
    &&& smalls(ts)
    &&& act_ok(sm.actions@[a], cx, act)
}

/// 遷移契約 `k` を文脈 `kx` で下ろした結果 `con` の性質。
pub open spec fn contract_at(sm: SModel, cv: Seq<SVal>, st: Seq<Layout>, kx: LowerCtx, k: int, con: Contract) -> bool {
    let a = sm.contracts@[k].action as int;
    &&& con.action == sm.contracts@[k].action
    &&& a < sm.actions@.len()
    &&& ctx_is(kx, sm.enums@, cv, st, kx.args@, true, sm.actions@[a].output)
    &&& layouts_at(kx.args@, s_arg_tys(sm, a), sm.enums@)
    &&& prop_low(sm.contracts@[k].expr, kx, con.expr)
}

} // verus!
