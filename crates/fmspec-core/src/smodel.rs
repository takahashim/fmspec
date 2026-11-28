//! 名前を解決したIRのモデルと、値の上の意味論（仕様書 §5）。
//!
//! [`SModel`] は、型付きの式の木（[`TExpr`]）で書いたモデルで、`fmspec-ir` が名前を解決して作る。
//! 状態は状態変数ごとの値の列で、遷移、到達可能性、安全性は、
//! 中核のモデルの定義（[`crate::semantics`]）と同じ形で値の上に定める。
//!
//! 中核の状態は、状態変数ごとの値の正規形の符号化をつなげた符号の列である。
//! 中核の符号の列と値の列の対応は [`crate::srel::rel`] で、各状態変数のスロットが値の符号化になっていることである。

#[cfg(verus_keep_ghost)]
use crate::encoding::{member, members, sty, stys, STy};
use crate::encoding::{SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::eval::ErrKind;
#[cfg(verus_keep_ghost)]
use crate::semantics::Conditions;
use crate::source::TExpr;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, src_bool, SEnv};
use vstd::prelude::*;

verus! {

// ---- モデル ----

/// 状態変数 `var` への代入。
pub struct SUpdate {
    pub var: usize,
    pub expr: TExpr,
}

/// 操作の出力。型はBool、Int、Enumのどれかである。
pub struct SOutput {
    pub ty: SType,
    pub expr: TExpr,
}

pub struct SAction {
    /// 公開引数のスロットの数（中核の操作の `n_params`）。
    pub n_params: usize,
    /// 公開引数に続けて内部選択の型。
    pub args: Vec<SType>,
    /// 動的ドメイン（`in`）の検査を含む。
    pub guard: TExpr,
    pub updates: Vec<SUpdate>,
    pub output: Option<SOutput>,
}

pub struct SContract {
    pub action: usize,
    pub expr: TExpr,
}

/// 名前付きの定数。式は、それより前の定数だけを参照できる。
pub struct SConst {
    pub ty: SType,
    pub expr: TExpr,
}

pub struct SModel {
    /// 各列挙型のラベルの数。
    pub enums: Vec<i64>,
    pub consts: Vec<SConst>,
    pub states: Vec<SType>,
    /// 状態変数ごとの初期値の候補。
    pub inits: Vec<Vec<TExpr>>,
    /// 初期条件。
    pub constraint: Option<TExpr>,
    pub actions: Vec<SAction>,
    pub invariants: Vec<TExpr>,
    pub contracts: Vec<SContract>,
    pub terminal: Option<TExpr>,
}

// ---- 値の上の意味論 ----

pub open spec fn s_env(
    sm: SModel,
    cv: Seq<SVal>,
    pre: Seq<SVal>,
    args: Seq<SVal>,
    post: Seq<SVal>,
    out: Option<SVal>,
) -> SEnv {
    SEnv { pre: pre, args: args, post: post, out: out, consts: cv, enums: sm.enums@ }
}

pub open spec fn s_state_tys(sm: SModel) -> Seq<STy> {
    stys(sm.states@)
}

pub open spec fn s_arg_tys(sm: SModel, a: int) -> Seq<STy> {
    stys(sm.actions@[a].args@)
}

/// 定数の値 `cv` は、定数の式の値である。各式は、それより前の定数の値のもとで評価する。
pub open spec fn consts_ok(sm: SModel, cv: Seq<SVal>) -> bool {
    &&& cv.len() == sm.consts@.len()
    &&& forall|i: int|
        0 <= i < cv.len() ==> eval_src(
            (#[trigger] sm.consts@[i]).expr,
            s_env(sm, cv.take(i), Seq::empty(), Seq::empty(), Seq::empty(), None),
            Seq::empty(),
        ) == Ok::<SVal, ErrKind>(cv[i]) && member(cv[i], sty(sm.consts@[i].ty), sm.enums@)
}

proof fn lemma_consts_prefix(sm: SModel, a: Seq<SVal>, b: Seq<SVal>, i: int)
    requires
        consts_ok(sm, a),
        consts_ok(sm, b),
        0 <= i <= a.len(),
    ensures
        a.take(i) == b.take(i),
    decreases i,
{
    if i == 0 {
        assert(a.take(0) =~= b.take(0));
    } else {
        lemma_consts_prefix(sm, a, b, i - 1);
        let e = sm.consts@[i - 1].expr;
        let ea = s_env(sm, a.take(i - 1), Seq::empty(), Seq::empty(), Seq::empty(), None);
        let eb = s_env(sm, b.take(i - 1), Seq::empty(), Seq::empty(), Seq::empty(), None);
        assert(ea == eb);
        assert(eval_src(e, ea, Seq::empty()) == Ok::<SVal, ErrKind>(a[i - 1]));
        assert(eval_src(e, eb, Seq::empty()) == Ok::<SVal, ErrKind>(b[i - 1]));
        assert(a.take(i) =~= a.take(i - 1).push(a[i - 1]));
        assert(b.take(i) =~= b.take(i - 1).push(b[i - 1]));
    }
}

/// 定数の値は、定数の式から一意に決まる。
pub proof fn lemma_consts_unique(sm: SModel, a: Seq<SVal>, b: Seq<SVal>)
    requires
        consts_ok(sm, a),
        consts_ok(sm, b),
    ensures
        a == b,
{
    lemma_consts_prefix(sm, a, b, a.len() as int);
    assert(a.take(a.len() as int) =~= a);
    assert(b.take(b.len() as int) =~= b);
}

/// 1つの代入。値が状態変数の型に属さなければ失敗する。
pub open spec fn s_write(u: SUpdate, env: SEnv, tys: Seq<STy>, acc: Seq<SVal>) -> Option<Seq<SVal>> {
    match eval_src(u.expr, env, Seq::empty()) {
        Ok(v) => if u.var < acc.len() && u.var < tys.len() && member(v, tys[u.var as int], env.enums) {
            Some(acc.update(u.var as int, v))
        } else {
            None
        },
        Err(_) => None,
    }
}

/// 代入の列を、記述の順に `acc` に適用する。式はどれも遷移前の環境 `env` で評価する。
pub open spec fn s_apply(ups: Seq<SUpdate>, env: SEnv, tys: Seq<STy>, acc: Seq<SVal>) -> Option<Seq<SVal>>
    decreases ups.len(),
{
    if ups.len() == 0 {
        Some(acc)
    } else {
        match s_apply(ups.drop_last(), env, tys, acc) {
            None => None,
            Some(t) => s_write(ups.last(), env, tys, t),
        }
    }
}

/// 出力の評価。失敗なら `None`、出力のない操作では `Some(None)`。
pub open spec fn s_output(o: Option<SOutput>, env: SEnv) -> Option<Option<SVal>> {
    match o {
        None => Some(None),
        Some(so) => match eval_src(so.expr, env, Seq::empty()) {
            Ok(v) => if member(v, sty(so.ty), env.enums) {
                Some(Some(v))
            } else {
                None
            },
            Err(_) => None,
        },
    }
}

/// 値の上の遷移の結果。
pub ghost enum SStep {
    Disabled,
    Fail,
    To(Seq<SVal>, Option<SVal>),
}

/// 操作 `a` を引数 `args` で状態 `s` に適用する。guard、代入、出力の順に評価する。
pub open spec fn s_step(sm: SModel, cv: Seq<SVal>, a: int, args: Seq<SVal>, s: Seq<SVal>) -> SStep {
    let act = sm.actions@[a];
    let env = s_env(sm, cv, s, args, Seq::empty(), None);
    match src_bool(eval_src(act.guard, env, Seq::empty())) {
        Err(_) => SStep::Fail,
        Ok(false) => SStep::Disabled,
        Ok(true) => match s_apply(act.updates@, env, s_state_tys(sm), s) {
            None => SStep::Fail,
            Some(t) => match s_output(act.output, env) {
                None => SStep::Fail,
                Some(o) => SStep::To(t, o),
            },
        },
    }
}

pub open spec fn s_args_ok(sm: SModel, a: int, args: Seq<SVal>) -> bool {
    members(args, s_arg_tys(sm, a), sm.enums@)
}

pub open spec fn s_act_on(sm: SModel, c: Conditions, a: int) -> bool {
    0 <= a < sm.actions@.len() && a < c.actions@.len() && c.actions@[a]
}

pub open spec fn s_inv_on(sm: SModel, c: Conditions, i: int) -> bool {
    0 <= i < sm.invariants@.len() && i < c.invariants@.len() && c.invariants@[i]
}

pub open spec fn s_con_on(sm: SModel, c: Conditions, k: int) -> bool {
    0 <= k < sm.contracts@.len() && k < c.contracts@.len() && c.contracts@[k]
}

/// 状態の性質（不変条件、終端条件、初期条件）の評価。
pub open spec fn s_prop(sm: SModel, cv: Seq<SVal>, e: TExpr, s: Seq<SVal>) -> Result<bool, ErrKind> {
    src_bool(eval_src(e, s_env(sm, cv, s, Seq::empty(), Seq::empty(), None), Seq::empty()))
}

pub open spec fn s_terminal(sm: SModel, cv: Seq<SVal>, s: Seq<SVal>) -> Result<bool, ErrKind> {
    match sm.terminal {
        None => Ok(false),
        Some(e) => s_prop(sm, cv, e, s),
    }
}

/// 遷移契約 `k` の、遷移 `pre --(args, o)--> post` での評価。
pub open spec fn s_con(
    sm: SModel,
    cv: Seq<SVal>,
    k: int,
    pre: Seq<SVal>,
    args: Seq<SVal>,
    post: Seq<SVal>,
    o: Option<SVal>,
) -> Result<bool, ErrKind> {
    let con = sm.contracts@[k];
    if con.action < sm.actions@.len() {
        src_bool(eval_src(con.expr, s_env(sm, cv, pre, args, post, o), Seq::empty()))
    } else {
        Err(ErrKind::Unbound)
    }
}

/// 初期値の候補の式の値。
pub open spec fn s_cand(sm: SModel, cv: Seq<SVal>, e: TExpr) -> Result<SVal, ErrKind> {
    eval_src(e, s_env(sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None), Seq::empty())
}

/// `v` は、状態変数 `i` の初期値の候補のどれかの値である。
pub open spec fn s_init_var(sm: SModel, cv: Seq<SVal>, i: int, v: SVal) -> bool {
    exists|j: int| 0 <= j < sm.inits@[i].len() && #[trigger] s_cand(sm, cv, sm.inits@[i][j]) == Ok::<SVal, ErrKind>(v)
}

/// `s` は初期状態である。各状態変数の値は候補のどれかの値で型に属し、初期条件を満たす。
pub open spec fn s_init(sm: SModel, cv: Seq<SVal>, s: Seq<SVal>) -> bool {
    &&& s.len() == sm.states@.len()
    &&& members(s, s_state_tys(sm), sm.enums@)
    &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] s_init_var(sm, cv, i, s[i])
    &&& match sm.constraint {
        None => true,
        Some(e) => s_prop(sm, cv, e, s) == Ok::<bool, ErrKind>(true),
    }
}

pub open spec fn s_edge(
    sm: SModel,
    cv: Seq<SVal>,
    c: Conditions,
    p: Seq<SVal>,
    a: int,
    args: Seq<SVal>,
    o: Option<SVal>,
    s: Seq<SVal>,
) -> bool {
    s_act_on(sm, c, a) && s_args_ok(sm, a, args) && s_step(sm, cv, a, args, p) == SStep::To(s, o)
}

pub open spec fn s_reach(sm: SModel, cv: Seq<SVal>, c: Conditions, s: Seq<SVal>, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        s_init(sm, cv, s)
    } else {
        exists|p: Seq<SVal>, a: int, args: Seq<SVal>, o: Option<SVal>|
            s_reach(sm, cv, c, p, (n - 1) as nat) && #[trigger] s_edge(sm, cv, c, p, a, args, o, s)
    }
}

pub open spec fn s_invs_hold(sm: SModel, cv: Seq<SVal>, c: Conditions, s: Seq<SVal>) -> bool {
    forall|i: int| #[trigger] s_inv_on(sm, c, i) ==> s_prop(sm, cv, sm.invariants@[i], s) == Ok::<bool, ErrKind>(true)
}

pub open spec fn s_cons_hold(
    sm: SModel,
    cv: Seq<SVal>,
    c: Conditions,
    a: int,
    pre: Seq<SVal>,
    args: Seq<SVal>,
    post: Seq<SVal>,
    o: Option<SVal>,
) -> bool {
    forall|k: int| #[trigger]
        s_con_on(sm, c, k) && sm.contracts@[k].action == a ==> s_con(sm, cv, k, pre, args, post, o) == Ok::<
            bool,
            ErrKind,
        >(true)
}

pub open spec fn s_trans_safe(sm: SModel, cv: Seq<SVal>, c: Conditions, a: int, args: Seq<SVal>, s: Seq<SVal>) -> bool {
    match s_step(sm, cv, a, args, s) {
        SStep::Disabled => true,
        SStep::Fail => false,
        SStep::To(t, o) => s_cons_hold(sm, cv, c, a, s, args, t, o),
    }
}

pub open spec fn s_stuck(sm: SModel, cv: Seq<SVal>, c: Conditions, s: Seq<SVal>) -> bool {
    forall|a: int, args: Seq<SVal>|
        #[trigger] s_act_on(sm, c, a) && #[trigger] s_args_ok(sm, a, args) ==> s_step(sm, cv, a, args, s) is Disabled
}

pub open spec fn s_no_deadlock(sm: SModel, cv: Seq<SVal>, c: Conditions, s: Seq<SVal>) -> bool {
    c.deadlock && s_stuck(sm, cv, c, s) ==> s_terminal(sm, cv, s) == Ok::<bool, ErrKind>(true)
}

pub open spec fn s_state_safe(sm: SModel, cv: Seq<SVal>, c: Conditions, s: Seq<SVal>) -> bool {
    &&& s_invs_hold(sm, cv, c, s)
    &&& forall|a: int, args: Seq<SVal>|
        #[trigger] s_act_on(sm, c, a) && #[trigger] s_args_ok(sm, a, args) ==> s_trans_safe(sm, cv, c, a, args, s)
    &&& s_no_deadlock(sm, cv, c, s)
}

/// 値の上の安全性。到達できるすべての状態と有効な遷移が性質を満たし、評価エラーがない。
pub open spec fn s_safe(sm: SModel, cv: Seq<SVal>, c: Conditions) -> bool {
    forall|s: Seq<SVal>, n: nat| #[trigger] s_reach(sm, cv, c, s, n) ==> s_state_safe(sm, cv, c, s)
}

} // verus!
