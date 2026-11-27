//! 名前を解決したIRのモデルと、値の上の意味論（仕様書 §5）。
//!
//! [`SModel`] は、型付きの式の木（[`TExpr`]）で書いたモデルで、`fmspec-ir` が名前を解決して作る。
//! 状態は状態変数ごとの値の列で、遷移、到達可能性、安全性は、
//! 中核のモデルの定義（[`crate::semantics`]）と同じ形で値の上に定める。
//!
//! 中核の状態は、状態変数ごとの値の正規形の符号化をつなげた符号の列である。
//! 中核の符号の列と値の列の対応は [`rel`] で、各状態変数のスロットが値の符号化になっていることである。

#[cfg(verus_keep_ghost)]
use crate::canon::{canon_ok, canon_wf};
use crate::canon::{canonical, slot_types_list};
#[cfg(verus_keep_ghost)]
use crate::canon::{in_slot, in_slots, lemma_member_in, lemma_seq_in, lemma_slot_tys_len, lemma_slot_tys_seq_len};
#[cfg(verus_keep_ghost)]
use crate::canon::{lemma_enc_seq_sub, lemma_slot_tys_seq_sub, lemma_wf_index, slot_tys, slot_tys_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::lemma_enc_len;
use crate::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, enc_seq, member, members, sty, stys, wf_stype, wf_stypes, width, width_sum};
use crate::encoding::{STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::equality::smalls;
use crate::eval::ErrKind;
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, code_of, decode, eval_l, eval_spec, lookup, prop_spec, Env};
use crate::expr_copy::copy_expr;
use crate::lowering::{lower_prop, lower_stored, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::model::RawModel;
#[cfg(verus_keep_ghost)]
use crate::model::Value;
use crate::model::{Action, Expr, Output, Type, Update};
#[cfg(verus_keep_ghost)]
use crate::preserve::{clean, layout_ok, layouts_ok, lemma_members, pure_below, slot_vals, stored_result, top_ok};
#[cfg(verus_keep_ghost)]
use crate::preserve::{env_rel, prop_result};
#[cfg(verus_keep_ghost)]
use crate::semantics::Conditions;
use crate::slots::stype_width;
use crate::source::TExpr;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, src_bool, SEnv};
#[cfg(verus_keep_ghost)]
use crate::step::{act_env, apply_updates, encode_spec, in_type, output_spec, step_spec, vals_ok, Step};
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

// ---- 符号の列と値の列の対応 ----

/// `l` は、型の列 `ts` の `i` 番目の位置である。位置は、それより前の型の幅の和である。
pub open spec fn layout_at(l: Layout, ts: Seq<STy>, i: int, enums: Seq<i64>) -> bool {
    sty(l.ty) == ts[i] && l.offset == width_sum(ts.take(i), enums)
}

pub open spec fn layouts_at(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>) -> bool {
    &&& ls.len() == ts.len()
    &&& width_sum(ts, enums) <= usize::MAX
    &&& forall|i: int| 0 <= i < ls.len() ==> #[trigger] layout_at(ls[i], ts, i, enums)
}

/// 符号の列 `xs` は型 `tys` に従い、値の列 `vs` を表す。
pub open spec fn rel(ls: Seq<Layout>, vs: Seq<SVal>, tys: Seq<Type>, xs: Seq<i64>, enums: Seq<i64>) -> bool {
    layouts_ok(ls, vs, tys, xs, enums) && vals_ok(enums, tys, xs)
}

/// 値の列の符号。
pub open spec fn codes(xs: Seq<Value>) -> Seq<i64> {
    Seq::new(xs.len(), |q: int| code_of(xs[q]))
}

/// スロットの型の値の符号は型に属し、符号を値に戻すと元の値になる。
pub proof fn lemma_code_in(ty: Type, x: Value, enums: Seq<i64>)
    requires
        in_slot(ty, x, enums),
    ensures
        in_type(enums, ty, code_of(x)),
        decode(ty, code_of(x)) == x,
        encode_spec(enums, ty, x) == Ok::<i64, ErrKind>(code_of(x)),
{
}

/// 型に属する符号を値に戻すと、スロットの型の値で、符号は元の符号である。
pub proof fn lemma_decode_in(ty: Type, x: i64, enums: Seq<i64>)
    requires
        in_type(enums, ty, x),
    ensures
        in_slot(ty, decode(ty, x), enums),
        code_of(decode(ty, x)) == x,
{
}

/// 型の列の幅の累積和は増える。
proof fn lemma_width_mono(ts: Seq<STy>, i: int, j: int, enums: Seq<i64>)
    requires
        0 <= i <= j <= ts.len(),
    ensures
        width_sum(ts.take(i), enums) <= width_sum(ts.take(j), enums),
        j == i + 1 ==> width_sum(ts.take(j), enums) == width_sum(ts.take(i), enums) + width(ts[i], enums),
    decreases j - i,
{
    if i < j {
        lemma_width_mono(ts, i, j - 1, enums);
        assert(ts.take(j).drop_last() =~= ts.take(j - 1));
        assert(ts.take(j).last() == ts[j - 1]);
    }
}

/// 型の列の幅の累積和は増え、全体の幅を超えない。
pub proof fn lemma_width_take(ts: Seq<STy>, i: int, j: int, enums: Seq<i64>)
    requires
        0 <= i <= j <= ts.len(),
    ensures
        width_sum(ts.take(i), enums) <= width_sum(ts.take(j), enums),
        j == i + 1 ==> width_sum(ts.take(j), enums) == width_sum(ts.take(i), enums) + width(ts[i], enums),
        width_sum(ts.take(j), enums) <= width_sum(ts, enums),
{
    lemma_width_mono(ts, i, j, enums);
    lemma_width_mono(ts, j, ts.len() as int, enums);
    assert(ts.take(ts.len() as int) =~= ts);
}

/// 型に属する値の列の符号は、値の列を表す。
pub proof fn lemma_rel_codes(ls: Seq<Layout>, vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(ls, ts, enums),
        members(vs, ts, enums),
        wf_stypes(ts, enums),
        smalls(ts),
    ensures
        rel(ls, vs, slot_tys_seq(ts, enums), codes(enc_seq(vs, ts, enums)), enums),
{
    let s = enc_seq(vs, ts, enums);
    let tys = slot_tys_seq(ts, enums);
    let xs = codes(s);
    lemma_seq_in(vs, ts, enums);
    lemma_members(vs, ts, enums);
    assert forall|q: int| 0 <= q < tys.len() implies in_type(enums, #[trigger] tys[q], xs[q]) by {
        assert(in_slot(tys[q], s[q], enums));
        lemma_code_in(tys[q], s[q], enums);
    }
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] layout_ok(ls[i], vs[i], tys, xs, enums) by {
        assert(layout_at(ls[i], ts, i, enums));
        let t = ts[i];
        let off = width_sum(ts.take(i), enums) as int;
        lemma_enc_seq_sub(vs, ts, i, enums);
        lemma_slot_tys_seq_sub(ts, i, enums);
        lemma_wf_index(ts, i, enums);
        lemma_member_in(vs[i], t, enums);
        lemma_slot_tys_len(t, enums);
        lemma_slot_tys_seq_len(ts, enums);
        assert forall|j: int| 0 <= j < width(t, enums) implies #[trigger] lookup(tys, xs, (ls[i].offset + j) as usize)
            == Ok::<Value, ErrKind>(enc(vs[i], t, enums)[j]) by {
            assert(s.subrange(off, off + width(t, enums))[j] == s[off + j]);
            assert(tys.subrange(off, off + width(t, enums))[j] == tys[off + j]);
            assert(in_slot(slot_tys(t, enums)[j], enc(vs[i], t, enums)[j], enums));
            lemma_code_in(tys[off + j], s[off + j], enums);
        }
    }
}

// ---- 中核の更新の列 ----

/// 中核の1つの更新。
pub open spec fn c_write(u: Update, env: Env, enums: Seq<i64>, acc: Seq<i64>) -> Option<Seq<i64>> {
    match eval_spec(u.expr, env) {
        Ok(v) => if u.target < acc.len() && u.target < env.st_tys.len() {
            match encode_spec(enums, env.st_tys[u.target as int], v) {
                Ok(x) => Some(acc.update(u.target as int, x)),
                Err(_) => None,
            }
        } else {
            None
        },
        Err(_) => None,
    }
}

/// 中核の更新の列を、記述の順に適用する。
pub open spec fn c_apply(ups: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>) -> Option<Seq<i64>>
    decreases ups.len(),
{
    if ups.len() == 0 {
        Some(acc)
    } else {
        match c_apply(ups.drop_last(), env, enums, acc) {
            None => None,
            Some(t) => c_write(ups.last(), env, enums, t),
        }
    }
}

pub proof fn lemma_c_apply_concat(a: Seq<Update>, b: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    ensures
        c_apply(a + b, env, enums, acc) == match c_apply(a, env, enums, acc) {
            None => None,
            Some(t) => c_apply(b, env, enums, t),
        },
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        if c_apply(a, env, enums, acc) is Some {
            assert(c_apply(b, env, enums, c_apply(a, env, enums, acc)->Some_0) == c_apply(a, env, enums, acc));
        }
    } else {
        lemma_c_apply_concat(a, b.drop_last(), env, enums, acc);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

pub proof fn lemma_c_apply_first(u: Update, rest: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    ensures
        c_apply(seq![u] + rest, env, enums, acc) == match c_write(u, env, enums, acc) {
            None => None,
            Some(t) => c_apply(rest, env, enums, t),
        },
{
    lemma_c_apply_concat(seq![u], rest, env, enums, acc);
    assert(seq![u].drop_last() =~= Seq::<Update>::empty());
    assert(seq![u].last() == u);
    assert(c_apply(Seq::<Update>::empty(), env, enums, acc) == Some(acc));
    assert(c_apply(seq![u], env, enums, acc) == c_write(u, env, enums, acc));
}

// ---- 引数の正規形 ----

/// 引数 `l` のスロットの式。
pub open spec fn arg_slots(l: Layout, enums: Seq<i64>) -> Seq<Expr> {
    Seq::new(width(sty(l.ty), enums), |j: int| Expr::Arg((l.offset + j) as usize))
}

/// 引数 `la[i]` のスロットの値は、その型のある値の正規形の符号化である。
pub open spec fn canon_at(la: Seq<Layout>, i: int, env: Env, enums: Seq<i64>) -> bool {
    canon_ok(slot_vals(arg_slots(la[i], enums), env, Seq::empty()), sty(la[i].ty), enums)
}

/// `k` 番目以降の引数は正規形である。
pub open spec fn canon_from(la: Seq<Layout>, k: int, env: Env, enums: Seq<i64>) -> bool {
    forall|i: int| k <= i < la.len() ==> #[trigger] canon_at(la, i, env, enums)
}

/// 引数の符号は、ドメインのスロットの型に従う。
pub open spec fn dom_ok(env: Env, doms: Seq<Type>, enums: Seq<i64>) -> bool {
    env.arg_tys == doms && vals_ok(enums, doms, env.args)
}

/// `g` は、`k` 番目以降の引数が正規形なら `body` と同じ真偽になり、そうでなければ偽になる。
pub open spec fn fold_ok(g: Expr, body: Expr, la: Seq<Layout>, k: int, doms: Seq<Type>, enums: Seq<i64>) -> bool {
    forall|env: Env|
        dom_ok(env, doms, enums) ==> if canon_from(la, k, env, enums) {
            as_bool(#[trigger] eval_spec(g, env)) == as_bool(eval_spec(body, env))
        } else {
            eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false))
        }
}

/// 引数のスロットの式は純粋で、値はスロットの型の値である。
proof fn lemma_arg_slots(la: Seq<Layout>, i: int, env: Env, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        0 <= i < la.len(),
    ensures
        clean(arg_slots(la[i], enums), env, Seq::empty()),
        in_slots(slot_vals(arg_slots(la[i], enums), env, Seq::empty()), slot_tys(ts[i], enums), enums),
        la[i].offset + width(ts[i], enums) <= width_sum(ts, enums),
        forall|j: int|
            0 <= j < width(ts[i], enums) ==> #[trigger] eval_l(arg_slots(la[i], enums)[j], env, Seq::empty())
                == lookup(env.arg_tys, env.args, (la[i].offset + j) as usize),
{
    let t = ts[i];
    let doms = slot_tys_seq(ts, enums);
    let s = arg_slots(la[i], enums);
    let off = la[i].offset as int;
    assert(layout_at(la[i], ts, i, enums));
    lemma_slot_tys_seq_sub(ts, i, enums);
    lemma_slot_tys_seq_len(ts, enums);
    lemma_slot_tys_len(t, enums);
    let w = width(t, enums) as int;
    assert forall|j: int| 0 <= j < w implies #[trigger] eval_l(s[j], env, Seq::empty()) == lookup(
        env.arg_tys,
        env.args,
        (la[i].offset + j) as usize,
    ) && eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j]))
        && in_slot(slot_tys(t, enums)[j], decode(doms[off + j], env.args[off + j]), enums) by {
        assert(doms.subrange(off, off + w)[j] == doms[off + j]);
        assert(in_type(enums, doms[off + j], env.args[off + j]));
        lemma_decode_in(doms[off + j], env.args[off + j], enums);
    }
    assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], 0) && eval_l(s[j], env, Seq::empty()) is Ok by {
        assert(eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j])));
    }
    let sv = slot_vals(s, env, Seq::empty());
    assert forall|j: int| 0 <= j < sv.len() implies #[trigger] in_slot(slot_tys(t, enums)[j], sv[j], enums) by {
        assert(eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j])));
    }
}

/// 引数の正規形の判定式の値。
proof fn lemma_canon_eval(la: Seq<Layout>, i: int, env: Env, ts: Seq<STy>, enums: Seq<i64>, c: Expr)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        wf_stypes(ts, enums),
        smalls(ts),
        0 <= i < la.len(),
        canon_wf(sty(la[i].ty), arg_slots(la[i], enums), enums, c),
    ensures
        eval_spec(c, env) == Ok::<Value, ErrKind>(Value::Bool(canon_at(la, i, env, enums))),
{
    assert(layout_at(la[i], ts, i, enums));
    lemma_wf_index(ts, i, enums);
    lemma_arg_slots(la, i, env, ts, enums);
}

/// 値を表す引数の符号は、どれも正規形である。
pub proof fn lemma_rel_canon(la: Seq<Layout>, vs: Seq<SVal>, env: Env, enums: Seq<i64>)
    requires
        layouts_ok(la, vs, env.arg_tys, env.args, enums),
    ensures
        canon_from(la, 0, env, enums),
{
    assert forall|i: int| 0 <= i < la.len() implies #[trigger] canon_at(la, i, env, enums) by {
        assert(layout_ok(la[i], vs[i], env.arg_tys, env.args, enums));
        let t = sty(la[i].ty);
        let s = arg_slots(la[i], enums);
        let sv = slot_vals(s, env, Seq::empty());
        lemma_enc_len(vs[i], t, enums);
        assert forall|j: int| 0 <= j < sv.len() implies #[trigger] sv[j] == enc(vs[i], t, enums)[j] by {
            assert(lookup(env.arg_tys, env.args, (la[i].offset + j) as usize) == Ok::<Value, ErrKind>(
                enc(vs[i], t, enums)[j],
            ));
        }
        assert(sv =~= enc(vs[i], t, enums));
    }
}

/// 値の候補。引数の符号が正規形なら、その値。
pub open spec fn arg_val(la: Seq<Layout>, i: int, env: Env, enums: Seq<i64>) -> SVal {
    choose|v: SVal|
        member(v, sty(la[i].ty), enums) && #[trigger] enc(v, sty(la[i].ty), enums) == slot_vals(
            arg_slots(la[i], enums),
            env,
            Seq::empty(),
        )
}

pub open spec fn arg_vals(la: Seq<Layout>, env: Env, enums: Seq<i64>) -> Seq<SVal> {
    Seq::new(la.len(), |i: int| arg_val(la, i, env, enums))
}

/// 正規形の引数の符号は、値の列を表す。
pub proof fn lemma_canon_rel(la: Seq<Layout>, env: Env, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        canon_from(la, 0, env, enums),
    ensures
        layouts_ok(la, arg_vals(la, env, enums), env.arg_tys, env.args, enums),
{
    let vs = arg_vals(la, env, enums);
    assert forall|i: int| 0 <= i < la.len() implies #[trigger] layout_ok(la[i], vs[i], env.arg_tys, env.args, enums) by {
        assert(canon_at(la, i, env, enums));
        let t = sty(la[i].ty);
        let s = arg_slots(la[i], enums);
        let sv = slot_vals(s, env, Seq::empty());
        let v = vs[i];
        assert(member(v, t, enums) && enc(v, t, enums) == sv);
        lemma_arg_slots(la, i, env, ts, enums);
        assert(layout_at(la[i], ts, i, enums));
        assert forall|j: int| 0 <= j < width(t, enums) implies #[trigger] lookup(
            env.arg_tys,
            env.args,
            (la[i].offset + j) as usize,
        ) == Ok::<Value, ErrKind>(enc(v, t, enums)[j]) by {
            assert(eval_l(s[j], env, Seq::empty()) == lookup(env.arg_tys, env.args, (la[i].offset + j) as usize));
        }
    }
}

/// 引数 `l` のスロットの式を作る。
fn arg_exprs(l: &Layout, enums: &Vec<i64>) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(xs) ==> xs@ == arg_slots(*l, enums@),
{
    let w = stype_width(&l.ty, enums)?;
    let _ = l.offset.checked_add(w)?;
    let mut xs: Vec<Expr> = Vec::new();
    let mut j: usize = 0;
    while j < w
        invariant
            j <= w,
            w == width(sty(l.ty), enums@),
            l.offset + w <= usize::MAX,
            xs@ == arg_slots(*l, enums@).take(j as int),
        decreases w - j,
    {
        xs.push(Expr::Arg(l.offset + j));
        j += 1;
        proof {
            assert(xs@ =~= arg_slots(*l, enums@).take(j as int));
        }
    }
    proof {
        assert(arg_slots(*l, enums@).take(w as int) =~= arg_slots(*l, enums@));
    }
    Some(xs)
}

/// guard の前に、引数ごとの正規形の判定を `&&` でつなぐ。
fn guard_fold(Ghost(ts): Ghost<Seq<STy>>, la: &Vec<Layout>, body: Expr, enums: &Vec<i64>) -> (r: Result<Expr, usize>)
    requires
        layouts_at(la@, ts, enums@),
        wf_stypes(ts, enums@),
        smalls(ts),
    ensures
        r matches Ok(g) ==> fold_ok(g, body, la@, 0, slot_tys_seq(ts, enums@), enums@),
{
    let ghost doms = slot_tys_seq(ts, enums@);
    let ghost b = body;
    let mut g = body;
    let mut k = la.len();
    while k > 0
        invariant
            k <= la@.len(),
            doms == slot_tys_seq(ts, enums@),
            layouts_at(la@, ts, enums@),
            wf_stypes(ts, enums@),
            smalls(ts),
            fold_ok(g, b, la@, k as int, doms, enums@),
        decreases k,
    {
        k -= 1;
        let slots = match arg_exprs(&la[k], enums) {
            Some(s) => s,
            None => return Err(k),
        };
        let c = match canonical(&la[k].ty, &slots, enums) {
            Some(c) => c,
            None => return Err(k),
        };
        let ghost g0 = g;
        g = Expr::And(Box::new(c), Box::new(g));
        proof {
            assert forall|env: Env| dom_ok(env, doms, enums@) implies if canon_from(la@, k as int, env, enums@) {
                as_bool(#[trigger] eval_spec(g, env)) == as_bool(eval_spec(b, env))
            } else {
                eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false))
            } by {
                lemma_canon_eval(la@, k as int, env, ts, enums@, c);
                assert(eval_spec(g0, env) == eval_spec(g0, env));
                assert(as_bool(eval_l(c, env, Seq::empty())) == Ok::<bool, ErrKind>(canon_at(la@, k as int, env, enums@)));
                if canon_at(la@, k as int, env, enums@) {
                    assert(eval_spec(g, env) == match as_bool(eval_l(g0, env, Seq::empty())) {
                        Err(e) => Err(e),
                        Ok(y) => Ok::<Value, ErrKind>(Value::Bool(y)),
                    });
                    if canon_from(la@, (k + 1) as int, env, enums@) {
                        assert(canon_from(la@, k as int, env, enums@));
                        assert(as_bool(eval_spec(g, env)) == as_bool(eval_spec(g0, env)));
                    } else {
                        let i = choose|i: int| k + 1 <= i < la@.len() && !#[trigger] canon_at(la@, i, env, enums@);
                        assert(!canon_from(la@, k as int, env, enums@));
                    }
                } else {
                    assert(!canon_from(la@, k as int, env, enums@));
                    assert(eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false)));
                }
            }
        }
    }
    Ok(g)
}

// ---- 代入の下ろし ----

/// 中核の更新の列の式。
pub open spec fn upd_exprs(blk: Seq<Update>) -> Seq<Expr> {
    Seq::new(blk.len(), |j: int| blk[j].expr)
}

/// 中核の更新の列 `blk` は、代入 `su` の値の各スロットを、状態変数のスロットに書く。
pub open spec fn block_ok(su: SUpdate, cx: LowerCtx, blk: Seq<Update>) -> bool {
    let st = cx.states->Some_0@;
    &&& cx.states is Some
    &&& su.var < st.len()
    &&& blk.len() >= 1
    &&& forall|j: int| 0 <= j < blk.len() ==> #[trigger] blk[j].target == st[su.var as int].offset + j
    &&& forall|env: Env, se: SEnv|
        #[trigger] top_ok(cx, env, se, Seq::empty(), 0) ==> stored_result(
            eval_src(su.expr, se, Seq::empty()),
            upd_exprs(blk),
            env,
            Seq::empty(),
            sty(st[su.var as int].ty),
            cx.enums@,
        )
}

/// 更新の列をつなげた列。
pub open spec fn flat_ups(bs: Seq<Seq<Update>>) -> Seq<Update>
    decreases bs.len(),
{
    if bs.len() == 0 {
        Seq::empty()
    } else {
        flat_ups(bs.drop_last()) + bs.last()
    }
}

/// 中核の更新の列 `ups` は、代入ごとの更新の列 `bs` をつなげたものである。
pub open spec fn upds_ok(sups: Seq<SUpdate>, cx: LowerCtx, bs: Seq<Seq<Update>>, ups: Seq<Update>) -> bool {
    &&& bs.len() == sups.len()
    &&& ups == flat_ups(bs)
    &&& forall|u: int| 0 <= u < sups.len() ==> #[trigger] block_ok(sups[u], cx, bs[u])
}

/// `acc` の `off` 番目からを `cs` で置き換える。
pub open spec fn put(acc: Seq<i64>, off: int, cs: Seq<i64>) -> Seq<i64> {
    Seq::new(acc.len(), |q: int| if off <= q < off + cs.len() { cs[q - off] } else { acc[q] })
}

/// 符号に変換できる値は、スロットの型の値である。
pub proof fn lemma_encode_in(ty: Type, x: Value, enums: Seq<i64>)
    requires
        encode_spec(enums, ty, x) is Ok,
    ensures
        in_slot(ty, x, enums),
{
}

/// どの列にも適用できない更新があれば、更新の列の適用は失敗する。
proof fn lemma_c_apply_none(ups: Seq<Update>, i: int, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    requires
        0 <= i < ups.len(),
        forall|acc2: Seq<i64>| #[trigger] c_write(ups[i], env, enums, acc2) is None,
    ensures
        c_apply(ups, env, enums, acc) is None,
    decreases ups.len(),
{
    if i < ups.len() - 1 {
        assert(ups.drop_last()[i] == ups[i]);
        lemma_c_apply_none(ups.drop_last(), i, env, enums, acc);
    } else {
        if c_apply(ups.drop_last(), env, enums, acc) is Some {
            assert(c_write(ups.last(), env, enums, c_apply(ups.drop_last(), env, enums, acc)->Some_0) is None);
        }
    }
}

/// 連続するスロットへの更新がどれも成功すれば、その範囲が値の符号で置き換わる。
proof fn lemma_c_apply_put(ups: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>, off: int, xs: Seq<Value>)
    requires
        xs.len() == ups.len(),
        0 <= off,
        off + ups.len() <= acc.len(),
        off + ups.len() <= env.st_tys.len(),
        forall|j: int|
            0 <= j < ups.len() ==> #[trigger] ups[j].target == off + j && eval_spec(ups[j].expr, env) == Ok::<
                Value,
                ErrKind,
            >(xs[j]) && encode_spec(enums, env.st_tys[off + j], xs[j]) == Ok::<i64, ErrKind>(code_of(xs[j])),
    ensures
        c_apply(ups, env, enums, acc) == Some(put(acc, off, codes(xs))),
    decreases ups.len(),
{
    if ups.len() == 0 {
        assert(put(acc, off, codes(xs)) =~= acc);
    } else {
        let n = ups.len() - 1;
        let a = ups.drop_last();
        let b = xs.drop_last();
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] a[j].target == off + j && eval_spec(a[j].expr, env)
            == Ok::<Value, ErrKind>(b[j]) && encode_spec(enums, env.st_tys[off + j], b[j]) == Ok::<i64, ErrKind>(
            code_of(b[j]),
        ) by {
            assert(a[j] == ups[j]);
        }
        lemma_c_apply_put(a, env, enums, acc, off, b);
        let t = put(acc, off, codes(b));
        assert(ups.last() == ups[n]);
        assert(c_write(ups[n], env, enums, t) == Some(t.update(off + n, code_of(xs[n]))));
        assert(t.update(off + n, code_of(xs[n])) =~= put(acc, off, codes(xs)));
    }
}

/// 別々の状態変数のスロットは重ならない。
proof fn lemma_disjoint(st: Seq<Layout>, ts: Seq<STy>, i: int, x: int, enums: Seq<i64>)
    requires
        layouts_at(st, ts, enums),
        0 <= i < st.len(),
        0 <= x < st.len(),
        i != x,
    ensures
        st[i].offset + width(ts[i], enums) <= st[x].offset || st[x].offset + width(ts[x], enums) <= st[i].offset,
{
    assert(layout_at(st[i], ts, i, enums));
    assert(layout_at(st[x], ts, x, enums));
    if i < x {
        lemma_width_take(ts, i, i + 1, enums);
        lemma_width_take(ts, i + 1, x, enums);
    } else {
        lemma_width_take(ts, x, x + 1, enums);
        lemma_width_take(ts, x + 1, i, enums);
    }
}

/// 状態変数 `x` のスロットを型に属する値 `v` の符号で置き換えると、値の列の `x` 番目を `v` にした列を表す。
proof fn lemma_rel_put(
    st: Seq<Layout>,
    vs: Seq<SVal>,
    tys: Seq<Type>,
    xs: Seq<i64>,
    ts: Seq<STy>,
    enums: Seq<i64>,
    x: int,
    v: SVal,
)
    requires
        rel(st, vs, tys, xs, enums),
        layouts_at(st, ts, enums),
        tys == slot_tys_seq(ts, enums),
        wf_stypes(ts, enums),
        smalls(ts),
        0 <= x < ts.len(),
        member(v, ts[x], enums),
    ensures
        rel(st, vs.update(x, v), tys, put(xs, st[x].offset as int, codes(enc(v, ts[x], enums))), enums),
{
    let t = ts[x];
    let off = st[x].offset as int;
    let e = enc(v, t, enums);
    let cs = codes(e);
    let w = width(t, enums) as int;
    let ys = put(xs, off, cs);
    let ws = vs.update(x, v);
    assert(layout_at(st[x], ts, x, enums));
    lemma_wf_index(ts, x, enums);
    lemma_member_in(v, t, enums);
    lemma_enc_len(v, t, enums);
    lemma_slot_tys_len(t, enums);
    lemma_slot_tys_seq_sub(ts, x, enums);
    lemma_slot_tys_seq_len(ts, enums);
    assert(tys.len() == xs.len());
    assert forall|q: int| off <= q < off + w implies tys[q] == #[trigger] slot_tys(t, enums)[q - off] && in_slot(
        tys[q],
        e[q - off],
        enums,
    ) && in_type(enums, tys[q], ys[q]) && decode(tys[q], ys[q]) == e[q - off] by {
        assert(tys.subrange(off, off + w)[q - off] == tys[q]);
        assert(in_slot(slot_tys(t, enums)[q - off], e[q - off], enums));
        lemma_code_in(tys[q], e[q - off], enums);
    }
    assert forall|q: int| 0 <= q < tys.len() implies in_type(enums, #[trigger] tys[q], ys[q]) by {
        if off <= q < off + w {
            assert(slot_tys(t, enums)[q - off] == tys[q]);
        }
    }
    assert forall|i: int| 0 <= i < st.len() implies #[trigger] layout_ok(st[i], ws[i], tys, ys, enums) by {
        if i == x {
            assert forall|j: int| 0 <= j < w implies #[trigger] lookup(tys, ys, (st[i].offset + j) as usize) == Ok::<
                Value,
                ErrKind,
            >(e[j]) by {
                assert(slot_tys(t, enums)[(off + j) - off] == tys[off + j]);
            }
        } else {
            assert(layout_ok(st[i], vs[i], tys, xs, enums));
            assert(layout_at(st[i], ts, i, enums));
            lemma_disjoint(st, ts, i, x, enums);
            let ti = sty(st[i].ty);
            assert forall|j: int| 0 <= j < width(ti, enums) implies #[trigger] lookup(
                tys,
                ys,
                (st[i].offset + j) as usize,
            ) == Ok::<Value, ErrKind>(enc(ws[i], ti, enums)[j]) by {
                assert(lookup(tys, xs, (st[i].offset + j) as usize) == Ok::<Value, ErrKind>(enc(vs[i], ti, enums)[j]));
            }
        }
    }
}

/// 1つの代入と、その下ろしの更新の列の対応。
proof fn lemma_block(
    su: SUpdate,
    cx: LowerCtx,
    blk: Seq<Update>,
    env: Env,
    se: SEnv,
    acc_s: Seq<SVal>,
    acc_c: Seq<i64>,
    ts: Seq<STy>,
)
    requires
        block_ok(su, cx, blk),
        top_ok(cx, env, se, Seq::empty(), 0),
        layouts_at(cx.states->Some_0@, ts, cx.enums@),
        env.st_tys == slot_tys_seq(ts, cx.enums@),
        wf_stypes(ts, cx.enums@),
        smalls(ts),
        rel(cx.states->Some_0@, acc_s, env.st_tys, acc_c, cx.enums@),
    ensures
        match (s_write(su, se, ts, acc_s), c_apply(blk, env, cx.enums@, acc_c)) {
            (None, None) => true,
            (Some(t), Some(y)) => rel(cx.states->Some_0@, t, env.st_tys, y, cx.enums@),
            _ => false,
        },
{
    let enums = cx.enums@;
    let st = cx.states->Some_0@;
    let x = su.var as int;
    let l = st[x];
    let t = ts[x];
    let off = l.offset as int;
    assert(layout_at(l, ts, x, enums));
    lemma_wf_index(ts, x, enums);
    lemma_slot_tys_len(t, enums);
    lemma_slot_tys_seq_sub(ts, x, enums);
    lemma_slot_tys_seq_len(ts, enums);
    let w = width(t, enums) as int;
    let tys = env.st_tys;
    let out = upd_exprs(blk);
    let r = eval_src(su.expr, se, Seq::empty());
    assert(stored_result(r, out, env, Seq::empty(), t, enums));
    assert(se.enums == enums);
    match r {
        Err(k) => {
            assert(eval_l(out[0], env, Seq::empty()) == Err::<Value, ErrKind>(k));
            assert forall|acc2: Seq<i64>| #[trigger] c_write(blk[0], env, enums, acc2) is None by {
                assert(eval_spec(blk[0].expr, env) == Err::<Value, ErrKind>(k));
            }
            lemma_c_apply_none(blk, 0, env, enums, acc_c);
        },
        Ok(v) => {
            let e = enc(v, t, enums);
            assert(out.len() == w);
            if member(v, t, enums) {
                lemma_member_in(v, t, enums);
                assert forall|j: int| 0 <= j < blk.len() implies #[trigger] blk[j].target == off + j && eval_spec(
                    blk[j].expr,
                    env,
                ) == Ok::<Value, ErrKind>(e[j]) && encode_spec(enums, tys[off + j], e[j]) == Ok::<i64, ErrKind>(
                    code_of(e[j]),
                ) by {
                    assert(eval_l(out[j], env, Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                    assert(tys.subrange(off, off + w)[j] == tys[off + j]);
                    assert(in_slot(slot_tys(t, enums)[j], e[j], enums));
                    lemma_code_in(tys[off + j], e[j], enums);
                }
                assert(acc_c.len() == tys.len());
                lemma_c_apply_put(blk, env, enums, acc_c, off, e);
                lemma_rel_put(st, acc_s, tys, acc_c, ts, enums, x, v);
            } else {
                assert(!in_slots(e, slot_tys(t, enums), enums));
                let j = choose|j: int| 0 <= j < e.len() && !#[trigger] in_slot(slot_tys(t, enums)[j], e[j], enums);
                assert forall|acc2: Seq<i64>| #[trigger] c_write(blk[j], env, enums, acc2) is None by {
                    assert(eval_l(out[j], env, Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                    assert(tys.subrange(off, off + w)[j] == tys[off + j]);
                    if encode_spec(enums, tys[off + j], e[j]) is Ok {
                        lemma_encode_in(tys[off + j], e[j], enums);
                    }
                }
                lemma_c_apply_none(blk, j, env, enums, acc_c);
            }
        },
    }
}

/// 代入の列と、その下ろしの更新の列の対応。
proof fn lemma_upds(
    sups: Seq<SUpdate>,
    cx: LowerCtx,
    bs: Seq<Seq<Update>>,
    env: Env,
    se: SEnv,
    acc_s: Seq<SVal>,
    acc_c: Seq<i64>,
    ts: Seq<STy>,
)
    requires
        bs.len() == sups.len(),
        forall|u: int| 0 <= u < sups.len() ==> #[trigger] block_ok(sups[u], cx, bs[u]),
        top_ok(cx, env, se, Seq::empty(), 0),
        layouts_at(cx.states->Some_0@, ts, cx.enums@),
        env.st_tys == slot_tys_seq(ts, cx.enums@),
        wf_stypes(ts, cx.enums@),
        smalls(ts),
        rel(cx.states->Some_0@, acc_s, env.st_tys, acc_c, cx.enums@),
    ensures
        match (s_apply(sups, se, ts, acc_s), c_apply(flat_ups(bs), env, cx.enums@, acc_c)) {
            (None, None) => true,
            (Some(t), Some(y)) => rel(cx.states->Some_0@, t, env.st_tys, y, cx.enums@),
            _ => false,
        },
    decreases sups.len(),
{
    let enums = cx.enums@;
    if sups.len() > 0 {
        let a = sups.drop_last();
        let b = bs.drop_last();
        assert forall|u: int| 0 <= u < a.len() implies #[trigger] block_ok(a[u], cx, b[u]) by {
            assert(a[u] == sups[u]);
            assert(b[u] == bs[u]);
        }
        lemma_upds(a, cx, b, env, se, acc_s, acc_c, ts);
        lemma_c_apply_concat(flat_ups(b), bs.last(), env, enums, acc_c);
        match s_apply(a, se, ts, acc_s) {
            None => {},
            Some(t) => {
                let y = c_apply(flat_ups(b), env, enums, acc_c)->Some_0;
                assert(block_ok(sups[sups.len() - 1], cx, bs[bs.len() - 1]));
                lemma_block(sups.last(), cx, bs.last(), env, se, t, y, ts);
            },
        }
    }
}

/// 中核の更新の適用（前からの再帰）は、[`c_apply`] と同じ結果になる。
proof fn lemma_apply_c(m: RawModel, a: int, env: Env, k: nat, acc: Seq<i64>)
    requires
        0 <= a < m.actions@.len(),
        env.st_tys == m.state_types@,
        k <= m.actions@[a].updates@.len(),
    ensures
        match apply_updates(m, a, env, k, acc) {
            Ok(t) => c_apply(
                m.actions@[a].updates@.subrange(k as int, m.actions@[a].updates@.len() as int),
                env,
                m.enums@,
                acc,
            ) == Some(t),
            Err(_) => c_apply(
                m.actions@[a].updates@.subrange(k as int, m.actions@[a].updates@.len() as int),
                env,
                m.enums@,
                acc,
            ) is None,
        },
    decreases m.actions@[a].updates@.len() - k,
{
    let ups = m.actions@[a].updates@;
    let n = ups.len() as int;
    if k == n {
        assert(ups.subrange(k as int, n) =~= Seq::<Update>::empty());
    } else {
        let u = ups[k as int];
        assert(ups.subrange(k as int, n) =~= seq![u] + ups.subrange(k + 1 as int, n));
        lemma_c_apply_first(u, ups.subrange(k + 1 as int, n), env, m.enums@, acc);
        match c_write(u, env, m.enums@, acc) {
            None => {},
            Some(t) => {
                lemma_apply_c(m, a, env, k + 1, t);
            },
        }
    }
}

// ---- 出力の下ろし ----

/// 出力の下ろし。出力の型はBool、Int、Enumのどれかで、中核の出力の型はそのスロットの型である。
pub open spec fn out_ok(so: Option<SOutput>, cx: LowerCtx, mo: Option<Output>) -> bool {
    match (so, mo) {
        (None, None) => true,
        (Some(s), Some(o)) => {
            &&& (sty(s.ty) is Bool || sty(s.ty) is Int || sty(s.ty) is Enum)
            &&& o.ty == slot_tys(sty(s.ty), cx.enums@)[0]
            &&& forall|env: Env, se: SEnv|
                #[trigger] top_ok(cx, env, se, Seq::empty(), 0) ==> stored_result(
                    eval_src(s.expr, se, Seq::empty()),
                    seq![o.expr],
                    env,
                    Seq::empty(),
                    sty(s.ty),
                    cx.enums@,
                )
        },
        _ => false,
    }
}

/// 値の上の出力と、中核の出力の符号の対応。
pub open spec fn out_rel(so: Option<SOutput>, o: Option<SVal>, y: Option<i64>, enums: Seq<i64>) -> bool {
    match (o, y) {
        (None, None) => so is None,
        (Some(v), Some(c)) => so matches Some(s) && member(v, sty(s.ty), enums) && c == code_of(
            enc(v, sty(s.ty), enums)[0],
        ),
        _ => false,
    }
}

proof fn lemma_out(so: Option<SOutput>, cx: LowerCtx, m: RawModel, a: int, env: Env, se: SEnv)
    requires
        0 <= a < m.actions@.len(),
        out_ok(so, cx, m.actions@[a].output),
        top_ok(cx, env, se, Seq::empty(), 0),
        m.enums@ == cx.enums@,
    ensures
        match (s_output(so, se), output_spec(m, a, env)) {
            (None, Err(_)) => true,
            (Some(o), Ok(y)) => out_rel(so, o, y, cx.enums@),
            _ => false,
        },
{
    let enums = cx.enums@;
    assert(se.enums == enums);
    match so {
        None => {},
        Some(s) => {
            let o = m.actions@[a].output->Some_0;
            let t = sty(s.ty);
            let r = eval_src(s.expr, se, Seq::empty());
            assert(stored_result(r, seq![o.expr], env, Seq::empty(), t, enums));
            match r {
                Err(k) => {
                    assert(seq![o.expr][0] == o.expr);
                },
                Ok(v) => {
                    assert(seq![o.expr][0] == o.expr);
                    let e = enc(v, t, enums);
                    assert(eval_l(o.expr, env, Seq::empty()) == Ok::<Value, ErrKind>(e[0]));
                    if member(v, t, enums) {
                        assert(wf_stype(t, enums)) by {
                            lemma_enc_len(v, t, enums);
                        }
                        lemma_member_in(v, t, enums);
                        lemma_code_in(o.ty, e[0], enums);
                    } else {
                        if encode_spec(enums, o.ty, e[0]) is Ok {
                            lemma_encode_in(o.ty, e[0], enums);
                            lemma_slot_tys_len(t, enums);
                            assert(in_slots(e, slot_tys(t, enums), enums));
                        }
                    }
                },
            }
        },
    }
}

// ---- 操作の下ろし ----

/// 下ろしの失敗の理由。
pub enum Fault {
    /// 式を下ろせない（型が合わない、または参照が未定義）。
    Lower,
    /// 式の評価に失敗した。範囲外の値は `OutOfRange` である。
    Eval(ErrKind),
}

/// 下ろしの失敗の場所。
pub enum LowerError {
    /// 状態変数の型が整形式でないか、符号化が大きすぎる。
    State(usize),
    /// 定数。
    Const(usize, Fault),
    /// 状態変数 `.0` の `.1` 番目の初期値の候補。
    Init(usize, usize, Fault),
    /// 初期値の候補の列の数が状態変数の数と違うか、候補の組み合わせが多すぎる。
    InitCount,
    /// 初期条件。
    Constraint(Fault),
    /// 初期条件を満たす初期状態がない。
    NoInit,
    /// 操作 `.0` の `.1` 番目の引数の型。
    Args(usize, usize),
    /// 操作のguard。
    Guard(usize),
    /// 操作 `.0` の `.1` 番目の代入。
    Update(usize, usize),
    /// 操作の出力。
    Output(usize),
    /// 不変条件。
    Invariant(usize),
    /// 遷移契約。
    Contract(usize),
    /// 終端条件。
    Terminal,
}

/// 中核のguard `g` は、引数が正規形でなければ偽で、正規形なら値の上のguardと同じ真偽になる。
pub open spec fn guard_ok(sa: SAction, cx: LowerCtx, g: Expr) -> bool {
    let doms = slot_tys_seq(stys(sa.args@), cx.enums@);
    &&& forall|env: Env|
        dom_ok(env, doms, cx.enums@) && !canon_from(cx.args@, 0, env, cx.enums@) ==> #[trigger] eval_spec(g, env)
            == Ok::<Value, ErrKind>(Value::Bool(false))
    &&& forall|env: Env, se: SEnv|
        #[trigger] env_rel(cx, env, se) && dom_ok(env, doms, cx.enums@) ==> prop_spec(g, env) == src_bool(
            eval_src(sa.guard, se, Seq::empty()),
        )
}

/// 中核の操作 `m` は、操作 `sa` を文脈 `cx` で下ろしたものである。
pub open spec fn act_ok(sa: SAction, cx: LowerCtx, m: Action) -> bool {
    &&& m.n_params == sa.n_params
    &&& m.domains@ == slot_tys_seq(stys(sa.args@), cx.enums@)
    &&& guard_ok(sa, cx, m.guard)
    &&& exists|bs: Seq<Seq<Update>>| #[trigger] upds_ok(sa.updates@, cx, bs, m.updates@)
    &&& out_ok(sa.output, cx, m.output)
}

/// 位置 `off` からのスロットへの更新を、`ups` の後ろに加える。
fn push_block(ups: &mut Vec<Update>, off: usize, out: &Vec<Expr>) -> (r: bool)
    ensures
        r ==> final(ups)@.len() == old(ups)@.len() + out@.len(),
        r ==> final(ups)@.subrange(0, old(ups)@.len() as int) == old(ups)@,
        r ==> forall|k: int|
            0 <= k < out@.len() ==> #[trigger] final(ups)@[old(ups)@.len() + k].target == off + k && final(ups)@[old(
                ups,
            )@.len() + k].expr == out@[k],
{
    let ghost before = ups@;
    let mut j = 0;
    while j < out.len()
        invariant
            j <= out@.len(),
            ups@.len() == before.len() + j,
            ups@.subrange(0, before.len() as int) == before,
            forall|k: int|
                0 <= k < j ==> #[trigger] ups@[before.len() + k].target == off + k && ups@[before.len() + k].expr
                    == out@[k],
        decreases out@.len() - j,
    {
        let target = match off.checked_add(j) {
            Some(t) => t,
            None => return false,
        };
        ups.push(Update { target, expr: copy_expr(&out[j]) });
        proof {
            assert(ups@.subrange(0, before.len() as int) =~= before);
        }
        j += 1;
    }
    true
}

/// 操作を下ろす。guardの前に引数の正規形の判定を置き、代入は値のスロットごとの更新にする。
pub(crate) fn lower_action(sa: &SAction, cx: &LowerCtx, a: usize) -> (r: Result<Action, LowerError>)
    requires
        cx.states is Some,
        !cx.next,
        cx.out is None,
        layouts_at(cx.args@, stys(sa.args@), cx.enums@),
        wf_stypes(stys(sa.args@), cx.enums@),
        smalls(stys(sa.args@)),
    ensures
        r matches Ok(m) ==> act_ok(*sa, *cx, m),
{
    let ghost enums = cx.enums@;
    let ghost doms = slot_tys_seq(stys(sa.args@), enums);
    let body = match lower_prop(&sa.guard, cx) {
        Ok(g) => g,
        Err(_) => return Err(LowerError::Guard(a)),
    };
    let ghost b = body;
    let guard = match guard_fold(Ghost(stys(sa.args@)), &cx.args, body, &cx.enums) {
        Ok(g) => g,
        Err(i) => return Err(LowerError::Args(a, i)),
    };
    proof {
        assert forall|env: Env, se: SEnv| #[trigger] env_rel(*cx, env, se) && dom_ok(env, doms, enums) implies prop_spec(
            guard,
            env,
        ) == src_bool(eval_src(sa.guard, se, Seq::empty())) by {
            lemma_rel_canon(cx.args@, se.args, env, enums);
            assert(eval_spec(guard, env) == eval_spec(guard, env));
            assert(prop_result(eval_src(sa.guard, se, Seq::empty()), eval_l(b, env, Seq::empty())));
        }
    }
    let domains = slot_types_list(&sa.args, &cx.enums);
    let st = match &cx.states {
        Some(st) => st,
        None => return Err(LowerError::Update(a, 0)),
    };
    let mut ups: Vec<Update> = Vec::new();
    let ghost mut bs: Seq<Seq<Update>> = Seq::empty();
    let mut u = 0;
    while u < sa.updates.len()
        invariant
            u <= sa.updates@.len(),
            cx.states == Some(*st),
            bs.len() == u,
            ups@ == flat_ups(bs),
            forall|k: int| 0 <= k < u ==> #[trigger] block_ok(sa.updates@[k], *cx, bs[k]),
        decreases sa.updates@.len() - u,
    {
        let su = &sa.updates[u];
        if su.var >= st.len() {
            return Err(LowerError::Update(a, u));
        }
        let l = &st[su.var];
        let out = match lower_stored(&su.expr, cx, &l.ty, 0) {
            Ok(o) => o,
            Err(_) => return Err(LowerError::Update(a, u)),
        };
        if out.len() == 0 {
            return Err(LowerError::Update(a, u));
        }
        let ghost before = ups@;
        if !push_block(&mut ups, l.offset, &out) {
            return Err(LowerError::Update(a, u));
        }
        let ghost blk = ups@.subrange(before.len() as int, ups@.len() as int);
        proof {
            let bs0 = bs;
            bs = bs.push(blk);
            assert(bs.drop_last() =~= bs0);
            assert(ups@ =~= before + blk);
            assert forall|k: int| 0 <= k < blk.len() implies #[trigger] upd_exprs(blk)[k] == out@[k] by {
                assert(blk[k] == ups@[before.len() + k]);
                assert(ups@[before.len() + k].target == l.offset + k);
            }
            assert(upd_exprs(blk) =~= out@);
            assert forall|k: int| 0 <= k < blk.len() implies #[trigger] blk[k].target == l.offset + k by {
                assert(blk[k] == ups@[before.len() + k]);
            }
            assert forall|k: int| 0 <= k <= u implies #[trigger] block_ok(sa.updates@[k], *cx, bs[k]) by {
                if k < u {
                    assert(bs[k] == bs0[k]);
                }
            }
        }
        u += 1;
    }
    let output = match &sa.output {
        None => None,
        Some(so) => {
            let ty = match &so.ty {
                SType::Bool => Type::Bool,
                SType::Int(lo, hi) => Type::Int(*lo, *hi),
                SType::Enum(id) => Type::Enum(*id),
                _ => return Err(LowerError::Output(a)),
            };
            let mut out = match lower_stored(&so.expr, cx, &so.ty, 0) {
                Ok(o) => o,
                Err(_) => return Err(LowerError::Output(a)),
            };
            if out.len() != 1 {
                return Err(LowerError::Output(a));
            }
            let ghost out0 = out@;
            let expr = match out.pop() {
                Some(e) => e,
                None => return Err(LowerError::Output(a)),
            };
            proof {
                assert(out0 =~= seq![expr]);
            }
            Some(Output { ty, expr })
        },
    };
    let m = Action { n_params: sa.n_params, domains, guard, updates: ups, output };
    proof {
        assert(upds_ok(sa.updates@, *cx, bs, m.updates@));
    }
    Ok(m)
}

// ---- 遷移の対応 ----

/// 値の上の遷移の結果と、中核の遷移の結果の対応。
pub open spec fn step_rel(
    ss: SStep,
    cs: Step,
    st: Seq<Layout>,
    tys: Seq<Type>,
    so: Option<SOutput>,
    enums: Seq<i64>,
) -> bool {
    match (ss, cs) {
        (SStep::Disabled, Step::Disabled) => true,
        (SStep::Fail, Step::Fail(_, _)) => true,
        (SStep::To(t, o), Step::To(y, x)) => rel(st, t, tys, y, enums) && out_rel(so, o, x, enums),
        _ => false,
    }
}

/// 正規形でない引数では、下ろした操作は無効である。
pub proof fn lemma_step_off(sa: SAction, m: RawModel, a: int, cx: LowerCtx, ps: Seq<i64>, xs: Seq<i64>)
    requires
        0 <= a < m.actions@.len(),
        act_ok(sa, cx, m.actions@[a]),
        vals_ok(cx.enums@, m.actions@[a].domains@, xs),
        !canon_from(cx.args@, 0, act_env(m, a, xs, ps), cx.enums@),
    ensures
        step_spec(m, a, xs, ps) == Step::Disabled,
{
    let env = act_env(m, a, xs, ps);
    assert(dom_ok(env, slot_tys_seq(stys(sa.args@), cx.enums@), cx.enums@));
    assert(eval_spec(m.actions@[a].guard, env) == Ok::<Value, ErrKind>(Value::Bool(false)));
}

/// 値の列を表す状態と引数での遷移は、値の上の遷移に対応する。
pub proof fn lemma_step(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    a: int,
    cx: LowerCtx,
    p: Seq<SVal>,
    ps: Seq<i64>,
    vs: Seq<SVal>,
    xs: Seq<i64>,
)
    requires
        0 <= a < sm.actions@.len(),
        0 <= a < m.actions@.len(),
        act_ok(sm.actions@[a], cx, m.actions@[a]),
        cx.states is Some,
        layouts_at(cx.states->Some_0@, s_state_tys(sm), sm.enums@),
        wf_stypes(s_state_tys(sm), sm.enums@),
        smalls(s_state_tys(sm)),
        m.state_types@ == slot_tys_seq(s_state_tys(sm), sm.enums@),
        m.enums@ == sm.enums@,
        cx.enums@ == sm.enums@,
        env_rel(cx, act_env(m, a, xs, ps), s_env(sm, cv, p, vs, Seq::empty(), None)),
        vals_ok(sm.enums@, m.state_types@, ps),
        vals_ok(sm.enums@, m.actions@[a].domains@, xs),
    ensures
        step_rel(
            s_step(sm, cv, a, vs, p),
            step_spec(m, a, xs, ps),
            cx.states->Some_0@,
            m.state_types@,
            sm.actions@[a].output,
            sm.enums@,
        ),
{
    let sa = sm.actions@[a];
    let enums = sm.enums@;
    let ts = s_state_tys(sm);
    let env = act_env(m, a, xs, ps);
    let se = s_env(sm, cv, p, vs, Seq::empty(), None);
    assert(dom_ok(env, slot_tys_seq(stys(sa.args@), enums), enums));
    assert(prop_spec(m.actions@[a].guard, env) == src_bool(eval_src(sa.guard, se, Seq::empty())));
    assert(top_ok(cx, env, se, Seq::empty(), 0));
    let ups = m.actions@[a].updates@;
    lemma_apply_c(m, a, env, 0, ps);
    assert(ups.subrange(0, ups.len() as int) =~= ups);
    let bs = choose|bs: Seq<Seq<Update>>| #[trigger] upds_ok(sa.updates@, cx, bs, ups);
    lemma_upds(sa.updates@, cx, bs, env, se, p, ps, ts);
    lemma_out(sa.output, cx, m, a, env, se);
}

} // verus!
