//! 検査条件、到達可能性、安全性の定義。
//!
//! 判定の意味は、探索器とは無関係に、ここにある定義だけで決まる。
//! `safe` が `Verified` の意味で、`reach` が到達可能性である（仕様書 §5、§8.3）。

use crate::eval::*;
use crate::model::*;
#[cfg(verus_keep_ghost)]
use crate::state_enc::args_ok;
#[allow(unused_imports)]
use crate::step::*;
use vstd::prelude::*;

verus! {

/// 検査条件。対象の操作、不変条件、遷移契約と、デッドロック検査の有無（仕様書 §14.2）。
/// 各列は定義の添字に対応し、列より後ろの添字は対象外として扱う。
pub struct Conditions {
    pub actions: Vec<bool>,
    pub invariants: Vec<bool>,
    pub contracts: Vec<bool>,
    pub deadlock: bool,
}

pub open spec fn act_on(m: RawModel, c: Conditions, a: int) -> bool {
    0 <= a < m.actions@.len() && a < c.actions@.len() && c.actions@[a]
}

pub open spec fn inv_on(m: RawModel, c: Conditions, i: int) -> bool {
    0 <= i < m.invariants@.len() && i < c.invariants@.len() && c.invariants@[i]
}

pub open spec fn con_on(m: RawModel, c: Conditions, k: int) -> bool {
    0 <= k < m.contracts@.len() && k < c.contracts@.len() && c.contracts@[k]
}

// ---- 性質の評価 ----

pub open spec fn inv_env(m: RawModel, s: Seq<i64>) -> Env {
    Env {
        st_tys: m.state_types@,
        arg_tys: Seq::empty(),
        pre: s,
        args: Seq::empty(),
        post: Seq::empty(),
        out: None,
    }
}

/// 不変条件 `i` の状態 `s` での評価。
pub open spec fn inv_spec(m: RawModel, i: int, s: Seq<i64>) -> Result<bool, ErrKind> {
    prop_spec(m.invariants@[i], inv_env(m, s))
}

/// 終端条件の評価。終端条件のないモデルでは、どの状態も終端でない。
pub open spec fn terminal_spec(m: RawModel, s: Seq<i64>) -> Result<bool, ErrKind> {
    match m.terminal {
        None => Ok(false),
        Some(e) => prop_spec(e, inv_env(m, s)),
    }
}

/// 出力の符号を、操作の出力型の値に戻す。
pub open spec fn out_value(m: RawModel, a: int, o: Option<i64>) -> Option<Value> {
    match (m.actions@[a].output, o) {
        (Some(out), Some(x)) => Some(decode(out.ty, x)),
        _ => None,
    }
}

pub open spec fn con_env(m: RawModel, a: int, pre: Seq<i64>, args: Seq<i64>, post: Seq<i64>, o: Option<i64>) -> Env {
    Env {
        st_tys: m.state_types@,
        arg_tys: m.actions@[a].domains@,
        pre: pre,
        args: args,
        post: post,
        out: out_value(m, a, o),
    }
}

/// 遷移契約 `k` の、遷移 `pre --(args, o)--> post` での評価。
pub open spec fn con_spec(
    m: RawModel,
    k: int,
    pre: Seq<i64>,
    args: Seq<i64>,
    post: Seq<i64>,
    o: Option<i64>,
) -> Result<bool, ErrKind> {
    let con = m.contracts@[k];
    if con.action < m.actions@.len() {
        prop_spec(con.expr, con_env(m, con.action as int, pre, args, post, o))
    } else {
        Err(ErrKind::Unbound)
    }
}

// ---- 到達可能性 ----

/// 対象の操作 `a` と引数 `args` による、`p` から `s` への有効な遷移。出力は `o`。
pub open spec fn is_edge(
    m: RawModel,
    c: Conditions,
    p: Seq<i64>,
    a: int,
    args: Seq<i64>,
    o: Option<i64>,
    s: Seq<i64>,
) -> bool {
    act_on(m, c, a) && args_ok(m, a, args) && step_spec(m, a, args, p) == Step::To(s, o)
}

/// `s` は初期状態の1つである。
pub open spec fn is_init(m: RawModel, s: Seq<i64>) -> bool {
    exists|i: int| 0 <= i < m.inits@.len() && (#[trigger] m.inits@[i])@ == s
}

/// `s` は初期状態から対象の操作の遷移 `n` 回で到達できる。
pub open spec fn reach(m: RawModel, c: Conditions, s: Seq<i64>, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        is_init(m, s)
    } else {
        exists|p: Seq<i64>, a: int, args: Seq<i64>, o: Option<i64>|
            reach(m, c, p, (n - 1) as nat) && #[trigger] is_edge(m, c, p, a, args, o, s)
    }
}

// ---- 安全性 ----

/// 対象の不変条件がすべて真に評価される。
pub open spec fn invs_hold(m: RawModel, c: Conditions, s: Seq<i64>) -> bool {
    forall|i: int| #[trigger] inv_on(m, c, i) ==> inv_spec(m, i, s) == Ok::<bool, ErrKind>(true)
}

/// 操作 `a` の遷移に適用する対象の契約が、すべて真に評価される。
pub open spec fn cons_hold(
    m: RawModel,
    c: Conditions,
    a: int,
    pre: Seq<i64>,
    args: Seq<i64>,
    post: Seq<i64>,
    o: Option<i64>,
) -> bool {
    forall|k: int| #[trigger]
        con_on(m, c, k) && m.contracts@[k].action == a ==> con_spec(m, k, pre, args, post, o) == Ok::<bool, ErrKind>(
            true,
        )
}

/// 状態 `s` での操作 `a`、引数 `args` の適用が安全である。評価エラーがなく、有効なら契約を満たす。
pub open spec fn trans_safe(m: RawModel, c: Conditions, a: int, args: Seq<i64>, s: Seq<i64>) -> bool {
    match step_spec(m, a, args, s) {
        Step::Disabled => true,
        Step::Fail(_, _) => false,
        Step::To(t, o) => cons_hold(m, c, a, s, args, t, o),
    }
}

/// 状態 `s` に対象の操作の有効な遷移がない。
pub open spec fn stuck(m: RawModel, c: Conditions, s: Seq<i64>) -> bool {
    forall|a: int| #[trigger] act_on(m, c, a) ==> all_disabled(m, a, s)
}

/// デッドロック検査が有効なら、有効な遷移のない状態は終端である。
pub open spec fn no_deadlock(m: RawModel, c: Conditions, s: Seq<i64>) -> bool {
    c.deadlock && stuck(m, c, s) ==> terminal_spec(m, s) == Ok::<bool, ErrKind>(true)
}

pub open spec fn state_safe(m: RawModel, c: Conditions, s: Seq<i64>) -> bool {
    &&& invs_hold(m, c, s)
    &&& forall|a: int, args: Seq<i64>| #[trigger]
        act_on(m, c, a) && #[trigger] args_ok(m, a, args) ==> trans_safe(m, c, a, args, s)
    &&& no_deadlock(m, c, s)
}

/// `Verified` の意味。検査条件 `c` の下で、到達できるすべての状態と有効な遷移が指定の性質を満たし、
/// 到達できる評価エラーがなく、指定時は非終端のデッドロックもない。
pub open spec fn safe(m: RawModel, c: Conditions) -> bool {
    forall|s: Seq<i64>, n: nat| #[trigger] reach(m, c, s, n) ==> state_safe(m, c, s)
}

// ---- 性質の評価の実装 ----

pub fn act_on_exec(m: &RawModel, c: &Conditions, a: usize) -> (r: bool)
    ensures
        r == act_on(*m, *c, a as int),
{
    a < m.actions.len() && a < c.actions.len() && c.actions[a]
}

pub fn inv_on_exec(m: &RawModel, c: &Conditions, i: usize) -> (r: bool)
    ensures
        r == inv_on(*m, *c, i as int),
{
    i < m.invariants.len() && i < c.invariants.len() && c.invariants[i]
}

pub fn con_on_exec(m: &RawModel, c: &Conditions, k: usize) -> (r: bool)
    ensures
        r == con_on(*m, *c, k as int),
{
    k < m.contracts.len() && k < c.contracts.len() && c.contracts[k]
}

pub(crate) fn eval_invariant(m: &RawModel, i: usize, s: &Vec<i64>) -> (r: Result<bool, ErrKind>)
    requires
        i < m.invariants@.len(),
    ensures
        r == inv_spec(*m, i as int, s@),
{
    let no_tys: Vec<Type> = Vec::new();
    let no_vals: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &m.state_types, arg_tys: &no_tys, pre: s, args: &no_vals, post: &no_vals, out: None };
    assert(ctx@ == inv_env(*m, s@)) by {
        assert(no_tys@ =~= Seq::<Type>::empty());
        assert(no_vals@ =~= Seq::<i64>::empty());
    }
    eval_prop(&m.invariants[i], &ctx)
}

pub fn eval_terminal(m: &RawModel, s: &Vec<i64>) -> (r: Result<bool, ErrKind>)
    ensures
        r == terminal_spec(*m, s@),
{
    match &m.terminal {
        None => Ok(false),
        Some(e) => {
            let no_tys: Vec<Type> = Vec::new();
            let no_vals: Vec<i64> = Vec::new();
            let ctx = Ctx {
                st_tys: &m.state_types,
                arg_tys: &no_tys,
                pre: s,
                args: &no_vals,
                post: &no_vals,
                out: None,
            };
            assert(ctx@ == inv_env(*m, s@)) by {
                assert(no_tys@ =~= Seq::<Type>::empty());
                assert(no_vals@ =~= Seq::<i64>::empty());
            }
            eval_prop(e, &ctx)
        },
    }
}

pub(crate) fn eval_contract(
    m: &RawModel,
    k: usize,
    pre: &Vec<i64>,
    args: &Vec<i64>,
    post: &Vec<i64>,
    o: &Option<i64>,
) -> (r: Result<bool, ErrKind>)
    requires
        k < m.contracts@.len(),
    ensures
        r == con_spec(*m, k as int, pre@, args@, post@, *o),
{
    let con = &m.contracts[k];
    if con.action < m.actions.len() {
        let act = &m.actions[con.action];
        let out = match (&act.output, o) {
            (Some(out), Some(x)) => Some(decode_value(&out.ty, *x)),
            _ => None,
        };
        let ctx = Ctx { st_tys: &m.state_types, arg_tys: &act.domains, pre, args, post, out };
        assert(ctx@ == con_env(*m, con.action as int, pre@, args@, post@, *o));
        eval_prop(&con.expr, &ctx)
    } else {
        Err(ErrKind::Unbound)
    }
}

/// 真に評価されなかった性質の添字と、その評価結果。
pub open spec fn not_true(r: Result<bool, ErrKind>) -> bool {
    r != Ok::<bool, ErrKind>(true)
}

/// 対象の不変条件を定義順に評価し、真でない最初のものを返す。
pub fn check_invariants(m: &RawModel, c: &Conditions, s: &Vec<i64>) -> (r: Option<(usize, Result<bool, ErrKind>)>)
    ensures
        match r {
            None => invs_hold(*m, *c, s@),
            Some((i, v)) => inv_on(*m, *c, i as int) && inv_spec(*m, i as int, s@) == v && not_true(v),
        },
{
    let mut i: usize = 0;
    while i < m.invariants.len()
        invariant
            i <= m.invariants@.len(),
            forall|j: int| 0 <= j < i && #[trigger] inv_on(*m, *c, j) ==> inv_spec(*m, j, s@) == Ok::<bool, ErrKind>(true),
        decreases m.invariants@.len() - i,
    {
        if inv_on_exec(m, c, i) {
            match eval_invariant(m, i, s) {
                Ok(true) => {},
                v => {
                    return Some((i, v));
                },
            }
        }
        i = i + 1;
    }
    None
}

/// 操作 `a` の遷移に適用する対象の契約を定義順に評価し、真でない最初のものを返す。
pub fn check_contracts(
    m: &RawModel,
    c: &Conditions,
    a: usize,
    pre: &Vec<i64>,
    args: &Vec<i64>,
    post: &Vec<i64>,
    o: &Option<i64>,
) -> (r: Option<(usize, Result<bool, ErrKind>)>)
    ensures
        match r {
            None => cons_hold(*m, *c, a as int, pre@, args@, post@, *o),
            Some((k, v)) => con_on(*m, *c, k as int) && m.contracts@[k as int].action == a && con_spec(
                *m,
                k as int,
                pre@,
                args@,
                post@,
                *o,
            ) == v && not_true(v),
        },
{
    let mut k: usize = 0;
    while k < m.contracts.len()
        invariant
            k <= m.contracts@.len(),
            forall|j: int|
                0 <= j < k && #[trigger] con_on(*m, *c, j) && m.contracts@[j].action == a ==> con_spec(
                    *m,
                    j,
                    pre@,
                    args@,
                    post@,
                    *o,
                ) == Ok::<bool, ErrKind>(true),
        decreases m.contracts@.len() - k,
    {
        if con_on_exec(m, c, k) && m.contracts[k].action == a {
            match eval_contract(m, k, pre, args, post, o) {
                Ok(true) => {},
                v => {
                    return Some((k, v));
                },
            }
        }
        k = k + 1;
    }
    None
}

/// 検査条件の列の `i` 番目が対象である。列より後ろは対象外とする（`act_on` などと同じ）。
pub open spec fn flag_on(a: Seq<bool>, i: int) -> bool {
    0 <= i < a.len() && a[i]
}

/// 2つの列が、添字 `n` 未満で同じものを対象にする。
pub open spec fn flags_same(n: int, a: Seq<bool>, b: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] flag_on(a, i) == flag_on(b, i)
}

/// 2つの検査条件が、モデル `m` について同じ意味を持つ。対象の操作、不変条件、契約と、デッドロック検査の
/// 有無が同じである。列の長さは問わない（列より後ろと、モデルにない添字は対象外）。
pub open spec fn same_conditions(m: RawModel, x: Conditions, y: Conditions) -> bool {
    &&& flags_same(m.actions@.len() as int, x.actions@, y.actions@)
    &&& flags_same(m.invariants@.len() as int, x.invariants@, y.invariants@)
    &&& flags_same(m.contracts@.len() as int, x.contracts@, y.contracts@)
    &&& x.deadlock == y.deadlock
}

pub(crate) fn flags_eq(n: usize, a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
    ensures
        r == flags_same(n as int, a@, b@),
{
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] flag_on(a@, j) == flag_on(b@, j),
        decreases n - i,
    {
        let x = i < a.len() && a[i];
        let y = i < b.len() && b[i];
        if x != y {
            assert(flag_on(a@, i as int) != flag_on(b@, i as int));
            return false;
        }
        i = i + 1;
    }
    true
}

/// 証明書の検査条件 `a` と要求された検査条件 `b` を、モデル `m` についての意味で比べる。
/// 判定の健全性はこの比較に依らない（証明書は要求された検査条件で検査する）。別の検査条件で作られた
/// 証明書を、取り違えとして拒否するための比較である。
pub(crate) fn conditions_eq(m: &RawModel, a: &Conditions, b: &Conditions) -> (r: bool)
    ensures
        r == same_conditions(*m, *a, *b),
{
    flags_eq(m.actions.len(), &a.actions, &b.actions) && flags_eq(m.invariants.len(), &a.invariants, &b.invariants)
        && flags_eq(m.contracts.len(), &a.contracts, &b.contracts) && a.deadlock == b.deadlock
}

} // verus!
