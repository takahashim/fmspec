//! 対称性による状態の削減（docs/plans/refinement_symmetry_constants.md の3）。
//!
//! 利用者は、入れ替えても区別のない要素（プロセスのインスタンスなど）を、状態変数の**ブロック**の列として宣言する。
//! 読み込みは、隣り合う2つのブロックを入れ替える**入れ替え**ごとに、状態のスロットの置換 `p` を作る。
//! 判定ゲートは宣言を信用しない。入れ替えごとに、下ろした中核のモデルが、スロットの添字を `p` で付け替えても
//! 構文として変わらないこと（操作、不変条件、遷移契約は互いに写り合い、終端条件は変わらないこと）を確かめる。
//! そのうえで、式の評価が付け替えと可換であること（`lemma_rename_eval`）から、遷移と性質が入れ替えで保たれる。
//!
//! 証明書は、軌道の代表元の集合でよい。検査器は、各状態の後続を遷移列挙で計算し直し、
//! 後続に入れ替えを並べて施した状態（`canonicalize`）が証明書に含まれることを確かめる。
//! 正規化が一意であることは証明しない。正規化が探索器とずれても、拒否になるだけで、誤った `Verified` にはならない。

use crate::checked::CheckedModel;
use crate::eval::*;
use crate::model::*;
use crate::semantics::*;
use crate::state_enc::copy_vec;
#[cfg(verus_keep_ghost)]
use crate::state_enc::{args_ok, encode_spec};
use crate::state_set::cmp_state;
#[cfg(verus_keep_ghost)]
use crate::state_set::in_cert;
#[cfg(verus_keep_ghost)]
use crate::step::{act_env, all_disabled, apply_updates, Step, step_spec};
use vstd::prelude::*;

verus! {

// ---- 式の付け替え ----

/// スロットの添字 `i` の付け替え先。範囲外の添字は変えない。
pub open spec fn rn(i: usize, p: Seq<usize>) -> usize {
    if i < p.len() {
        p[i as int]
    } else {
        i
    }
}

/// 状態のスロットの添字（`Var` と `Next`）を `p` で付け替えた式。
pub open spec fn rename(e: Expr, p: Seq<usize>) -> Expr
    decreases e,
{
    match e {
        Expr::Var(i) => Expr::Var(rn(i, p)),
        Expr::Next(i) => Expr::Next(rn(i, p)),
        Expr::Bin(op, a, b) => Expr::Bin(op, Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Not(a) => Expr::Not(Box::new(rename(*a, p))),
        Expr::And(a, b) => Expr::And(Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Or(a, b) => Expr::Or(Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Implies(a, b) => Expr::Implies(Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Ite(c, a, b) => Expr::Ite(Box::new(rename(*c, p)), Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Let(a, b) => Expr::Let(Box::new(rename(*a, p)), Box::new(rename(*b, p))),
        Expr::Forall(ty, lo, hi, b) => Expr::Forall(ty, lo, hi, Box::new(rename(*b, p))),
        Expr::Exists(ty, lo, hi, b) => Expr::Exists(ty, lo, hi, Box::new(rename(*b, p))),
        Expr::Code(a) => Expr::Code(Box::new(rename(*a, p))),
        _ => e,
    }
}

/// `p` は、型 `tys` のスロットの入れ替え（対合）で、入れ替える2つのスロットは同じ型を持つ。
pub open spec fn perm_ok(p: Seq<usize>, tys: Seq<Type>) -> bool {
    &&& p.len() == tys.len()
    &&& forall|j: int|
        0 <= j < p.len() ==> (#[trigger] p[j]) < p.len() && p[p[j] as int] == j && tys[p[j] as int] == tys[j]
}

/// `y` は `x` のスロットを `p` で入れ替えた列である。
pub open spec fn seq_sw(x: Seq<i64>, y: Seq<i64>, p: Seq<usize>) -> bool {
    &&& x.len() == p.len()
    &&& y.len() == p.len()
    &&& forall|j: int| 0 <= j < p.len() ==> #[trigger] y[j] == x[p[j] as int]
}

/// スロットを `p` で入れ替えた列。
pub open spec fn permute(s: Seq<i64>, p: Seq<usize>) -> Seq<i64> {
    Seq::new(p.len(), |j: int| s[p[j] as int])
}

/// 環境 `e2` は、環境 `e1` の状態（遷移の前と後）のスロットを `p` で入れ替えたものである。
pub open spec fn env_sw(e1: Env, e2: Env, p: Seq<usize>) -> bool {
    &&& e2.st_tys == e1.st_tys
    &&& e2.arg_tys == e1.arg_tys
    &&& e2.args == e1.args
    &&& e2.out == e1.out
    &&& perm_ok(p, e1.st_tys)
    &&& seq_sw(e1.pre, e2.pre, p)
    &&& ((e1.post.len() == 0 && e2.post.len() == 0) || seq_sw(e1.post, e2.post, p))
}

proof fn lemma_lookup_sw(tys: Seq<Type>, x: Seq<i64>, y: Seq<i64>, p: Seq<usize>, i: usize)
    requires
        perm_ok(p, tys),
        (x.len() == 0 && y.len() == 0) || seq_sw(x, y, p),
    ensures
        lookup(tys, y, rn(i, p)) == lookup(tys, x, i),
{
    if i < p.len() && x.len() > 0 {
        let j = p[i as int];
        assert(p[j as int] == i);
        assert(y[j as int] == x[p[j as int] as int]);
    }
}

/// 付け替えた式を入れ替えた環境で評価すると、元の式を元の環境で評価した結果と同じになる。
pub proof fn lemma_rename_eval(e: Expr, p: Seq<usize>, e1: Env, e2: Env, ls: Seq<Value>)
    requires
        env_sw(e1, e2, p),
    ensures
        eval_l(rename(e, p), e2, ls) == eval_l(e, e1, ls),
    decreases e, 0int,
{
    match e {
        Expr::Var(i) => {
            lemma_lookup_sw(e1.st_tys, e1.pre, e2.pre, p, i);
        },
        Expr::Next(i) => {
            lemma_lookup_sw(e1.st_tys, e1.post, e2.post, p, i);
        },
        Expr::Bin(_, a, b) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
            lemma_rename_eval(*b, p, e1, e2, ls);
        },
        Expr::Not(a) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
        },
        Expr::And(a, b) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
            lemma_rename_eval(*b, p, e1, e2, ls);
        },
        Expr::Or(a, b) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
            lemma_rename_eval(*b, p, e1, e2, ls);
        },
        Expr::Implies(a, b) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
            lemma_rename_eval(*b, p, e1, e2, ls);
        },
        Expr::Ite(c, a, b) => {
            lemma_rename_eval(*c, p, e1, e2, ls);
            lemma_rename_eval(*a, p, e1, e2, ls);
            lemma_rename_eval(*b, p, e1, e2, ls);
        },
        Expr::Let(a, b) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
            match eval_l(*a, e1, ls) {
                Ok(v) => {
                    lemma_rename_eval(*b, p, e1, e2, ls.push(v));
                },
                Err(_) => {},
            }
        },
        Expr::Forall(ty, lo, hi, b) => {
            lemma_rename_quant(true, ty, *b, p, e1, e2, ls, lo as int, hi as int, None);
        },
        Expr::Exists(ty, lo, hi, b) => {
            lemma_rename_quant(false, ty, *b, p, e1, e2, ls, lo as int, hi as int, None);
        },
        Expr::Code(a) => {
            lemma_rename_eval(*a, p, e1, e2, ls);
        },
        _ => {},
    }
}

/// 量化についての `lemma_rename_eval`。
pub proof fn lemma_rename_quant(
    all: bool,
    ty: Type,
    body: Expr,
    p: Seq<usize>,
    e1: Env,
    e2: Env,
    ls: Seq<Value>,
    x: int,
    hi: int,
    pend: Option<ErrKind>,
)
    requires
        env_sw(e1, e2, p),
    ensures
        quant_l(all, ty, rename(body, p), e2, ls, x, hi, pend) == quant_l(all, ty, body, e1, ls, x, hi, pend),
    decreases body, hi - x + 1,
{
    if x <= hi {
        let l = ls.push(decode(ty, x as i64));
        lemma_rename_eval(body, p, e1, e2, l);
        match as_bool(eval_l(body, e1, l)) {
            Err(k) => {
                lemma_rename_quant(all, ty, body, p, e1, e2, ls, x + 1, hi, if pend is Some { pend } else { Some(k) });
            },
            Ok(b) => {
                lemma_rename_quant(all, ty, body, p, e1, e2, ls, x + 1, hi, pend);
            },
        }
    }
}

// ---- モデルの入れ替え ----

pub open spec fn update_renamed(u: Update, v: Update, p: Seq<usize>) -> bool {
    v.target == rn(u.target, p) && v.expr == rename(u.expr, p)
}

pub open spec fn output_renamed(x: Option<Output>, y: Option<Output>, p: Seq<usize>) -> bool {
    match (x, y) {
        (None, None) => true,
        (Some(a), Some(b)) => b.ty == a.ty && b.expr == rename(a.expr, p),
        _ => false,
    }
}

/// 操作 `y` は、操作 `x` の式のスロットの添字を `p` で付け替えたものである。
pub open spec fn action_renamed(x: Action, y: Action, p: Seq<usize>) -> bool {
    &&& y.n_params == x.n_params
    &&& y.domains@ == x.domains@
    &&& y.guard == rename(x.guard, p)
    &&& y.updates@.len() == x.updates@.len()
    &&& forall|k: int| 0 <= k < x.updates@.len() ==> #[trigger] update_renamed(x.updates@[k], y.updates@[k], p)
    &&& output_renamed(x.output, y.output, p)
}

pub open spec fn term_renamed(t: Option<Expr>, p: Seq<usize>) -> bool {
    match t {
        None => true,
        Some(e) => rename(e, p) == e,
    }
}

/// `f` は `0..n` の対合である。
pub open spec fn invol(f: Seq<usize>, n: int) -> bool {
    &&& f.len() == n
    &&& forall|i: int| 0 <= i < n ==> (#[trigger] f[i]) < n && f[f[i] as int] == i
}

/// 1つの入れ替え。状態のスロットの置換と、それが引き起こす操作、不変条件、遷移契約の置換。
pub struct SwapMaps {
    pub p: Vec<usize>,
    pub act: Vec<usize>,
    pub inv: Vec<usize>,
    pub con: Vec<usize>,
}

/// 入れ替え `w` は、モデル `m` と検査条件 `c` の対称性である。
/// 終端条件はデッドロック検査でだけ使うので、そのときだけ入れ替えで変わらないことを求める。
pub open spec fn sym_ok(m: RawModel, c: Conditions, w: SwapMaps) -> bool {
    let p = w.p@;
    &&& perm_ok(p, m.state_types@)
    &&& invol(w.act@, m.actions@.len() as int)
    &&& forall|a: int|
        0 <= a < m.actions@.len() ==> #[trigger] action_renamed(m.actions@[a], m.actions@[w.act@[a] as int], p)
            && act_on(m, c, a) == act_on(m, c, w.act@[a] as int)
    &&& invol(w.inv@, m.invariants@.len() as int)
    &&& forall|i: int|
        0 <= i < m.invariants@.len() ==> m.invariants@[w.inv@[i] as int] == rename(#[trigger] m.invariants@[i], p)
            && inv_on(m, c, i) == inv_on(m, c, w.inv@[i] as int)
    &&& invol(w.con@, m.contracts@.len() as int)
    &&& forall|k: int|
        0 <= k < m.contracts@.len() ==> {
            let x = #[trigger] m.contracts@[k];
            let y = m.contracts@[w.con@[k] as int];
            &&& x.action < m.actions@.len()
            &&& y.action == w.act@[x.action as int]
            &&& y.expr == rename(x.expr, p)
            &&& con_on(m, c, k) == con_on(m, c, w.con@[k] as int)
        }
    &&& c.deadlock ==> term_renamed(m.terminal, p)
}

pub open spec fn step_rel(r1: Step, r2: Step, p: Seq<usize>) -> bool {
    match (r1, r2) {
        (Step::Disabled, Step::Disabled) => true,
        (Step::Fail(x, e), Step::Fail(y, f)) => x == y && e == f,
        (Step::To(t, o), Step::To(u, q)) => o == q && seq_sw(t, u, p),
        _ => false,
    }
}

pub open spec fn upd_rel(r1: Result<Seq<i64>, (usize, ErrKind)>, r2: Result<Seq<i64>, (usize, ErrKind)>, p: Seq<usize>) -> bool {
    match (r1, r2) {
        (Ok(t), Ok(u)) => seq_sw(t, u, p),
        (Err(x), Err(y)) => x == y,
        _ => false,
    }
}

proof fn lemma_updates_sw(m: RawModel, c: Conditions, w: SwapMaps, a: int, e1: Env, e2: Env, k: nat, acc1: Seq<i64>, acc2: Seq<i64>)
    requires
        sym_ok(m, c, w),
        0 <= a < m.actions@.len(),
        env_sw(e1, e2, w.p@),
        e1.st_tys == m.state_types@,
        seq_sw(acc1, acc2, w.p@),
    ensures
        upd_rel(apply_updates(m, a, e1, k, acc1), apply_updates(m, w.act@[a] as int, e2, k, acc2), w.p@),
    decreases m.actions@[a].updates@.len() - k,
{
    let p = w.p@;
    let b = w.act@[a] as int;
    assert(action_renamed(m.actions@[a], m.actions@[b], p));
    let ups = m.actions@[a].updates@;
    if k < ups.len() {
        let u = ups[k as int];
        let v = m.actions@[b].updates@[k as int];
        assert(update_renamed(u, v, p));
        lemma_rename_eval(u.expr, p, e1, e2, Seq::empty());
        match eval_spec(u.expr, e1) {
            Err(_) => {},
            Ok(val) => {
                if u.target < acc1.len() && u.target < m.state_types@.len() {
                    let t = u.target as int;
                    let t2 = p[t] as int;
                    assert(v.target as int == t2);
                    assert(m.state_types@[t2] == m.state_types@[t]);
                    match encode_spec(m.enums@, m.state_types@[t], val) {
                        Err(_) => {},
                        Ok(x) => {
                            let n1 = acc1.update(t, x);
                            let n2 = acc2.update(t2, x);
                            assert forall|j: int| 0 <= j < p.len() implies #[trigger] n2[j] == n1[p[j] as int] by {
                                assert(p[p[j] as int] == j);
                                assert(p[t2] == t);
                            }
                            lemma_updates_sw(m, c, w, a, e1, e2, k + 1, n1, n2);
                        },
                    }
                }
            },
        }
    }
}

/// 入れ替えた状態で、入れ替えた操作を適用した結果は、元の結果を入れ替えたものである。
pub proof fn lemma_step_sw(m: RawModel, c: Conditions, w: SwapMaps, a: int, args: Seq<i64>, s: Seq<i64>, s2: Seq<i64>)
    requires
        sym_ok(m, c, w),
        0 <= a < m.actions@.len(),
        seq_sw(s, s2, w.p@),
    ensures
        step_rel(step_spec(m, a, args, s), step_spec(m, w.act@[a] as int, args, s2), w.p@),
{
    let p = w.p@;
    let b = w.act@[a] as int;
    assert(action_renamed(m.actions@[a], m.actions@[b], p));
    let e1 = act_env(m, a, args, s);
    let e2 = act_env(m, b, args, s2);
    assert(env_sw(e1, e2, p));
    lemma_rename_eval(m.actions@[a].guard, p, e1, e2, Seq::empty());
    lemma_updates_sw(m, c, w, a, e1, e2, 0, s, s2);
    match (m.actions@[a].output, m.actions@[b].output) {
        (Some(o1), Some(o2)) => {
            lemma_rename_eval(o1.expr, p, e1, e2, Seq::empty());
        },
        _ => {},
    }
}

proof fn lemma_inv_sw(m: RawModel, c: Conditions, w: SwapMaps, i: int, s: Seq<i64>, s2: Seq<i64>)
    requires
        sym_ok(m, c, w),
        0 <= i < m.invariants@.len(),
        seq_sw(s, s2, w.p@),
    ensures
        inv_spec(m, w.inv@[i] as int, s2) == inv_spec(m, i, s),
{
    assert(m.invariants@[w.inv@[i] as int] == rename(m.invariants@[i], w.p@));
    lemma_rename_eval(m.invariants@[i], w.p@, inv_env(m, s), inv_env(m, s2), Seq::empty());
}

proof fn lemma_term_sw(m: RawModel, c: Conditions, w: SwapMaps, s: Seq<i64>, s2: Seq<i64>)
    requires
        sym_ok(m, c, w),
        c.deadlock,
        seq_sw(s, s2, w.p@),
    ensures
        terminal_spec(m, s2) == terminal_spec(m, s),
{
    if let Some(e) = m.terminal {
        lemma_rename_eval(e, w.p@, inv_env(m, s), inv_env(m, s2), Seq::empty());
    }
}

proof fn lemma_con_sw(
    m: RawModel,
    c: Conditions,
    w: SwapMaps,
    k: int,
    pre: Seq<i64>,
    pre2: Seq<i64>,
    args: Seq<i64>,
    post: Seq<i64>,
    post2: Seq<i64>,
    o: Option<i64>,
)
    requires
        sym_ok(m, c, w),
        0 <= k < m.contracts@.len(),
        seq_sw(pre, pre2, w.p@),
        seq_sw(post, post2, w.p@),
    ensures
        con_spec(m, w.con@[k] as int, pre2, args, post2, o) == con_spec(m, k, pre, args, post, o),
{
    let x = m.contracts@[k];
    let y = m.contracts@[w.con@[k] as int];
    let a = x.action as int;
    let b = w.act@[a] as int;
    assert(action_renamed(m.actions@[a], m.actions@[b], w.p@));
    let e1 = con_env(m, a, pre, args, post, o);
    let e2 = con_env(m, b, pre2, args, post2, o);
    assert(out_value(m, b, o) == out_value(m, a, o));
    assert(env_sw(e1, e2, w.p@));
    lemma_rename_eval(x.expr, w.p@, e1, e2, Seq::empty());
}

/// 入れ替えた状態が安全なら、元の状態も安全である。
pub proof fn lemma_safe_sw(m: RawModel, c: Conditions, w: SwapMaps, s: Seq<i64>)
    requires
        sym_ok(m, c, w),
        s.len() == w.p@.len(),
        state_safe(m, c, permute(s, w.p@)),
    ensures
        state_safe(m, c, s),
{
    let p = w.p@;
    let s2 = permute(s, p);
    assert(seq_sw(s, s2, p));
    assert forall|i: int| #[trigger] inv_on(m, c, i) implies inv_spec(m, i, s) == Ok::<bool, ErrKind>(true) by {
        lemma_inv_sw(m, c, w, i, s, s2);
        assert(inv_on(m, c, w.inv@[i] as int));
    }
    assert forall|a: int, args: Seq<i64>| #[trigger] act_on(m, c, a) && #[trigger] args_ok(m, a, args) implies trans_safe(
        m,
        c,
        a,
        args,
        s,
    ) by {
        let b = w.act@[a] as int;
        assert(action_renamed(m.actions@[a], m.actions@[b], p));
        assert(act_on(m, c, b));
        assert(args_ok(m, b, args));
        lemma_step_sw(m, c, w, a, args, s, s2);
        assert(trans_safe(m, c, b, args, s2));
        if let Step::To(t, o) = step_spec(m, a, args, s) {
            let t2 = permute(t, p);
            assert(step_spec(m, b, args, s2) == Step::To(t2, o)) by {
                if let Step::To(u, q) = step_spec(m, b, args, s2) {
                    assert(u =~= t2);
                }
            }
            assert(seq_sw(t, t2, p));
            assert forall|k: int| #[trigger] con_on(m, c, k) && m.contracts@[k].action == a implies con_spec(
                m,
                k,
                s,
                args,
                t,
                o,
            ) == Ok::<bool, ErrKind>(true) by {
                let k2 = w.con@[k] as int;
                assert(con_on(m, c, k2));
                lemma_con_sw(m, c, w, k, s, s2, args, t, t2, o);
            }
        }
    }
    if c.deadlock && stuck(m, c, s) {
        assert(stuck(m, c, s2)) by {
            assert forall|b: int| #[trigger] act_on(m, c, b) implies all_disabled(m, b, s2) by {
                let a = w.act@[b] as int;
                assert(0 <= b < m.actions@.len());
                assert(w.act@[a] == b);
                assert(action_renamed(m.actions@[a], m.actions@[w.act@[a] as int], p));
                assert(act_on(m, c, a));
                assert forall|args: Seq<i64>| #[trigger] args_ok(m, b, args) implies step_spec(m, b, args, s2) is Disabled by {
                    assert(action_renamed(m.actions@[a], m.actions@[b], p));
                    assert(args_ok(m, a, args));
                    assert(all_disabled(m, a, s));
                    lemma_step_sw(m, c, w, a, args, s, s2);
                }
            }
        }
        lemma_term_sw(m, c, w, s, s2);
    }
}

/// 入れ替えは有効な遷移を、入れ替えた操作による入れ替えた状態の間の有効な遷移に写す。
pub proof fn lemma_edge_sw(
    m: RawModel,
    c: Conditions,
    w: SwapMaps,
    s: Seq<i64>,
    a: int,
    args: Seq<i64>,
    o: Option<i64>,
    t: Seq<i64>,
)
    requires
        sym_ok(m, c, w),
        s.len() == w.p@.len(),
        is_edge(m, c, s, a, args, o, t),
    ensures
        t.len() == w.p@.len(),
        is_edge(m, c, permute(s, w.p@), w.act@[a] as int, args, o, permute(t, w.p@)),
{
    let p = w.p@;
    let b = w.act@[a] as int;
    let s2 = permute(s, p);
    assert(seq_sw(s, s2, p));
    assert(action_renamed(m.actions@[a], m.actions@[b], p));
    lemma_step_sw(m, c, w, a, args, s, s2);
    if let Step::To(u, q) = step_spec(m, b, args, s2) {
        assert(u =~= permute(t, p));
    }
}

// ---- 入れ替えの列 ----

/// 入れ替え `sw[w[0]]`、`sw[w[1]]`、… を順に施した状態。
pub open spec fn apply_word(sw: Seq<SwapMaps>, w: Seq<usize>, s: Seq<i64>) -> Seq<i64>
    decreases w.len(),
{
    if w.len() == 0 {
        s
    } else {
        permute(apply_word(sw, w.drop_last(), s), sw[w.last() as int].p@)
    }
}

/// 入れ替えの列が、操作の添字 `a` を写した先。
pub open spec fn map_act(sw: Seq<SwapMaps>, w: Seq<usize>, a: int) -> int
    decreases w.len(),
{
    if w.len() == 0 {
        a
    } else {
        sw[w.last() as int].act@[map_act(sw, w.drop_last(), a)] as int
    }
}

pub open spec fn word_ok(sw: Seq<SwapMaps>, w: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> (#[trigger] w[i]) < sw.len()
}

pub open spec fn all_sym(m: RawModel, c: Conditions, sw: Seq<SwapMaps>) -> bool {
    forall|i: int| 0 <= i < sw.len() ==> sym_ok(m, c, #[trigger] sw[i])
}

proof fn lemma_word_drop(sw: Seq<SwapMaps>, w: Seq<usize>)
    requires
        word_ok(sw, w),
        w.len() > 0,
    ensures
        word_ok(sw, w.drop_last()),
        w.last() < sw.len(),
{
    assert(w[w.len() - 1] < sw.len());
    assert forall|i: int| 0 <= i < w.drop_last().len() implies (#[trigger] w.drop_last()[i]) < sw.len() by {
        assert(w.drop_last()[i] == w[i]);
    }
}

proof fn lemma_edge_word(
    m: RawModel,
    c: Conditions,
    sw: Seq<SwapMaps>,
    w: Seq<usize>,
    s: Seq<i64>,
    a: int,
    args: Seq<i64>,
    o: Option<i64>,
    t: Seq<i64>,
)
    requires
        all_sym(m, c, sw),
        word_ok(sw, w),
        s.len() == m.state_types@.len(),
        is_edge(m, c, s, a, args, o, t),
    ensures
        t.len() == m.state_types@.len(),
        apply_word(sw, w, s).len() == m.state_types@.len(),
        is_edge(m, c, apply_word(sw, w, s), map_act(sw, w, a), args, o, apply_word(sw, w, t)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(step_spec(m, a, args, s) == Step::To(t, o));
        lemma_updates_len(m, a, act_env(m, a, args, s), 0, s);
    } else {
        lemma_word_drop(sw, w);
        lemma_edge_word(m, c, sw, w.drop_last(), s, a, args, o, t);
        let x = sw[w.last() as int];
        assert(sym_ok(m, c, x));
        lemma_edge_sw(
            m,
            c,
            x,
            apply_word(sw, w.drop_last(), s),
            map_act(sw, w.drop_last(), a),
            args,
            o,
            apply_word(sw, w.drop_last(), t),
        );
    }
}

/// 更新は状態の長さを変えない。
proof fn lemma_updates_len(m: RawModel, a: int, env: Env, k: nat, acc: Seq<i64>)
    ensures
        apply_updates(m, a, env, k, acc) matches Ok(t) ==> t.len() == acc.len(),
    decreases m.actions@[a].updates@.len() - k,
{
    let ups = m.actions@[a].updates@;
    if k < ups.len() {
        let u = ups[k as int];
        match eval_spec(u.expr, env) {
            Ok(v) => if u.target < acc.len() && u.target < m.state_types@.len() {
                match encode_spec(m.enums@, m.state_types@[u.target as int], v) {
                    Ok(x) => lemma_updates_len(m, a, env, k + 1, acc.update(u.target as int, x)),
                    Err(_) => {},
                }
            },
            Err(_) => {},
        }
    }
}

proof fn lemma_safe_word(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, w: Seq<usize>, s: Seq<i64>)
    requires
        all_sym(m, c, sw),
        word_ok(sw, w),
        s.len() == m.state_types@.len(),
        state_safe(m, c, apply_word(sw, w, s)),
    ensures
        state_safe(m, c, s),
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_word_drop(sw, w);
        lemma_word_len(m, c, sw, w.drop_last(), s);
        let x = sw[w.last() as int];
        assert(sym_ok(m, c, x));
        lemma_safe_sw(m, c, x, apply_word(sw, w.drop_last(), s));
        lemma_safe_word(m, c, sw, w.drop_last(), s);
    }
}

proof fn lemma_word_len(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, w: Seq<usize>, s: Seq<i64>)
    requires
        all_sym(m, c, sw),
        word_ok(sw, w),
        s.len() == m.state_types@.len(),
    ensures
        apply_word(sw, w, s).len() == m.state_types@.len(),
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_word_drop(sw, w);
        lemma_word_len(m, c, sw, w.drop_last(), s);
        assert(sym_ok(m, c, sw[w.last() as int]));
    }
}

proof fn lemma_word_concat(sw: Seq<SwapMaps>, w1: Seq<usize>, w2: Seq<usize>, s: Seq<i64>)
    ensures
        apply_word(sw, w1 + w2, s) == apply_word(sw, w2, apply_word(sw, w1, s)),
    decreases w2.len(),
{
    if w2.len() == 0 {
        assert(w1 + w2 =~= w1);
    } else {
        assert((w1 + w2).drop_last() =~= w1 + w2.drop_last());
        assert((w1 + w2).last() == w2.last());
        lemma_word_concat(sw, w1, w2.drop_last(), s);
    }
}

// ---- 代表元の証明書 ----

/// 状態 `s` から、入れ替えの列で証明書の状態に移れる。
pub open spec fn reps(sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    exists|w: Seq<usize>| word_ok(sw, w) && #[trigger] in_cert(cert, apply_word(sw, w, s))
}

/// 証明書の状態 `s` は性質を満たし、有効な遷移の後続は、入れ替えの列で証明書の状態に移れる。
pub open spec fn sym_state_closed(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    &&& s.len() == m.state_types@.len()
    &&& invs_hold(m, c, s)
    &&& no_deadlock(m, c, s)
    &&& forall|a: int, args: Seq<i64>| #[trigger]
        act_on(m, c, a) && #[trigger] args_ok(m, a, args) ==> match step_spec(m, a, args, s) {
            Step::Disabled => true,
            Step::Fail(_, _) => false,
            Step::To(t, o) => cons_hold(m, c, a, s, args, t, o) && reps(sw, cert, t),
        }
}

pub open spec fn sym_inductive(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>) -> bool {
    &&& forall|i: int|
        0 <= i < m.inits@.len() ==> (#[trigger] m.inits@[i])@.len() == m.state_types@.len() && reps(
            sw,
            cert,
            m.inits@[i]@,
        )
    &&& forall|j: int| 0 <= j < cert.len() ==> sym_state_closed(m, c, sw, cert, (#[trigger] cert[j])@)
}

proof fn lemma_sym_closed_safe(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>, s: Seq<i64>)
    requires
        sym_state_closed(m, c, sw, cert, s),
    ensures
        state_safe(m, c, s),
{
    assert forall|a: int, args: Seq<i64>| #[trigger] act_on(m, c, a) && #[trigger] args_ok(m, a, args) implies trans_safe(
        m,
        c,
        a,
        args,
        s,
    ) by {}
}

proof fn lemma_reach_reps(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>, s: Seq<i64>, n: nat)
    requires
        all_sym(m, c, sw),
        sym_inductive(m, c, sw, cert),
        reach(m, c, s, n),
    ensures
        s.len() == m.state_types@.len(),
        reps(sw, cert, s),
    decreases n,
{
    if n == 0 {
        let i = choose|i: int| 0 <= i < m.inits@.len() && (#[trigger] m.inits@[i])@ == s;
        assert(reps(sw, cert, m.inits@[i]@));
    } else {
        let (q, a, args, o) = choose|q: Seq<i64>, a: int, args: Seq<i64>, o: Option<i64>|
            reach(m, c, q, (n - 1) as nat) && #[trigger] is_edge(m, c, q, a, args, o, s);
        lemma_reach_reps(m, c, sw, cert, q, (n - 1) as nat);
        let w = choose|w: Seq<usize>| word_ok(sw, w) && #[trigger] in_cert(cert, apply_word(sw, w, q));
        lemma_edge_word(m, c, sw, w, q, a, args, o, s);
        let r = apply_word(sw, w, q);
        let j = choose|j: int| 0 <= j < cert.len() && (#[trigger] cert[j])@ == r;
        assert(sym_state_closed(m, c, sw, cert, cert[j]@));
        let b = map_act(sw, w, a);
        let t = apply_word(sw, w, s);
        assert(is_edge(m, c, r, b, args, o, t));
        assert(act_on(m, c, b) && args_ok(m, b, args));
        assert(reps(sw, cert, t));
        let w2 = choose|w2: Seq<usize>| word_ok(sw, w2) && #[trigger] in_cert(cert, apply_word(sw, w2, t));
        lemma_word_concat(sw, w, w2, s);
        assert forall|i: int| 0 <= i < (w + w2).len() implies (#[trigger] (w + w2)[i]) < sw.len() by {
            if i < w.len() {
                assert((w + w2)[i] == w[i]);
            } else {
                assert((w + w2)[i] == w2[i - w.len()]);
            }
        }
        assert(in_cert(cert, apply_word(sw, w + w2, s)));
    }
}

/// 代表元の証明書が帰納的で、入れ替えがどれも対称性なら、モデルは安全である。
pub proof fn lemma_sym_safe(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, cert: Seq<Vec<i64>>)
    requires
        all_sym(m, c, sw),
        sym_inductive(m, c, sw, cert),
    ensures
        safe(m, c),
{
    assert forall|s: Seq<i64>, n: nat| #[trigger] reach(m, c, s, n) implies state_safe(m, c, s) by {
        lemma_reach_reps(m, c, sw, cert, s, n);
        let w = choose|w: Seq<usize>| word_ok(sw, w) && #[trigger] in_cert(cert, apply_word(sw, w, s));
        let j = choose|j: int| 0 <= j < cert.len() && (#[trigger] cert[j])@ == apply_word(sw, w, s);
        assert(sym_state_closed(m, c, sw, cert, cert[j]@));
        lemma_sym_closed_safe(m, c, sw, cert, cert[j]@);
        lemma_safe_word(m, c, sw, w, s);
    }
}

// ---- 実行 ----

fn type_eq(a: &Type, b: &Type) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (Type::Bool, Type::Bool) => true,
        (Type::Int(x, y), Type::Int(z, w)) => *x == *z && *y == *w,
        (Type::Enum(x), Type::Enum(y)) => *x == *y,
        _ => false,
    }
}

fn op_eq(a: &BinOp, b: &BinOp) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (BinOp::Add, BinOp::Add) => true,
        (BinOp::Sub, BinOp::Sub) => true,
        (BinOp::Mul, BinOp::Mul) => true,
        (BinOp::Lt, BinOp::Lt) => true,
        (BinOp::Le, BinOp::Le) => true,
        (BinOp::Gt, BinOp::Gt) => true,
        (BinOp::Ge, BinOp::Ge) => true,
        (BinOp::Eq, BinOp::Eq) => true,
        (BinOp::Ne, BinOp::Ne) => true,
        (BinOp::Div, BinOp::Div) => true,
        (BinOp::Mod, BinOp::Mod) => true,
        _ => false,
    }
}

fn rn_exec(i: usize, p: &Vec<usize>) -> (r: usize)
    ensures
        r == rn(i, p@),
{
    if i < p.len() {
        p[i]
    } else {
        i
    }
}

/// `f` が、`e` のスロットの添字を `p` で付け替えた式と一致するか。
pub fn renamed_eq(e: &Expr, f: &Expr, p: &Vec<usize>) -> (r: bool)
    ensures
        r ==> *f == rename(*e, p@),
    decreases e,
{
    match (e, f) {
        (Expr::Const(x), Expr::Const(y)) => value_eq(x, y),
        (Expr::Var(i), Expr::Var(j)) => *j == rn_exec(*i, p),
        (Expr::Arg(i), Expr::Arg(j)) => *i == *j,
        (Expr::Next(i), Expr::Next(j)) => *j == rn_exec(*i, p),
        (Expr::Out, Expr::Out) => true,
        (Expr::Bin(o1, a1, b1), Expr::Bin(o2, a2, b2)) => op_eq(o1, o2) && renamed_eq(a1, a2, p) && renamed_eq(b1, b2, p),
        (Expr::Not(a1), Expr::Not(a2)) => renamed_eq(a1, a2, p),
        (Expr::And(a1, b1), Expr::And(a2, b2)) => renamed_eq(a1, a2, p) && renamed_eq(b1, b2, p),
        (Expr::Or(a1, b1), Expr::Or(a2, b2)) => renamed_eq(a1, a2, p) && renamed_eq(b1, b2, p),
        (Expr::Implies(a1, b1), Expr::Implies(a2, b2)) => renamed_eq(a1, a2, p) && renamed_eq(b1, b2, p),
        (Expr::Ite(c1, a1, b1), Expr::Ite(c2, a2, b2)) => renamed_eq(c1, c2, p) && renamed_eq(a1, a2, p) && renamed_eq(
            b1,
            b2,
            p,
        ),
        (Expr::Local(i), Expr::Local(j)) => *i == *j,
        (Expr::Let(a1, b1), Expr::Let(a2, b2)) => renamed_eq(a1, a2, p) && renamed_eq(b1, b2, p),
        (Expr::Forall(t1, l1, h1, b1), Expr::Forall(t2, l2, h2, b2)) => type_eq(t1, t2) && *l1 == *l2 && *h1 == *h2
            && renamed_eq(b1, b2, p),
        (Expr::Exists(t1, l1, h1, b1), Expr::Exists(t2, l2, h2, b2)) => type_eq(t1, t2) && *l1 == *l2 && *h1 == *h2
            && renamed_eq(b1, b2, p),
        (Expr::Code(a1), Expr::Code(a2)) => renamed_eq(a1, a2, p),
        (Expr::Fail(t1, k1), Expr::Fail(t2, k2)) => type_eq(t1, t2) && *k1 == *k2,
        _ => false,
    }
}

fn types_eq(a: &Vec<Type>, b: &Vec<Type>) -> (r: bool)
    ensures
        r ==> a@ == b@,
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if !type_eq(&a[i], &b[i]) {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

fn action_renamed_exec(x: &Action, y: &Action, p: &Vec<usize>) -> (r: bool)
    ensures
        r ==> action_renamed(*x, *y, p@),
{
    if y.n_params != x.n_params || !types_eq(&x.domains, &y.domains) || !renamed_eq(&x.guard, &y.guard, p) {
        return false;
    }
    if y.updates.len() != x.updates.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < x.updates.len()
        invariant
            k <= x.updates@.len(),
            y.updates@.len() == x.updates@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] update_renamed(x.updates@[j], y.updates@[j], p@),
        decreases x.updates@.len() - k,
    {
        let u = &x.updates[k];
        let v = &y.updates[k];
        if v.target != rn_exec(u.target, p) || !renamed_eq(&u.expr, &v.expr, p) {
            return false;
        }
        k = k + 1;
    }
    match (&x.output, &y.output) {
        (None, None) => true,
        (Some(a), Some(b)) => type_eq(&a.ty, &b.ty) && renamed_eq(&a.expr, &b.expr, p),
        _ => false,
    }
}

fn perm_ok_exec(p: &Vec<usize>, tys: &Vec<Type>) -> (r: bool)
    ensures
        r ==> perm_ok(p@, tys@),
{
    if p.len() != tys.len() {
        return false;
    }
    let mut j: usize = 0;
    while j < p.len()
        invariant
            p@.len() == tys@.len(),
            j <= p@.len(),
            forall|i: int|
                0 <= i < j ==> (#[trigger] p@[i]) < p@.len() && p@[p@[i] as int] == i && tys@[p@[i] as int] == tys@[i],
        decreases p@.len() - j,
    {
        let q = p[j];
        if q >= p.len() || p[q] != j || !type_eq(&tys[q], &tys[j]) {
            return false;
        }
        j = j + 1;
    }
    true
}

fn invol_exec(f: &Vec<usize>, n: usize) -> (r: bool)
    ensures
        r ==> invol(f@, n as int),
{
    if f.len() != n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            f@.len() == n,
            i <= n,
            forall|j: int| 0 <= j < i ==> (#[trigger] f@[j]) < n && f@[f@[j] as int] == j,
        decreases n - i,
    {
        if f[i] >= n || f[f[i]] != i {
            return false;
        }
        i = i + 1;
    }
    true
}

/// 入れ替え `p` が、モデル `m` と検査条件 `c` の対称性かを確かめ、操作、不変条件、遷移契約の置換を求める。
/// 対称性でなければ `None`。
#[verifier::loop_isolation(false)]
pub fn swap_maps(m: &RawModel, c: &Conditions, p: &Vec<usize>) -> (r: Option<SwapMaps>)
    ensures
        r matches Some(w) ==> sym_ok(*m, *c, w) && w.p@ == p@,
{
    if !perm_ok_exec(p, &m.state_types) {
        return None;
    }
    // 操作
    let n = m.actions.len();
    let mut act: Vec<usize> = Vec::new();
    let mut a: usize = 0;
    while a < n
        invariant
            n == m.actions@.len(),
            a <= n,
            act@.len() == a,
            forall|i: int| 0 <= i < a ==> (#[trigger] act@[i]) < n && action_renamed(m.actions@[i], m.actions@[act@[i] as int], p@),
        decreases n - a,
    {
        let mut b: usize = 0;
        let mut found = false;
        while b < n && !found
            invariant
                n == m.actions@.len(),
                b <= n,
                found ==> b >= 1 && action_renamed(m.actions@[a as int], m.actions@[(b - 1) as int], p@),
            decreases n - b, (if found { 0int } else { 1int }),
        {
            if action_renamed_exec(&m.actions[a], &m.actions[b], p) {
                found = true;
            }
            b = b + 1;
        }
        if !found {
            return None;
        }
        act.push(b - 1);
        a = a + 1;
    }
    if !invol_exec(&act, n) {
        return None;
    }
    let mut a: usize = 0;
    while a < n
        invariant
            n == m.actions@.len(),
            act@.len() == n,
            invol(act@, n as int),
            a <= n,
            forall|i: int| 0 <= i < a ==> act_on(*m, *c, i) == act_on(*m, *c, #[trigger] act@[i] as int),
        decreases n - a,
    {
        if act_on_exec(m, c, a) != act_on_exec(m, c, act[a]) {
            return None;
        }
        a = a + 1;
    }
    // 不変条件
    let ni = m.invariants.len();
    let mut inv: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < ni
        invariant
            ni == m.invariants@.len(),
            i <= ni,
            inv@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] inv@[j]) < ni && m.invariants@[inv@[j] as int] == rename(m.invariants@[j], p@),
        decreases ni - i,
    {
        let mut j: usize = 0;
        let mut found = false;
        while j < ni && !found
            invariant
                ni == m.invariants@.len(),
                j <= ni,
                found ==> j >= 1 && m.invariants@[(j - 1) as int] == rename(m.invariants@[i as int], p@),
            decreases ni - j, (if found { 0int } else { 1int }),
        {
            if renamed_eq(&m.invariants[i], &m.invariants[j], p) {
                found = true;
            }
            j = j + 1;
        }
        if !found {
            return None;
        }
        inv.push(j - 1);
        i = i + 1;
    }
    if !invol_exec(&inv, ni) {
        return None;
    }
    let mut i: usize = 0;
    while i < ni
        invariant
            ni == m.invariants@.len(),
            inv@.len() == ni,
            i <= ni,
            forall|j: int| 0 <= j < i ==> inv_on(*m, *c, j) == inv_on(*m, *c, #[trigger] inv@[j] as int),
        decreases ni - i,
    {
        if inv_on_exec(m, c, i) != inv_on_exec(m, c, inv[i]) {
            return None;
        }
        i = i + 1;
    }
    // 遷移契約
    let nc = m.contracts.len();
    let mut con: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < nc
        invariant
            nc == m.contracts@.len(),
            n == m.actions@.len(),
            act@.len() == n,
            k <= nc,
            con@.len() == k,
            forall|j: int|
                0 <= j < k ==> {
                    let x = #[trigger] m.contracts@[j];
                    let y = m.contracts@[con@[j] as int];
                    &&& con@[j] < nc
                    &&& x.action < n
                    &&& y.action == act@[x.action as int]
                    &&& y.expr == rename(x.expr, p@)
                },
        decreases nc - k,
    {
        let x = &m.contracts[k];
        if x.action >= n {
            return None;
        }
        let target = act[x.action];
        let mut j: usize = 0;
        let mut found = false;
        while j < nc && !found
            invariant
                nc == m.contracts@.len(),
                j <= nc,
                found ==> j >= 1 && m.contracts@[(j - 1) as int].action == target && m.contracts@[(j - 1) as int].expr
                    == rename(m.contracts@[k as int].expr, p@),
            decreases nc - j, (if found { 0int } else { 1int }),
        {
            if m.contracts[j].action == target && renamed_eq(&x.expr, &m.contracts[j].expr, p) {
                found = true;
            }
            j = j + 1;
        }
        if !found {
            return None;
        }
        con.push(j - 1);
        k = k + 1;
    }
    if !invol_exec(&con, nc) {
        return None;
    }
    let mut k: usize = 0;
    while k < nc
        invariant
            nc == m.contracts@.len(),
            con@.len() == nc,
            k <= nc,
            forall|j: int| 0 <= j < k ==> con_on(*m, *c, j) == con_on(*m, *c, #[trigger] con@[j] as int),
        decreases nc - k,
    {
        if con_on_exec(m, c, k) != con_on_exec(m, c, con[k]) {
            return None;
        }
        k = k + 1;
    }
    // 終端条件。デッドロック検査をするときだけ使う。
    if c.deadlock {
        match &m.terminal {
            None => {},
            Some(e) => {
                if !renamed_eq(e, e, p) {
                    return None;
                }
            },
        }
    }
    let w = SwapMaps { p: copy_usizes(p), act, inv, con };
    proof {
        assert(w.p@ =~= p@);
        assert forall|a: int| 0 <= a < m.actions@.len() implies #[trigger] action_renamed(
            m.actions@[a],
            m.actions@[w.act@[a] as int],
            w.p@,
        ) && act_on(*m, *c, a) == act_on(*m, *c, w.act@[a] as int) by {}
    }
    Some(w)
}

fn copy_usizes(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures
        r@ == v@,
{
    let mut r: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        assert(r@ =~= v@.subrange(0, i as int));
    }
    assert(r@ =~= v@);
    r
}

/// スロットを `p` で入れ替える。長さが合わなければ `None`。
pub fn permute_exec(s: &Vec<i64>, p: &Vec<usize>) -> (r: Option<Vec<i64>>)
    ensures
        r matches Some(t) ==> s@.len() == p@.len() && t@ == permute(s@, p@),
{
    if s.len() != p.len() {
        return None;
    }
    let mut t: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < p.len()
        invariant
            s@.len() == p@.len(),
            j <= p@.len(),
            t@.len() == j,
            forall|i: int| 0 <= i < j ==> t@[i] == s@[p@[i] as int] && p@[i] < s@.len(),
        decreases p@.len() - j,
    {
        if p[j] >= s.len() {
            return None;
        }
        t.push(s[p[j]]);
        j = j + 1;
    }
    assert(t@ =~= permute(s@, p@));
    Some(t)
}

/// 入れ替えを、状態が辞書順で小さくなる限り施す。施した入れ替えの列と、結果の状態を返す。
/// 入れ替えが隣り合うブロックの入れ替えなら、これはブロックの整列であり、軌道の最小元になる。
/// 一意であることは証明しない（健全性には要らない）。
pub fn canonicalize(sw: &Vec<SwapMaps>, s: &Vec<i64>) -> (r: (Vec<i64>, Vec<usize>))
    ensures
        r.0@ == apply_word(sw@, r.1@, s@),
        word_ok(sw@, r.1@),
{
    let mut cur: Vec<i64> = copy_vec(s);
    let mut word: Vec<usize> = Vec::new();
    let mut round: usize = 0;
    let rounds = if sw.len() < 4096 {
        sw.len() + 2
    } else {
        4098
    };
    let mut changed = true;
    while changed && round < rounds
        invariant
            cur@ == apply_word(sw@, word@, s@),
            word_ok(sw@, word@),
        decreases rounds - round,
    {
        changed = false;
        let mut i: usize = 0;
        while i < sw.len()
            invariant
                cur@ == apply_word(sw@, word@, s@),
                word_ok(sw@, word@),
            decreases sw@.len() - i,
        {
            match permute_exec(&cur, &sw[i].p) {
                Some(t) => {
                    if cmp_state(&t, &cur) < 0 {
                        proof {
                            let w2 = word@.push(i);
                            assert(w2.drop_last() =~= word@);
                            assert(w2.last() == i);
                        }
                        word.push(i);
                        cur = t;
                        changed = true;
                    }
                },
                None => {},
            }
            i = i + 1;
        }
        round = round + 1;
    }
    (cur, word)
}

/// 入れ替えの列 `swaps`（各要素はスロットの置換）が、どれもモデルと検査条件の対称性かを確かめる。
/// 対称性でない最初の入れ替えの添字を `Err` で返す。
pub(crate) fn symmetry(m: &RawModel, c: &Conditions, swaps: &Vec<Vec<usize>>) -> (r: Result<Vec<SwapMaps>, usize>)
    ensures
        r matches Ok(sw) ==> sw@.len() == swaps@.len() && all_sym(*m, *c, sw@),
{
    let mut sw: Vec<SwapMaps> = Vec::new();
    let mut i: usize = 0;
    while i < swaps.len()
        invariant
            i <= swaps@.len(),
            sw@.len() == i,
            all_sym(*m, *c, sw@),
        decreases swaps@.len() - i,
    {
        match swap_maps(m, c, &swaps[i]) {
            Some(w) => {
                let ghost prev = sw@;
                sw.push(w);
                proof {
                    assert forall|j: int| 0 <= j < sw@.len() implies sym_ok(*m, *c, #[trigger] sw@[j]) by {
                        if j < i {
                            assert(sw@[j] == prev[j]);
                        }
                    }
                }
            },
            None => {
                return Err(i);
            },
        }
        i = i + 1;
    }
    Ok(sw)
}


/// 入れ替えの列が、どれもモデルと検査条件の対称性かを確かめる（`symmetry` と同じ）。未検証コード向け。
pub fn symmetry_of(model: &CheckedModel, c: &Conditions, swaps: &Vec<Vec<usize>>) -> (r: Result<Vec<SwapMaps>, usize>)
    ensures
        r matches Ok(sw) ==> sw@.len() == swaps@.len() && all_sym(model@, *c, sw@),
{
    symmetry(model.raw(), c, swaps)
}

} // verus!
