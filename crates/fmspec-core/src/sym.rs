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
//!
//! ここには、付け替えの意味論と、入れ替えで遷移と性質が保たれることの補題を置く。
//! 入れ替えの構文の照合と正規化の実行関数は [`crate::sym_check`] に、代表元の証明書の仕様と検査器は
//! [`crate::cert`] にある。

#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, decode, eval_l, eval_spec, lookup, quant_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::model::{Action, Expr, Output, RawModel, Type, Update, Value};
#[cfg(verus_keep_ghost)]
use crate::semantics::{act_on, con_env, con_on, con_spec, inv_env, inv_on, inv_spec, Conditions};
#[cfg(verus_keep_ghost)]
use crate::semantics::{is_edge, out_value, state_safe, stuck, terminal_spec, trans_safe};
#[cfg(verus_keep_ghost)]
use crate::state_enc::{args_ok, encode_spec};
#[cfg(verus_keep_ghost)]
use crate::step::{act_env, all_disabled, apply_updates, step_spec, Step};
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

pub(crate) proof fn lemma_edge_word(
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

pub(crate) proof fn lemma_safe_word(m: RawModel, c: Conditions, sw: Seq<SwapMaps>, w: Seq<usize>, s: Seq<i64>)
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

pub(crate) proof fn lemma_word_concat(sw: Seq<SwapMaps>, w1: Seq<usize>, w2: Seq<usize>, s: Seq<i64>)
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

} // verus!
