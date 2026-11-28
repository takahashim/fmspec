//! 入れ替えが対称性であることの検査（`swap_maps`、`symmetry`）と、状態の正規化（`canonicalize`）。下ろした中核のモデルの式が、スロットの付け替えで写り合うかを構文として照合する。

use crate::checked::CheckedModel;
use crate::eval::value_eq;
use crate::model::{Action, BinOp, Expr, RawModel, Type};
#[cfg(verus_keep_ghost)]
use crate::semantics::{act_on, con_on, inv_on};
use crate::semantics::{act_on_exec, con_on_exec, inv_on_exec, Conditions};
use crate::state_enc::{copy_usizes, copy_vec};
use crate::state_set::cmp_state;
use crate::sym::SwapMaps;
#[cfg(verus_keep_ghost)]
use crate::sym::{action_renamed, all_sym, apply_word, invol, perm_ok, permute, rename, rn, sym_ok};
#[cfg(verus_keep_ghost)]
use crate::sym::{update_renamed, word_ok};
use vstd::prelude::*;

verus! {

pub(crate) fn type_eq(a: &Type, b: &Type) -> (r: bool)
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

pub(crate) fn op_eq(a: &BinOp, b: &BinOp) -> (r: bool)
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

pub(crate) fn rn_exec(i: usize, p: &Vec<usize>) -> (r: usize)
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

pub(crate) fn types_eq(a: &Vec<Type>, b: &Vec<Type>) -> (r: bool)
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

pub(crate) fn action_renamed_exec(x: &Action, y: &Action, p: &Vec<usize>) -> (r: bool)
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

pub(crate) fn perm_ok_exec(p: &Vec<usize>, tys: &Vec<Type>) -> (r: bool)
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

pub(crate) fn invol_exec(f: &Vec<usize>, n: usize) -> (r: bool)
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
