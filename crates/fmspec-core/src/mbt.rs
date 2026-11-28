//! Model-Based Testing の候補集合（仕様書 §11.4、§12.2）。
//!
//! 1ケース分の候補は、初期観測とこれまでの応答（入力、戻り値、観測）のすべてと矛盾しないモデルの状態である。
//! その集合を `consistent` で定義し、`Session` の型不変条件で、保持する候補の列がちょうどその集合であることを保つ。
//!
//! ```text
//! C0     = { t | is_init(t) and obs(t) = x0 }
//! Cnext  = { t | exists s in C, args, o: is_edge(s, a, args, o, t) and input(args) = k
//!                and output_matches(r, o) and obs(t) = x }
//! ```
//!
//! 未検証の呼び出し側が受け取る結果の意味は次のとおりである。
//!
//! - `Failure`：入力はどの候補でも有効で、応答と矛盾しない状態が1つもない（不適合）。
//! - `InvalidInput`：入力が無効な候補がある。
//! - `ModelError`：候補の1つで、対象の操作の評価エラーが起きる。
//! - `TooMany`、`ModelViolation`：何も主張しない。候補は変わらない。
//! - `common_inputs` が返す入力は、どの候補でも有効である。
//!
//! 候補の列は辞書順に整列し、重複を持たない。整列と重複の排除は候補数の上限の判定にだけ効き、
//! 集合としての正しさは整列に依存しない。

use crate::checked::CheckedModel;
use crate::eval::*;
use crate::model::*;
use crate::semantics::*;
#[cfg(verus_keep_ghost)]
use crate::semantics::{act_on, is_edge, stuck};
#[cfg(verus_keep_ghost)]
use crate::state_enc::args_ok;
use crate::state_enc::{copy_vec, vec_eq};
use crate::state_set::cmp_state;
#[cfg(verus_keep_ghost)]
use crate::state_set::in_cert;
use crate::step::*;
#[cfg(verus_keep_ghost)]
use crate::step::{all_disabled, enum_ok, lemma_enum_enabled, tr_sound};
use std::sync::Arc;
use vstd::prelude::*;

verus! {

/// 実装から得た値。モデルの型の符号にできない値（型の違う値、範囲外の整数、未定義のラベル）は、
/// モデルのどの値とも一致しない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seen {
    Value(i64),
    Unrepresentable,
}

/// 実装の戻り値。出力を宣言しない操作では比較しない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeenOutput {
    Unchecked,
    Returned(Seen),
}

// ---- 応答との一致 ----

/// 観測 `seen` は、状態 `s` の観測するスロット `obs` の値と一致する。
pub open spec fn agrees(obs: Seq<usize>, s: Seq<i64>, seen: Seq<Seen>) -> bool {
    &&& seen.len() == obs.len()
    &&& forall|j: int|
        0 <= j < obs.len() ==> (#[trigger] obs[j] as int) < s.len() && seen[j] == Seen::Value(s[obs[j] as int])
}

/// 実装の戻り値が、モデルの出力 `o` と一致する。
pub open spec fn output_matches(out: SeenOutput, o: Option<i64>) -> bool {
    match out {
        SeenOutput::Unchecked => true,
        SeenOutput::Returned(y) => o matches Some(x) && y == Seen::Value(x),
    }
}

/// 操作 `a` の注入する選択の添字。
pub open spec fn inj_of(inj: Seq<Vec<usize>>, a: int) -> Seq<usize> {
    if 0 <= a < inj.len() {
        inj[a]@
    } else {
        Seq::empty()
    }
}

/// 引数の列から、注入する選択の値を取り出す。範囲外の添字は読み飛ばす。
pub open spec fn picked(inj: Seq<usize>, args: Seq<i64>) -> Seq<i64>
    decreases inj.len(),
{
    if inj.len() == 0 {
        Seq::empty()
    } else {
        let rest = picked(inj.drop_last(), args);
        if (inj.last() as int) < args.len() {
            rest.push(args[inj.last() as int])
        } else {
            rest
        }
    }
}

/// 操作 `a` の引数の列 `args` に対応する入力。公開引数に、注入する選択の値を続けた列。
pub open spec fn input_of(m: RawModel, inj: Seq<Vec<usize>>, a: int, args: Seq<i64>) -> Seq<i64> {
    let np = m.actions@[a].n_params as int;
    let n = if np < args.len() {
        np
    } else {
        args.len() as int
    };
    args.take(n) + picked(inj_of(inj, a), args)
}

/// 状態 `s` で、入力 `(a, x)` の有効な遷移がある。
pub open spec fn accepts(m: RawModel, c: Conditions, inj: Seq<Vec<usize>>, s: Seq<i64>, a: int, x: Seq<i64>) -> bool {
    exists|args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
        #[trigger] is_edge(m, c, s, a, args, o, t) && input_of(m, inj, a, args) == x
}

/// `s` から `t` への遷移で、入力 `(a, x)` に対する実装の応答（戻り値 `out`、観測 `seen`）を説明できる。
pub open spec fn explains(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    s: Seq<i64>,
    a: int,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
    t: Seq<i64>,
) -> bool {
    exists|args: Seq<i64>, o: Option<i64>|
        #[trigger] is_edge(m, c, s, a, args, o, t) && input_of(m, inj, a, args) == x && output_matches(out, o)
            && agrees(obs, t, seen)
}

/// 1回の応答。操作、入力、戻り値、観測。
pub type Answer = (usize, Seq<i64>, SeenOutput, Seq<Seen>);

/// `t` は、初期観測 `first` と応答の列 `hist` のすべてと矛盾しない状態である。
pub open spec fn consistent(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    first: Seq<Seen>,
    hist: Seq<Answer>,
    t: Seq<i64>,
) -> bool
    decreases hist.len(),
{
    if hist.len() == 0 {
        is_init(m, t) && agrees(obs, t, first)
    } else {
        let r = hist.last();
        exists|s: Seq<i64>|
            consistent(m, c, obs, inj, first, hist.drop_last(), s) && #[trigger] explains(
                m,
                c,
                obs,
                inj,
                s,
                r.0 as int,
                r.1,
                r.2,
                r.3,
                t,
            )
    }
}

/// 応答と矛盾しない状態は、応答の数と同じ回数の遷移で初期状態から到達できる。
pub proof fn lemma_consistent_reach(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    first: Seq<Seen>,
    hist: Seq<Answer>,
    t: Seq<i64>,
)
    requires
        consistent(m, c, obs, inj, first, hist, t),
    ensures
        reach(m, c, t, hist.len() as nat),
    decreases hist.len(),
{
    if hist.len() > 0 {
        let r = hist.last();
        let s = choose|s: Seq<i64>|
            consistent(m, c, obs, inj, first, hist.drop_last(), s) && #[trigger] explains(
                m,
                c,
                obs,
                inj,
                s,
                r.0 as int,
                r.1,
                r.2,
                r.3,
                t,
            );
        lemma_consistent_reach(m, c, obs, inj, first, hist.drop_last(), s);
        let (args, o) = choose|args: Seq<i64>, o: Option<i64>|
            #[trigger] is_edge(m, c, s, r.0 as int, args, o, t) && input_of(m, inj, r.0 as int, args) == r.1
                && output_matches(r.2, o) && agrees(obs, t, r.3);
        assert(is_edge(m, c, s, r.0 as int, args, o, t));
    }
}

/// 候補の状態 `e.state` で、対象の操作 `e.action` を引数 `e.args` で適用すると、評価エラーが起きる。
pub struct ModelError {
    pub state: Vec<i64>,
    pub action: usize,
    pub args: Vec<i64>,
    pub site: Site,
    pub kind: ErrKind,
}

pub open spec fn model_error_at(m: RawModel, c: Conditions, e: ModelError) -> bool {
    &&& act_on(m, c, e.action as int)
    &&& args_ok(m, e.action as int, e.args@)
    &&& step_spec(m, e.action as int, e.args@, e.state@) == Step::Fail(e.site, e.kind)
}

// ---- 実行 ----

fn agrees_exec(obs: &Vec<usize>, s: &Vec<i64>, seen: &Vec<Seen>) -> (r: bool)
    ensures
        r == agrees(obs@, s@, seen@),
{
    if seen.len() != obs.len() {
        return false;
    }
    let mut j: usize = 0;
    while j < obs.len()
        invariant
            seen@.len() == obs@.len(),
            j <= obs@.len(),
            forall|k: int|
                0 <= k < j ==> (#[trigger] obs@[k] as int) < s@.len() && seen@[k] == Seen::Value(s@[obs@[k] as int]),
        decreases obs@.len() - j,
    {
        let var = obs[j];
        if var >= s.len() {
            return false;
        }
        match seen[j] {
            Seen::Value(x) => if x != s[var] {
                return false;
            },
            Seen::Unrepresentable => {
                return false;
            },
        }
        j = j + 1;
    }
    true
}

fn output_matches_exec(out: SeenOutput, o: Option<i64>) -> (r: bool)
    ensures
        r == output_matches(out, o),
{
    match (out, o) {
        (SeenOutput::Unchecked, _) => true,
        (SeenOutput::Returned(Seen::Value(y)), Some(x)) => x == y,
        _ => false,
    }
}

/// 操作 `a` の引数の列 `args` に対応する入力。
pub(crate) fn input_of_exec(m: &RawModel, inj: &Vec<Vec<usize>>, a: usize, args: &Vec<i64>) -> (r: Vec<i64>)
    requires
        a < m.actions@.len(),
    ensures
        r@ == input_of(*m, inj@, a as int, args@),
{
    let np = m.actions[a].n_params;
    let n = if np < args.len() {
        np
    } else {
        args.len()
    };
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n <= args@.len(),
            i <= n,
            r@ =~= args@.take(i as int),
        decreases n - i,
    {
        r.push(args[i]);
        i = i + 1;
        assert(r@ =~= args@.take(i as int));
    }
    let ghost base = r@;
    let ghost ks = inj_of(inj@, a as int);
    if a < inj.len() {
        let ks_exec = &inj[a];
        let mut k: usize = 0;
        while k < ks_exec.len()
            invariant
                ks == ks_exec@,
                k <= ks.len(),
                r@ == base + picked(ks.take(k as int), args@),
            decreases ks.len() - k,
        {
            let ghost before = r@;
            assert(ks.take(k as int + 1).drop_last() =~= ks.take(k as int));
            if ks_exec[k] < args.len() {
                r.push(args[ks_exec[k]]);
                assert(r@ =~= before.push(args@[ks[k as int] as int]));
            }
            k = k + 1;
        }
        assert(ks.take(ks.len() as int) =~= ks);
    } else {
        assert(picked(ks, args@) =~= Seq::<i64>::empty());
        assert(r@ =~= base + picked(ks, args@));
    }
    r
}

/// 状態の列に状態 `t` を加える。列が整列していれば、整列を保ち、すでにあれば加えない。
fn insert_state(v: &mut Vec<Vec<i64>>, t: Vec<i64>)
    ensures
        forall|s: Seq<i64>| #[trigger] in_cert(final(v)@, s) <==> in_cert(old(v)@, s) || s == t@,
{
    let ghost v0 = v@;
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi
        invariant
            v@ == v0,
            lo <= hi <= v@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let c = cmp_state(&v[mid], &t);
        if c == 0 {
            assert(v0[mid as int]@ == t@);
            assert forall|s: Seq<i64>| #[trigger] in_cert(v@, s) <==> in_cert(v0, s) || s == t@ by {
                if s == t@ {
                    assert(v0[mid as int]@ == s);
                }
            }
            return;
        } else if c < 0 {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    let ghost tv = t@;
    v.insert(lo, t);
    assert forall|s: Seq<i64>| #[trigger] in_cert(v@, s) <==> in_cert(v0, s) || s == tv by {
        if in_cert(v@, s) {
            let i = choose|i: int| 0 <= i < v@.len() && (#[trigger] v@[i])@ == s;
            if i < lo {
                assert(v@[i] == v0[i]);
            } else if i > lo {
                assert(v@[i] == v0[i - 1]);
            }
        }
        if in_cert(v0, s) {
            let i = choose|i: int| 0 <= i < v0.len() && (#[trigger] v0[i])@ == s;
            if i < lo {
                assert(v@[i] == v0[i]);
            } else {
                assert(v@[i + 1] == v0[i]);
            }
        }
        if s == tv {
            assert(v@[lo as int]@ == s);
        }
    }
}

/// 状態 `s` で、対象の操作を定義順に列挙し、操作 `want` の遷移を返す。
/// どれかの対象の操作で評価エラーが起きれば、最初のものを返す。
fn transitions_of(m: &RawModel, c: &Conditions, s: &Vec<i64>, want: usize) -> (r: Result<Vec<Transition>, ModelError>)
    ensures
        match r {
            Ok(ts) => (act_on(*m, *c, want as int) ==> enum_ok(*m, want as int, s@, ts@)) && (!act_on(
                *m,
                *c,
                want as int,
            ) ==> ts@.len() == 0),
            Err(e) => e.state@ == s@ && model_error_at(*m, *c, e),
        },
{
    let mut found: Vec<Transition> = Vec::new();
    let mut a: usize = 0;
    while a < m.actions.len()
        invariant
            a <= m.actions@.len(),
            (want < a && act_on(*m, *c, want as int)) ==> enum_ok(*m, want as int, s@, found@),
            !(want < a && act_on(*m, *c, want as int)) ==> found@.len() == 0,
        decreases m.actions@.len() - a,
    {
        if act_on_exec(m, c, a) {
            match enumerate(m, a, s) {
                Enumerated::Fail(args, site, kind) => {
                    return Err(ModelError { state: copy_vec(s), action: a, args, site, kind });
                },
                Enumerated::Ok(ts) => {
                    if a == want {
                        found = ts;
                    }
                },
            }
        }
        a = a + 1;
    }
    Ok(found)
}

/// 候補 `cands` の先頭 `n` 個のどれでも、入力 `(a, x)` が有効である。
pub open spec fn accepted_by(
    m: RawModel,
    c: Conditions,
    inj: Seq<Vec<usize>>,
    cands: Seq<Vec<i64>>,
    n: int,
    a: int,
    x: Seq<i64>,
) -> bool {
    forall|p: int| 0 <= p < n ==> accepts(m, c, inj, #[trigger] cands[p]@, a, x)
}

/// 遷移 `tr` の遷移先 `t` は、入力 `(a, x)` に対する応答と一致する。
pub open spec fn fits(
    m: RawModel,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    a: int,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
    tr: Transition,
    t: Seq<i64>,
) -> bool {
    tr.state@ == t && input_of(m, inj, a, tr.args@) == x && output_matches(out, tr.output) && agrees(obs, t, seen)
}

/// 候補 `cands` の先頭 `n` 個のどれかからの遷移で、応答を説明できる。
pub open spec fn explained(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    cands: Seq<Vec<i64>>,
    n: int,
    a: int,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
    t: Seq<i64>,
) -> bool {
    exists|p: int| 0 <= p < n && #[trigger] explains(m, c, obs, inj, cands[p]@, a, x, out, seen, t)
}

/// 初期状態の列 `inits` の先頭 `n` 個のどれかが `t` で、観測と一致する。
spec fn seeded(inits: Seq<Vec<i64>>, obs: Seq<usize>, seen: Seq<Seen>, n: int, t: Seq<i64>) -> bool {
    exists|j: int| 0 <= j < n && (#[trigger] inits[j])@ == t && agrees(obs, t, seen)
}

/// 候補の列がちょうど遷移の列挙と一致することの補題。`ts` の遷移のどれかで説明できることと、
/// `s` からの遷移で説明できることは同値である。
proof fn lemma_fits_explains(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    s: Seq<i64>,
    a: int,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
    ts: Seq<Transition>,
    t: Seq<i64>,
)
    requires
        act_on(m, c, a) ==> enum_ok(m, a, s, ts),
        !act_on(m, c, a) ==> ts.len() == 0,
    ensures
        (exists|q: int| 0 <= q < ts.len() && fits(m, obs, inj, a, x, out, seen, #[trigger] ts[q], t)) <==> explains(
            m,
            c,
            obs,
            inj,
            s,
            a,
            x,
            out,
            seen,
            t,
        ),
{
    if exists|q: int| 0 <= q < ts.len() && fits(m, obs, inj, a, x, out, seen, #[trigger] ts[q], t) {
        let q = choose|q: int| 0 <= q < ts.len() && fits(m, obs, inj, a, x, out, seen, #[trigger] ts[q], t);
        assert(tr_sound(m, a, s, ts[q]));
        assert(is_edge(m, c, s, a, ts[q].args@, ts[q].output, t));
    }
    if explains(m, c, obs, inj, s, a, x, out, seen, t) {
        let (args, o) = choose|args: Seq<i64>, o: Option<i64>|
            #[trigger] is_edge(m, c, s, a, args, o, t) && input_of(m, inj, a, args) == x && output_matches(out, o)
                && agrees(obs, t, seen);
        assert(covered(m, a, s, ts, args));
        let q = choose|q: int| 0 <= q < ts.len() && (#[trigger] ts[q]).args@ == args;
        assert(tr_sound(m, a, s, ts[q]));
        assert(fits(m, obs, inj, a, x, out, seen, ts[q], t));
    }
}

/// 状態 `s` からの操作 `a` の遷移の遷移先 `t` で、不変条件（`inv` が真）または遷移契約 `k` が真に評価されない。
pub open spec fn violation_at(m: RawModel, c: Conditions, s: Seq<i64>, a: int, inv: bool, k: int, t: Seq<i64>) -> bool {
    if inv {
        inv_on(m, c, k) && not_true(inv_spec(m, k, t))
    } else {
        exists|args: Seq<i64>, o: Option<i64>|
            #[trigger] is_edge(m, c, s, a, args, o, t) && con_on(m, c, k) && m.contracts@[k].action == a && not_true(
                con_spec(m, k, s, args, t, o),
            )
    }
}

/// `absorb` の結果。
enum Absorbed {
    /// 入力の遷移があった。
    Enabled,
    /// 入力の遷移がない。
    Disabled,
    /// 候補数が上限を超えた。
    TooMany,
}

/// 状態 `s` からの操作 `a` の遷移 `ts` のうち、入力と応答に一致する遷移の遷移先を `next` に加える。
/// 一致する遷移が対象の性質を破れば、最初のものを `violation` に記録する。
#[verifier::loop_isolation(false)]
fn absorb(
    m: &RawModel,
    c: &Conditions,
    obs: &Vec<usize>,
    inj: &Vec<Vec<usize>>,
    s: &Vec<i64>,
    a: usize,
    ts: &Vec<Transition>,
    input: &Vec<i64>,
    output: SeenOutput,
    seen: &Vec<Seen>,
    max: usize,
    next: &mut Vec<Vec<i64>>,
    violation: &mut Option<(bool, usize, Vec<i64>)>,
) -> (r: Absorbed)
    requires
        act_on(*m, *c, a as int) ==> enum_ok(*m, a as int, s@, ts@),
        !act_on(*m, *c, a as int) ==> ts@.len() == 0,
    ensures
        r is Disabled ==> !accepts(*m, *c, inj@, s@, a as int, input@),
        r is Enabled ==> {
            &&& accepts(*m, *c, inj@, s@, a as int, input@)
            &&& forall|t: Seq<i64>| #[trigger]
                in_cert(final(next)@, t) <==> (in_cert(old(next)@, t) || explains(
                    *m,
                    *c,
                    obs@,
                    inj@,
                    s@,
                    a as int,
                    input@,
                    output,
                    seen@,
                    t,
                ))
            &&& *final(violation) matches Some(v) ==> *final(violation) == *old(violation) || (in_cert(final(next)@, v.2@)
                && violation_at(*m, *c, s@, a as int, v.0, v.1 as int, v.2@))
        },
{
    let ghost x = input@;
    let ghost sn = seen@;
    let ghost next0 = next@;
    let ghost v0 = *violation;
    let mut enabled = false;
    let mut j: usize = 0;
    while j < ts.len()
        invariant
            j <= ts@.len(),
            forall|t: Seq<i64>|
                #![trigger in_cert(next@, t)]
                in_cert(next@, t) <==> (in_cert(next0, t) || exists|q: int|
                    0 <= q < j && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t)),
            enabled ==> accepts(*m, *c, inj@, s@, a as int, x),
            !enabled ==> forall|q: int| 0 <= q < j ==> input_of(*m, inj@, a as int, (#[trigger] ts@[q]).args@) != x,
            *violation matches Some(v) ==> *violation == v0 || (in_cert(next@, v.2@) && violation_at(*m, *c, s@, a as int, v.0, v.1 as int, v.2@)),
        decreases ts@.len() - j,
    {
        let tr = &ts[j];
        let ghost next1 = next@;
        let xin = input_of_exec(m, inj, a, &tr.args);
        if vec_eq(&xin, input) {
            proof {
                assert(tr_sound(*m, a as int, s@, ts@[j as int]));
                assert(is_edge(*m, *c, s@, a as int, tr.args@, tr.output, tr.state@));
            }
            enabled = true;
            if output_matches_exec(output, tr.output) && agrees_exec(obs, &tr.state, seen) {
                if violation.is_none() {
                    match check_contracts(m, c, a, s, &tr.args, &tr.state, &tr.output) {
                        Some((k, _)) => {
                            *violation = Some((false, k, copy_vec(&tr.state)));
                        },
                        None => match check_invariants(m, c, &tr.state) {
                            Some((k, _)) => {
                                *violation = Some((true, k, copy_vec(&tr.state)));
                            },
                            None => {},
                        },
                    }
                }
                insert_state(next, copy_vec(&tr.state));
                assert(fits(*m, obs@, inj@, a as int, x, output, sn, ts@[j as int], tr.state@));
                if next.len() > max {
                    return Absorbed::TooMany;
                }
            }
        }
        proof {
            assert forall|t: Seq<i64>| #[trigger] in_cert(next@, t) <==> (in_cert(next0, t) || exists|q: int|
                0 <= q < j + 1 && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t)) by {
                if exists|q: int| 0 <= q < j + 1 && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t) {
                    let q = choose|q: int| 0 <= q < j + 1 && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t);
                    if q < j {
                        assert(exists|q: int| 0 <= q < j && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t));
                    }
                }
                if in_cert(next1, t) && !in_cert(next0, t) {
                    let q = choose|q: int| 0 <= q < j && fits(*m, obs@, inj@, a as int, x, output, sn, #[trigger] ts@[q], t);
                    assert(0 <= q < j + 1);
                }
            }
        }
        j = j + 1;
    }
    if !enabled {
        proof {
            if accepts(*m, *c, inj@, s@, a as int, x) {
                let (args, o, t) = choose|args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
                    #[trigger] is_edge(*m, *c, s@, a as int, args, o, t) && input_of(*m, inj@, a as int, args) == x;
                assert(covered(*m, a as int, s@, ts@, args));
                let q = choose|q: int| 0 <= q < ts@.len() && (#[trigger] ts@[q]).args@ == args;
                assert(input_of(*m, inj@, a as int, ts@[q].args@) != x);
            }
        }
        return Absorbed::Disabled;
    }
    proof {
        assert forall|t: Seq<i64>| #[trigger] in_cert(next@, t) <==> (in_cert(next0, t) || explains(
            *m,
            *c,
            obs@,
            inj@,
            s@,
            a as int,
            x,
            output,
            sn,
            t,
        )) by {
            lemma_fits_explains(*m, *c, obs@, inj@, s@, a as int, x, output, sn, ts@, t);
        }
    }
    Absorbed::Enabled
}

/// 候補の先頭 `i` 個で説明できる状態の列 `next0` に、`i` 番目の候補で説明できる状態を加えた `next1` は、
/// 先頭 `i + 1` 個で説明できる状態の列である。
proof fn lemma_explained_grows(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    cands: Seq<Vec<i64>>,
    i: int,
    a: int,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
    next0: Seq<Vec<i64>>,
    next1: Seq<Vec<i64>>,
)
    requires
        0 <= i < cands.len(),
        forall|t: Seq<i64>|
            #![trigger in_cert(next0, t)]
            #![trigger explained(m, c, obs, inj, cands, i, a, x, out, seen, t)]
            in_cert(next0, t) <==> explained(m, c, obs, inj, cands, i, a, x, out, seen, t),
        forall|t: Seq<i64>| #[trigger]
            in_cert(next1, t) <==> (in_cert(next0, t) || explains(m, c, obs, inj, cands[i]@, a, x, out, seen, t)),
    ensures
        forall|t: Seq<i64>|
            #![trigger in_cert(next1, t)]
            #![trigger explained(m, c, obs, inj, cands, i + 1, a, x, out, seen, t)]
            in_cert(next1, t) <==> explained(m, c, obs, inj, cands, i + 1, a, x, out, seen, t),
{
    assert forall|t: Seq<i64>| #[trigger] in_cert(next1, t) <==> explained(m, c, obs, inj, cands, i + 1, a, x, out, seen, t) by {
        if explained(m, c, obs, inj, cands, i + 1, a, x, out, seen, t) {
            let p = choose|p: int| 0 <= p < i + 1 && #[trigger] explains(m, c, obs, inj, cands[p]@, a, x, out, seen, t);
            if p < i {
                assert(explained(m, c, obs, inj, cands, i, a, x, out, seen, t));
            }
        }
        if in_cert(next0, t) {
            assert(explained(m, c, obs, inj, cands, i, a, x, out, seen, t));
            let p = choose|p: int| 0 <= p < i && #[trigger] explains(m, c, obs, inj, cands[p]@, a, x, out, seen, t);
            assert(0 <= p < i + 1);
        }
        if explains(m, c, obs, inj, cands[i]@, a, x, out, seen, t) {
            assert(0 <= i < i + 1);
        }
    }
}

/// 候補 `cands` が応答の列 `hist` と矛盾しない状態の集合で、`next` が候補のどれかからの遷移で説明できる
/// 状態の集合なら、`next` は応答 `(a, x, out, seen)` を加えた列と矛盾しない状態の集合である。
proof fn lemma_next_exact(
    m: RawModel,
    c: Conditions,
    obs: Seq<usize>,
    inj: Seq<Vec<usize>>,
    first: Seq<Seen>,
    hist: Seq<Answer>,
    cands: Seq<Vec<i64>>,
    next: Seq<Vec<i64>>,
    a: usize,
    x: Seq<i64>,
    out: SeenOutput,
    seen: Seq<Seen>,
)
    requires
        forall|t: Seq<i64>|
            #![trigger in_cert(cands, t)]
            #![trigger consistent(m, c, obs, inj, first, hist, t)]
            in_cert(cands, t) <==> consistent(m, c, obs, inj, first, hist, t),
        forall|t: Seq<i64>|
            #![trigger in_cert(next, t)]
            #![trigger explained(m, c, obs, inj, cands, cands.len() as int, a as int, x, out, seen, t)]
            in_cert(next, t) <==> explained(m, c, obs, inj, cands, cands.len() as int, a as int, x, out, seen, t),
    ensures
        forall|t: Seq<i64>|
            #![trigger in_cert(next, t)]
            #![trigger consistent(m, c, obs, inj, first, hist.push((a, x, out, seen)), t)]
            in_cert(next, t) <==> consistent(m, c, obs, inj, first, hist.push((a, x, out, seen)), t),
{
    let h1 = hist.push((a, x, out, seen));
    assert(h1.drop_last() =~= hist);
    assert(h1.len() > 0 && h1.last() == (a, x, out, seen));
    assert forall|t: Seq<i64>| #[trigger] in_cert(next, t) <==> consistent(m, c, obs, inj, first, h1, t) by {
        if in_cert(next, t) {
            assert(explained(m, c, obs, inj, cands, cands.len() as int, a as int, x, out, seen, t));
            let p = choose|p: int| 0 <= p < cands.len() && #[trigger] explains(m, c, obs, inj, cands[p]@, a as int, x, out, seen, t);
            let s = cands[p]@;
            assert(in_cert(cands, s));
            assert(consistent(m, c, obs, inj, first, h1.drop_last(), s));
            assert(explains(m, c, obs, inj, s, h1.last().0 as int, h1.last().1, h1.last().2, h1.last().3, t));
            assert(consistent(m, c, obs, inj, first, h1, t));
        }
        if consistent(m, c, obs, inj, first, h1, t) {
            let s = choose|s: Seq<i64>|
                consistent(m, c, obs, inj, first, h1.drop_last(), s) && #[trigger] explains(m, c, obs, inj, s, a as int, x, out, seen, t);
            assert(in_cert(cands, s));
            let p = choose|p: int| 0 <= p < cands.len() && (#[trigger] cands[p])@ == s;
            assert(explains(m, c, obs, inj, cands[p]@, a as int, x, out, seen, t));
            assert(explained(m, c, obs, inj, cands, cands.len() as int, a as int, x, out, seen, t));
        }
    }
}

// ---- セッション ----

/// 1ケース分の候補集合。`start` だけが構築する。
pub struct Session {
    model: Arc<CheckedModel>,
    cond: Conditions,
    /// 観測するスロットの添字。
    observed: Vec<usize>,
    /// 操作ごとの、注入する選択。引数の列（公開引数に続けて内部選択）の添字。
    injected: Vec<Vec<usize>>,
    max: usize,
    cands: Candidates,
    /// 初期観測。証明でだけ読む。
    #[allow(dead_code)]
    first: Ghost<Seq<Seen>>,
}

/// 候補と、それを絞り込んだ応答の列。2つは同時に更新する。
struct Candidates {
    /// 候補。辞書順に整列し、重複を持たない。
    states: Vec<Vec<i64>>,
    /// 候補を絞り込んだ応答の列。証明でだけ読む。
    #[allow(dead_code)]
    hist: Ghost<Seq<Answer>>,
}

/// `start` の結果。
pub enum Begun {
    Started(Session),
    /// 初期観測と一致する初期状態がない。
    Failure,
    /// 候補数が上限を超えた。
    TooMany,
}

/// `observe` の結果。
pub enum ObserveOutcome {
    /// 候補が残った。
    Continue,
    /// 入力はどの候補でも有効で、応答と矛盾しない状態がない。
    Failure,
    /// 入力が、ある候補で無効である。
    InvalidInput,
    /// 候補数が上限を超えた。
    TooMany,
    ModelError(ModelError),
    /// 残った候補への遷移が、モデルの不変条件（`true`）または遷移契約（`false`）を満たさない。
    /// 添字と、遷移後の状態を持つ。
    ModelViolation(bool, usize, Vec<i64>),
}

impl Session {
    /// 候補の列は、応答と矛盾しない状態の集合とちょうど一致し、空でない。
    #[verifier::type_invariant]
    spec fn exact(self) -> bool {
        &&& self.cands.states@.len() > 0
        &&& forall|t: Seq<i64>|
            #![trigger in_cert(self.cands.states@, t)]
            #![trigger consistent((*self.model)@, self.cond, self.observed@, self.injected@, self.first@, self.cands.hist@, t)]
            in_cert(self.cands.states@, t) <==> consistent(
                (*self.model)@,
                self.cond,
                self.observed@,
                self.injected@,
                self.first@,
                self.cands.hist@,
                t,
            )
    }

    pub closed spec fn spec_model(self) -> RawModel {
        (*self.model)@
    }

    pub closed spec fn spec_cond(self) -> Conditions {
        self.cond
    }

    pub closed spec fn spec_observed(self) -> Seq<usize> {
        self.observed@
    }

    pub closed spec fn spec_injected(self) -> Seq<Vec<usize>> {
        self.injected@
    }

    pub closed spec fn first(self) -> Seq<Seen> {
        self.first@
    }

    pub closed spec fn history(self) -> Seq<Answer> {
        self.cands.hist@
    }

    /// `t` は、これまでの応答のすべてと矛盾しない。
    pub open spec fn possible(self, t: Seq<i64>) -> bool {
        consistent(
            self.spec_model(),
            self.spec_cond(),
            self.spec_observed(),
            self.spec_injected(),
            self.first(),
            self.history(),
            t,
        )
    }

    /// `t` は、これまでの応答と、入力 `(a, x)` に対する応答 `(out, seen)` のすべてと矛盾しない。
    pub open spec fn possible_after(self, a: usize, x: Seq<i64>, out: SeenOutput, seen: Seq<Seen>, t: Seq<i64>) -> bool {
        consistent(
            self.spec_model(),
            self.spec_cond(),
            self.spec_observed(),
            self.spec_injected(),
            self.first(),
            self.history().push((a, x, out, seen)),
            t,
        )
    }

    /// 初期観測から候補集合を作る。
    pub fn start(
        model: Arc<CheckedModel>,
        cond: Conditions,
        observed: Vec<usize>,
        injected: Vec<Vec<usize>>,
        max: usize,
        seen: &Vec<Seen>,
    ) -> (r: Begun)
        ensures
            match r {
                Begun::Started(s) => {
                    &&& s.spec_model() == (*model)@
                    &&& s.spec_cond() == cond
                    &&& s.spec_observed() == observed@
                    &&& s.spec_injected() == injected@
                    &&& s.first() == seen@
                    &&& s.history() == Seq::<Answer>::empty()
                },
                Begun::Failure => forall|t: Seq<i64>| !(is_init((*model)@, t) && agrees(observed@, t, seen@)),
                Begun::TooMany => true,
            },
    {
        let cm: &CheckedModel = &model;
        let inits = cm.initials();
        let ghost m = cm@;
        let mut cands: Vec<Vec<i64>> = Vec::new();
        let mut i: usize = 0;
        while i < inits.len()
            invariant
                *inits == m.inits,
                i <= inits@.len(),
                forall|t: Seq<i64>|
                    #![trigger in_cert(cands@, t)]
                    #![trigger seeded(inits@, observed@, seen@, i as int, t)]
                    in_cert(cands@, t) <==> seeded(inits@, observed@, seen@, i as int, t),
            decreases inits@.len() - i,
        {
            let ghost before = cands@;
            let ok = agrees_exec(&observed, &inits[i], seen);
            if ok {
                insert_state(&mut cands, copy_vec(&inits[i]));
                if cands.len() > max {
                    return Begun::TooMany;
                }
            }
            assert forall|t: Seq<i64>| #[trigger] in_cert(cands@, t) <==> seeded(inits@, observed@, seen@, i + 1, t) by {
                if seeded(inits@, observed@, seen@, i + 1, t) {
                    let j = choose|j: int| 0 <= j < i + 1 && (#[trigger] inits@[j])@ == t && agrees(observed@, t, seen@);
                    if j < i {
                        assert(seeded(inits@, observed@, seen@, i as int, t));
                        assert(in_cert(before, t));
                    }
                }
                if in_cert(before, t) {
                    assert(seeded(inits@, observed@, seen@, i as int, t));
                    let j = choose|j: int| 0 <= j < i && (#[trigger] inits@[j])@ == t && agrees(observed@, t, seen@);
                    assert(0 <= j < i + 1 && inits@[j]@ == t);
                }
                if ok && t == inits@[i as int]@ {
                    assert(0 <= i < i + 1 && inits@[i as int]@ == t);
                }
            }
            i = i + 1;
        }
        let ghost hist = Seq::<Answer>::empty();
        assert forall|t: Seq<i64>| #[trigger] in_cert(cands@, t) <==> consistent(m, cond, observed@, injected@, seen@, hist, t) by {
            if is_init(m, t) && agrees(observed@, t, seen@) {
                let j = choose|j: int| 0 <= j < m.inits@.len() && (#[trigger] m.inits@[j])@ == t;
                assert(inits@[j]@ == t);
                assert(seeded(inits@, observed@, seen@, inits@.len() as int, t));
            }
            if in_cert(cands@, t) {
                assert(seeded(inits@, observed@, seen@, inits@.len() as int, t));
                let j = choose|j: int| 0 <= j < inits@.len() && (#[trigger] inits@[j])@ == t && agrees(observed@, t, seen@);
                assert(m.inits@[j]@ == t);
            }
        }
        if cands.len() == 0 {
            assert forall|t: Seq<i64>| !(is_init(m, t) && agrees(observed@, t, seen@)) by {
                assert(!in_cert(cands@, t));
            }
            return Begun::Failure;
        }
        Begun::Started(Session { model, cond, observed, injected, max, cands: Candidates { states: cands, hist: Ghost(hist) }, first: Ghost(seen@) })
    }

    /// 候補の状態。辞書順に並ぶ。応答と矛盾しない状態の集合とちょうど一致し、空でない。
    pub fn candidates(&self) -> (r: &Vec<Vec<i64>>)
        ensures
            r@.len() > 0,
            forall|t: Seq<i64>| #[trigger] in_cert(r@, t) <==> self.possible(t),
    {
        proof {
            use_type_invariant(self);
        }
        &self.cands.states
    }

    pub fn model(&self) -> (r: &CheckedModel)
        ensures
            r@ == self.spec_model(),
    {
        &self.model
    }

    /// 全候補で有効な入力と、有効な入力を持つ候補があるかどうか。
    /// 入力の順は、辞書順で最初の候補での操作の定義順である。
    #[verifier::loop_isolation(false)]
    pub fn common_inputs(&self) -> (r: Result<(Vec<(usize, Vec<i64>)>, bool), ModelError>)
        ensures
            match r {
                Ok((common, any)) => {
                    &&& forall|k: int, s: Seq<i64>|
                        0 <= k < common@.len() && #[trigger] self.possible(s) ==> accepts(
                            self.spec_model(),
                            self.spec_cond(),
                            self.spec_injected(),
                            s,
                            (#[trigger] common@[k]).0 as int,
                            common@[k].1@,
                        )
                    &&& !any ==> forall|s: Seq<i64>| #[trigger] self.possible(s) ==> stuck(self.spec_model(), self.spec_cond(), s)
                },
                Err(e) => self.possible(e.state@) && model_error_at(self.spec_model(), self.spec_cond(), e),
            },
    {
        proof {
            use_type_invariant(self);
        }
        let cm: &CheckedModel = &self.model;
        let m = cm.raw();
        let ghost gm = *m;
        let cands = &self.cands.states;
        assert(in_cert(cands@, cands@[0]@));
        let mut common = match inputs_at(m, &self.cond, &self.injected, &cands[0]) {
            Ok(l) => l,
            Err(e) => {
                return Err(e);
            },
        };
        let mut any = common.len() > 0;
        let mut i: usize = 1;
        while i < cands.len()
            invariant
                gm == self.spec_model(),
                1 <= i <= cands@.len(),
                forall|k: int|
                    0 <= k < common@.len() ==> accepted_by(
                        gm,
                        self.cond,
                        self.injected@,
                        cands@,
                        i as int,
                        (#[trigger] common@[k]).0 as int,
                        common@[k].1@,
                    ),
                !any ==> forall|p: int| 0 <= p < i ==> stuck(gm, self.cond, #[trigger] cands@[p]@),
            decreases cands@.len() - i,
        {
            assert(in_cert(cands@, cands@[i as int]@));
            let l = match inputs_at(m, &self.cond, &self.injected, &cands[i]) {
                Ok(l) => l,
                Err(e) => {
                    return Err(e);
                },
            };
            any = any || l.len() > 0;
            let mut kept: Vec<(usize, Vec<i64>)> = Vec::new();
            let mut k: usize = 0;
            while k < common.len()
                invariant
                    i < cands@.len(),
                    k <= common@.len(),
                    forall|q: int|
                        0 <= q < common@.len() ==> accepted_by(
                            gm,
                            self.cond,
                            self.injected@,
                            cands@,
                            i as int,
                            (#[trigger] common@[q]).0 as int,
                            common@[q].1@,
                        ),
                    forall|q: int|
                        0 <= q < kept@.len() ==> accepted_by(
                            gm,
                            self.cond,
                            self.injected@,
                            cands@,
                            i + 1,
                            (#[trigger] kept@[q]).0 as int,
                            kept@[q].1@,
                        ),
                decreases common@.len() - k,
            {
                let a = common[k].0;
                if has_input(&l, a, &common[k].1) {
                    let x = copy_vec(&common[k].1);
                    proof {
                        let ghost e = common@[k as int];
                        assert(accepted_by(gm, self.cond, self.injected@, cands@, i as int, e.0 as int, e.1@));
                        let w = choose|w: int| 0 <= w < l@.len() && (#[trigger] l@[w]).0 == a && l@[w].1@ == x@;
                        assert(accepts(gm, self.cond, self.injected@, cands@[i as int]@, l@[w].0 as int, l@[w].1@));
                        assert forall|p: int| 0 <= p < i + 1 implies accepts(
                            gm,
                            self.cond,
                            self.injected@,
                            #[trigger] cands@[p]@,
                            a as int,
                            x@,
                        ) by {
                            if p < i {
                                assert(accepts(gm, self.cond, self.injected@, cands@[p]@, e.0 as int, e.1@));
                            }
                        }
                    }
                    kept.push((a, x));
                }
                k = k + 1;
            }
            common = kept;
            i = i + 1;
        }
        proof {
            assert forall|k: int, s: Seq<i64>|
                0 <= k < common@.len() && #[trigger] self.possible(s) implies accepts(
                gm,
                self.cond,
                self.injected@,
                s,
                (#[trigger] common@[k]).0 as int,
                common@[k].1@,
            ) by {
                assert(in_cert(cands@, s));
                let p = choose|p: int| 0 <= p < cands@.len() && (#[trigger] cands@[p])@ == s;
                assert(accepted_by(gm, self.cond, self.injected@, cands@, cands@.len() as int, common@[k].0 as int, common@[k].1@));
            }
            if !any {
                assert forall|s: Seq<i64>| #[trigger] self.possible(s) implies stuck(gm, self.cond, s) by {
                    assert(in_cert(cands@, s));
                    let p = choose|p: int| 0 <= p < cands@.len() && (#[trigger] cands@[p])@ == s;
                }
            }
        }
        Ok((common, any))
    }

    /// 入力 `(a, x)` が全候補で有効かどうか。
    pub fn check_input(&self, a: usize, x: &Vec<i64>) -> (r: Result<bool, ModelError>)
        ensures
            match r {
                Ok(valid) => valid ==> forall|s: Seq<i64>| #[trigger] self.possible(s) ==> accepts(
                    self.spec_model(),
                    self.spec_cond(),
                    self.spec_injected(),
                    s,
                    a as int,
                    x@,
                ),
                Err(e) => self.possible(e.state@) && model_error_at(self.spec_model(), self.spec_cond(), e),
            },
    {
        match self.common_inputs() {
            Err(e) => Err(e),
            Ok((common, _)) => {
                let valid = has_input(&common, a, x);
                proof {
                    if valid {
                        let k = choose|k: int| 0 <= k < common@.len() && (#[trigger] common@[k]).0 == a && common@[k].1@ == x@;
                        assert forall|s: Seq<i64>| #[trigger] self.possible(s) implies accepts(
                            self.spec_model(),
                            self.spec_cond(),
                            self.spec_injected(),
                            s,
                            a as int,
                            x@,
                        ) by {
                            assert(0 <= k < common@.len() && self.possible(s));
                        }
                    }
                }
                Ok(valid)
            },
        }
    }

    /// 実装の応答（入力 `(action, input)` に対する戻り値 `output` と観測 `seen`）で候補集合を更新する。
    /// 候補を更新するのは `Continue` のときだけで、それ以外では何も変えない。
    #[verifier::loop_isolation(false)]
    pub fn observe(&mut self, action: usize, input: &Vec<i64>, output: SeenOutput, seen: &Vec<Seen>) -> (r: ObserveOutcome)
        ensures
            final(self).spec_model() == old(self).spec_model(),
            final(self).spec_cond() == old(self).spec_cond(),
            final(self).spec_observed() == old(self).spec_observed(),
            final(self).spec_injected() == old(self).spec_injected(),
            final(self).first() == old(self).first(),
            r is Continue ==> final(self).history() == old(self).history().push((action, input@, output, seen@)),
            !(r is Continue) ==> *final(self) == *old(self),
            r is Failure ==> {
                &&& forall|s: Seq<i64>| #[trigger] old(self).possible(s) ==> accepts(
                    old(self).spec_model(),
                    old(self).spec_cond(),
                    old(self).spec_injected(),
                    s,
                    action as int,
                    input@,
                )
                &&& forall|t: Seq<i64>| !(#[trigger] old(self).possible_after(action, input@, output, seen@, t))
            },
            r is InvalidInput ==> exists|s: Seq<i64>| #[trigger] old(self).possible(s) && !accepts(
                old(self).spec_model(),
                old(self).spec_cond(),
                old(self).spec_injected(),
                s,
                action as int,
                input@,
            ),
            r matches ObserveOutcome::ModelViolation(inv, k, st) ==> {
                &&& old(self).possible_after(action, input@, output, seen@, st@)
                &&& exists|s: Seq<i64>| #[trigger] old(self).possible(s) && violation_at(old(self).spec_model(), old(self).spec_cond(), s, action as int, inv, k as int, st@)
            },
            r matches ObserveOutcome::ModelError(e) ==> old(self).possible(e.state@) && model_error_at(
                old(self).spec_model(),
                old(self).spec_cond(),
                e,
            ),
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost s0 = *self;
        let cm: &CheckedModel = &self.model;
        let m = cm.raw();
        let ghost gm = *m;
        let ghost c = self.cond;
        let ghost obs = self.observed@;
        let ghost inj = self.injected@;
        let ghost x = input@;
        let ghost sn = seen@;
        let mut next: Vec<Vec<i64>> = Vec::new();
        let mut violation: Option<(bool, usize, Vec<i64>)> = None;
        let mut i: usize = 0;
        while i < self.cands.states.len()
            invariant
                *self == s0,
                gm == s0.spec_model(),
                i <= self.cands.states@.len(),
                forall|t: Seq<i64>|
                    #![trigger in_cert(next@, t)]
                    #![trigger explained(gm, c, obs, inj, self.cands.states@, i as int, action as int, x, output, sn, t)]
                    in_cert(next@, t) <==> explained(gm, c, obs, inj, self.cands.states@, i as int, action as int, x, output, sn, t),
                accepted_by(gm, c, inj, self.cands.states@, i as int, action as int, x),
                violation matches Some(v) ==> in_cert(next@, v.2@) && exists|p: int| 0 <= p < i && #[trigger] violation_at(gm, c, self.cands.states@[p]@, action as int, v.0, v.1 as int, v.2@),
            decreases self.cands.states@.len() - i,
        {
            let s = &self.cands.states[i];
            assert(in_cert(self.cands.states@, s@));
            let ts = match transitions_of(m, &self.cond, s, action) {
                Ok(ts) => ts,
                Err(e) => {
                    return ObserveOutcome::ModelError(e);
                },
            };
            let ghost next0 = next@;
            let ghost viol0 = violation;
            match absorb(m, &self.cond, &self.observed, &self.injected, s, action, &ts, input, output, seen, self.max, &mut next, &mut violation) {
                Absorbed::TooMany => {
                    return ObserveOutcome::TooMany;
                },
                Absorbed::Disabled => {
                    assert(s0.possible(s@));
                    return ObserveOutcome::InvalidInput;
                },
                Absorbed::Enabled => {},
            }
            proof {
                lemma_explained_grows(gm, c, obs, inj, self.cands.states@, i as int, action as int, x, output, sn, next0, next@);
                if let Some(v) = &violation {
                    if violation == viol0 {
                        let p = choose|p: int| 0 <= p < i && #[trigger] violation_at(gm, c, self.cands.states@[p]@, action as int, v.0, v.1 as int, v.2@);
                        assert(0 <= p < i + 1);
                    } else {
                        assert(violation_at(gm, c, self.cands.states@[i as int]@, action as int, v.0, v.1 as int, v.2@));
                    }
                }
                assert forall|p: int| 0 <= p < i + 1 implies accepts(gm, c, inj, #[trigger] self.cands.states@[p]@, action as int, x) by {
                    if p < i {
                        assert(accepted_by(gm, c, inj, self.cands.states@, i as int, action as int, x));
                    }
                }
            }
            i = i + 1;
        }
        let ghost h1 = s0.cands.hist@.push((action, x, output, sn));
        proof {
            lemma_next_exact(gm, c, obs, inj, s0.first@, s0.cands.hist@, self.cands.states@, next@, action, x, output, sn);
            assert forall|s: Seq<i64>| #[trigger] s0.possible(s) implies accepts(gm, c, inj, s, action as int, x) by {
                assert(in_cert(self.cands.states@, s));
                let p = choose|p: int| 0 <= p < self.cands.states@.len() && (#[trigger] self.cands.states@[p])@ == s;
            }
        }
        if next.len() == 0 {
            proof {
                assert forall|t: Seq<i64>| !(#[trigger] s0.possible_after(action, x, output, sn, t)) by {
                    assert(!in_cert(next@, t));
                }
            }
            return ObserveOutcome::Failure;
        }
        if let Some((invariant, index, state)) = violation {
            proof {
                let p = choose|p: int| 0 <= p < self.cands.states@.len() && #[trigger] violation_at(gm, c, self.cands.states@[p]@, action as int, invariant, index as int, state@);
                assert(in_cert(self.cands.states@, self.cands.states@[p]@));
                assert(s0.possible(self.cands.states@[p]@));
            }
            return ObserveOutcome::ModelViolation(invariant, index, state);
        }
        self.cands = Candidates { states: next, hist: Ghost(h1) };
        ObserveOutcome::Continue
    }
}

/// 入力の列の中に `(a, x)` がある。
pub(crate) fn has_input(l: &Vec<(usize, Vec<i64>)>, a: usize, x: &Vec<i64>) -> (r: bool)
    ensures
        r ==> exists|k: int| 0 <= k < l@.len() && (#[trigger] l@[k]).0 == a && l@[k].1@ == x@,
{
    let mut k: usize = 0;
    while k < l.len()
        invariant
            k <= l@.len(),
        decreases l@.len() - k,
    {
        if l[k].0 == a && vec_eq(&l[k].1, x) {
            assert(l@[k as int].0 == a && l@[k as int].1@ == x@);
            return true;
        }
        k = k + 1;
    }
    false
}

/// 状態 `s` で有効な入力。操作の定義順に並び、同じ入力は1つにまとめる。空なら、`s` に有効な遷移はない。
pub(crate) fn inputs_at(m: &RawModel, c: &Conditions, inj: &Vec<Vec<usize>>, s: &Vec<i64>) -> (r: Result<
    Vec<(usize, Vec<i64>)>,
    ModelError,
>)
    ensures
        match r {
            Ok(l) => (forall|k: int|
                0 <= k < l@.len() ==> accepts(*m, *c, inj@, s@, (#[trigger] l@[k]).0 as int, l@[k].1@)) && (l@.len()
                == 0 ==> stuck(*m, *c, s@)),
            Err(e) => e.state@ == s@ && model_error_at(*m, *c, e),
        },
{
    let mut l: Vec<(usize, Vec<i64>)> = Vec::new();
    let mut a: usize = 0;
    while a < m.actions.len()
        invariant
            a <= m.actions@.len(),
            forall|k: int| 0 <= k < l@.len() ==> accepts(*m, *c, inj@, s@, (#[trigger] l@[k]).0 as int, l@[k].1@),
            l@.len() == 0 ==> forall|b: int| 0 <= b < a && #[trigger] act_on(*m, *c, b) ==> all_disabled(*m, b, s@),
        decreases m.actions@.len() - a,
    {
        if act_on_exec(m, c, a) {
            match enumerate(m, a, s) {
                Enumerated::Fail(args, site, kind) => {
                    return Err(ModelError { state: copy_vec(s), action: a, args, site, kind });
                },
                Enumerated::Ok(ts) => {
                    let ghost l0 = l@;
                    let mut j: usize = 0;
                    while j < ts.len()
                        invariant
                            a < m.actions@.len(),
                            act_on(*m, *c, a as int),
                            enum_ok(*m, a as int, s@, ts@),
                            j <= ts@.len(),
                            forall|k: int|
                                0 <= k < l@.len() ==> accepts(*m, *c, inj@, s@, (#[trigger] l@[k]).0 as int, l@[k].1@),
                            l@.len() >= l0.len(),
                            j > 0 ==> l@.len() > 0,
                        decreases ts@.len() - j,
                    {
                        let tr = &ts[j];
                        let x = input_of_exec(m, inj, a, &tr.args);
                        assert(tr_sound(*m, a as int, s@, ts@[j as int]));
                        assert(is_edge(*m, *c, s@, a as int, tr.args@, tr.output, tr.state@));
                        if !has_input(&l, a, &x) {
                            l.push((a, x));
                        }
                        j = j + 1;
                    }
                    proof {
                        if l@.len() == 0 {
                            lemma_enum_enabled(*m, a as int, s@, ts@);
                        }
                    }
                },
            }
        }
        a = a + 1;
    }
    Ok(l)
}

} // verus!
