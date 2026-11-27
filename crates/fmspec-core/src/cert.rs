//! 安全性証明書の検査器（仕様書 §14.2）。
//!
//! 証明書を受理するのは、状態集合が初期状態を含み、対象の操作の遷移で閉じていて、
//! どの状態でも指定の性質が成立するときである。このとき `safe` が従う
//! （仕様書 §14.1 Certificate Soundness）。
//! 検査器は探索器が記録した辺を使わず、各状態の後続を遷移列挙で再計算する。

use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
use crate::state_set::find;
#[cfg(verus_keep_ghost)]
use crate::state_set::in_cert;
use crate::step::*;
use crate::sym::*;
use vstd::prelude::*;

verus! {

/// 引数 `args` での適用が、評価エラーでなく、有効なら遷移先が証明書に含まれ、契約を満たす。
pub open spec fn trans_closed(
    m: RawModel,
    c: Conditions,
    cert: Seq<Vec<i64>>,
    a: int,
    args: Seq<i64>,
    s: Seq<i64>,
) -> bool {
    match step_spec(m, a, args, s) {
        Step::Disabled => true,
        Step::Fail(_, _) => false,
        Step::To(t, o) => in_cert(cert, t) && cons_hold(m, c, a, s, args, t, o),
    }
}

pub open spec fn act_closed(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, a: int, s: Seq<i64>) -> bool {
    forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) ==> trans_closed(m, c, cert, a, args, s)
}

pub open spec fn state_closed(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    &&& invs_hold(m, c, s)
    &&& forall|a: int| #[trigger] act_on(m, c, a) ==> act_closed(m, c, cert, a, s)
    &&& no_deadlock(m, c, s)
}

/// 証明書が帰納的である。初期状態をすべて含み、どの状態も性質を満たし、遷移で閉じている。
pub open spec fn inductive(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>) -> bool {
    &&& forall|i: int| 0 <= i < m.inits@.len() ==> in_cert(cert, (#[trigger] m.inits@[i])@)
    &&& forall|i: int| 0 <= i < cert.len() ==> state_closed(m, c, cert, (#[trigger] cert[i])@)
}

pub(crate) proof fn lemma_reach_in_cert(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, s: Seq<i64>, n: nat)
    requires
        inductive(m, c, cert),
        reach(m, c, s, n),
    ensures
        in_cert(cert, s),
    decreases n,
{
    if n == 0 {
        let i = choose|i: int| 0 <= i < m.inits@.len() && (#[trigger] m.inits@[i])@ == s;
        assert(in_cert(cert, m.inits@[i]@));
    } else {
        let (p, a, args, o) = choose|p: Seq<i64>, a: int, args: Seq<i64>, o: Option<i64>|
            reach(m, c, p, (n - 1) as nat) && #[trigger] is_edge(m, c, p, a, args, o, s);
        lemma_reach_in_cert(m, c, cert, p, (n - 1) as nat);
        let i = choose|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == p;
        assert(state_closed(m, c, cert, cert[i]@));
        assert(act_closed(m, c, cert, a, p));
        assert(trans_closed(m, c, cert, a, args, p));
    }
}

/// 帰納的な証明書があれば、モデルは安全である。
pub proof fn lemma_inductive_safe(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>)
    requires
        inductive(m, c, cert),
    ensures
        safe(m, c),
{
    assert forall|s: Seq<i64>, n: nat| #[trigger] reach(m, c, s, n) implies state_safe(m, c, s) by {
        lemma_reach_in_cert(m, c, cert, s, n);
        let i = choose|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s;
        assert(state_closed(m, c, cert, cert[i]@));
        assert forall|a: int, args: Seq<i64>| #[trigger]
            act_on(m, c, a) && #[trigger] args_ok(m, a, args) implies trans_safe(m, c, a, args, s) by {
            assert(act_closed(m, c, cert, a, s));
            assert(trans_closed(m, c, cert, a, args, s));
        }
    }
}

// ---- 検査器 ----
//
// 対称性による削減の有無によらず、検査器は1つである。後続の状態の所属を、入れ替えの列 `sw` のもとでの
// 代表元（`reps`）で判定する。`sw` が空なら、代表元は状態そのもので、所属は `in_cert` と同じである
// （`lemma_reps_empty`）。

/// 入れ替えの列が空なら、代表元は状態そのものである。
pub proof fn lemma_reps_empty(cert: Seq<Vec<i64>>, s: Seq<i64>)
    ensures
        reps(Seq::<SwapMaps>::empty(), cert, s) <==> in_cert(cert, s),
{
    let sw = Seq::<SwapMaps>::empty();
    if reps(sw, cert, s) {
        let w = choose|w: Seq<usize>| word_ok(sw, w) && #[trigger] in_cert(cert, apply_word(sw, w, s));
        if w.len() > 0 {
            assert(w[0] < sw.len());
        }
        assert(apply_word(sw, w, s) == s);
    }
    if in_cert(cert, s) {
        let w = Seq::<usize>::empty();
        assert(word_ok(sw, w));
        assert(apply_word(sw, w, s) == s);
        assert(in_cert(cert, apply_word(sw, w, s)));
    }
}

/// 入れ替えのない検査で閉じている状態は、`state_closed` を満たす。
pub proof fn lemma_closed_without_swaps(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, s: Seq<i64>)
    requires
        sym_state_closed(m, c, Seq::empty(), cert, s),
    ensures
        state_closed(m, c, cert, s),
{
    assert forall|a: int| #[trigger] act_on(m, c, a) implies act_closed(m, c, cert, a, s) by {
        assert forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) implies trans_closed(m, c, cert, a, args, s) by {
            match step_spec(m, a, args, s) {
                Step::To(t, _) => {
                    lemma_reps_empty(cert, t);
                },
                _ => {},
            }
        }
    }
}

/// 入れ替えのない検査で帰納的な証明書は、`inductive` を満たす。
pub proof fn lemma_inductive_without_swaps(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>)
    requires
        sym_inductive(m, c, Seq::empty(), cert),
    ensures
        inductive(m, c, cert),
{
    assert forall|i: int| 0 <= i < m.inits@.len() implies in_cert(cert, (#[trigger] m.inits@[i])@) by {
        lemma_reps_empty(cert, m.inits@[i]@);
    }
    assert forall|j: int| 0 <= j < cert.len() implies state_closed(m, c, cert, (#[trigger] cert[j])@) by {
        lemma_closed_without_swaps(m, c, cert, cert[j]@);
    }
}

/// 状態 `t` の代表元が証明書に含まれるかを確かめる。入れ替えがなければ、正規化せずに探す。
fn find_rep(sw: &Vec<SwapMaps>, cert: &Vec<Vec<i64>>, t: &Vec<i64>) -> (r: bool)
    ensures
        r ==> reps(sw@, cert@, t@),
{
    if sw.len() == 0 {
        let found = find(cert, t);
        proof {
            if found {
                let w = Seq::<usize>::empty();
                assert(word_ok(sw@, w));
                assert(apply_word(sw@, w, t@) == t@);
                assert(in_cert(cert@, apply_word(sw@, w, t@)));
            }
        }
        return found;
    }
    let (ct, _w) = canonicalize(sw, t);
    if find(cert, &ct) {
        assert(word_ok(sw@, _w@) && in_cert(cert@, apply_word(sw@, _w@, t@)));
        true
    } else {
        false
    }
}

/// 証明書の `k` 番目の状態 `s` で操作 `a` を検査する。有効な遷移があれば `Ok(true)`。
#[verifier::loop_isolation(false)]
fn check_action(
    m: &RawModel,
    c: &Conditions,
    sw: &Vec<SwapMaps>,
    cert: &Vec<Vec<i64>>,
    k: usize,
    a: usize,
    s: &Vec<i64>,
) -> (r: Result<bool, Reject>)
    requires
        a < m.actions@.len(),
    ensures
        r matches Ok(enabled) ==> (forall|args: Seq<i64>| #[trigger] args_ok(*m, a as int, args) ==> match step_spec(
            *m,
            a as int,
            args,
            s@,
        ) {
            Step::Disabled => true,
            Step::Fail(_, _) => false,
            Step::To(t, o) => cons_hold(*m, *c, a as int, s@, args, t, o) && reps(sw@, cert@, t),
        }) && (enabled <==> !all_disabled(*m, a as int, s@)),
{
    let ghost ai = a as int;
    match enumerate(m, a, s) {
        Enumerated::Fail(_, _, _) => Err(Reject::StepFailed(k, a)),
        Enumerated::Ok(ts) => {
            let mut i: usize = 0;
            while i < ts.len()
                invariant
                    i <= ts@.len(),
                    forall|j: int|
                        0 <= j < i ==> cons_hold(*m, *c, ai, s@, (#[trigger] ts@[j]).args@, ts@[j].state@, ts@[j].output)
                            && reps(sw@, cert@, ts@[j].state@),
                decreases ts@.len() - i,
            {
                let t = &ts[i];
                if !find_rep(sw, cert, &t.state) {
                    return Err(Reject::MissingSuccessor(k, a));
                }
                match check_contracts(m, c, a, s, &t.args, &t.state, &t.output) {
                    Some((con, _)) => {
                        return Err(Reject::ContractNotHeld(k, con));
                    },
                    None => {},
                }
                i = i + 1;
            }
            proof {
                lemma_enum_enabled(*m, ai, s@, ts@);
                assert forall|args: Seq<i64>| #[trigger] args_ok(*m, ai, args) implies match step_spec(*m, ai, args, s@) {
                    Step::Disabled => true,
                    Step::Fail(_, _) => false,
                    Step::To(t, o) => cons_hold(*m, *c, ai, s@, args, t, o) && reps(sw@, cert@, t),
                } by {
                    assert(covered(*m, ai, s@, ts@, args));
                    if step_spec(*m, ai, args, s@) is To {
                        let j = choose|j: int| 0 <= j < ts@.len() && (#[trigger] ts@[j]).args@ == args;
                        assert(tr_sound(*m, ai, s@, ts@[j]));
                    }
                }
            }
            Ok(ts.len() > 0)
        },
    }
}

/// 証明書の `k` 番目の状態を検査する。
#[verifier::loop_isolation(false)]
pub(crate) fn check_state(m: &RawModel, c: &Conditions, sw: &Vec<SwapMaps>, cert: &Vec<Vec<i64>>, k: usize) -> (r: Option<Reject>)
    requires
        k < cert@.len(),
    ensures
        r is None ==> sym_state_closed(*m, *c, sw@, cert@, cert@[k as int]@),
{
    let s = &cert[k];
    if !vals_ok_exec(&m.enums, &m.state_types, s) {
        return Some(Reject::IllTypedState(k));
    }
    match check_invariants(m, c, s) {
        Some((i, _)) => {
            return Some(Reject::InvariantNotHeld(k, i));
        },
        None => {},
    }
    let mut enabled = false;
    let mut a: usize = 0;
    while a < m.actions.len()
        invariant
            a <= m.actions@.len(),
            forall|b: int, args: Seq<i64>|
                0 <= b < a && #[trigger] act_on(*m, *c, b) && #[trigger] args_ok(*m, b, args) ==> match step_spec(
                    *m,
                    b,
                    args,
                    s@,
                ) {
                    Step::Disabled => true,
                    Step::Fail(_, _) => false,
                    Step::To(t, o) => cons_hold(*m, *c, b, s@, args, t, o) && reps(sw@, cert@, t),
                },
            enabled ==> !stuck(*m, *c, s@),
            !enabled ==> forall|b: int| 0 <= b < a && #[trigger] act_on(*m, *c, b) ==> all_disabled(*m, b, s@),
        decreases m.actions@.len() - a,
    {
        if act_on_exec(m, c, a) {
            match check_action(m, c, sw, cert, k, a, s) {
                Err(r) => {
                    return Some(r);
                },
                Ok(en) => {
                    if en {
                        enabled = true;
                        assert(act_on(*m, *c, a as int) && !all_disabled(*m, a as int, s@));
                    }
                },
            }
        }
        a = a + 1;
    }
    if c.deadlock && !enabled {
        match eval_terminal(m, s) {
            Ok(true) => {},
            _ => {
                return Some(Reject::Deadlock(k));
            },
        }
    }
    proof {
        assert forall|b: int, args: Seq<i64>| #[trigger] act_on(*m, *c, b) && #[trigger] args_ok(*m, b, args) implies match step_spec(
            *m,
            b,
            args,
            s@,
        ) {
            Step::Disabled => true,
            Step::Fail(_, _) => false,
            Step::To(t, o) => cons_hold(*m, *c, b, s@, args, t, o) && reps(sw@, cert@, t),
        } by {
            assert(0 <= b < m.actions@.len());
        }
    }
    None
}

/// 証明書が初期状態の代表元をすべて含むことを検査する。
pub(crate) fn check_initials(m: &RawModel, sw: &Vec<SwapMaps>, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> forall|j: int|
            0 <= j < m.inits@.len() ==> (#[trigger] m.inits@[j])@.len() == m.state_types@.len() && reps(sw@, cert@, m.inits@[j]@),
{
    let mut i: usize = 0;
    while i < m.inits.len()
        invariant
            i <= m.inits@.len(),
            forall|j: int|
                0 <= j < i ==> (#[trigger] m.inits@[j])@.len() == m.state_types@.len() && reps(sw@, cert@, m.inits@[j]@),
        decreases m.inits@.len() - i,
    {
        if m.inits[i].len() != m.state_types.len() || !find_rep(sw, cert, &m.inits[i]) {
            return Some(Reject::MissingInitial(i));
        }
        i = i + 1;
    }
    None
}

/// 入れ替えの列 `sw` のもとで、証明書を検査する。`None`（受理）なら、証明書は代表元の証明書として帰納的である。
fn check_with_swaps(m: &RawModel, c: &Conditions, sw: &Vec<SwapMaps>, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> sym_inductive(*m, *c, sw@, cert@),
{
    match check_initials(m, sw, cert) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    let mut k: usize = 0;
    while k < cert.len()
        invariant
            k <= cert@.len(),
            forall|j: int|
                0 <= j < m.inits@.len() ==> (#[trigger] m.inits@[j])@.len() == m.state_types@.len() && reps(sw@, cert@, m.inits@[j]@),
            forall|j: int| 0 <= j < k ==> sym_state_closed(*m, *c, sw@, cert@, (#[trigger] cert@[j])@),
        decreases cert@.len() - k,
    {
        match check_state(m, c, sw, cert, k) {
            Some(r) => {
                return Some(r);
            },
            None => {},
        }
        k = k + 1;
    }
    None
}

/// 安全性証明書を検査する。`None`（受理）を返すなら、証明書は帰納的で、モデルは安全である。
pub fn check_certificate(m: &RawModel, c: &Conditions, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> inductive(*m, *c, cert@) && safe(*m, *c),
{
    let none: Vec<SwapMaps> = Vec::new();
    let r = check_with_swaps(m, c, &none, cert);
    proof {
        if r is None {
            assert(none@ =~= Seq::<SwapMaps>::empty());
            lemma_inductive_without_swaps(*m, *c, cert@);
            lemma_inductive_safe(*m, *c, cert@);
        }
    }
    r
}

/// 代表元の証明書を検査する。入れ替えは、どれも `sym_ok` を満たすものとする。
pub(crate) fn check_sym_certificate(m: &RawModel, c: &Conditions, sw: &Vec<SwapMaps>, cert: &Vec<Vec<i64>>) -> (r: Option<
    Reject,
>)
    requires
        all_sym(*m, *c, sw@),
    ensures
        r is None ==> safe(*m, *c),
{
    let r = check_with_swaps(m, c, sw, cert);
    proof {
        if r is None {
            lemma_sym_safe(*m, *c, sw@, cert@);
        }
    }
    r
}

} // verus!
