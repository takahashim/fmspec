//! 安全性証明書の検査器（仕様書 §14.2）。
//!
//! 証明書を受理するのは、状態集合が初期状態を含み、対象の操作の遷移で閉じていて、
//! どの状態でも指定の性質が成立するときである。このとき `safe` が従う
//! （仕様書 §14.1 Certificate Soundness）。
//! 検査器は探索器が記録した辺を使わず、各状態の後続を遷移列挙で再計算する。

#[allow(unused_imports)]
use crate::eval::*;
use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
use crate::step::*;
use vstd::prelude::*;

verus! {

pub open spec fn in_cert(cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    exists|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s
}

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

proof fn lemma_reach_in_cert(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, s: Seq<i64>, n: nat)
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

// ---- 状態集合の所属判定 ----

/// 符号化列の辞書順の比較。`0` を返すのは、2つの列が等しいときだけである。
fn cmp_state(a: &Vec<i64>, b: &Vec<i64>) -> (r: i8)
    ensures
        r == 0 ==> a@ == b@,
{
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a@.len(),
            i <= b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] < b[i] {
            return -1;
        }
        if a[i] > b[i] {
            return 1;
        }
        i = i + 1;
    }
    if a.len() < b.len() {
        -1
    } else if a.len() > b.len() {
        1
    } else {
        assert(a@ =~= b@);
        0
    }
}

/// 二分探索による所属判定。`true` を返すのは、状態が証明書に含まれるときだけである。
/// 証明書が整列されていなければ、含まれる状態を見落として `false` を返すことがある。
/// その場合は証明書を拒否するだけで、誤って受理することはない（仕様書 §7.3）。
fn find(cert: &Vec<Vec<i64>>, t: &Vec<i64>) -> (r: bool)
    ensures
        r ==> in_cert(cert@, t@),
{
    let mut lo: usize = 0;
    let mut hi: usize = cert.len();
    while lo < hi
        invariant
            lo <= hi <= cert@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let c = cmp_state(&cert[mid], t);
        if c == 0 {
            assert(cert@[mid as int]@ == t@);
            return true;
        } else if c < 0 {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    false
}

// ---- 検査器 ----

spec fn tr_closed(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>, a: int, s: Seq<i64>, t: Transition) -> bool {
    in_cert(cert, t.state@) && cons_hold(m, c, a, s, t.args@, t.state@, t.output)
}

/// 証明書の `k` 番目の状態 `s` で操作 `a` を検査する。有効な遷移があれば `Ok(true)`。
#[verifier::loop_isolation(false)]
fn check_action(m: &RawModel, c: &Conditions, cert: &Vec<Vec<i64>>, k: usize, a: usize, s: &Vec<i64>) -> (r: Result<
    bool,
    Reject,
>)
    requires
        a < m.actions@.len(),
    ensures
        r matches Ok(enabled) ==> act_closed(*m, *c, cert@, a as int, s@) && (enabled <==> !all_disabled(
            *m,
            a as int,
            s@,
        )),
{
    let ghost ai = a as int;
    match enumerate(m, a, s) {
        Enumerated::Fail(_, _, _) => Err(Reject::StepFailed(k, a)),
        Enumerated::Ok(ts) => {
            let mut i: usize = 0;
            while i < ts.len()
                invariant
                    i <= ts@.len(),
                    forall|j: int| 0 <= j < i ==> tr_closed(*m, *c, cert@, ai, s@, #[trigger] ts@[j]),
                decreases ts@.len() - i,
            {
                let t = &ts[i];
                if !find(cert, &t.state) {
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
                assert forall|args: Seq<i64>| #[trigger] args_ok(*m, ai, args) implies trans_closed(
                    *m,
                    *c,
                    cert@,
                    ai,
                    args,
                    s@,
                ) by {
                    assert(covered(*m, ai, s@, ts@, args));
                    if step_spec(*m, ai, args, s@) is To {
                        let j = choose|j: int| 0 <= j < ts@.len() && (#[trigger] ts@[j]).args@ == args;
                        assert(tr_sound(*m, ai, s@, ts@[j]));
                        assert(tr_closed(*m, *c, cert@, ai, s@, ts@[j]));
                    }
                }
            }
            Ok(ts.len() > 0)
        },
    }
}

/// 証明書の `k` 番目の状態を検査する。
#[verifier::loop_isolation(false)]
pub(crate) fn check_state(m: &RawModel, c: &Conditions, cert: &Vec<Vec<i64>>, k: usize) -> (r: Option<Reject>)
    requires
        k < cert@.len(),
    ensures
        r is None ==> state_closed(*m, *c, cert@, cert@[k as int]@),
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
            forall|b: int| 0 <= b < a && #[trigger] act_on(*m, *c, b) ==> act_closed(*m, *c, cert@, b, s@),
            enabled ==> !stuck(*m, *c, s@),
            !enabled ==> forall|b: int| 0 <= b < a && #[trigger] act_on(*m, *c, b) ==> all_disabled(*m, b, s@),
        decreases m.actions@.len() - a,
    {
        if act_on_exec(m, c, a) {
            match check_action(m, c, cert, k, a, s) {
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
    None
}

/// 証明書が初期状態をすべて含むことを検査する。
pub(crate) fn check_initials(m: &RawModel, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> forall|j: int| 0 <= j < m.inits@.len() ==> in_cert(cert@, (#[trigger] m.inits@[j])@),
{
    let mut i: usize = 0;
    while i < m.inits.len()
        invariant
            i <= m.inits@.len(),
            forall|j: int| 0 <= j < i ==> in_cert(cert@, (#[trigger] m.inits@[j])@),
        decreases m.inits@.len() - i,
    {
        if !find(cert, &m.inits[i]) {
            return Some(Reject::MissingInitial(i));
        }
        i = i + 1;
    }
    None
}

/// 安全性証明書を検査する。`None`（受理）を返すなら、証明書は帰納的で、モデルは安全である。
pub fn check_certificate(m: &RawModel, c: &Conditions, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> inductive(*m, *c, cert@) && safe(*m, *c),
{
    match check_initials(m, cert) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    let mut k: usize = 0;
    while k < cert.len()
        invariant
            k <= cert@.len(),
            forall|j: int| 0 <= j < k ==> state_closed(*m, *c, cert@, (#[trigger] cert@[j])@),
        decreases cert@.len() - k,
    {
        match check_state(m, c, cert, k) {
            Some(r) => {
                return Some(r);
            },
            None => {},
        }
        k = k + 1;
    }
    proof {
        lemma_inductive_safe(*m, *c, cert@);
    }
    None
}

} // verus!
