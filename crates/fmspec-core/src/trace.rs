//! トレースの検査器。
//!
//! トレースを受理するのは、初期状態から各ステップのラベルと状態がモデルの遷移に一致し、
//! 末尾で主張どおりの事象が起きるときである（仕様書 §14.1 Trace Validity）。
//! 保証は「違反に到達できる」という存在の主張ではなく、表示するトレースそのものについて述べる。

use crate::eval::*;
use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
use crate::step::*;
use vstd::prelude::*;

verus! {

/// `k` ステップ後の状態。`k == 0` は開始状態。
pub open spec fn state_at(start: Seq<i64>, steps: Seq<TraceStep>, k: int) -> Seq<i64> {
    if k <= 0 {
        start
    } else {
        steps[k - 1].state@
    }
}

/// `k` 番目のステップは、直前の状態からの、対象の操作による有効な遷移である。
pub open spec fn step_ok(m: RawModel, c: Conditions, start: Seq<i64>, steps: Seq<TraceStep>, k: int) -> bool {
    let st = steps[k];
    is_edge(m, c, state_at(start, steps, k), st.action as int, st.args@, st.output, st.state@)
}

pub open spec fn trace_ok(m: RawModel, c: Conditions, start: Seq<i64>, steps: Seq<TraceStep>) -> bool {
    forall|k: int| 0 <= k < steps.len() ==> #[trigger] step_ok(m, c, start, steps, k)
}

/// 違反の主張（`Violated`）か、評価エラーの主張（`Error`）か。
pub open spec fn is_violation(claim: Claim) -> bool {
    claim is Invariant || claim is Contract || claim is Deadlock
}

/// 契約 `k` は対象で、最後の遷移に適用される。
pub open spec fn con_applies(m: RawModel, c: Conditions, steps: Seq<TraceStep>, k: int) -> bool {
    &&& steps.len() >= 1
    &&& con_on(m, c, k)
    &&& m.contracts@[k].action == steps[steps.len() - 1].action
}

/// 契約 `k` の、最後の遷移での評価。
pub open spec fn last_con_spec(m: RawModel, start: Seq<i64>, steps: Seq<TraceStep>, k: int) -> Result<bool, ErrKind> {
    let n = steps.len() as int;
    let st = steps[n - 1];
    con_spec(m, k, state_at(start, steps, n - 1), st.args@, st.state@, st.output)
}

/// トレースの末尾で、主張どおりの事象が起きる。
pub open spec fn claim_holds(m: RawModel, c: Conditions, start: Seq<i64>, steps: Seq<TraceStep>, claim: Claim) -> bool {
    let last = state_at(start, steps, steps.len() as int);
    match claim {
        Claim::Invariant(i) => inv_on(m, c, i as int) && inv_spec(m, i as int, last) == Ok::<bool, ErrKind>(false),
        Claim::InvariantError(i, e) => inv_on(m, c, i as int) && inv_spec(m, i as int, last) == Err::<bool, ErrKind>(
            e,
        ),
        Claim::Contract(k) => con_applies(m, c, steps, k as int) && last_con_spec(m, start, steps, k as int) == Ok::<
            bool,
            ErrKind,
        >(false),
        Claim::ContractError(k, e) => con_applies(m, c, steps, k as int) && last_con_spec(m, start, steps, k as int)
            == Err::<bool, ErrKind>(e),
        Claim::Deadlock => c.deadlock && stuck(m, c, last) && terminal_spec(m, last) == Ok::<bool, ErrKind>(false),
        Claim::TerminalError(e) => c.deadlock && stuck(m, c, last) && terminal_spec(m, last) == Err::<bool, ErrKind>(
            e,
        ),
        Claim::StepError(a, args, site, e) => act_on(m, c, a as int) && args_ok(m, a as int, args@) && step_spec(
            m,
            a as int,
            args@,
            last,
        ) == Step::Fail(site, e),
    }
}

/// 初期状態から始まる有効なトレースの各状態は、そのステップ数で到達できる。
pub proof fn lemma_trace_reach(m: RawModel, c: Conditions, start: Seq<i64>, steps: Seq<TraceStep>, k: nat)
    requires
        is_init(m, start),
        trace_ok(m, c, start, steps),
        k <= steps.len(),
    ensures
        reach(m, c, state_at(start, steps, k as int), k),
    decreases k,
{
    if k > 0 {
        lemma_trace_reach(m, c, start, steps, (k - 1) as nat);
        assert(step_ok(m, c, start, steps, k - 1));
        let st = steps[k - 1];
        assert(is_edge(
            m,
            c,
            state_at(start, steps, k - 1),
            st.action as int,
            st.args@,
            st.output,
            state_at(start, steps, k as int),
        ));
    }
}

/// 安全なモデルには、主張の成り立つ有効なトレースが存在しない。
/// したがって、同じモデルと検査条件に対する `Verified` と、`Violated` または `Error` は両立しない。
pub proof fn lemma_safe_excludes_trace(
    m: RawModel,
    c: Conditions,
    start: Seq<i64>,
    steps: Seq<TraceStep>,
    claim: Claim,
)
    requires
        safe(m, c),
        is_init(m, start),
        trace_ok(m, c, start, steps),
        claim_holds(m, c, start, steps, claim),
    ensures
        false,
{
    let n = steps.len();
    let last = state_at(start, steps, n as int);
    lemma_trace_reach(m, c, start, steps, n);
    assert(state_safe(m, c, last));
    match claim {
        Claim::Invariant(i) => {},
        Claim::InvariantError(i, e) => {},
        Claim::Contract(k) => {
            lemma_last_contract(m, c, start, steps, k as int);
        },
        Claim::ContractError(k, e) => {
            lemma_last_contract(m, c, start, steps, k as int);
        },
        Claim::Deadlock => {},
        Claim::TerminalError(e) => {},
        Claim::StepError(a, args, site, e) => {
            assert(trans_safe(m, c, a as int, args@, last));
        },
    }
}

proof fn lemma_last_contract(m: RawModel, c: Conditions, start: Seq<i64>, steps: Seq<TraceStep>, k: int)
    requires
        safe(m, c),
        is_init(m, start),
        trace_ok(m, c, start, steps),
        con_applies(m, c, steps, k),
    ensures
        last_con_spec(m, start, steps, k) == Ok::<bool, ErrKind>(true),
{
    let n = steps.len() as int;
    let st = steps[n - 1];
    let prev = state_at(start, steps, n - 1);
    lemma_trace_reach(m, c, start, steps, (n - 1) as nat);
    assert(state_safe(m, c, prev));
    assert(step_ok(m, c, start, steps, n - 1));
    assert(trans_safe(m, c, st.action as int, st.args@, prev));
}

// ---- 検査器 ----

/// `s` が初期状態の1つであることを確かめる。
pub(crate) fn is_initial(m: &RawModel, s: &Vec<i64>) -> (r: bool)
    ensures
        r ==> is_init(*m, s@),
{
    let mut i: usize = 0;
    while i < m.inits.len()
        invariant
            i <= m.inits@.len(),
        decreases m.inits@.len() - i,
    {
        if vec_eq(&m.inits[i], s) {
            assert(m.inits@[i as int]@ == s@);
            return true;
        }
        i = i + 1;
    }
    false
}

/// 開始状態から操作列を再生し、各ステップの出力と状態を照合する。
#[verifier::loop_isolation(false)]
pub(crate) fn replay(m: &RawModel, c: &Conditions, start: &Vec<i64>, steps: &Vec<TraceStep>) -> (r: Option<Reject>)
    ensures
        r is None ==> trace_ok(*m, *c, start@, steps@),
{
    let mut k: usize = 0;
    while k < steps.len()
        invariant
            k <= steps@.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] step_ok(*m, *c, start@, steps@, j),
        decreases steps@.len() - k,
    {
        let st = &steps[k];
        if !act_on_exec(m, c, st.action) {
            return Some(Reject::BadStep(k));
        }
        if !vals_ok_exec(&m.enums, &m.actions[st.action].domains, &st.args) {
            return Some(Reject::BadStep(k));
        }
        let cur: &Vec<i64> = if k == 0 {
            start
        } else {
            &steps[k - 1].state
        };
        assert(cur@ == state_at(start@, steps@, k as int));
        match step(m, st.action, &st.args, cur) {
            StepR::To(t, o) => {
                if !vec_eq(&t, &st.state) || !opt_eq(&o, &st.output) {
                    return Some(Reject::StepMismatch(k));
                }
            },
            _ => {
                return Some(Reject::StepMismatch(k));
            },
        }
        assert(step_ok(*m, *c, start@, steps@, k as int));
        k = k + 1;
    }
    None
}

/// 状態 `s` に対象の操作の有効な遷移がないことを確かめる。
#[verifier::loop_isolation(false)]
fn is_stuck(m: &RawModel, c: &Conditions, s: &Vec<i64>) -> (r: bool)
    ensures
        r ==> stuck(*m, *c, s@),
{
    let mut a: usize = 0;
    while a < m.actions.len()
        invariant
            a <= m.actions@.len(),
            forall|b: int| 0 <= b < a && #[trigger] act_on(*m, *c, b) ==> all_disabled(*m, b, s@),
        decreases m.actions@.len() - a,
    {
        if act_on_exec(m, c, a) {
            match enumerate(m, a, s) {
                Enumerated::Ok(ts) => {
                    if ts.len() > 0 {
                        return false;
                    }
                    proof {
                        lemma_enum_enabled(*m, a as int, s@, ts@);
                    }
                },
                Enumerated::Fail(_, _, _) => {
                    return false;
                },
            }
        }
        a = a + 1;
    }
    true
}

fn result_is(r: &Result<bool, ErrKind>, want: bool) -> (b: bool)
    ensures
        b == (*r == Ok::<bool, ErrKind>(want)),
{
    match r {
        Ok(x) => *x == want,
        Err(_) => false,
    }
}

fn result_fails(r: &Result<bool, ErrKind>, want: &ErrKind) -> (b: bool)
    ensures
        b == (*r == Err::<bool, ErrKind>(*want)),
{
    match r {
        Ok(_) => false,
        Err(e) => errkind_eq(e, want),
    }
}

/// 契約 `k` を最後の遷移で評価する。契約が対象でない、または最後の遷移に適用されなければ `None`。
fn eval_last_contract(m: &RawModel, c: &Conditions, start: &Vec<i64>, steps: &Vec<TraceStep>, k: usize) -> (r: Option<
    Result<bool, ErrKind>,
>)
    ensures
        r matches Some(v) ==> con_applies(*m, *c, steps@, k as int) && last_con_spec(*m, start@, steps@, k as int) == v,
{
    let n = steps.len();
    if n == 0 || !con_on_exec(m, c, k) {
        return None;
    }
    let st = &steps[n - 1];
    if m.contracts[k].action != st.action {
        return None;
    }
    let prev: &Vec<i64> = if n == 1 {
        start
    } else {
        &steps[n - 2].state
    };
    assert(prev@ == state_at(start@, steps@, n - 1));
    Some(eval_contract(m, k, prev, &st.args, &st.state, &st.output))
}

/// 末尾の状態で、主張どおりの事象が起きることを確かめる。
pub(crate) fn check_claim(m: &RawModel, c: &Conditions, start: &Vec<i64>, steps: &Vec<TraceStep>, claim: &Claim) -> (r: bool)
    ensures
        r ==> claim_holds(*m, *c, start@, steps@, *claim),
{
    let n = steps.len();
    let last: &Vec<i64> = if n == 0 {
        start
    } else {
        &steps[n - 1].state
    };
    assert(last@ == state_at(start@, steps@, n as int));
    match claim {
        Claim::Invariant(i) => inv_on_exec(m, c, *i) && result_is(&eval_invariant(m, *i, last), false),
        Claim::InvariantError(i, e) => inv_on_exec(m, c, *i) && result_fails(&eval_invariant(m, *i, last), e),
        Claim::Contract(k) => match eval_last_contract(m, c, start, steps, *k) {
            Some(v) => result_is(&v, false),
            None => false,
        },
        Claim::ContractError(k, e) => match eval_last_contract(m, c, start, steps, *k) {
            Some(v) => result_fails(&v, e),
            None => false,
        },
        Claim::Deadlock => c.deadlock && is_stuck(m, c, last) && result_is(&eval_terminal(m, last), false),
        Claim::TerminalError(e) => c.deadlock && is_stuck(m, c, last) && result_fails(&eval_terminal(m, last), e),
        Claim::StepError(a, args, site, e) => {
            if !act_on_exec(m, c, *a) {
                return false;
            }
            if !vals_ok_exec(&m.enums, &m.actions[*a].domains, args) {
                return false;
            }
            match step(m, *a, args, last) {
                StepR::Fail(site2, e2) => site_eq(site, &site2) && errkind_eq(e, &e2),
                _ => false,
            }
        },
    }
}

/// トレースを検査する。`None`（受理）を返すなら、トレースは有効で、末尾で主張どおりの事象が起きる。
pub fn check_trace(m: &RawModel, c: &Conditions, start: &Vec<i64>, steps: &Vec<TraceStep>, claim: &Claim) -> (r: Option<Reject>)
    ensures
        r is None ==> is_init(*m, start@) && trace_ok(*m, *c, start@, steps@) && claim_holds(
            *m,
            *c,
            start@,
            steps@,
            *claim,
        ),
{
    if !is_initial(m, start) {
        return Some(Reject::BadStart);
    }
    match replay(m, c, start, steps) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    if check_claim(m, c, start, steps, claim) {
        None
    } else {
        Some(Reject::ClaimNotReproduced)
    }
}

} // verus!
