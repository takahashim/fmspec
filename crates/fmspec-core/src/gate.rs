//! 判定ゲートと、未検証コード向けの公開API。
//!
//! 利用者が受け取る判定の意味は `decide` だけで決まる（仕様書 §3.1、§14.1 Verdict Gate）。
//! `Verdict` と `CheckedModel` のフィールドは非公開で、このモジュールの外では構築できない。
//! ここにある公開関数は前提条件を持たない。

use crate::cert::*;
use crate::eval::*;
use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
use crate::step::*;
use crate::trace::*;
use crate::typing::*;
use vstd::prelude::*;

verus! {

/// IR検証を通過したモデル。`validate` だけが構築する。
pub struct CheckedModel {
    raw: RawModel,
}

impl CheckedModel {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        wf(self.raw)
    }

    pub closed spec fn view(self) -> RawModel {
        self.raw
    }

    /// 検証済みのモデルの中身。整形式である。
    pub fn raw(&self) -> (r: &RawModel)
        ensures
            *r == self@,
            wf(*r),
    {
        proof {
            use_type_invariant(self);
        }
        &self.raw
    }

    /// 初期状態の符号化列。1つ以上ある。
    pub fn initials(&self) -> (r: &Vec<Vec<i64>>)
        ensures
            *r == self@.inits,
            r@.len() >= 1,
    {
        proof {
            use_type_invariant(self);
        }
        &self.raw.inits
    }

    /// 符号化列が状態型に従うか。
    pub fn state_ok(&self, s: &Vec<i64>) -> (r: bool)
        ensures
            r == state_ok(self@, s@),
    {
        vals_ok_exec(&self.raw.enums, &self.raw.state_types, s)
    }

    /// 状態 `s` での操作 `a` の有効な遷移を、引数の辞書順に、漏れなく列挙する。
    /// 操作が未定義か、状態が状態型に従わなければ `None`。
    pub fn successors(&self, a: usize, s: &Vec<i64>) -> (r: Option<Enumerated>)
        ensures
            r matches Some(e) ==> a < self@.actions@.len() && state_ok(self@, s@) && enumerated_ok(
                self@,
                a as int,
                s@,
                e,
            ),
    {
        if a < self.raw.actions.len() && self.state_ok(s) {
            Some(enumerate(&self.raw, a, s))
        } else {
            None
        }
    }

    /// 対象の不変条件を定義順に評価し、真でない最初のものと、その評価結果を返す。
    pub fn invariants(&self, c: &Conditions, s: &Vec<i64>) -> (r: Option<(usize, Result<bool, ErrKind>)>)
        ensures
            r is None ==> invs_hold(self@, *c, s@),
    {
        check_invariants(&self.raw, c, s)
    }

    /// 操作 `a` の遷移に適用する対象の契約を定義順に評価し、真でない最初のものと、その評価結果を返す。
    pub fn contracts(
        &self,
        c: &Conditions,
        a: usize,
        pre: &Vec<i64>,
        args: &Vec<i64>,
        post: &Vec<i64>,
        o: &Option<i64>,
    ) -> (r: Option<(usize, Result<bool, ErrKind>)>)
        ensures
            r is None ==> cons_hold(self@, *c, a as int, pre@, args@, post@, *o),
    {
        check_contracts(&self.raw, c, a, pre, args, post, o)
    }

    /// 終端条件を評価する。
    pub fn terminal(&self, s: &Vec<i64>) -> (r: Result<bool, ErrKind>)
        ensures
            r == terminal_spec(self@, s@),
    {
        eval_terminal(&self.raw, s)
    }
}

/// IRを検証する。受理するのは、モデルが整形式であるとき、かつそのときに限る。
pub fn validate(raw: RawModel) -> (r: Result<CheckedModel, InvalidModel>)
    ensures
        match r {
            Ok(cm) => cm@ == raw && wf(raw),
            Err(_) => !wf(raw),
        },
{
    match validate_raw(&raw) {
        Ok(()) => Ok(CheckedModel { raw }),
        Err(e) => Err(e),
    }
}

/// 判定の種類（仕様書 §8.3）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerdictKind {
    /// 証明書を受理した。モデルは検査条件の下で安全である。
    Verified,
    /// 違反に至るトレースを受理した。
    Violated,
    /// 評価エラーに至るトレースを受理した。
    Error,
    /// 証拠を得られなかった。
    Inconclusive,
    /// モデルが整形式でない。
    InvalidModel,
    /// 証拠を拒否した。探索器が生成した証拠なら、探索器の不具合を示す。
    Rejected,
}

/// 判定。`decide` と `decide_raw` だけが構築する。
pub struct Verdict {
    kind: VerdictKind,
    reject: Option<Reject>,
    invalid: Option<InvalidModel>,
    limit: Option<Limit>,
}

impl Verdict {
    pub closed spec fn spec_kind(self) -> VerdictKind {
        self.kind
    }

    pub fn kind(&self) -> (k: VerdictKind)
        ensures
            k == self.spec_kind(),
    {
        self.kind
    }

    /// 証拠を拒否した理由。
    pub fn reject(&self) -> Option<Reject> {
        self.reject
    }

    /// モデルを拒否した理由。
    pub fn invalid(&self) -> Option<InvalidModel> {
        self.invalid
    }

    /// 証拠を得られなかった理由。
    pub fn limit(&self) -> Option<Limit> {
        self.limit
    }

    fn of(kind: VerdictKind) -> (v: Verdict)
        ensures
            v.spec_kind() == kind,
    {
        Verdict { kind, reject: None, invalid: None, limit: None }
    }

    fn rejected(r: Reject) -> (v: Verdict)
        ensures
            v.spec_kind() == VerdictKind::Rejected,
    {
        Verdict { kind: VerdictKind::Rejected, reject: Some(r), invalid: None, limit: None }
    }
}

/// 判定の意味。
///
/// - `Verified`: 証拠は証明書で、モデルは検査条件の下で安全である。
/// - `Violated` / `Error`: 証拠はトレースで、そのトレースは初期状態から始まって有効であり、末尾で主張どおりの違反 / 評価エラーが起きる。
/// - `Inconclusive`: 証拠が得られなかった場合に限る。
/// - `InvalidModel`: モデルが整形式でない場合に限る。それ以外の判定では、モデルは整形式である。
/// - `Rejected`: 証拠が提示された場合に限る。証拠の拒否を成功や違反として扱わない。
pub open spec fn verdict_sound(m: RawModel, c: Conditions, ev: Evidence, k: VerdictKind) -> bool {
    match k {
        VerdictKind::Verified => wf(m) && ev is Certificate && safe(m, c),
        VerdictKind::Violated => wf(m) && match ev {
            Evidence::Trace(start, steps, claim) => is_violation(claim) && is_init(m, start@) && trace_ok(
                m,
                c,
                start@,
                steps@,
            ) && claim_holds(m, c, start@, steps@, claim),
            _ => false,
        },
        VerdictKind::Error => wf(m) && match ev {
            Evidence::Trace(start, steps, claim) => !is_violation(claim) && is_init(m, start@) && trace_ok(
                m,
                c,
                start@,
                steps@,
            ) && claim_holds(m, c, start@, steps@, claim),
            _ => false,
        },
        VerdictKind::Inconclusive => wf(m) && ev is Unavailable,
        VerdictKind::InvalidModel => !wf(m),
        VerdictKind::Rejected => wf(m) && !(ev is Unavailable),
    }
}

fn bools_eq(a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
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
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

fn conditions_eq(a: &Conditions, b: &Conditions) -> bool {
    bools_eq(&a.actions, &b.actions) && bools_eq(&a.invariants, &b.invariants) && bools_eq(
        &a.contracts,
        &b.contracts,
    ) && a.deadlock == b.deadlock
}

fn is_violation_exec(claim: &Claim) -> (r: bool)
    ensures
        r == is_violation(*claim),
{
    match claim {
        Claim::Invariant(_) => true,
        Claim::Contract(_) => true,
        Claim::Deadlock => true,
        _ => false,
    }
}

fn decide_wf(m: &RawModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    requires
        wf(*m),
    ensures
        verdict_sound(*m, *c, *ev, v.spec_kind()),
        !(v.spec_kind() is InvalidModel),
{
    match ev {
        Evidence::Certificate(cert) => {
            if !conditions_eq(&cert.conditions, c) {
                return Verdict::rejected(Reject::ConditionMismatch);
            }
            match check_certificate(m, c, &cert.states) {
                None => Verdict::of(VerdictKind::Verified),
                Some(r) => Verdict::rejected(r),
            }
        },
        Evidence::Trace(start, steps, claim) => match check_trace(m, c, start, steps, claim) {
            None => if is_violation_exec(claim) {
                Verdict::of(VerdictKind::Violated)
            } else {
                Verdict::of(VerdictKind::Error)
            },
            Some(r) => Verdict::rejected(r),
        },
        Evidence::Unavailable(limit) => Verdict {
            kind: VerdictKind::Inconclusive,
            reject: None,
            invalid: None,
            limit: Some(*limit),
        },
    }
}

/// 判定ゲート。モデルと証拠を受け取り、証拠を検査してから判定を返す。前提条件を持たない。
pub fn decide(model: &CheckedModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    ensures
        verdict_sound(model@, *c, *ev, v.spec_kind()),
        !(v.spec_kind() is InvalidModel),
{
    decide_wf(model.raw(), c, ev)
}

/// IR検証を経ていないモデルに対する判定ゲート。モデルを検証してから `decide` と同じ検査を行う。
pub fn decide_raw(m: &RawModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    ensures
        verdict_sound(*m, *c, *ev, v.spec_kind()),
{
    match validate_raw(m) {
        Err(e) => Verdict { kind: VerdictKind::InvalidModel, reject: None, invalid: Some(e), limit: None },
        Ok(()) => decide_wf(m, c, ev),
    }
}

} // verus!
