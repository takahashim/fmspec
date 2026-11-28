//! 判定ゲートと、未検証コード向けの公開API。
//!
//! 利用者が受け取る判定の意味は `decide` だけで決まる（仕様書 §3.1、§14.1 Verdict Gate）。
//! `Verdict` のフィールドは非公開で、このモジュールの外では構築できない。
//! 判定ゲートに渡すモデル（`CheckedModel`）は `crate::checked` にあり、同じく `validate` を通らずには作れない。
//! ここにある公開関数は前提条件を持たない。

use crate::cert::*;
use crate::checked::CheckedModel;
use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
#[cfg(verus_keep_ghost)]
use crate::state_set::in_cert;
use crate::sym::SwapMaps;
use crate::trace::*;
use crate::typing::*;
use vstd::prelude::*;

verus! {

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

/// 判定と、その理由。[`Verdict::outcome`] が返す。理由のある判定は、理由を必ず持つ。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerdictOutcome {
    /// 証明書を受理した。
    Verified,
    /// 違反に至るトレースを受理した。
    Violated,
    /// 評価エラーに至るトレースを受理した。
    Error,
    /// 証拠を得られなかった。理由を持つ。
    Inconclusive(Limit),
    /// モデルが整形式でない。モデルを拒否した理由を持つ。
    InvalidModel(InvalidModel),
    /// 証拠を拒否した。拒否の理由を持つ。
    Rejected(Reject),
}

/// 判定。`decide` と `decide_raw` だけが構築する。
pub struct Verdict {
    kind: VerdictKind,
    reject: Option<Reject>,
    invalid: Option<InvalidModel>,
    limit: Option<Limit>,
}

impl Verdict {
    /// 理由は、判定の種類に対応するものだけがある（`reasons_ok`）。
    #[verifier::type_invariant]
    spec fn reasons_match(self) -> bool {
        self.reasons_ok()
    }

    pub closed spec fn spec_kind(self) -> VerdictKind {
        self.kind
    }

    pub fn kind(&self) -> (k: VerdictKind)
        ensures
            k == self.spec_kind(),
    {
        self.kind
    }

    pub closed spec fn spec_reject(self) -> Option<Reject> {
        self.reject
    }

    pub closed spec fn spec_invalid(self) -> Option<InvalidModel> {
        self.invalid
    }

    pub closed spec fn spec_limit(self) -> Option<Limit> {
        self.limit
    }

    /// 理由は、判定の種類に対応するものだけがある。`Rejected` には拒否の理由が、`InvalidModel` にはモデルを
    /// 拒否した理由が、`Inconclusive` には証拠を得られなかった理由が必ずあり、それ以外の判定にはない。
    pub open spec fn reasons_ok(self) -> bool {
        &&& (self.spec_kind() is Rejected <==> self.spec_reject() is Some)
        &&& (self.spec_kind() is InvalidModel <==> self.spec_invalid() is Some)
        &&& (self.spec_kind() is Inconclusive <==> self.spec_limit() is Some)
    }

    /// 証拠を拒否した理由。判定が `Rejected` のとき、かつそのときに限り `Some`。
    pub fn reject(&self) -> (r: Option<Reject>)
        ensures
            r == self.spec_reject(),
    {
        self.reject
    }

    /// モデルを拒否した理由。判定が `InvalidModel` のとき、かつそのときに限り `Some`。
    pub fn invalid(&self) -> (r: Option<InvalidModel>)
        ensures
            r == self.spec_invalid(),
    {
        self.invalid
    }

    /// 証拠を得られなかった理由。判定が `Inconclusive` のとき、かつそのときに限り `Some`。
    pub fn limit(&self) -> (r: Option<Limit>)
        ensures
            r == self.spec_limit(),
    {
        self.limit
    }

    /// 判定と、その理由。理由のある判定（`Rejected`、`InvalidModel`、`Inconclusive`）は、その理由を持つ。
    pub fn outcome(&self) -> (o: VerdictOutcome)
        ensures
            match o {
                VerdictOutcome::Verified => self.spec_kind() is Verified,
                VerdictOutcome::Violated => self.spec_kind() is Violated,
                VerdictOutcome::Error => self.spec_kind() is Error,
                VerdictOutcome::Inconclusive(l) => self.spec_kind() is Inconclusive && self.spec_limit() == Some(l),
                VerdictOutcome::InvalidModel(e) => self.spec_kind() is InvalidModel && self.spec_invalid() == Some(e),
                VerdictOutcome::Rejected(r) => self.spec_kind() is Rejected && self.spec_reject() == Some(r),
            },
    {
        proof {
            use_type_invariant(self);
        }
        match self.kind {
            VerdictKind::Verified => VerdictOutcome::Verified,
            VerdictKind::Violated => VerdictOutcome::Violated,
            VerdictKind::Error => VerdictOutcome::Error,
            VerdictKind::Inconclusive => VerdictOutcome::Inconclusive(self.limit.unwrap()),
            VerdictKind::InvalidModel => VerdictOutcome::InvalidModel(self.invalid.unwrap()),
            VerdictKind::Rejected => VerdictOutcome::Rejected(self.reject.unwrap()),
        }
    }

    fn of(kind: VerdictKind) -> (v: Verdict)
        requires
            !(kind is Rejected || kind is InvalidModel || kind is Inconclusive),
        ensures
            v.spec_kind() == kind,
            v.spec_reject() is None,
            v.spec_invalid() is None,
            v.spec_limit() is None,
    {
        Verdict { kind, reject: None, invalid: None, limit: None }
    }

    fn rejected(r: Reject) -> (v: Verdict)
        ensures
            v.spec_kind() == VerdictKind::Rejected,
            v.spec_reject() == Some(r),
            v.spec_invalid() is None,
            v.spec_limit() is None,
    {
        Verdict { kind: VerdictKind::Rejected, reject: Some(r), invalid: None, limit: None }
    }
}

/// 判定の意味。
///
/// - `Verified`: 証拠は証明書で、モデルは検査条件の下で安全である。
/// - `Violated` / `Error`: 証拠はトレースで、そのトレースは初期状態から始まって有効であり、末尾で主張どおりの違反 / 評価エラーが起きる。
/// - `Inconclusive`: モデルについて何も主張しない。`decide` は、証拠が得られなかった場合に限って返す。
///   `CertCheck` は、証明書の検査を資源上限か中断で打ち切った場合に返す。
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
        VerdictKind::Inconclusive => wf(m),
        VerdictKind::InvalidModel => !wf(m),
        VerdictKind::Rejected => wf(m) && !(ev is Unavailable),
    }
}

fn decide_wf(m: &RawModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    requires
        wf(*m),
    ensures
        verdict_sound(*m, *c, *ev, v.spec_kind()),
        !(v.spec_kind() is InvalidModel),
        v.spec_kind() is Inconclusive ==> ev is Unavailable,
        v.reasons_ok(),
        *ev matches Evidence::Unavailable(l) ==> v.spec_kind() is Inconclusive && v.spec_limit() == Some(l),
{
    match ev {
        Evidence::Certificate(cert) => {
            if !conditions_eq(m, &cert.conditions, c) {
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
///
/// 判定には、その種類に対応する理由がある（`Verdict::reasons_ok`）。証拠が `Unavailable(l)` なら、
/// 判定は `Inconclusive` で、理由は `l` である。
pub fn decide(model: &CheckedModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    ensures
        verdict_sound(model@, *c, *ev, v.spec_kind()),
        !(v.spec_kind() is InvalidModel),
        v.spec_kind() is Inconclusive ==> ev is Unavailable,
        v.reasons_ok(),
        *ev matches Evidence::Unavailable(l) ==> v.spec_kind() is Inconclusive && v.spec_limit() == Some(l),
{
    decide_wf(model.raw(), c, ev)
}

/// 途中で打ち切れる証明書の検査。`decide` と同じ検査を、状態の数を区切って進める。
///
/// 未検証の呼び出し側が、区切りごとに中断要求と資源上限を確かめ、必要なら `stop` で打ち切る。
/// 打ち切った検査は `Inconclusive` になり、モデルについて何も主張しない。
pub struct CertCheck<'a> {
    model: &'a CheckedModel,
    cond: &'a Conditions,
    cert: &'a Certificate,
    /// 検査を終えた状態の数。
    next: usize,
}

impl<'a> CertCheck<'a> {
    /// 初期状態をすべて含み、検査を終えた状態は性質を満たして遷移で閉じている。
    #[verifier::type_invariant]
    spec fn checked_prefix(self) -> bool {
        let m = self.model@;
        let states = self.cert.states@;
        &&& wf(m)
        &&& self.next <= states.len()
        &&& forall|i: int| 0 <= i < m.inits@.len() ==> in_cert(states, (#[trigger] m.inits@[i])@)
        &&& forall|j: int| 0 <= j < self.next ==> state_closed(m, *self.cond, states, (#[trigger] states[j])@)
    }

    pub closed spec fn spec_model(self) -> RawModel {
        self.model@
    }

    pub closed spec fn spec_cond(self) -> Conditions {
        *self.cond
    }

    pub closed spec fn spec_cert(self) -> Certificate {
        *self.cert
    }

    /// 検査を始める。検査条件が一致しない証明書と、初期状態を含まない証明書は、ここで拒否する。
    pub fn start(model: &'a CheckedModel, c: &'a Conditions, cert: &'a Certificate) -> (r: Result<
        CertCheck<'a>,
        Verdict,
    >)
        ensures
            match r {
                Ok(chk) => chk.spec_model() == model@ && chk.spec_cond() == *c && chk.spec_cert() == *cert,
                Err(v) => v.spec_kind() is Rejected && v.reasons_ok(),
            },
    {
        let m = model.raw();
        if !conditions_eq(m, &cert.conditions, c) {
            return Err(Verdict::rejected(Reject::ConditionMismatch));
        }
        let none: Vec<SwapMaps> = Vec::new();
        match check_initials(m, &none, &cert.states) {
            Some(r) => Err(Verdict::rejected(r)),
            None => {
                proof {
                    assert(none@ =~= Seq::<SwapMaps>::empty());
                    assert forall|i: int| 0 <= i < m.inits@.len() implies in_cert(cert.states@, (#[trigger] m.inits@[i])@) by {
                        lemma_reps_empty(cert.states@, m.inits@[i]@);
                    }
                }
                Ok(CertCheck { model, cond: c, cert, next: 0 })
            },
        }
    }

    /// まだ検査していない状態の数。
    pub fn remaining(&self) -> usize {
        proof {
            use_type_invariant(self);
        }
        self.cert.states.len() - self.next
    }

    /// 状態を最大 `n` 個検査する。証明書をすべて検査し終えるか、拒否したら、判定を返す。
    #[verifier::loop_isolation(false)]
    pub fn advance(&mut self, n: usize) -> (r: Option<Verdict>)
        ensures
            final(self).spec_model() == old(self).spec_model(),
            final(self).spec_cond() == old(self).spec_cond(),
            final(self).spec_cert() == old(self).spec_cert(),
            r matches Some(v) ==> (v.spec_kind() is Verified || v.spec_kind() is Rejected) && verdict_sound(
                old(self).spec_model(),
                old(self).spec_cond(),
                Evidence::Certificate(old(self).spec_cert()),
                v.spec_kind(),
            ) && v.reasons_ok(),
    {
        proof {
            use_type_invariant(&*self);
        }
        let m = self.model.raw();
        let states = &self.cert.states;
        let none: Vec<SwapMaps> = Vec::new();
        proof {
            assert(none@ =~= Seq::<SwapMaps>::empty());
        }
        let k = match check_states_range(m, self.cond, &none, states, self.next, n) {
            Err(r) => {
                return Some(Verdict::rejected(r));
            },
            Ok(k) => k,
        };
        proof {
            assert forall|j: int| 0 <= j < k implies state_closed(*m, *self.cond, states@, (#[trigger] states@[j])@) by {
                if j >= self.next {
                    lemma_closed_without_swaps(*m, *self.cond, states@, states@[j]@);
                }
            }
        }
        self.next = k;
        if k < states.len() {
            return None;
        }
        proof {
            lemma_inductive_safe(*m, *self.cond, states@);
        }
        Some(Verdict::of(VerdictKind::Verified))
    }

    /// 検査を打ち切る。判定は `Inconclusive` で、理由に `limit` を記録する。
    pub fn stop(self, limit: Limit) -> (v: Verdict)
        ensures
            v.spec_kind() is Inconclusive,
            v.spec_limit() == Some(limit),
            v.reasons_ok(),
            verdict_sound(self.spec_model(), self.spec_cond(), Evidence::Certificate(self.spec_cert()), v.spec_kind()),
    {
        proof {
            use_type_invariant(&self);
        }
        Verdict { kind: VerdictKind::Inconclusive, reject: None, invalid: None, limit: Some(limit) }
    }
}

/// 対称性による削減を使う判定ゲート。前提条件を持たない。
///
/// `swaps` は、状態のスロットの入れ替え（隣り合うブロックの入れ替え）の列である。
/// 証明書は軌道の代表元の集合でよい。判定ゲートは、入れ替えがどれもモデルと検査条件の対称性であること
/// （`sym::swap_maps`）を確かめてから、代表元の証明書を検査する。トレースは `decide` と同じく検査する。
/// 判定の意味は `decide` と同じ `verdict_sound` である。
pub fn decide_symmetric(model: &CheckedModel, c: &Conditions, swaps: &Vec<Vec<usize>>, ev: &Evidence) -> (v: Verdict)
    ensures
        verdict_sound(model@, *c, *ev, v.spec_kind()),
        !(v.spec_kind() is InvalidModel),
        v.spec_kind() is Inconclusive ==> ev is Unavailable,
        v.reasons_ok(),
        *ev matches Evidence::Unavailable(l) ==> v.spec_kind() is Inconclusive && v.spec_limit() == Some(l),
{
    let m = model.raw();
    match ev {
        Evidence::Certificate(cert) => {
            if !conditions_eq(m, &cert.conditions, c) {
                return Verdict::rejected(Reject::ConditionMismatch);
            }
            match crate::sym_check::symmetry(m, c, swaps) {
                Err(i) => Verdict::rejected(Reject::NotSymmetric(i)),
                Ok(sw) => match check_sym_certificate(m, c, &sw, &cert.states) {
                    None => Verdict::of(VerdictKind::Verified),
                    Some(r) => Verdict::rejected(r),
                },
            }
        },
        _ => decide_wf(m, c, ev),
    }
}

/// IR検証を経ていないモデルに対する判定ゲート。モデルを検証してから `decide` と同じ検査を行う。
/// モデルが整形式なら、判定の理由も `decide` と同じである。
pub fn decide_raw(m: &RawModel, c: &Conditions, ev: &Evidence) -> (v: Verdict)
    ensures
        verdict_sound(*m, *c, *ev, v.spec_kind()),
        v.reasons_ok(),
        match *ev {
            Evidence::Unavailable(l) => wf(*m) ==> v.spec_kind() is Inconclusive && v.spec_limit() == Some(l),
            _ => true,
        },
{
    match validate_raw(m) {
        Err(e) => Verdict { kind: VerdictKind::InvalidModel, reject: None, invalid: Some(e), limit: None },
        Ok(()) => decide_wf(m, c, ev),
    }
}

} // verus!
