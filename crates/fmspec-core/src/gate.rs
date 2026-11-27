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
    /// 操作が未定義か、状態が状態型に従わなければ `None`。それ以外は `Some`。
    pub fn successors(&self, a: usize, s: &Vec<i64>) -> (r: Option<Enumerated>)
        ensures
            r is Some <==> a < self@.actions@.len() && state_ok(self@, s@),
            r matches Some(e) ==> enumerated_ok(self@, a as int, s@, e),
    {
        if a < self.raw.actions.len() && self.state_ok(s) {
            Some(enumerate(&self.raw, a, s))
        } else {
            None
        }
    }

    /// 状態 `s` で操作 `a` を引数 `args`（公開引数と内部選択）で適用した結果を計算する。
    /// 他の引数の評価に関係しないので、列挙が評価エラーになる状態でも、この引数の遷移を計算できる。
    /// 操作が未定義か、状態が状態型に、引数が操作のドメインに従わなければ `None`。それ以外は `Some`。
    pub fn apply(&self, a: usize, args: &Vec<i64>, s: &Vec<i64>) -> (r: Option<StepR>)
        ensures
            r is Some <==> a < self@.actions@.len() && state_ok(self@, s@) && args_ok(self@, a as int, args@),
            r matches Some(x) ==> x@ == step_spec(self@, a as int, args@, s@),
    {
        if a < self.raw.actions.len() && self.state_ok(s) && vals_ok_exec(
            &self.raw.enums,
            &self.raw.actions[a].domains,
            args,
        ) {
            Some(step(&self.raw, a, args, s))
        } else {
            None
        }
    }

    /// 対象の不変条件を定義順に評価し、真でない最初のものと、その評価結果を返す。
    /// `None` なら対象の不変条件はすべて真で、`Some((i, v))` なら `i` は対象の不変条件で、`v` はその評価結果
    /// （真でない）である。
    pub fn invariants(&self, c: &Conditions, s: &Vec<i64>) -> (r: Option<(usize, Result<bool, ErrKind>)>)
        ensures
            match r {
                None => invs_hold(self@, *c, s@),
                Some((i, v)) => inv_on(self@, *c, i as int) && inv_spec(self@, i as int, s@) == v && not_true(v),
            },
    {
        check_invariants(&self.raw, c, s)
    }

    /// 操作 `a` の遷移に適用する対象の契約を定義順に評価し、真でない最初のものと、その評価結果を返す。
    /// `None` なら適用する対象の契約はすべて真で、`Some((k, v))` なら `k` は操作 `a` の対象の契約で、`v` は
    /// その評価結果（真でない）である。
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
            match r {
                None => cons_hold(self@, *c, a as int, pre@, args@, post@, *o),
                Some((k, v)) => con_on(self@, *c, k as int) && self@.contracts@[k as int].action == a && con_spec(
                    self@,
                    k as int,
                    pre@,
                    args@,
                    post@,
                    *o,
                ) == v && not_true(v),
            },
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

    fn of(kind: VerdictKind) -> (v: Verdict)
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

fn flags_eq(n: usize, a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
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

pub(crate) fn is_violation_exec(claim: &Claim) -> (r: bool)
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
        match check_initials(m, &cert.states) {
            Some(r) => Err(Verdict::rejected(r)),
            None => Ok(CertCheck { model, cond: c, cert, next: 0 }),
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
        let mut k = self.next;
        let mut left = n;
        while k < states.len() && left > 0
            invariant
                self.next <= k <= states@.len(),
                forall|j: int| 0 <= j < k ==> state_closed(*m, *self.cond, states@, (#[trigger] states@[j])@),
            decreases states@.len() - k,
        {
            match check_state(m, self.cond, states, k) {
                Some(r) => {
                    return Some(Verdict::rejected(r));
                },
                None => {},
            }
            k = k + 1;
            left = left - 1;
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
            match crate::sym::symmetry(m, c, swaps) {
                Err(i) => Verdict::rejected(Reject::NotSymmetric(i)),
                Ok(sw) => match crate::sym::check_sym_certificate(m, c, &sw, &cert.states) {
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
