//! 判定ゲートの呼び出し。証拠の検査に、資源上限と中断を付ける。
//!
//! 検査の計算量は、式の評価回数の上限で見積もる。量化の範囲と引数のドメインはモデルの中で固定なので、
//! 1つの状態の検査にかかる評価回数の上限は、状態によらずモデルと検査条件だけで決まる。
//! 見積もりが上限を超える証拠は検査しない。証明書の検査は状態の数を区切って進め、区切りごとに中断要求を確かめる。
//!
//! 打ち切った検査は `Inconclusive` になる。打ち切る判断がどう誤っても、`Verified` や `Violated` の意味は変わらない。

use crate::claim::selected;
use fmspec_core::evidence::{Evidence, Limit};
use fmspec_core::gate::{decide, CertCheck, CheckedModel, Verdict};
use fmspec_core::model::{Expr, RawModel, Type};
use fmspec_core::semantics::Conditions;

/// 中断要求を確かめる間隔の目安。この評価回数ごとに、証明書の検査を区切る。
const CHUNK_COST: u64 = 1 << 20;

#[derive(Clone, Copy, Default)]
pub struct GateOptions<'a> {
    /// 証拠の検査にかける評価回数の上限。見積もりがこれを超える証拠は検査しない。
    pub max_cost: Option<u64>,
    /// 中断要求の問い合わせ。真を返したら、証明書の検査を打ち切る。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
}

/// 式を1回評価するときの、部分式の評価回数の上限。
pub fn expr_cost(e: &Expr) -> u64 {
    match e {
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Arg(_)
        | Expr::Next(_)
        | Expr::Out
        | Expr::Local(_)
        | Expr::Fail(_, _) => 1,
        Expr::Not(x) | Expr::Code(x) => expr_cost(x).saturating_add(1),
        Expr::Bin(_, x, y) | Expr::And(x, y) | Expr::Or(x, y) | Expr::Implies(x, y) | Expr::Let(x, y) => {
            expr_cost(x).saturating_add(expr_cost(y)).saturating_add(1)
        }
        // 評価するのは、条件と、選ばれた一方の枝だけである。
        Expr::Ite(c, x, y) => expr_cost(c)
            .saturating_add(expr_cost(x).max(expr_cost(y)))
            .saturating_add(1),
        Expr::Forall(_, lo, hi, body) | Expr::Exists(_, lo, hi, body) => {
            let n = u64::try_from(i128::from(*hi) - i128::from(*lo) + 1).unwrap_or(0);
            n.saturating_mul(expr_cost(body).saturating_add(1)).saturating_add(1)
        }
    }
}

fn domain_size(m: &RawModel, ty: &Type) -> u64 {
    match ty {
        Type::Bool => 2,
        Type::Int(lo, hi) => u64::try_from(i128::from(*hi) - i128::from(*lo) + 1).unwrap_or(0),
        Type::Enum(id) => m.enums.get(*id).and_then(|n| u64::try_from(*n).ok()).unwrap_or(0),
    }
}

/// 1つの状態の検査（対象の不変条件、対象の操作の全引数での遷移と遷移契約、終端条件）の評価回数の上限。
pub fn state_cost(model: &CheckedModel, cond: &Conditions) -> u64 {
    let m = model.raw();
    let mut cost: u64 = 1;
    for (i, inv) in m.invariants.iter().enumerate() {
        if selected(&cond.invariants, i) {
            cost = cost.saturating_add(expr_cost(inv));
        }
    }
    for (a, act) in m.actions.iter().enumerate() {
        if !selected(&cond.actions, a) {
            continue;
        }
        let args = act
            .domains
            .iter()
            .fold(1u64, |n, ty| n.saturating_mul(domain_size(m, ty)));
        let mut per = expr_cost(&act.guard).saturating_add(1);
        for u in &act.updates {
            per = per.saturating_add(expr_cost(&u.expr));
        }
        if let Some(o) = &act.output {
            per = per.saturating_add(expr_cost(&o.expr));
        }
        for (k, con) in m.contracts.iter().enumerate() {
            if con.action == a && selected(&cond.contracts, k) {
                per = per.saturating_add(expr_cost(&con.expr));
            }
        }
        cost = cost.saturating_add(args.saturating_mul(per));
    }
    if cond.deadlock {
        if let Some(t) = &m.terminal {
            cost = cost.saturating_add(expr_cost(t));
        }
    }
    cost
}

/// 証拠の検査の評価回数の上限。トレースは、各ステップの遷移と、末尾の主張の検査を、1状態の検査で抑える。
pub fn evidence_cost(model: &CheckedModel, cond: &Conditions, evidence: &Evidence) -> u64 {
    let per_state = state_cost(model, cond);
    match evidence {
        Evidence::Certificate(cert) => per_state.saturating_mul(cert.states.len() as u64),
        Evidence::Trace(_, steps, _) => per_state.saturating_mul(steps.len() as u64 + 1),
        Evidence::Unavailable(_) => 0,
    }
}

/// 証拠を判定ゲートで検査する。検査を打ち切ったときは、証拠を `Unavailable`（打ち切った理由）に置き換えて返す。
pub fn judge(model: &CheckedModel, cond: &Conditions, evidence: Evidence, opts: &GateOptions) -> (Verdict, Evidence) {
    let given_up = |limit: Limit| {
        let evidence = Evidence::Unavailable(limit);
        (decide(model, cond, &evidence), evidence)
    };
    if opts
        .max_cost
        .is_some_and(|max| evidence_cost(model, cond, &evidence) > max)
    {
        return given_up(Limit::CheckBudget);
    }
    let Evidence::Certificate(cert) = &evidence else {
        return (decide(model, cond, &evidence), evidence);
    };
    let chunk = usize::try_from((CHUNK_COST / state_cost(model, cond).max(1)).max(1)).unwrap_or(usize::MAX);
    let mut check = match CertCheck::start(model, cond, cert) {
        Ok(check) => check,
        Err(verdict) => return (verdict, evidence),
    };
    loop {
        if let Some(verdict) = check.advance(chunk) {
            return (verdict, evidence);
        }
        if opts.interrupt.is_some_and(|requested| requested()) {
            return (
                check.stop(Limit::Interrupted),
                Evidence::Unavailable(Limit::Interrupted),
            );
        }
    }
}
