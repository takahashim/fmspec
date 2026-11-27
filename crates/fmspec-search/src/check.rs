//! モデル検査の経路。探索器で証拠を生成し、判定ゲートを通してから結果を返す（仕様書 §3.1、§8.3）。

use crate::bfs::{bfs, BfsOptions, SearchResult, Stats};
use crate::gate::{judge, GateOptions};
use crate::inconsistency::Inconsistency;
use crate::simulate::{simulate, SimOptions, SimStats};
use fmspec_core::evidence::{Evidence, Limit, Reject};
use fmspec_core::gate::{CheckedModel, Verdict, VerdictKind};
use fmspec_core::semantics::Conditions;
use std::time::{Duration, Instant};

/// 検査結果の分類。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    /// 判定ゲートが証明書を受理した。
    Verified,
    /// 判定ゲートが違反に至るトレースを受理した。
    Violated,
    /// 判定ゲートが評価エラーに至るトレースを受理した。
    Error,
    /// 資源上限または中断で、証拠を得られなかった。
    Inconclusive(Limit),
    /// 探索器が生成した証拠を判定ゲートが拒否したか、探索器の内部の不整合。fmspec の不具合を示す。
    InternalError(Internal),
}

/// `Status::InternalError` の内容。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Internal {
    /// 探索器が生成した証拠を判定ゲートが拒否した。
    Rejected(Reject),
    /// 探索器が内部の不整合を見つけ、証拠を生成できなかった。
    Inconsistent(Inconsistency),
}

pub struct Outcome {
    pub status: Status,
    /// 判定ゲートが返した判定。
    pub verdict: Verdict,
    /// 判定ゲートに渡した証拠。検査を打ち切った場合は、打ち切った理由の `Unavailable`。
    /// 探索器の内部の不整合（`Internal::Inconsistent`）では、証拠がないことを表す `Unavailable` で、
    /// その理由（`Limit`）に意味はない。不整合の内容は `status` にある。
    pub evidence: Evidence,
    /// 探索器の報告。検査済みの値ではない。
    pub stats: Stats,
    pub search_time: Duration,
    /// 判定ゲートが証拠の検査にかけた時間。
    pub gate_time: Duration,
}

/// 探索器が生成した証拠を判定ゲートに渡し、判定を検査結果に分類する。
/// 判定ゲートが証拠を拒否した場合は、探索器の不具合として `InternalError` にする。
pub fn check_evidence(model: &CheckedModel, cond: &Conditions, evidence: Evidence, stats: Stats) -> Outcome {
    check_evidence_with(model, cond, evidence, stats, &GateOptions::default())
}

/// `check_evidence` に、証拠の検査の資源上限と中断を付けたもの。
pub fn check_evidence_with(
    model: &CheckedModel,
    cond: &Conditions,
    evidence: Evidence,
    stats: Stats,
    gate: &GateOptions,
) -> Outcome {
    let started = Instant::now();
    let (verdict, evidence) = judge(model, cond, evidence, gate);
    let gate_time = started.elapsed();
    let status = match verdict.kind() {
        VerdictKind::Verified => Status::Verified,
        VerdictKind::Violated => Status::Violated,
        VerdictKind::Error => Status::Error,
        VerdictKind::Inconclusive => Status::Inconclusive(verdict.limit().unwrap_or(Limit::Interrupted)),
        VerdictKind::Rejected => Status::InternalError(Internal::Rejected(
            verdict.reject().unwrap_or(Reject::ClaimNotReproduced),
        )),
        // `decide` は検証済みのモデルに対して InvalidModel を返さない。
        VerdictKind::InvalidModel => Status::InternalError(Internal::Rejected(Reject::ClaimNotReproduced)),
    };
    Outcome {
        status,
        verdict,
        evidence,
        stats,
        search_time: Duration::ZERO,
        gate_time,
    }
}

/// 探索器の内部の不整合を、検査結果にする。
///
/// 判定ゲートには、証拠がないこと（`Unavailable`）を渡す。判定ゲートが返す判定は `Inconclusive` であり、
/// `Verified`、`Violated`、`Error` にはならない。そのうえで、分類を中断ではなく `InternalError` にする。
fn inconsistent(model: &CheckedModel, cond: &Conditions, inconsistency: Inconsistency, stats: Stats) -> Outcome {
    let mut outcome = check_evidence(model, cond, Evidence::Unavailable(Limit::Interrupted), stats);
    outcome.status = Status::InternalError(Internal::Inconsistent(inconsistency));
    outcome
}

/// 探索の結果を検査結果にする。証拠は判定ゲートに渡し、不整合は `InternalError` にする。
fn judge_search(model: &CheckedModel, cond: &Conditions, found: SearchResult, gate: &GateOptions) -> Outcome {
    match found.evidence {
        Ok(evidence) => check_evidence_with(model, cond, evidence, found.stats, gate),
        Err(inconsistency) => inconsistent(model, cond, inconsistency, found.stats),
    }
}

/// 幅優先探索でモデルを検査する。
pub fn check(model: &CheckedModel, cond: &Conditions, opts: &BfsOptions) -> Outcome {
    let started = Instant::now();
    let found = bfs(model, cond, opts);
    let search_time = started.elapsed();
    let gate = GateOptions {
        max_cost: opts.max_check_cost,
        interrupt: opts.interrupt,
        deadline: opts.deadline,
    };
    let mut outcome = judge_search(model, cond, found, &gate);
    outcome.search_time = search_time;
    outcome
}

/// シミュレーションの結果。
pub struct Sampled {
    /// 違反または評価エラーを見つけた場合は、判定ゲートを通した結果。
    /// 見つからなければ `None`。指定したサンプルの検査を完了しただけで、網羅性の主張はない。
    pub found: Option<Outcome>,
    pub stats: SimStats,
}

/// ランダムシミュレーションでモデルを検査する。違反や評価エラーは、判定ゲートを通してから返す。
pub fn sample(model: &CheckedModel, cond: &Conditions, opts: &SimOptions) -> Sampled {
    let started = Instant::now();
    let result = simulate(model, cond, opts);
    let search_time = started.elapsed();
    let outcome = match result.evidence {
        Ok(evidence) => evidence.map(|evidence| check_evidence(model, cond, evidence, Stats::default())),
        Err(inconsistency) => Some(inconsistent(model, cond, inconsistency, Stats::default())),
    };
    let found = outcome.map(|mut outcome| {
        outcome.search_time = search_time;
        outcome
    });
    Sampled {
        found,
        stats: result.stats,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{judge_search, Internal, Status};
    use crate::bfs::{SearchResult, Stats};
    use crate::gate::GateOptions;
    use crate::inconsistency::tests::counter;
    use crate::inconsistency::Inconsistency;
    use fmspec_core::evidence::{Certificate, Evidence};
    use fmspec_core::gate::VerdictKind;
    use fmspec_ir::default_conditions;

    #[test]
    fn an_inconsistency_is_an_internal_error_and_not_a_verdict() {
        let m = counter();
        let cond = default_conditions(&m, false);
        let inconsistency = Inconsistency::Successors {
            action: 0,
            state: vec![0, 0],
        };
        let found = SearchResult {
            evidence: Err(inconsistency.clone()),
            stats: Stats::default(),
        };
        let o = judge_search(m.checked(), &cond, found, &GateOptions::default());
        assert_eq!(o.status, Status::InternalError(Internal::Inconsistent(inconsistency)));
        // 判定ゲートは証拠のないことしか受け取っていないので、判定は Inconclusive である。
        assert_eq!(o.verdict.kind(), VerdictKind::Inconclusive);
        assert!(matches!(o.evidence, Evidence::Unavailable(_)));
    }

    #[test]
    fn evidence_from_the_search_still_goes_through_the_gate() {
        let m = counter();
        let cond = default_conditions(&m, false);
        // 初期状態だけの証明書は、遷移先を含まないので拒否される。
        let found = SearchResult {
            evidence: Ok(Evidence::Certificate(Certificate {
                conditions: cond.clone(),
                states: vec![vec![0]],
            })),
            stats: Stats::default(),
        };
        let o = judge_search(m.checked(), &cond, found, &GateOptions::default());
        assert!(matches!(o.status, Status::InternalError(Internal::Rejected(_))));
        assert_eq!(o.verdict.kind(), VerdictKind::Rejected);
    }
}
