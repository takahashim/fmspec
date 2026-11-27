//! モデル検査の経路。探索器で証拠を生成し、判定ゲートを通してから結果を返す（仕様書 §3.1、§8.3）。

use crate::bfs::{bfs, BfsOptions, Stats};
use crate::gate::{judge, GateOptions};
use crate::simulate::{simulate, SimOptions, SimStats};
use fmspec_core::evidence::{Evidence, Limit, Reject};
use fmspec_core::gate::{CheckedModel, Verdict, VerdictKind};
use fmspec_core::semantics::Conditions;
use std::time::{Duration, Instant};

/// 検査結果の分類。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    /// 判定ゲートが証明書を受理した。
    Verified,
    /// 判定ゲートが違反に至るトレースを受理した。
    Violated,
    /// 判定ゲートが評価エラーに至るトレースを受理した。
    Error,
    /// 資源上限または中断で、証拠を得られなかった。
    Inconclusive(Limit),
    /// 探索器が生成した証拠を判定ゲートが拒否した。探索器の不具合を示す。
    InternalError(Reject),
}

pub struct Outcome {
    pub status: Status,
    /// 判定ゲートが返した判定。
    pub verdict: Verdict,
    /// 判定ゲートに渡した証拠。検査を打ち切った場合は、打ち切った理由の `Unavailable`。
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
        VerdictKind::Rejected => Status::InternalError(verdict.reject().unwrap_or(Reject::ClaimNotReproduced)),
        // `decide` は検証済みのモデルに対して InvalidModel を返さない。
        VerdictKind::InvalidModel => Status::InternalError(Reject::ClaimNotReproduced),
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

/// 幅優先探索でモデルを検査する。
pub fn check(model: &CheckedModel, cond: &Conditions, opts: &BfsOptions) -> Outcome {
    let started = Instant::now();
    let found = bfs(model, cond, opts);
    let search_time = started.elapsed();
    let gate = GateOptions {
        max_cost: opts.max_check_cost,
        interrupt: opts.interrupt,
    };
    let mut outcome = check_evidence_with(model, cond, found.evidence, found.stats, &gate);
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
    let found = result.evidence.map(|evidence| {
        let mut outcome = check_evidence(model, cond, evidence, Stats::default());
        outcome.search_time = search_time;
        outcome
    });
    Sampled {
        found,
        stats: result.stats,
    }
}
