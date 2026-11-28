//! ランダムシミュレーション（仕様書 §9）。
//!
//! 各トレースを初期状態から始め、有効な具体的遷移から1つを一様に選んで進む。
//! 初期状態と各到達状態の不変条件、選んだ辺の遷移契約を検査し、違反で止まる。
//!
//! 乱数は SplitMix64 で、遷移の列挙順は幅優先探索と同じ（操作の定義順、引数の辞書順）である。
//! 同じモデル、検査条件、seed、トレース数、最大ステップ数に対して、結果は同じになる。

use crate::claim::{contract_claim, deadlock_claim, invariant_claim, selected};
use crate::inconsistency::{successors, Inconsistency};
use crate::stop::stopped;
use fmspec_core::checked::CheckedModel;
use fmspec_core::evidence::{Claim, Evidence, TraceStep};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{Enumerated, Transition};
use std::time::Instant;

/// 乱数のアルゴリズムの名前。結果に記録する。
pub const PRNG_NAME: &str = "splitmix64";

pub(crate) struct SplitMix64(u64);

impl SplitMix64 {
    pub(crate) fn new(seed: u64) -> SplitMix64 {
        SplitMix64(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// `0..n` の一様な整数。`n` は1以上。剰余の偏りは、棄却して取り除く。
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        let threshold = n.wrapping_neg() % n;
        loop {
            let x = self.next();
            if x >= threshold {
                return x % n;
            }
        }
    }
}

pub struct SimOptions<'a> {
    pub seed: u64,
    /// 生成するトレースの数。
    pub traces: usize,
    /// 1つのトレースの最大ステップ数。
    pub max_steps: usize,
    /// 中断要求の問い合わせ。真を返したら打ち切る。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
    /// 時間の上限の時刻。中断要求と同じく、トレースごとと、ステップごとに確かめる。
    pub deadline: Option<Instant>,
}

/// シミュレータの報告。検査済みの値ではない。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SimStats {
    /// 最後まで検査したトレースの数。
    pub traces: usize,
    /// 実行したステップの総数。
    pub steps: usize,
}

pub struct SimResult {
    /// 違反または評価エラーに至るトレース、または中断。すべてのサンプルを検査し終えたら `None`。
    /// 探索器の内部の不整合を見つけたら、証拠の代わりに不整合（`Err`）。
    pub evidence: Result<Option<Evidence>, Inconsistency>,
    pub stats: SimStats,
}

/// ランダムシミュレーションで証拠を探す。
pub fn simulate(model: &CheckedModel, cond: &Conditions, opts: &SimOptions) -> SimResult {
    run(model, cond, opts, |a, s| successors(model, a, s))
}

/// `simulate` の本体。遷移の列挙 `successors` を引数に取るのは、列挙の不整合をシミュレータが返すことをテストするためである。
fn run<F>(model: &CheckedModel, cond: &Conditions, opts: &SimOptions, successors: F) -> SimResult
where
    F: Fn(usize, &Vec<i64>) -> Result<Enumerated, Inconsistency>,
{
    let n_actions = model.raw().actions.len();
    let mut rng = SplitMix64::new(opts.seed);
    let mut stats = SimStats::default();
    let found = |evidence: Evidence, stats: SimStats| SimResult {
        evidence: Ok(Some(evidence)),
        stats,
    };
    // 有効な遷移の作業用の列。ステップごとに空にして使い回す。
    let mut enabled: Vec<(usize, Transition)> = Vec::new();

    let interrupted = || stopped(opts.interrupt, opts.deadline);
    for _ in 0..opts.traces {
        // 最大ステップ数が0で、ステップのないトレースが続いても打ち切れるように、トレースごとにも確かめる。
        if let Some(limit) = interrupted() {
            return found(Evidence::Unavailable(limit), stats);
        }
        // 初期状態が1つなら乱数を消費しない。同じシードで、初期状態が1つのモデルの結果を変えないためである。
        let inits = model.initials();
        let start = if inits.len() > 1 {
            inits[rng.below(inits.len() as u64) as usize].clone()
        } else {
            inits[0].clone()
        };
        let mut steps: Vec<TraceStep> = Vec::new();
        if let Some(claim) = invariant_claim(model, cond, &start) {
            return found(Evidence::Trace(start, steps, claim), stats);
        }
        for _ in 0..opts.max_steps {
            if let Some(limit) = interrupted() {
                return found(Evidence::Unavailable(limit), stats);
            }
            // 現在の状態は、最後のステップの遷移先である。状態を複製して別に持たない。
            let state = steps.last().map_or(&start, |step| &step.state);
            enabled.clear();
            for a in 0..n_actions {
                if !selected(&cond.actions, a) {
                    continue;
                }
                match successors(a, state) {
                    // 到達した状態は型に従い、操作の添字は範囲内なので、ここには来ないはずである。
                    // 来たら中断とは報告せず、不整合として返す。
                    Err(inconsistency) => {
                        return SimResult {
                            evidence: Err(inconsistency),
                            stats,
                        }
                    }
                    Ok(Enumerated::Fail(args, site, kind)) => {
                        return found(
                            Evidence::Trace(start, steps, Claim::StepError(a, args, site, kind)),
                            stats,
                        );
                    }
                    Ok(Enumerated::Ok(ts)) => enabled.extend(ts.into_iter().map(|t| (a, t))),
                }
            }
            if enabled.is_empty() {
                if cond.deadlock {
                    if let Some(claim) = deadlock_claim(model, state) {
                        return found(Evidence::Trace(start, steps, claim), stats);
                    }
                }
                break;
            }
            let pick = rng.below(enabled.len() as u64) as usize;
            let (a, t) = enabled.swap_remove(pick);
            stats.steps += 1;
            // 遷移契約を先に検査し、満たせば遷移先の不変条件を検査する。
            let violation = contract_claim(model, cond, a, state, &t.args, &t.state, &t.output)
                .or_else(|| invariant_claim(model, cond, &t.state));
            steps.push(TraceStep {
                action: a,
                args: t.args,
                output: t.output,
                state: t.state,
            });
            if let Some(claim) = violation {
                return found(Evidence::Trace(start, steps, claim), stats);
            }
        }
        stats.traces += 1;
    }
    SimResult {
        evidence: Ok(None),
        stats,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{run, simulate, SimOptions, SplitMix64};
    use crate::inconsistency::tests::counter;
    use crate::inconsistency::{successors, Inconsistency};
    use fmspec_ir::default_conditions;

    fn options() -> SimOptions<'static> {
        SimOptions {
            seed: 0,
            traces: 3,
            max_steps: 10,
            interrupt: None,
            deadline: None,
        }
    }

    #[test]
    fn an_inconsistent_enumeration_is_returned_instead_of_evidence() {
        let m = counter();
        let cond = default_conditions(&m, false);
        // 状態 x = 1 で、列挙が状態を受け付けなかったものとする。
        let result = run(m.checked(), &cond, &options(), |a, s| {
            if s == &vec![1] {
                Err(Inconsistency::Successors {
                    action: a,
                    state: s.clone(),
                })
            } else {
                successors(m.checked(), a, s)
            }
        });
        assert_eq!(
            result.evidence.err(),
            Some(Inconsistency::Successors {
                action: 0,
                state: vec![1]
            })
        );
        assert_eq!(result.stats.traces, 0);
        assert_eq!(result.stats.steps, 1);
    }

    #[test]
    fn a_consistent_simulation_samples_every_trace() {
        let m = counter();
        let result = simulate(m.checked(), &default_conditions(&m, false), &options());
        assert!(matches!(result.evidence, Ok(None)));
        assert_eq!(result.stats.traces, 3);
    }

    /// 結果に記録する乱数の名前 `PRNG_NAME` のとおり、標準の SplitMix64 の列を作る。
    /// 参照実装と同じ seed で同じトレースをたどることは、この列に依存する。
    #[test]
    fn the_generator_produces_the_standard_splitmix64_sequence() {
        let mut rng = SplitMix64::new(0);
        let first: Vec<u64> = (0..4).map(|_| rng.next()).collect();
        assert_eq!(
            first,
            [
                0xE220_A839_7B1D_CDAF,
                0x6E78_9E6A_A1B9_65F4,
                0x06C4_5D18_8009_454F,
                0xF88B_B8A8_724C_81EC
            ]
        );
    }
}
