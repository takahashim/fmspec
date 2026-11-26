//! ランダムシミュレーション（仕様書 §9）。
//!
//! 各トレースを初期状態から始め、有効な具体的遷移から1つを一様に選んで進む。
//! 初期状態と各到達状態の不変条件、選んだ辺の遷移契約を検査し、違反で止まる。
//!
//! 乱数は SplitMix64 で、遷移の列挙順は幅優先探索と同じ（操作の定義順、引数の辞書順）である。
//! 同じモデル、検査条件、seed、トレース数、最大ステップ数に対して、結果は同じになる。

use fmspec_core::evidence::{Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{Enumerated, Transition};

/// 乱数のアルゴリズムの名前。結果に記録する。
pub const PRNG_NAME: &str = "splitmix64";

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// `0..n` の一様な整数。`n` は1以上。剰余の偏りは、棄却して取り除く。
    fn below(&mut self, n: u64) -> u64 {
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
    pub evidence: Option<Evidence>,
    pub stats: SimStats,
}

fn property_claim(
    index: usize,
    value: Result<bool, fmspec_core::eval::ErrKind>,
    violated: fn(usize) -> Claim,
    failed: fn(usize, fmspec_core::eval::ErrKind) -> Claim,
) -> Claim {
    match value {
        Err(e) => failed(index, e),
        Ok(_) => violated(index),
    }
}

/// ランダムシミュレーションで証拠を探す。
pub fn simulate(model: &CheckedModel, cond: &Conditions, opts: &SimOptions) -> SimResult {
    let n_actions = model.raw().actions.len();
    let mut rng = SplitMix64(opts.seed);
    let mut stats = SimStats::default();
    let found = |evidence: Evidence, stats: SimStats| SimResult {
        evidence: Some(evidence),
        stats,
    };

    for _ in 0..opts.traces {
        let mut state = model.initial();
        let mut steps: Vec<TraceStep> = Vec::new();
        if let Some((i, v)) = model.invariants(cond, &state) {
            return found(
                Evidence::Trace(steps, property_claim(i, v, Claim::Invariant, Claim::InvariantError)),
                stats,
            );
        }
        for _ in 0..opts.max_steps {
            if opts.interrupt.is_some_and(|requested| requested()) {
                return found(Evidence::Unavailable(Limit::Interrupted), stats);
            }
            let mut enabled: Vec<(usize, Transition)> = Vec::new();
            for a in 0..n_actions {
                if !cond.actions.get(a).copied().unwrap_or(false) {
                    continue;
                }
                match model.successors(a, &state) {
                    // 到達した状態は型に従い、操作の添字は範囲内なので、ここには来ない。
                    None => return found(Evidence::Unavailable(Limit::Interrupted), stats),
                    Some(Enumerated::Fail(args, site, kind)) => {
                        return found(Evidence::Trace(steps, Claim::StepError(a, args, site, kind)), stats);
                    }
                    Some(Enumerated::Ok(ts)) => enabled.extend(ts.into_iter().map(|t| (a, t))),
                }
            }
            if enabled.is_empty() {
                if cond.deadlock {
                    match model.terminal(&state) {
                        Ok(true) => {}
                        Ok(false) => return found(Evidence::Trace(steps, Claim::Deadlock), stats),
                        Err(e) => return found(Evidence::Trace(steps, Claim::TerminalError(e)), stats),
                    }
                }
                break;
            }
            let pick = rng.below(enabled.len() as u64) as usize;
            let (a, t) = enabled.swap_remove(pick);
            stats.steps += 1;
            let violation = model.contracts(cond, a, &state, &t.args, &t.state, &t.output);
            steps.push(TraceStep {
                action: a,
                args: t.args,
                output: t.output,
                state: t.state.clone(),
            });
            if let Some((k, v)) = violation {
                return found(
                    Evidence::Trace(steps, property_claim(k, v, Claim::Contract, Claim::ContractError)),
                    stats,
                );
            }
            state = t.state;
            if let Some((i, v)) = model.invariants(cond, &state) {
                return found(
                    Evidence::Trace(steps, property_claim(i, v, Claim::Invariant, Claim::InvariantError)),
                    stats,
                );
            }
        }
        stats.traces += 1;
    }
    SimResult { evidence: None, stats }
}
