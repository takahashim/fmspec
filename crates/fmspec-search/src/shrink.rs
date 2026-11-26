//! モデル違反のトレースの縮小（仕様書 §10）。
//!
//! 操作列からステップを削った候補を作り、初期状態から再実行して状態と出力を計算し直す。
//! 候補を採用するのは、判定ゲートが同じ主張（同じ違反種別と対象）で受理したときだけである。
//! したがって、縮小器に不具合があっても、誤ったトレースを縮小結果として返すことはない。
//!
//! 結果は局所最小であり、大域最小とは主張しない。

use fmspec_core::evidence::{Claim, Evidence, TraceStep};
use fmspec_core::gate::{decide, CheckedModel, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;

/// 操作と引数の列を初期状態から再実行する。無効な遷移があれば `None`。
fn replay(model: &CheckedModel, inputs: &[(usize, Vec<i64>)]) -> Option<Vec<TraceStep>> {
    let mut state = model.initial();
    let mut steps = Vec::new();
    for (action, args) in inputs {
        let Some(Enumerated::Ok(transitions)) = model.successors(*action, &state) else {
            return None;
        };
        let t = transitions.into_iter().find(|t| t.args == *args)?;
        steps.push(TraceStep {
            action: *action,
            args: t.args,
            output: t.output,
            state: t.state.clone(),
        });
        state = t.state;
    }
    Some(steps)
}

fn accepted(model: &CheckedModel, cond: &Conditions, steps: Vec<TraceStep>, claim: &Claim) -> Option<Vec<TraceStep>> {
    let evidence = Evidence::Trace(steps, claim.clone());
    let kind = decide(model, cond, &evidence).kind();
    match (kind, evidence) {
        (VerdictKind::Violated | VerdictKind::Error, Evidence::Trace(steps, _)) => Some(steps),
        _ => None,
    }
}

/// トレースを縮小する。同じ主張を保つ、より短いトレースを返す。縮小できなければ、元のトレースを返す。
/// `attempts` は、試す候補の数の上限である。
pub fn shrink(
    model: &CheckedModel,
    cond: &Conditions,
    steps: &[TraceStep],
    claim: &Claim,
    attempts: usize,
) -> Vec<TraceStep> {
    let mut best: Vec<TraceStep> = steps.to_vec();
    let mut left = attempts;
    // 削る塊の大きさを、半分から1ステップまで小さくしていく。
    let mut chunk = best.len().div_ceil(2).max(1);
    loop {
        let mut start = 0;
        let mut removed = false;
        while start < best.len() && left > 0 {
            left -= 1;
            let end = (start + chunk).min(best.len());
            let inputs: Vec<(usize, Vec<i64>)> = best[..start]
                .iter()
                .chain(best[end..].iter())
                .map(|s| (s.action, s.args.clone()))
                .collect();
            match replay(model, &inputs).and_then(|candidate| accepted(model, cond, candidate, claim)) {
                Some(shorter) => {
                    best = shorter;
                    removed = true;
                }
                None => start = end,
            }
        }
        if left == 0 || (chunk == 1 && !removed) {
            return best;
        }
        if !removed {
            chunk = chunk.div_ceil(2);
        }
        chunk = chunk.min(best.len().max(1));
    }
}
