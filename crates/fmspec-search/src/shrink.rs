//! モデル違反のトレースの縮小（仕様書 §10）。
//!
//! 候補は2種類ある。操作列からステップを削った候補と、1つのステップの1つの引数（公開引数または内部選択）を、
//! ドメインの正規順でより前の値に変えた候補である。どちらも同じ開始状態から再実行して状態と出力を計算し直す。
//! 引数を変えると遷移先の状態が変わるので、後続のステップも同じ操作と引数で再実行する。
//! 候補を採用するのは、判定ゲートが同じ主張（同じ違反種別と対象）で受理したときだけである。
//! したがって、縮小器に不具合があっても、誤ったトレースを縮小結果として返すことはない。
//!
//! 結果は局所最小であり、大域最小とは主張しない。

use fmspec_core::evidence::{Claim, Evidence, TraceStep};
use fmspec_core::gate::{decide, CheckedModel, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{type_range_exec, StepR};

/// 操作と引数の列を開始状態から再実行する。無効な遷移があれば `None`。
///
/// 各ステップは、その引数だけで計算する（同じ状態で他の引数の評価が失敗しても、このステップは再実行できる）。
fn replay(model: &CheckedModel, start: &[i64], inputs: &[(usize, Vec<i64>)]) -> Option<Vec<TraceStep>> {
    let mut state = start.to_vec();
    let mut steps = Vec::new();
    for (action, args) in inputs {
        // 無効（`Disabled`）か評価エラー（`Fail`）なら、候補は無効である。`None`（操作の添字が範囲外か、状態や引数が型に従わない）は、
        // 操作と引数が判定ゲートの受理したトレースか列挙した遷移のもので、状態が開始状態か計算した遷移先なので来ないはずである。
        // 来ても候補を採用しないだけで、縮小の結果は元のトレースか、判定ゲートが受理した候補のままである。
        let Some(StepR::To(next, output)) = model.apply(*action, args, &state) else {
            return None;
        };
        steps.push(TraceStep {
            action: *action,
            args: args.clone(),
            output,
            state: next.clone(),
        });
        state = next;
    }
    Some(steps)
}

/// 引数の列の位置 `j` に置ける値のうち `current` より前のものを、ドメインの正規順に（前の値から）返す。
/// 範囲の広い整数型でも並べ切らないよう、値は1つずつ作る。
fn lower_values(model: &CheckedModel, action: usize, j: usize, current: i64) -> impl Iterator<Item = i64> {
    let raw = model.raw();
    let (lo, hi) = match raw.actions.get(action).and_then(|a| a.domains.get(j)) {
        Some(ty) => type_range_exec(&raw.enums, ty),
        None => (1, 0),
    };
    let hi = hi.min(i128::from(current) - 1);
    // 型の範囲は i64 に収まる（`type_range_exec` の事後条件）ので、変換は失敗しない。
    (lo..=hi).filter_map(|x| i64::try_from(x).ok())
}

fn accepted(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    steps: Vec<TraceStep>,
    claim: &Claim,
) -> Option<Vec<TraceStep>> {
    let evidence = Evidence::Trace(start.to_vec(), steps, claim.clone());
    let kind = decide(model, cond, &evidence).kind();
    match (kind, evidence) {
        (VerdictKind::Violated | VerdictKind::Error, Evidence::Trace(_, steps, _)) => Some(steps),
        _ => None,
    }
}

fn inputs_of(steps: &[TraceStep]) -> Vec<(usize, Vec<i64>)> {
    steps.iter().map(|s| (s.action, s.args.clone())).collect()
}

/// 候補の操作列を再実行し、判定ゲートが同じ主張で受理すれば、そのステップを返す。
fn try_inputs(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    inputs: &[(usize, Vec<i64>)],
    claim: &Claim,
) -> Option<Vec<TraceStep>> {
    replay(model, start, inputs).and_then(|candidate| accepted(model, cond, start, candidate, claim))
}

/// ステップを削る。削れる塊の大きさを、半分から1ステップまで小さくしていく。
/// 戻り値は、何か削れたか。`left` が尽きたら途中で戻る。
fn remove_steps(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    best: &mut Vec<TraceStep>,
    claim: &Claim,
    left: &mut usize,
) -> bool {
    let mut changed = false;
    let mut chunk = best.len().div_ceil(2).max(1);
    loop {
        let mut from = 0;
        let mut removed = false;
        while from < best.len() && *left > 0 {
            *left -= 1;
            let end = (from + chunk).min(best.len());
            let inputs: Vec<(usize, Vec<i64>)> = inputs_of(&best[..from])
                .into_iter()
                .chain(inputs_of(&best[end..]))
                .collect();
            match try_inputs(model, cond, start, &inputs, claim) {
                Some(shorter) => {
                    *best = shorter;
                    removed = true;
                    changed = true;
                }
                None => from = end,
            }
        }
        if *left == 0 || (chunk == 1 && !removed) {
            return changed;
        }
        if !removed {
            chunk = chunk.div_ceil(2);
        }
        chunk = chunk.min(best.len().max(1));
    }
}

/// 引数を小さくする。前のステップから順に、各ステップの引数の列（公開引数、内部選択の順）の前の位置から順に、
/// その1つの位置だけを、ドメインの正規順でより前の値に変えた候補を、前の値から試す。
/// 後続のステップは同じ操作と引数で再実行する。戻り値は、何か変えたか。`left` が尽きたら途中で戻る。
fn lower_args(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    best: &mut Vec<TraceStep>,
    claim: &Claim,
    left: &mut usize,
) -> bool {
    let mut changed = false;
    for i in 0..best.len() {
        for j in 0..best[i].args.len() {
            let current = best[i].args[j];
            for value in lower_values(model, best[i].action, j, current) {
                if *left == 0 {
                    return changed;
                }
                *left -= 1;
                let mut inputs = inputs_of(best);
                inputs[i].1[j] = value;
                if let Some(smaller) = try_inputs(model, cond, start, &inputs, claim) {
                    // より前の値はすでに試して棄却されたので、この位置ではこれより小さくできない。
                    *best = smaller;
                    changed = true;
                    break;
                }
            }
        }
    }
    changed
}

/// トレースを縮小する。同じ開始状態と主張を保つ、より短いか、引数のより小さいトレースを返す。
/// 縮小できなければ、元のトレースを返す。`attempts` は、試す候補（削除と引数の変更の両方）の数の上限である。
///
/// ステップの削除をできなくなるまで行い、次に引数を小さくする。引数を変えたら、削除からやり直す。
/// 上限に達せずに終われば、結果は次の意味で局所最小である：どの1ステップを除いても、
/// どの1ステップの1つの引数をドメインの正規順でより前の値に変えても（後続のステップは同じ操作と引数で再実行する）、
/// 判定ゲートが同じ主張で受理するトレースにならない。
pub fn shrink(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    steps: &[TraceStep],
    claim: &Claim,
    attempts: usize,
) -> Vec<TraceStep> {
    let mut best: Vec<TraceStep> = steps.to_vec();
    let mut left = attempts;
    // 候補を採用するたびに、長さが減るか、長さが同じで引数の列が辞書順で前になるので、この繰り返しは終わる。
    loop {
        remove_steps(model, cond, start, &mut best, claim, &mut left);
        if !lower_args(model, cond, start, &mut best, claim, &mut left) || left == 0 {
            return best;
        }
    }
}
