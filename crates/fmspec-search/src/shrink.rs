//! モデル違反のトレースの縮小（仕様書 §10）。
//!
//! 候補は2種類ある。操作列からステップを削った候補と、1つのステップの1つの引数（公開引数または内部選択）を、
//! ドメインの正規順でより前の値に変えた候補である。変えた位置より前のステップは、今の縮小結果のものをそのまま使い、
//! 変えた位置から後を、その直前の状態から再実行して状態と出力を計算し直す。
//! 引数を変えると遷移先の状態が変わるので、後続のステップも同じ操作と引数で再実行する。
//! 候補を採用するのは、判定ゲートが同じ主張（同じ違反種別と対象）で、開始状態からトレース全体を再生して受理したときだけである。
//! したがって、縮小器に不具合があっても、誤ったトレースを縮小結果として返すことはない。
//!
//! 試す候補の数の上限、中断要求、時間の上限で打ち切る。打ち切ったときは、それまでに判定ゲートが受理したトレースを返す。
//! 結果は局所最小であり、大域最小とは主張しない。打ち切った結果は、局所最小であることも主張しない。

use crate::stop::stopped;
use fmspec_core::evidence::{Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::{decide, CheckedModel, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{type_range_exec, StepR};
use std::time::Instant;

/// 縮小のオプション。
#[derive(Clone, Copy)]
pub struct ShrinkOptions<'a> {
    /// 試す候補（削除と引数の変更の両方）の数の上限。
    pub attempts: usize,
    /// 中断要求の問い合わせ。真を返したら、縮小を打ち切る。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
    /// 時間の上限の時刻。過ぎたら、縮小を打ち切る。
    pub deadline: Option<Instant>,
}

impl ShrinkOptions<'_> {
    /// 試す候補の数の上限だけを持つオプション。
    pub fn attempts(attempts: usize) -> Self {
        ShrinkOptions {
            attempts,
            interrupt: None,
            deadline: None,
        }
    }
}

/// 縮小を打ち切った理由。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShrinkStop {
    /// 試す候補の数の上限に達した。
    Attempts,
    /// 中断要求（`Limit::Interrupted`）か時間の上限（`Limit::MaxTime`）。
    Limit(Limit),
}

/// 縮小の結果。
#[derive(Clone, Debug, PartialEq)]
pub struct Shrunk {
    /// 縮小したトレースのステップ。判定ゲートが同じ主張で受理した候補か、元のトレースである。
    pub steps: Vec<TraceStep>,
    /// 試した候補の数。
    pub attempts: usize,
    /// 打ち切った理由。`None` なら、縮小は打ち切らずに終わり、結果は局所最小である。
    pub stopped: Option<ShrinkStop>,
}

/// 操作と引数の列を状態 `state` から再実行する。無効な遷移があれば `None`。
///
/// 各ステップは、その引数だけで計算する（同じ状態で他の引数の評価が失敗しても、このステップは再実行できる）。
fn replay(model: &CheckedModel, state: &[i64], inputs: &[(usize, Vec<i64>)]) -> Option<Vec<TraceStep>> {
    let mut state = state.to_vec();
    let mut steps = Vec::new();
    for (action, args) in inputs {
        // 無効（`Disabled`）か評価エラー（`Fail`）なら、候補は無効である。`None`（操作の添字が範囲外か、状態や引数が型に従わない）は、
        // 操作と引数が判定ゲートの受理したトレースのもので、状態が開始状態か計算した遷移先なので来ないはずである。
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

fn inputs_of(steps: &[TraceStep]) -> Vec<(usize, Vec<i64>)> {
    steps.iter().map(|s| (s.action, s.args.clone())).collect()
}

/// 縮小を打ち切ったこと。`?` で縮小の手順から抜ける。
struct Stopped;

struct Shrinker<'a> {
    model: &'a CheckedModel,
    cond: &'a Conditions,
    start: &'a [i64],
    claim: &'a Claim,
    opts: &'a ShrinkOptions<'a>,
    /// 判定ゲートが最後に受理した候補（はじめは元のトレース）。
    best: Vec<TraceStep>,
    tried: usize,
    stopped: Option<ShrinkStop>,
}

impl Shrinker<'_> {
    /// 候補を1つ試す。候補は、今のトレースの先頭 `keep` ステップに、その後の状態から `inputs` を再実行したステップを続けたものである。
    /// 判定ゲートが同じ主張で受理すれば、今のトレースをそれに置き換えて `true` を返す。
    /// 試す前に、候補の数の上限、中断要求、時間の上限を確かめ、達していれば打ち切る。
    fn attempt(&mut self, keep: usize, inputs: &[(usize, Vec<i64>)]) -> Result<bool, Stopped> {
        if self.tried >= self.opts.attempts {
            self.stopped = Some(ShrinkStop::Attempts);
            return Err(Stopped);
        }
        if let Some(limit) = stopped(self.opts.interrupt, self.opts.deadline) {
            self.stopped = Some(ShrinkStop::Limit(limit));
            return Err(Stopped);
        }
        self.tried += 1;
        let state = match keep.checked_sub(1) {
            Some(last) => &self.best[last].state,
            None => self.start,
        };
        let Some(tail) = replay(self.model, state, inputs) else {
            return Ok(false);
        };
        let mut candidate = self.best[..keep].to_vec();
        candidate.extend(tail);
        // 判定ゲートは、開始状態からトレース全体を再生して検査するので、前のステップを使い回したことには依らない。
        let evidence = Evidence::Trace(self.start.to_vec(), candidate, self.claim.clone());
        let kind = decide(self.model, self.cond, &evidence).kind();
        match (kind, evidence) {
            (VerdictKind::Violated | VerdictKind::Error, Evidence::Trace(_, steps, _)) => {
                self.best = steps;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// ステップを削る。削る塊の大きさを、半分から1ステップまで小さくしていく。1ステップの塊も削れなくなったら戻る。
    fn remove_steps(&mut self) -> Result<(), Stopped> {
        let mut chunk = self.best.len().div_ceil(2).max(1);
        loop {
            let mut from = 0;
            let mut removed = false;
            while from < self.best.len() {
                let end = (from + chunk).min(self.best.len());
                let rest = inputs_of(&self.best[end..]);
                if self.attempt(from, &rest)? {
                    removed = true;
                } else {
                    from = end;
                }
            }
            if chunk == 1 && !removed {
                return Ok(());
            }
            if !removed {
                chunk = chunk.div_ceil(2);
            }
            chunk = chunk.min(self.best.len().max(1));
        }
    }

    /// ステップ `i` の引数の列の位置 `j` に置ける、ドメインの正規順で最初の値と、今の値。ドメインが分からなければ `None`。
    fn bounds(&self, i: usize, j: usize) -> Option<(i128, i128)> {
        let raw = self.model.raw();
        let step = &self.best[i];
        let ty = raw.actions.get(step.action)?.domains.get(j)?;
        let (lo, _) = type_range_exec(&raw.enums, ty);
        Some((lo, i128::from(step.args[j])))
    }

    /// ステップ `i` の引数の列の位置 `j` を `value` に変えた候補を試す。
    fn try_value(&mut self, i: usize, j: usize, value: i128) -> Result<bool, Stopped> {
        // 値はドメインの最初の値と今の値の間にあり、型の範囲は i64 に収まる（`type_range_exec` の事後条件）ので、変換は失敗しない。
        let Ok(value) = i64::try_from(value) else {
            return Ok(false);
        };
        let mut inputs = inputs_of(&self.best[i..]);
        inputs[0].1[j] = value;
        self.attempt(i, &inputs)
    }

    /// 引数を小さくする。前のステップから順に、各ステップの引数の列（公開引数、内部選択の順）の前の位置から順に、
    /// その1つの位置だけを、ドメインの正規順でより前の値に変えた候補を、前の値から試す。戻り値は、何か変えたか。
    fn lower_args(&mut self) -> Result<bool, Stopped> {
        let mut changed = false;
        for i in 0..self.best.len() {
            for j in 0..self.best[i].args.len() {
                let Some((lo, current)) = self.bounds(i, j) else {
                    continue;
                };
                for value in lo..current {
                    if self.try_value(i, j, value)? {
                        // より前の値はすでに試して棄却されたので、この位置ではこれより小さくできない。
                        changed = true;
                        break;
                    }
                }
            }
        }
        Ok(changed)
    }

    /// ステップの削除をできなくなるまで行い、次に引数を小さくする。引数を変えたら、削除からやり直す。
    fn run(&mut self) -> Result<(), Stopped> {
        // 候補を採用するたびに、長さが減るか、長さが同じで引数の列が辞書順で前になるので、この繰り返しは終わる。
        loop {
            self.remove_steps()?;
            if !self.lower_args()? {
                return Ok(());
            }
        }
    }
}

/// トレースを縮小する。同じ開始状態と主張を保つ、より短いか、引数のより小さいトレースを返す。
/// 縮小できなければ、元のトレースを返す。
///
/// 試す候補の数が `opts.attempts` に達するか、中断要求か時間の上限に達したら、打ち切って、それまでに受理した候補を返す。
/// 打ち切らずに終われば、結果は次の意味で局所最小である：どの1ステップを除いても、
/// どの1ステップの1つの引数をドメインの正規順でより前の値に変えても（後続のステップは同じ操作と引数で再実行する）、
/// 判定ゲートが同じ主張で受理するトレースにならない。
pub fn shrink(
    model: &CheckedModel,
    cond: &Conditions,
    start: &[i64],
    steps: &[TraceStep],
    claim: &Claim,
    opts: &ShrinkOptions,
) -> Shrunk {
    let mut shrinker = Shrinker {
        model,
        cond,
        start,
        claim,
        opts,
        best: steps.to_vec(),
        tried: 0,
        stopped: None,
    };
    // 打ち切りは `stopped` に記録してある。
    let _ = shrinker.run();
    Shrunk {
        steps: shrinker.best,
        attempts: shrinker.tried,
        stopped: shrinker.stopped,
    }
}
