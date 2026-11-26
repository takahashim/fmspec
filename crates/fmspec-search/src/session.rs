//! Model-Based Testing のセッション（仕様書 §11.4、§12.2）。
//!
//! 1ケース分の候補状態集合を持つ。候補は、これまでの入力、戻り値、観測と矛盾しないモデルの状態である。
//! 実装の応答を受け取るたびに、候補を次の式で更新する。
//!
//! ```text
//! Cnext = { t | exists s in C, k, r: T(s, (a, k, r), t) and output_matches(r, y) and obs(t) = x }
//! ```
//!
//! 空集合になれば不適合である。候補を任意に1つへ絞ることはしない。
//! 次の入力は、全候補で有効な公開入力から選ぶ。
//!
//! 障害注入では、テストハーネスが一部の内部選択の値を決めて実装（の fake）に指示する。
//! その内部選択を**注入する選択**と呼び、公開引数と同じく入力の一部として扱う。
//! 入力を選ぶときも、候補を更新するときも、注入した値と一致する遷移だけを考える（仕様書 §12.2）。
//!
//! 後続状態は検証済みの遷移列挙器で求めるが、候補集合の更新そのものは証明の対象外で、
//! 境界ケース（仕様書 §17.2.1）と参照実装との比較で検査する。

use crate::simulate::SplitMix64;
use fmspec_core::eval::ErrKind;
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{Enumerated, Site, Transition};
use std::collections::BTreeSet;

/// 実装から得た値。モデルの型の符号にできない値（型の違う値、範囲外の整数、未定義のラベル）は、
/// モデルのどの値とも一致しない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seen {
    Value(i64),
    Unrepresentable,
}

/// 実装の戻り値。出力を宣言しない操作では比較しない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeenOutput {
    Unchecked,
    Returned(Seen),
}

/// モデルの評価エラー。モデルの側の問題であり、不適合とは区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelError {
    pub state: Vec<i64>,
    pub action: usize,
    pub args: Vec<i64>,
    pub site: Site,
    pub kind: ErrKind,
}

/// モデルが許す結果の1つ。出力と遷移後の状態。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Outcome {
    pub output: Option<i64>,
    pub state: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NextInput {
    /// 全候補で有効な公開入力。
    Input {
        action: usize,
        params: Vec<i64>,
    },
    /// どの候補にも有効な入力がない。
    End,
    /// 有効な入力を持つ候補があるが、全候補に共通する入力がない。
    NoCommonInput,
    ModelError(ModelError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputCheck {
    /// 全候補で有効。
    Valid,
    /// 無効な候補がある。
    Invalid,
    ModelError(ModelError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Observed {
    /// 候補が残った。
    Continue,
    /// 候補が空になった。実装の応答は、モデルが許すどの結果とも一致しない。
    Failure {
        possible: Vec<Outcome>,
    },
    /// 入力が、ある候補で無効である。
    InvalidInput,
    /// 候補数が上限を超えた。
    TooManyCandidates,
    ModelError(ModelError),
    /// 残った候補への遷移が、モデルの不変条件（`true`）または遷移契約（`false`）を満たさない。
    ModelViolation {
        invariant: bool,
        index: usize,
        state: Vec<i64>,
    },
}

pub struct Session {
    cond: Conditions,
    /// 観測する状態変数の添字。
    observed: Vec<usize>,
    /// 操作ごとの、注入する選択。引数の列（公開引数に続けて内部選択）の添字で、昇順に並ぶ。
    injected: Vec<Vec<usize>>,
    candidates: BTreeSet<Vec<i64>>,
    rng: SplitMix64,
    max_candidates: usize,
    /// command を実行して、戻り値と状態の照合まで完了した回数。
    matched: usize,
}

/// 入力。操作の添字と、公開引数に注入する選択の値を続けた列。
type Input = (usize, Vec<i64>);

/// 診断に含める「モデルが許す結果」の数の上限。
const MAX_POSSIBLE: usize = 16;

impl Session {
    pub fn new(
        cond: Conditions,
        observed: Vec<usize>,
        injected: Vec<Vec<usize>>,
        seed: u64,
        max_candidates: usize,
    ) -> Session {
        Session {
            cond,
            observed,
            injected,
            candidates: BTreeSet::new(),
            rng: SplitMix64::new(seed),
            max_candidates,
            matched: 0,
        }
    }

    /// 操作 `action` の、注入する選択の添字。
    pub fn injected(&self, action: usize) -> &[usize] {
        self.injected.get(action).map(Vec::as_slice).unwrap_or(&[])
    }

    /// 遷移の引数の列から、入力（公開引数と、注入する選択の値）を取り出す。
    fn input_of(&self, model: &CheckedModel, action: usize, args: &[i64]) -> Vec<i64> {
        let n = model.raw().actions[action].n_params.min(args.len());
        let mut input = args[..n].to_vec();
        input.extend(self.injected(action).iter().filter_map(|i| args.get(*i)));
        input
    }

    pub fn candidates(&self) -> usize {
        self.candidates.len()
    }

    pub fn candidate_states(&self) -> impl Iterator<Item = &Vec<i64>> {
        self.candidates.iter()
    }

    pub fn matched(&self) -> usize {
        self.matched
    }

    pub fn observed(&self) -> &[usize] {
        &self.observed
    }

    fn agrees(&self, state: &[i64], seen: &[Seen]) -> bool {
        self.observed
            .iter()
            .zip(seen)
            .all(|(var, seen)| state.get(*var).map(|x| Seen::Value(*x)) == Some(*seen))
    }

    /// 初期観測から候補集合を作る。
    /// 観測と一致する初期状態がなければ `Failure`、候補が上限を超えれば `TooManyCandidates` を返す。
    pub fn start(&mut self, model: &CheckedModel, seen: &[Seen]) -> Observed {
        self.candidates.clear();
        self.matched = 0;
        for init in model.initials() {
            if self.agrees(init, seen) {
                self.candidates.insert(init.clone());
                if self.candidates.len() > self.max_candidates {
                    self.candidates.clear();
                    return Observed::TooManyCandidates;
                }
            }
        }
        if self.candidates.is_empty() {
            let possible = model
                .initials()
                .iter()
                .take(MAX_POSSIBLE)
                .map(|init| Outcome {
                    output: None,
                    state: init.clone(),
                })
                .collect();
            return Observed::Failure { possible };
        }
        Observed::Continue
    }

    /// 状態での、対象の操作の有効な遷移。
    fn transitions(&self, model: &CheckedModel, state: &[i64]) -> Result<Vec<(usize, Transition)>, ModelError> {
        let state = state.to_vec();
        let mut all = Vec::new();
        for a in 0..model.raw().actions.len() {
            if !self.cond.actions.get(a).copied().unwrap_or(false) {
                continue;
            }
            match model.successors(a, &state) {
                Some(Enumerated::Ok(ts)) => all.extend(ts.into_iter().map(|t| (a, t))),
                Some(Enumerated::Fail(args, site, kind)) => {
                    return Err(ModelError {
                        state,
                        action: a,
                        args,
                        site,
                        kind,
                    });
                }
                // 候補は型に従う状態で、操作の添字は範囲内なので、ここには来ない。
                None => {}
            }
        }
        Ok(all)
    }

    /// 状態で有効な入力。操作の定義順に並び、同じ入力は1つにまとめる。
    fn inputs(&self, model: &CheckedModel, state: &[i64]) -> Result<Vec<Input>, ModelError> {
        let mut inputs: Vec<Input> = Vec::new();
        for (a, t) in self.transitions(model, state)? {
            let input = (a, self.input_of(model, a, &t.args));
            if !inputs.contains(&input) {
                inputs.push(input);
            }
        }
        Ok(inputs)
    }

    /// 全候補で有効な公開入力と、有効な入力を持つ候補があるかどうか。
    fn common_inputs(&self, model: &CheckedModel) -> Result<(Vec<Input>, bool), ModelError> {
        let mut common: Option<Vec<Input>> = None;
        let mut any = false;
        for state in &self.candidates {
            let inputs = self.inputs(model, state)?;
            any |= !inputs.is_empty();
            common = Some(match common {
                None => inputs,
                Some(kept) => kept.into_iter().filter(|i| inputs.contains(i)).collect(),
            });
        }
        Ok((common.unwrap_or_default(), any))
    }

    /// 次の入力を選ぶ。全候補で有効な公開入力から、一様に1つを選ぶ。
    pub fn next_input(&mut self, model: &CheckedModel) -> NextInput {
        let (common, any) = match self.common_inputs(model) {
            Ok(found) => found,
            Err(e) => return NextInput::ModelError(e),
        };
        if common.is_empty() {
            return if any { NextInput::NoCommonInput } else { NextInput::End };
        }
        let pick = self.rng.below(common.len() as u64) as usize;
        let (action, params) = common.into_iter().nth(pick).unwrap_or_default();
        NextInput::Input { action, params }
    }

    /// 入力が全候補で有効かどうか。記録した操作列を再実行するときに、実装へ適用する前に確かめる。
    pub fn check_input(&self, model: &CheckedModel, action: usize, params: &[i64]) -> InputCheck {
        match self.common_inputs(model) {
            Err(e) => InputCheck::ModelError(e),
            Ok((common, _)) => {
                if common.iter().any(|(a, p)| *a == action && p == params) {
                    InputCheck::Valid
                } else {
                    InputCheck::Invalid
                }
            }
        }
    }

    /// 実装の応答（戻り値と観測）で候補集合を更新する。
    pub fn observe(
        &mut self,
        model: &CheckedModel,
        action: usize,
        params: &[i64],
        output: SeenOutput,
        seen: &[Seen],
    ) -> Observed {
        if action >= model.raw().actions.len() {
            return Observed::InvalidInput;
        }
        let mut next: BTreeSet<Vec<i64>> = BTreeSet::new();
        let mut possible: BTreeSet<Outcome> = BTreeSet::new();
        let mut violation = None;
        for state in &self.candidates {
            let transitions = match self.transitions(model, state) {
                Ok(ts) => ts,
                Err(e) => return Observed::ModelError(e),
            };
            let mut enabled = false;
            for (a, t) in transitions {
                if a != action || self.input_of(model, a, &t.args) != params {
                    continue;
                }
                enabled = true;
                let output_matches = match output {
                    SeenOutput::Unchecked => true,
                    SeenOutput::Returned(seen) => t.output.map(Seen::Value) == Some(seen),
                };
                if output_matches && self.agrees(&t.state, seen) {
                    if let Some((k, _)) = model.contracts(&self.cond, a, state, &t.args, &t.state, &t.output) {
                        violation.get_or_insert((false, k, t.state.clone()));
                    }
                    if let Some((i, _)) = model.invariants(&self.cond, &t.state) {
                        violation.get_or_insert((true, i, t.state.clone()));
                    }
                    next.insert(t.state);
                    // 上限を超えた時点で打ち切り、それ以上の候補を作らない。
                    if next.len() > self.max_candidates {
                        return Observed::TooManyCandidates;
                    }
                } else if possible.len() < MAX_POSSIBLE {
                    possible.insert(Outcome {
                        output: t.output,
                        state: t.state,
                    });
                }
            }
            if !enabled {
                return Observed::InvalidInput;
            }
        }
        if next.is_empty() {
            return Observed::Failure {
                possible: possible.into_iter().collect(),
            };
        }
        if let Some((invariant, index, state)) = violation {
            return Observed::ModelViolation {
                invariant,
                index,
                state,
            };
        }
        self.candidates = next;
        self.matched += 1;
        Observed::Continue
    }
}
