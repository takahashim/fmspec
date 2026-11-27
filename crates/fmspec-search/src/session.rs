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
//! 候補集合の更新と、全候補で有効な入力の計算は、検証済みの中核（`fmspec_core::mbt`）が行う。
//! ここでは、入力の無作為な選択と、不適合の診断（モデルが許す結果の列挙）だけを行う。

use crate::graph;
use crate::simulate::SplitMix64;
use fmspec_core::eval::ErrKind;
use fmspec_core::gate::CheckedModel;
use fmspec_core::mbt::{self, Begun, Update};
pub use fmspec_core::mbt::{Seen, SeenOutput};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{Enumerated, Site};
use std::collections::BTreeSet;
use std::sync::Arc;

/// モデルの評価エラー。モデルの側の問題であり、不適合とは区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelError {
    pub state: Vec<i64>,
    pub action: usize,
    pub args: Vec<i64>,
    pub site: Site,
    pub kind: ErrKind,
}

impl From<mbt::ModelError> for ModelError {
    fn from(e: mbt::ModelError) -> ModelError {
        ModelError {
            state: e.state,
            action: e.action,
            args: e.args,
            site: e.site,
            kind: e.kind,
        }
    }
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
    /// 候補集合。初期観測と一致する初期状態があるまでは `None`。
    core: Option<mbt::Session>,
    rng: SplitMix64,
    max_candidates: usize,
    /// command を実行して、戻り値と状態の照合まで完了した回数。
    matched: usize,
    covered: Covered,
}

/// 直前の照合で、実装が確実に通ったと分かるモデルの状態と遷移。カバレッジの計測に使う。
/// 候補が1つに定まらない、または応答を説明できる遷移が1つに定まらないときは `None` である。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Covered {
    pub state: Option<Vec<i64>>,
    /// 遷移元の状態、操作、引数の列（公開引数に続けて内部選択）。
    pub transition: Option<(Vec<i64>, usize, Vec<i64>)>,
}

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
            core: None,
            rng: SplitMix64::new(seed),
            max_candidates,
            matched: 0,
            covered: Covered::default(),
        }
    }

    /// 操作 `action` の、注入する選択の添字。
    pub fn injected(&self, action: usize) -> &[usize] {
        self.injected.get(action).map(Vec::as_slice).unwrap_or(&[])
    }

    /// 遷移の引数の列から、入力（公開引数と、注入する選択の値）を取り出す。診断に使う。
    fn input_of(&self, model: &CheckedModel, action: usize, args: &[i64]) -> Vec<i64> {
        graph::input_of(model, &self.injected, action, args)
    }

    /// 直前の照合で確実に分かった状態と遷移。
    pub fn covered(&self) -> &Covered {
        &self.covered
    }

    /// 候補が1つなら、その状態。
    fn single(&self) -> Option<Vec<i64>> {
        match self.core.as_ref().map(|core| core.candidates().as_slice()) {
            Some([only]) => Some(only.clone()),
            _ => None,
        }
    }

    /// 状態の観測するスロットが、観測と一致する。
    fn agrees(&self, state: &[i64], seen: &[Seen]) -> bool {
        self.observed.len() == seen.len()
            && self
                .observed
                .iter()
                .zip(seen)
                .all(|(var, seen)| state.get(*var).map(|x| Seen::Value(*x)) == Some(*seen))
    }

    /// 候補 `before` からの遷移のうち、入力と応答を説明できるものが1つだけなら、その遷移。
    fn explanation(
        &self,
        model: &CheckedModel,
        before: &[Vec<i64>],
        action: usize,
        params: &[i64],
        output: SeenOutput,
        seen: &[Seen],
    ) -> Option<(Vec<i64>, usize, Vec<i64>)> {
        let mut found = None;
        for s in before {
            // 評価エラー（`Fail`）なら、遷移を確定しない。`None`（操作の添字が範囲外か、状態が状態型に従わない）は、
            // 候補が中核のセッションの状態で、操作は中核が受理した入力なので来ないはずである。来ても遷移を確定しないだけで、
            // 確実に通った遷移を多く報告することはなく、適合性の判定（中核の `mbt::Session::observe`）も変わらない。
            let Some(Enumerated::Ok(ts)) = model.successors(action, s) else {
                return None;
            };
            for t in ts {
                let output_ok = match output {
                    SeenOutput::Unchecked => true,
                    SeenOutput::Returned(y) => t.output.map(Seen::Value) == Some(y),
                };
                if output_ok && self.agrees(&t.state, seen) && self.input_of(model, action, &t.args) == params {
                    if found.is_some() {
                        return None;
                    }
                    found = Some((s.clone(), action, t.args));
                }
            }
        }
        found
    }

    pub fn candidates(&self) -> usize {
        self.core.as_ref().map_or(0, |core| core.candidates().len())
    }

    pub fn candidate_states(&self) -> impl Iterator<Item = &Vec<i64>> {
        self.core.iter().flat_map(|core| core.candidates().iter())
    }

    pub fn matched(&self) -> usize {
        self.matched
    }

    pub fn observed(&self) -> &[usize] {
        &self.observed
    }

    /// 初期観測から候補集合を作る。
    /// 観測と一致する初期状態がなければ `Failure`、候補が上限を超えれば `TooManyCandidates` を返す。
    pub fn start(&mut self, model: Arc<CheckedModel>, seen: &[Seen]) -> Observed {
        self.core = None;
        self.matched = 0;
        self.covered = Covered::default();
        let begun = mbt::Session::start(
            Arc::clone(&model),
            self.cond.clone(),
            self.observed.clone(),
            self.injected.clone(),
            self.max_candidates,
            &seen.to_vec(),
        );
        match begun {
            Begun::Started(core) => {
                self.core = Some(core);
                self.covered = Covered {
                    state: self.single(),
                    transition: None,
                };
                Observed::Continue
            }
            Begun::TooMany => Observed::TooManyCandidates,
            Begun::Failure => {
                let possible = model
                    .initials()
                    .iter()
                    .take(MAX_POSSIBLE)
                    .map(|init| Outcome {
                        output: None,
                        state: init.clone(),
                    })
                    .collect();
                Observed::Failure { possible }
            }
        }
    }

    /// 次の入力を選ぶ。全候補で有効な公開入力から、一様に1つを選ぶ。
    pub fn next_input(&mut self) -> NextInput {
        let Some(core) = &self.core else {
            return NextInput::End;
        };
        let (common, any) = match core.common_inputs() {
            Ok(found) => found,
            Err(e) => return NextInput::ModelError(e.into()),
        };
        if common.is_empty() {
            return if any { NextInput::NoCommonInput } else { NextInput::End };
        }
        let pick = self.rng.below(common.len() as u64) as usize;
        let (action, params) = common.into_iter().nth(pick).unwrap_or_default();
        NextInput::Input { action, params }
    }

    /// 入力が全候補で有効かどうか。記録した操作列を再実行するときに、実装へ適用する前に確かめる。
    pub fn check_input(&self, action: usize, params: &[i64]) -> InputCheck {
        let Some(core) = &self.core else {
            return InputCheck::Invalid;
        };
        match core.check_input(action, &params.to_vec()) {
            Err(e) => InputCheck::ModelError(e.into()),
            Ok(true) => InputCheck::Valid,
            Ok(false) => InputCheck::Invalid,
        }
    }

    /// 実装の応答（戻り値と観測）で候補集合を更新する。
    pub fn observe(&mut self, action: usize, params: &[i64], output: SeenOutput, seen: &[Seen]) -> Observed {
        let Some(core) = &mut self.core else {
            return Observed::Failure { possible: Vec::new() };
        };
        let before = core.candidates().clone();
        let update = core.observe(action, &params.to_vec(), output, &seen.to_vec());
        match update {
            Update::Continue => {
                self.matched += 1;
                let transition = self
                    .core
                    .as_ref()
                    .and_then(|core| self.explanation(core.model(), &before, action, params, output, seen));
                self.covered = Covered {
                    state: self.single(),
                    transition,
                };
                Observed::Continue
            }
            Update::Failure => Observed::Failure {
                possible: self.possible(action, params),
            },
            Update::InvalidInput => Observed::InvalidInput,
            Update::TooMany => Observed::TooManyCandidates,
            Update::ModelError(e) => Observed::ModelError(e.into()),
            Update::ModelViolation(invariant, index, state) => Observed::ModelViolation {
                invariant,
                index,
                state,
            },
        }
    }

    /// 入力 `(action, params)` に対してモデルが許す結果。不適合の診断に使う。辞書順で最初の数個に限る。
    fn possible(&self, action: usize, params: &[i64]) -> Vec<Outcome> {
        let Some(core) = &self.core else {
            return Vec::new();
        };
        let model = core.model();
        let mut possible: BTreeSet<Outcome> = BTreeSet::new();
        for state in core.candidates() {
            // 診断に添える結果を集めるだけである。`None` は `explanation` と同じ理由で来ないはずで、来ても診断の候補が減るだけで、
            // 不適合の判定（中核の `mbt::Session::observe` が返す）は変わらない。
            let Some(Enumerated::Ok(ts)) = model.successors(action, state) else {
                continue;
            };
            for t in ts {
                if self.input_of(model, action, &t.args) == params {
                    possible.insert(Outcome {
                        output: t.output,
                        state: t.state,
                    });
                    if possible.len() > MAX_POSSIBLE {
                        possible.pop_last();
                    }
                }
            }
        }
        possible.into_iter().collect()
    }
}
