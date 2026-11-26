//! Model-Based Testing のセッションのJSONレベルのAPI（仕様書 §11.4）。
//!
//! Ruby 側のドライバが `setup`、`command`、`observe` を実行し、その結果の値だけをここに渡す。
//! セッションは Ruby のコードを呼び出さない。

use crate::conditions;
use fmspec_core::evidence::Claim;
use fmspec_ir::{args_to_json, claim_to_json, output_to_json, state_to_json, value_from_json, value_to_json, Model};
use fmspec_search::{InputCheck, ModelError, NextInput, Observed, PossibleOutcome, Seen, SeenOutput};
use serde_json::{json, Map, Value};
use std::sync::Arc;

/// 候補数の上限の既定値。
const DEFAULT_MAX_CANDIDATES: u64 = 10_000;

pub struct Session {
    model: Arc<Model>,
    inner: fmspec_search::Session,
    started: bool,
}

fn seen(model: &Model, var: usize, v: Option<&Value>) -> Seen {
    let ty = &model.raw().state_types[var];
    match v.map(|v| value_from_json(&model.names.enums, ty, v)) {
        Some(Ok(x)) => Seen::Value(x),
        _ => Seen::Unrepresentable,
    }
}

impl Session {
    /// セッションを作る。
    ///
    /// オプションは、検査条件（`actions`、`invariants`、`contracts`）、`seed`、
    /// `observe`（観測する状態変数の名前。省略時はすべて）、`max_candidates`。
    pub fn new(model: Arc<Model>, opts: &Value) -> Result<Session, String> {
        let map = crate::options(opts, &["seed", "observe", "max_candidates"])?;
        let cond = conditions(&model, map)?;
        let seed = crate::count(map, "seed", 0)?.unwrap_or(0);
        let max = crate::count(map, "max_candidates", 1)?.unwrap_or(DEFAULT_MAX_CANDIDATES);
        let names = &model.names.states;
        let observed = match map.get("observe") {
            None | Some(Value::Null) => (0..names.len()).collect(),
            Some(v) => {
                let list = v.as_array().ok_or("observe は状態変数の名前の配列です")?;
                let mut observed = Vec::new();
                for name in list {
                    let name = name.as_str().ok_or("observe は状態変数の名前の配列です")?;
                    let index = names
                        .iter()
                        .position(|n| n == name)
                        .ok_or(format!("未定義の状態変数 {name:?}"))?;
                    if !observed.contains(&index) {
                        observed.push(index);
                    }
                }
                observed
            }
        };
        let inner = fmspec_search::Session::new(cond, observed, seed, usize::try_from(max).unwrap_or(usize::MAX));
        Ok(Session {
            model,
            inner,
            started: false,
        })
    }

    /// 観測のJSON（状態変数名から値へのオブジェクト）を読む。観測する変数が欠けていれば `Err`。
    fn observation(&self, v: &Value) -> Result<Vec<Seen>, String> {
        let map = v.as_object().ok_or("observation はオブジェクトです")?;
        let mut out = Vec::new();
        for var in self.inner.observed() {
            let name = &self.model.names.states[*var];
            if !map.contains_key(name) {
                return Err(format!("observation に状態変数 {name:?} がありません"));
            }
            out.push(seen(&self.model, *var, map.get(name)));
        }
        Ok(out)
    }

    /// 状態を、観測する変数だけのJSONにする。
    fn projected(&self, state: &[i64]) -> Value {
        let mut map = Map::new();
        for var in self.inner.observed() {
            if let (Some(name), Some(ty), Some(x)) = (
                self.model.names.states.get(*var),
                self.model.raw().state_types.get(*var),
                state.get(*var),
            ) {
                map.insert(name.clone(), value_to_json(&self.model.names, ty, *x));
            }
        }
        Value::Object(map)
    }

    fn model_error(&self, e: &ModelError) -> Value {
        let claim = Claim::StepError(e.action, e.args.clone(), e.site, e.kind);
        json!({
            "status": "model_error",
            "property": claim_to_json(&self.model, &claim),
            "state": state_to_json(&self.model, &e.state),
        })
    }

    fn input(&self, v: &Value) -> Result<(usize, Vec<i64>), String> {
        let map = v.as_object().ok_or("入力はオブジェクトです")?;
        let name = map
            .get("action")
            .and_then(Value::as_str)
            .ok_or("action は操作の名前です")?;
        let action = self
            .model
            .names
            .action_index(name)
            .ok_or(format!("未定義の操作 {name:?}"))?;
        let empty = json!({});
        let n_params = self.model.raw().actions[action].n_params;
        // 内部選択は実装に渡さないので、公開引数だけを読む。
        let mut params = Vec::new();
        let args = map
            .get("args")
            .unwrap_or(&empty)
            .as_object()
            .ok_or("args はオブジェクトです")?;
        let names = &self.model.names.actions[action].params;
        if args.len() != names.len() {
            return Err(format!("操作 {name:?} の引数の個数が合いません"));
        }
        for (i, param) in names.iter().enumerate().take(n_params) {
            let ty = &self.model.raw().actions[action].domains[i];
            let v = args.get(param).ok_or(format!("引数 {param:?} がありません"))?;
            params.push(value_from_json(&self.model.names.enums, ty, v).map_err(|e| format!("引数 {param:?}: {e}"))?);
        }
        Ok((action, params))
    }

    fn input_json(&self, action: usize, params: &[i64]) -> Value {
        // 公開引数だけの列を、名前付きのJSONにする。内部選択は含まない。
        let (args, _) = args_to_json(&self.model, action, params);
        json!({"action": self.model.names.actions[action].name, "args": args})
    }

    /// 観測した値のうち、モデルが許すどの結果とも一致しない項目。
    fn mismatch(&self, possible: &[PossibleOutcome], output: SeenOutput, seen: &[Seen]) -> Vec<Value> {
        let mut fields = Vec::new();
        if let SeenOutput::Returned(y) = output {
            if !possible.iter().any(|p| p.output.map(Seen::Value) == Some(y)) {
                fields.push(json!("output"));
            }
        }
        for (var, x) in self.inner.observed().iter().zip(seen) {
            if !possible
                .iter()
                .any(|p| p.state.get(*var).map(|v| Seen::Value(*v)) == Some(*x))
            {
                fields.push(json!(self.model.names.states[*var]));
            }
        }
        fields
    }

    /// 初期観測を渡す。
    pub fn start(&mut self, observation: &Value) -> Result<Value, String> {
        let seen = self.observation(observation)?;
        self.started = true;
        if self.inner.start(self.model.checked(), &seen) {
            return Ok(json!({"status": "continue", "candidates": self.inner.candidates(), "matched": 0}));
        }
        let init = self.model.raw().init.clone();
        let possible = [PossibleOutcome {
            output: None,
            state: init.clone(),
        }];
        Ok(json!({
            "status": "conformance_failure",
            "step": 0,
            "expected": [{"state": self.projected(&init)}],
            "observed": {"state": observation},
            "mismatch": self.mismatch(&possible, SeenOutput::Unchecked, &seen),
        }))
    }

    /// 次の入力を問い合わせる。
    pub fn next_input(&mut self) -> Result<Value, String> {
        if !self.started {
            return Err("初期観測を渡す前に、次の入力は選べません".to_string());
        }
        Ok(match self.inner.next_input(self.model.checked()) {
            NextInput::Input { action, params } => {
                let mut body = self.input_json(action, &params);
                body["status"] = json!("input");
                body
            }
            NextInput::End => json!({"status": "end", "matched": self.inner.matched()}),
            NextInput::NoCommonInput => json!({
                "status": "inconclusive",
                "reason": "no_common_input",
                "candidates": self.inner.candidates(),
                "matched": self.inner.matched(),
            }),
            NextInput::ModelError(e) => self.model_error(&e),
        })
    }

    /// 入力（`{"action", "args"}`）が全候補で有効かを確かめる。
    pub fn check_input(&self, input: &Value) -> Result<Value, String> {
        let (action, params) = self.input(input)?;
        Ok(match self.inner.check_input(self.model.checked(), action, &params) {
            InputCheck::Valid => json!({"status": "valid"}),
            InputCheck::Invalid => json!({"status": "invalid"}),
            InputCheck::ModelError(e) => self.model_error(&e),
        })
    }

    /// 実装の応答（`{"action", "args", "output", "observation"}`）を渡す。
    pub fn observe(&mut self, report: &Value) -> Result<Value, String> {
        if !self.started {
            return Err("初期観測を渡す前に、応答は渡せません".to_string());
        }
        let (action, params) = self.input(report)?;
        let observation = report.get("observation").ok_or("observation が必要です")?;
        let seen = self.observation(observation)?;
        let raw_output = report.get("output");
        let output = match &self.model.raw().actions[action].output {
            None => SeenOutput::Unchecked,
            Some(out) => SeenOutput::Returned(
                match raw_output.map(|v| value_from_json(&self.model.names.enums, &out.ty, v)) {
                    Some(Ok(x)) => Seen::Value(x),
                    _ => Seen::Unrepresentable,
                },
            ),
        };
        let step = self.inner.matched() + 1;
        let before = self.inner.candidates();
        Ok(
            match self.inner.observe(self.model.checked(), action, &params, output, &seen) {
                Observed::Continue => {
                    json!({"status": "continue", "candidates": self.inner.candidates(), "matched": self.inner.matched()})
                }
                Observed::Failure { possible } => {
                    let mut expected: Vec<Value> = Vec::new();
                    for p in &possible {
                        let mut entry = json!({"state": self.projected(&p.state)});
                        if output != SeenOutput::Unchecked {
                            entry["output"] = output_to_json(&self.model, action, p.output);
                        }
                        if !expected.contains(&entry) {
                            expected.push(entry);
                        }
                    }
                    let mut observed = json!({"state": observation});
                    if output != SeenOutput::Unchecked {
                        observed["output"] = raw_output.cloned().unwrap_or(Value::Null);
                    }
                    let mut body = self.input_json(action, &params);
                    body["status"] = json!("conformance_failure");
                    body["step"] = json!(step);
                    body["candidates"] = json!(before);
                    body["expected"] = json!(expected);
                    body["observed"] = observed;
                    body["mismatch"] = json!(self.mismatch(&possible, output, &seen));
                    body
                }
                Observed::InvalidInput => json!({"status": "invalid_input"}),
                Observed::TooManyCandidates => {
                    json!({"status": "inconclusive", "reason": "max_candidates", "matched": self.inner.matched()})
                }
                Observed::ModelError(e) => self.model_error(&e),
                Observed::ModelViolation {
                    invariant,
                    index,
                    state,
                } => {
                    let claim = if invariant {
                        Claim::Invariant(index)
                    } else {
                        Claim::Contract(index)
                    };
                    json!({
                        "status": "model_violation",
                        "property": claim_to_json(&self.model, &claim),
                        "state": state_to_json(&self.model, &state),
                    })
                }
            },
        )
    }

    /// 現在の候補の状態。診断とテストに使う。
    pub fn candidates(&self) -> Value {
        json!(self
            .inner
            .candidate_states()
            .map(|s| state_to_json(&self.model, s))
            .collect::<Vec<_>>())
    }
}
