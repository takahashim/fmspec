//! Model-Based Testing のセッションのJSONレベルのAPI（仕様書 §11.4）。
//!
//! Ruby 側のドライバが `setup`、`command`、`observe` を実行し、その結果の値だけをここに渡す。
//! セッションは Ruby のコードを呼び出さない。

use crate::inject::{inject_slots, input_json, parse_inject};
use crate::options::{conditions, count, keys, size};
use fmspec_core::evidence::Claim;
use fmspec_ir::{
    claim_to_json, output_to_json, output_value_from_json, state_to_json, value_from_json, value_to_json, Model,
};
use fmspec_search::{InputCheck, ModelError, NextInput, Observed, PossibleOutcome, Seen, SeenOutput};
use serde_json::{json, Map, Value};
use std::sync::Arc;

/// 候補数の上限の既定値。
const DEFAULT_MAX_CANDIDATES: u64 = 10_000;

pub struct Session {
    model: Arc<Model>,
    inner: fmspec_search::Session,
    /// 観測する状態変数。
    observed: Vec<usize>,
    /// 操作ごとの、注入する内部選択の添字（`choices` の中での添字、昇順）。
    injected: Vec<Vec<usize>>,
    /// 初期観測を受け取ったか。
    started: bool,
    /// 照合を続けない応答（不適合、未完了、モデルの誤り、入力の終わりなど）を返したか。
    /// 返したあとの問い合わせは誤りにする。誤った要求（`Err`）では終わらない。
    finished: bool,
}

/// 終わったセッションへの問い合わせの誤り。
const FINISHED: &str = "セッションは終わっています";

/// 照合が続くことを示す応答の `status`。これ以外の応答を返したら、セッションは終わる。
const GOING_ON: [&str; 4] = ["continue", "input", "valid", "invalid"];

/// 観測した値を、状態変数のスロットごとの値にする。型の符号にできなければ、すべてのスロットを一致しない値とする。
fn seen(model: &Model, var: usize, v: Option<&Value>) -> Vec<Seen> {
    let names = &model.names;
    let ty = &names.state_types[var];
    match v.map(|v| value_from_json(&names.enums, ty, v)) {
        Some(Ok(codes)) => codes.into_iter().map(Seen::Value).collect(),
        _ => vec![Seen::Unrepresentable; ty.width(&names.enums)],
    }
}

impl Session {
    /// セッションを作る。
    ///
    /// オプションは、検査条件（`actions`、`invariants`、`contracts`）、`seed`、
    /// `observe`（観測する状態変数の名前。省略時はすべて）、
    /// `inject`（操作名から、注入する内部選択の名前の配列へのオブジェクト）、`max_candidates`。
    /// 照合はデッドロックを検査しないので、`deadlock` は受け付けない。
    pub fn new(model: Arc<Model>, opts: &Value) -> Result<Session, String> {
        let map = keys(
            opts,
            &[
                "actions",
                "invariants",
                "contracts",
                "seed",
                "observe",
                "inject",
                "max_candidates",
            ],
        )?;
        let cond = conditions(&model, map)?;
        let seed = count(map, "seed", 0)?.unwrap_or(0);
        let max = count(map, "max_candidates", 1)?.unwrap_or(DEFAULT_MAX_CANDIDATES);
        let names = &model.names.states;
        let observed = match map.get("observe") {
            None | Some(Value::Null) => (0..names.len()).collect(),
            Some(v) => {
                let not_names = || format!("observe は状態変数の名前の配列です（{v}）");
                let list = v.as_array().ok_or_else(not_names)?;
                let mut observed = Vec::new();
                for name in list {
                    let name = name.as_str().ok_or_else(not_names)?;
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
        let injected = parse_inject(&model, map.get("inject"))?;
        let slots: Vec<usize> = observed.iter().flat_map(|v| model.names.state_slots(*v)).collect();
        let inner = fmspec_search::Session::new(cond, slots, inject_slots(&model, &injected), seed, size(max));
        Ok(Session {
            model,
            inner,
            observed,
            injected,
            started: false,
            finished: false,
        })
    }

    /// 初期観測を受け取っていて、まだ終わっていないことを確かめる。`before_start` は開始前の誤りの文。
    fn going_on(&self, before_start: &str) -> Result<(), String> {
        if !self.started {
            return Err(before_start.to_string());
        }
        if self.finished {
            return Err(FINISHED.to_string());
        }
        Ok(())
    }

    /// 応答を返す。照合を続けない応答なら、セッションを終える。
    fn answer(&mut self, body: Value) -> Value {
        if !body["status"].as_str().is_some_and(|s| GOING_ON.contains(&s)) {
            self.finished = true;
        }
        body
    }

    /// 観測のJSON（状態変数名から値へのオブジェクト）を読む。観測する変数が欠けていれば `Err`。
    fn observation(&self, v: &Value) -> Result<Vec<Seen>, String> {
        let map = v.as_object().ok_or("observation はオブジェクトです")?;
        let mut out = Vec::new();
        for var in &self.observed {
            let name = &self.model.names.states[*var];
            if !map.contains_key(name) {
                return Err(format!("observation に状態変数 {name:?} がありません"));
            }
            out.extend(seen(&self.model, *var, map.get(name)));
        }
        Ok(out)
    }

    /// 状態を、観測する変数だけのJSONにする。
    fn projected(&self, state: &[i64]) -> Value {
        let names = &self.model.names;
        let mut map = Map::new();
        for var in &self.observed {
            let slots = state.get(names.state_slots(*var)).unwrap_or(&[]);
            map.insert(
                names.states[*var].clone(),
                value_to_json(names, &names.state_types[*var], slots),
            );
        }
        Value::Object(map)
    }

    /// モデル自身の誤り（`model_error`、`model_violation`）の応答。主張と、それが起きた状態を示す。
    fn property_at(&self, status: &str, claim: &Claim, state: &[i64]) -> Value {
        json!({
            "status": status,
            "property": claim_to_json(&self.model, claim),
            "state": state_to_json(&self.model, state),
        })
    }

    fn model_error(&self, e: &ModelError) -> Value {
        let claim = Claim::StepError(e.action, e.args.clone(), e.site, e.kind);
        self.property_at("model_error", &claim, &e.state)
    }

    /// 照合が続くことの応答。
    fn continued(&self) -> Value {
        json!({
            "status": "continue",
            "candidates": self.inner.candidates(),
            "matched": self.inner.matched(),
            "covered": self.covered(),
        })
    }

    /// 候補数が上限を超えたことの応答。
    fn too_many_candidates(&self) -> Value {
        json!({"status": "inconclusive", "reason": "max_candidates", "matched": self.inner.matched()})
    }

    /// 入力（`{"action", "args", "choices"}`）を読む。`choices` は注入する選択の値である。
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
        let names = &self.model.names.actions[action];
        let args = map
            .get("args")
            .unwrap_or(&empty)
            .as_object()
            .ok_or("args はオブジェクトです")?;
        let choices = map
            .get("choices")
            .unwrap_or(&empty)
            .as_object()
            .ok_or("choices はオブジェクトです")?;
        let injected = &self.injected[action];
        if args.len() != names.params.len() || choices.len() != injected.len() {
            return Err(format!("操作 {name:?} の引数または注入する選択の個数が合いません"));
        }
        let mut values = Vec::new();
        let read = |given: &Map<String, Value>, binding: &String, index: usize| -> Result<Vec<i64>, String> {
            let v = given.get(binding).ok_or(format!("引数 {binding:?} がありません"))?;
            value_from_json(&self.model.names.enums, &names.arg_types[index], v)
                .map_err(|e| format!("引数 {binding:?}: {e}"))
        };
        for (i, param) in names.params.iter().enumerate() {
            values.extend(read(args, param, i)?);
        }
        for k in injected {
            values.extend(read(choices, &names.choices[*k], names.params.len() + k)?);
        }
        Ok((action, values))
    }

    /// 入力を、公開引数（`args`）と注入する選択（`choices`）の名前付きのJSONにする。
    fn input_json(&self, action: usize, values: &[i64]) -> Value {
        input_json(&self.model, &self.injected, action, values)
    }

    /// 直前の照合で確実に分かった状態と遷移。値は状態と引数の符号の列で、`coverage` に渡す。
    fn covered(&self) -> Value {
        let c = self.inner.covered();
        json!({
            "state": c.state,
            "transition": c.transition.as_ref().map(|(s, a, args)| json!([s, a, args])),
        })
    }

    /// 観測した値のうち、モデルが許すどの結果とも一致しない項目。
    fn mismatch(&self, possible: &[PossibleOutcome], output: SeenOutput, seen: &[Seen]) -> Vec<Value> {
        let names = &self.model.names;
        let mut fields = Vec::new();
        if let SeenOutput::Returned(y) = output {
            if !possible.iter().any(|p| p.output.map(Seen::Value) == Some(y)) {
                fields.push(json!("output"));
            }
        }
        let mut at = 0;
        for var in &self.observed {
            let range = names.state_slots(*var);
            let mine = &seen[at..at + range.len()];
            at += range.len();
            let matches = |p: &PossibleOutcome| {
                p.state
                    .get(range.clone())
                    .map(|xs| xs.iter().zip(mine).all(|(x, y)| Seen::Value(*x) == *y))
                    .unwrap_or(false)
            };
            if !possible.iter().any(matches) {
                fields.push(json!(names.states[*var]));
            }
        }
        fields
    }

    /// 初期観測を渡す。1つのセッションには1回だけ渡せる。
    pub fn start(&mut self, observation: &Value) -> Result<Value, String> {
        if self.started {
            return Err("初期観測はすでに渡しました".to_string());
        }
        let seen = self.observation(observation)?;
        self.started = true;
        let possible: Vec<PossibleOutcome> = match self.inner.start(self.model.shared(), &seen) {
            Observed::Continue => return Ok(self.continued()),
            Observed::TooManyCandidates => {
                let body = self.too_many_candidates();
                return Ok(self.answer(body));
            }
            Observed::Failure { possible } => possible,
            _ => return Err("初期観測の照合で想定しない結果になりました".to_string()),
        };
        let expected: Vec<Value> = possible
            .iter()
            .map(|p| json!({"state": self.projected(&p.state)}))
            .collect();
        let body = json!({
            "status": "conformance_failure",
            "step": 0,
            "expected": expected,
            "observed": {"state": observation},
            "mismatch": self.mismatch(&possible, SeenOutput::Unchecked, &seen),
        });
        Ok(self.answer(body))
    }

    /// 次の入力を問い合わせる。
    pub fn next_input(&mut self) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、次の入力は選べません")?;
        let body = match self.inner.next_input() {
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
        };
        Ok(self.answer(body))
    }

    /// 入力（`{"action", "args"}`）が全候補で有効かを確かめる。候補集合は変えないので、`invalid` でもセッションは続く。
    pub fn check_input(&mut self, input: &Value) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、入力は確かめられません")?;
        let (action, params) = self.input(input)?;
        let body = match self.inner.check_input(action, &params) {
            InputCheck::Valid => json!({"status": "valid"}),
            InputCheck::Invalid => json!({"status": "invalid"}),
            InputCheck::ModelError(e) => self.model_error(&e),
        };
        Ok(self.answer(body))
    }

    /// 実装の応答（`{"action", "args", "output", "observation"}`）を渡す。
    pub fn observe(&mut self, report: &Value) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、応答は渡せません")?;
        let (action, params) = self.input(report)?;
        let observation = report.get("observation").ok_or("observation が必要です")?;
        let seen = self.observation(observation)?;
        let raw_output = report.get("output");
        let output = match &self.model.names.actions[action].output {
            None => SeenOutput::Unchecked,
            Some(_) => SeenOutput::Returned(
                match raw_output.map(|v| output_value_from_json(&self.model, action, v)) {
                    Some(Ok(x)) => Seen::Value(x),
                    _ => Seen::Unrepresentable,
                },
            ),
        };
        let step = self.inner.matched() + 1;
        let before = self.inner.candidates();
        let body = match self.inner.observe(action, &params, output, &seen) {
            Observed::Continue => self.continued(),
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
            Observed::TooManyCandidates => self.too_many_candidates(),
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
                self.property_at("model_violation", &claim, &state)
            }
        };
        Ok(self.answer(body))
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
