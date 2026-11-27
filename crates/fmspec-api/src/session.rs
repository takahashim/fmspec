//! Model-Based Testing のセッションのJSONレベルのAPI（仕様書 §11.4）。
//!
//! Ruby 側のドライバが `setup`、`command`、`observe` を実行し、その結果の値だけをここに渡す。
//! セッションは Ruby のコードを呼び出さない。
//!
//! `Session` は照合の進み具合（`fmspec_search::Session` と、始まったか、終わったか）だけを持ち、
//! 入力、観測、応答のJSONの読み書きは `Wire` に任せる。

use crate::inject::{inject_slots, input_json, parse_inject, parse_input};
use crate::options::{conditions, count, indices, options_only, size};
use fmspec_core::evidence::Claim;
use fmspec_ir::{
    claim_to_json, output_to_json, output_value_from_json, state_to_json, value_from_json, value_to_json, Model,
};
use fmspec_search::{InputCheck, ModelError, NextInput, Observed, PossibleOutcome, Seen, SeenOutput};
use serde_json::{json, Map, Value};
use std::sync::Arc;

/// 候補数の上限の既定値。
const DEFAULT_MAX_CANDIDATES: u64 = 10_000;

/// 終わったセッションへの問い合わせの誤り。
const FINISHED: &str = "セッションは終わっています";

/// 応答のあとで照合を続けるか。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Flow {
    /// 続ける。候補集合を変えずに入力を退けただけの応答（`invalid`、`invalid_input`）も含む。
    Continue,
    /// 終える（不適合、未完了、モデルの誤り、入力の終わりなど）。
    Finish,
}

/// 応答の本体と、そのあとで照合を続けるか。
type Reply = (Value, Flow);

/// 観測した値を、状態変数のスロットごとの値にする。型の符号にできなければ、すべてのスロットを一致しない値とする。
fn seen(model: &Model, var: usize, v: Option<&Value>) -> Vec<Seen> {
    let names = &model.names;
    let ty = &names.state_types[var];
    match v.map(|v| value_from_json(&names.enums, ty, v)) {
        Some(Ok(codes)) => codes.into_iter().map(Seen::Value).collect(),
        _ => vec![Seen::Unrepresentable; ty.width(&names.enums)],
    }
}

/// 読んだ観測。応答に、渡されたJSONをそのまま示すため、元のJSONも持つ。
struct Observation<'a> {
    /// 観測のJSON（状態変数名から値へのオブジェクト）。
    state: &'a Value,
    /// 観測する状態変数のスロットごとの値。
    seen: Vec<Seen>,
    /// 操作の出力。初期観測と、出力のない操作では `Unchecked`。
    output: SeenOutput,
    /// 渡された出力のJSON。
    raw_output: Option<&'a Value>,
}

/// 照合した入力。不適合の応答に示す。
struct Step<'a> {
    action: usize,
    params: &'a [i64],
    /// 照合する前の候補の数。
    candidates: usize,
}

/// セッションのJSONの読み書き。モデル、観測する状態変数、注入する内部選択だけで決まり、照合の状態は持たない。
struct Wire {
    model: Arc<Model>,
    /// 観測する状態変数（指定の順）。
    observed: Vec<usize>,
    /// 操作ごとの、注入する内部選択の添字（`choices` の中での添字、昇順）。
    injected: Vec<Vec<usize>>,
}

impl Wire {
    /// `observe`（観測する状態変数の名前。省略時はすべて）と `inject` のオプションを読む。
    fn new(model: Arc<Model>, map: &Map<String, Value>) -> Result<Wire, String> {
        let names = &model.names;
        let observed = match map.get("observe") {
            None | Some(Value::Null) => (0..names.states.len()).collect(),
            // 観測の順は、指定の順に保つ（不一致の項目 `mismatch` の順になる）。
            Some(v) => indices(
                v,
                "状態変数",
                || format!("observe は状態変数の名前の配列です（{v}）"),
                |n| names.state_index(n),
            )?,
        };
        let injected = parse_inject(&model, map.get("inject"))?;
        Ok(Wire {
            model,
            observed,
            injected,
        })
    }

    /// 観測する状態変数のスロット（観測の値の並び）。
    fn observed_slots(&self) -> Vec<usize> {
        self.observed
            .iter()
            .flat_map(|v| self.model.names.state_slots(*v))
            .collect()
    }

    /// 注入する内部選択の、引数の列での添字。
    fn inject_slots(&self) -> Vec<Vec<usize>> {
        inject_slots(&self.model, &self.injected)
    }

    /// 観測のJSON（状態変数名から値へのオブジェクト）を読む。観測する変数が欠けていれば `Err`。
    fn observation<'a>(&self, v: &'a Value) -> Result<Observation<'a>, String> {
        let map = v.as_object().ok_or("observation はオブジェクトです")?;
        let mut seen_values = Vec::new();
        for var in &self.observed {
            let name = &self.model.names.states[*var];
            if !map.contains_key(name) {
                return Err(format!("observation に状態変数 {name:?} がありません"));
            }
            seen_values.extend(seen(&self.model, *var, map.get(name)));
        }
        Ok(Observation {
            state: v,
            seen: seen_values,
            output: SeenOutput::Unchecked,
            raw_output: None,
        })
    }

    /// 実装の応答（`{"action", "args", "output", "observation"}`）の、出力と観測を読む。
    fn response<'a>(&self, action: usize, report: &'a Value) -> Result<Observation<'a>, String> {
        let state = report.get("observation").ok_or("observation が必要です")?;
        let mut observed = self.observation(state)?;
        observed.raw_output = report.get("output");
        if self.model.names.actions[action].output.is_some() {
            observed.output = SeenOutput::Returned(
                match observed
                    .raw_output
                    .map(|v| output_value_from_json(&self.model, action, v))
                {
                    Some(Ok(x)) => Seen::Value(x),
                    _ => Seen::Unrepresentable,
                },
            );
        }
        Ok(observed)
    }

    /// 入力（`{"action", "args", "choices"}`）を読む。
    fn input(&self, v: &Value) -> Result<(usize, Vec<i64>), String> {
        parse_input(&self.model, &self.injected, v)
    }

    /// 入力を、公開引数（`args`）と注入する選択（`choices`）の名前付きのJSONにする。
    fn input_json(&self, action: usize, values: &[i64]) -> Value {
        input_json(&self.model, &self.injected, action, values)
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

    fn model_violation(&self, invariant: bool, index: usize, state: &[i64]) -> Value {
        let claim = if invariant {
            Claim::Invariant(index)
        } else {
            Claim::Contract(index)
        };
        self.property_at("model_violation", &claim, state)
    }

    /// 観測した値のうち、モデルが許すどの結果とも一致しない項目。
    fn mismatch(&self, possible: &[PossibleOutcome], observed: &Observation) -> Vec<Value> {
        let names = &self.model.names;
        let mut fields = Vec::new();
        if let SeenOutput::Returned(y) = observed.output {
            if !possible.iter().any(|p| p.output.map(Seen::Value) == Some(y)) {
                fields.push(json!("output"));
            }
        }
        let mut at = 0;
        for var in &self.observed {
            let range = names.state_slots(*var);
            let mine = &observed.seen[at..at + range.len()];
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

    /// 不適合（`conformance_failure`）の応答。`step` は照合したステップの番号（初期観測は0で、`input` はない）。
    /// `expected` はモデルが許す結果を観測する項目に写したもので、重複を除く。
    fn conformance_failure(
        &self,
        step: usize,
        input: Option<Step>,
        possible: &[PossibleOutcome],
        observed: &Observation,
    ) -> Value {
        let checks_output = observed.output != SeenOutput::Unchecked;
        let mut expected: Vec<Value> = Vec::new();
        for p in possible {
            let mut entry = json!({"state": self.projected(&p.state)});
            if let (true, Some(input)) = (checks_output, &input) {
                entry["output"] = output_to_json(&self.model, input.action, p.output);
            }
            if !expected.contains(&entry) {
                expected.push(entry);
            }
        }
        let mut seen_json = json!({"state": observed.state});
        if checks_output {
            seen_json["output"] = observed.raw_output.cloned().unwrap_or(Value::Null);
        }
        let mut body = match &input {
            Some(input) => {
                let mut body = self.input_json(input.action, input.params);
                body["candidates"] = json!(input.candidates);
                body
            }
            None => json!({}),
        };
        body["status"] = json!("conformance_failure");
        body["step"] = json!(step);
        body["expected"] = json!(expected);
        body["observed"] = seen_json;
        body["mismatch"] = json!(self.mismatch(possible, observed));
        body
    }
}

pub struct Session {
    wire: Wire,
    inner: fmspec_search::Session,
    /// 初期観測を受け取ったか。
    started: bool,
    /// 照合を続けない応答（`Flow::Finish`）を返したか。
    /// 返したあとの問い合わせは誤りにする。誤った要求（`Err`）では終わらない。
    finished: bool,
}

impl Session {
    /// セッションを作る。
    ///
    /// オプションは、検査条件（`actions`、`invariants`、`contracts`）、`seed`、
    /// `observe`（観測する状態変数の名前。省略時はすべて）、
    /// `inject`（操作名から、注入する内部選択の名前の配列へのオブジェクト）、`max_candidates`。
    /// 照合はデッドロックを検査しないので、`deadlock` は受け付けない。
    pub fn new(model: Arc<Model>, opts: &Value) -> Result<Session, String> {
        let map = options_only(
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
        let wire = Wire::new(model, map)?;
        let inner = fmspec_search::Session::new(cond, wire.observed_slots(), wire.inject_slots(), seed, size(max));
        Ok(Session {
            wire,
            inner,
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
    fn answer(&mut self, (body, flow): Reply) -> Value {
        if flow == Flow::Finish {
            self.finished = true;
        }
        body
    }

    /// 照合が続くことの応答。
    fn continued(&self) -> Reply {
        let covered = self.inner.covered();
        let body = json!({
            "status": "continue",
            "candidates": self.inner.candidates(),
            "matched": self.inner.matched(),
            // 直前の照合で確実に分かった状態と遷移。値は状態と引数の符号の列で、`coverage` に渡す。
            "covered": {
                "state": covered.state,
                "transition": covered.transition.as_ref().map(|(s, a, args)| json!([s, a, args])),
            },
        });
        (body, Flow::Continue)
    }

    /// 候補数が上限を超えたことの応答。
    fn too_many_candidates(&self) -> Reply {
        let body = json!({"status": "inconclusive", "reason": "max_candidates", "matched": self.inner.matched()});
        (body, Flow::Finish)
    }

    /// 初期観測を渡す。1つのセッションには1回だけ渡せる。
    pub fn start(&mut self, observation: &Value) -> Result<Value, String> {
        if self.started {
            return Err("初期観測はすでに渡しました".to_string());
        }
        let observed = self.wire.observation(observation)?;
        self.started = true;
        let reply = match self.inner.start(self.wire.model.shared(), &observed.seen) {
            Observed::Continue => self.continued(),
            Observed::TooManyCandidates => self.too_many_candidates(),
            Observed::Failure { possible } => (
                self.wire.conformance_failure(0, None, &possible, &observed),
                Flow::Finish,
            ),
            _ => return Err("初期観測の照合で想定しない結果になりました".to_string()),
        };
        Ok(self.answer(reply))
    }

    /// 次の入力を問い合わせる。
    pub fn next_input(&mut self) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、次の入力は選べません")?;
        let reply = match self.inner.next_input() {
            NextInput::Input { action, params } => {
                let mut body = self.wire.input_json(action, &params);
                body["status"] = json!("input");
                (body, Flow::Continue)
            }
            NextInput::End => (json!({"status": "end", "matched": self.inner.matched()}), Flow::Finish),
            NextInput::NoCommonInput => {
                let body = json!({
                    "status": "inconclusive",
                    "reason": "no_common_input",
                    "candidates": self.inner.candidates(),
                    "matched": self.inner.matched(),
                });
                (body, Flow::Finish)
            }
            NextInput::ModelError(e) => (self.wire.model_error(&e), Flow::Finish),
        };
        Ok(self.answer(reply))
    }

    /// 入力（`{"action", "args"}`）が全候補で有効かを確かめる。候補集合は変えないので、`invalid` でもセッションは続く。
    pub fn check_input(&mut self, input: &Value) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、入力は確かめられません")?;
        let (action, params) = self.wire.input(input)?;
        let reply = match self.inner.check_input(action, &params) {
            InputCheck::Valid => (json!({"status": "valid"}), Flow::Continue),
            InputCheck::Invalid => (json!({"status": "invalid"}), Flow::Continue),
            InputCheck::ModelError(e) => (self.wire.model_error(&e), Flow::Finish),
        };
        Ok(self.answer(reply))
    }

    /// 実装の応答（`{"action", "args", "output", "observation"}`）を渡す。
    pub fn observe(&mut self, report: &Value) -> Result<Value, String> {
        self.going_on("初期観測を渡す前に、応答は渡せません")?;
        let (action, params) = self.wire.input(report)?;
        let observed = self.wire.response(action, report)?;
        let step = self.inner.matched() + 1;
        let before = self.inner.candidates();
        let reply = match self.inner.observe(action, &params, observed.output, &observed.seen) {
            Observed::Continue => self.continued(),
            Observed::Failure { possible } => {
                let input = Step {
                    action,
                    params: &params,
                    candidates: before,
                };
                (
                    self.wire.conformance_failure(step, Some(input), &possible, &observed),
                    Flow::Finish,
                )
            }
            Observed::InvalidInput => (json!({"status": "invalid_input"}), Flow::Continue),
            Observed::TooManyCandidates => self.too_many_candidates(),
            Observed::ModelError(e) => (self.wire.model_error(&e), Flow::Finish),
            Observed::ModelViolation {
                invariant,
                index,
                state,
            } => (self.wire.model_violation(invariant, index, &state), Flow::Finish),
        };
        Ok(self.answer(reply))
    }

    /// 現在の候補の状態。診断とテストに使う。
    pub fn candidates(&self) -> Value {
        json!(self
            .inner
            .candidate_states()
            .map(|s| state_to_json(&self.wire.model, s))
            .collect::<Vec<_>>())
    }
}
