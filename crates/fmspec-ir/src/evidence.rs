//! 証明書とトレースのJSON表現（仕様書 §10、§14.2）。

use crate::conditions::{conditions_from_json, conditions_to_json};
use crate::model::Model;
use crate::value::{
    args_from_json, args_to_json, core_type_to_json, output_from_json, output_to_json, state_from_json, state_to_json,
    value_from_json, value_to_json,
};
use crate::{CERTIFICATE_VERSION, ENGINE_VERSION, TRACE_VERSION};
use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, TraceStep};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Site;
use serde_json::{json, Map, Value};
use std::fmt;

/// 証明書やトレースのファイルを読めなかった理由。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceError {
    Json(String),
    Format(String),
    /// 別のモデルに対して作成された。
    DigestMismatch {
        expected: String,
        found: String,
    },
    /// 別のモデルに対する証拠を、指定により読もうとしたが、このモデルでは読めなかった。
    /// `found` は証拠の digest、`error` は読めなかった理由（`Format`）。
    OtherModel {
        found: String,
        error: Box<TraceError>,
    },
}

impl fmt::Display for TraceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TraceError::Json(message) => write!(f, "JSONとして読めません: {message}"),
            TraceError::Format(message) => write!(f, "{message}"),
            TraceError::DigestMismatch { expected, found } => {
                write!(
                    f,
                    "別のモデルに対する証拠です（モデルのdigestは {expected}、証拠のdigestは {found}）"
                )
            }
            TraceError::OtherModel { found, error } => {
                write!(
                    f,
                    "別のモデル（証拠のdigestは {found}）に対する証拠を、このモデルでは読めません: {error}"
                )
            }
        }
    }
}

fn format<T>(message: impl Into<String>) -> Result<T, TraceError> {
    Err(TraceError::Format(message.into()))
}

/// 読み込んだ証拠。`other_model_digest` は、証拠が別のモデルに対するもので、指定により読んだときの、証拠の digest である。
#[derive(Clone, Debug)]
pub struct Loaded<T> {
    pub evidence: T,
    pub other_model_digest: Option<String>,
}

/// 証拠の版と digest を確かめる。digest が違えば、`allow_other_model` が真のときだけ読み進め、証拠の digest を返す。
fn header<'a>(
    json: &'a Value,
    model: &Model,
    version_key: &str,
    version: i64,
    allow_other_model: bool,
) -> Result<(&'a Map<String, Value>, Option<String>), TraceError> {
    let map = match json.as_object() {
        Some(map) => map,
        None => return format("オブジェクトが必要です"),
    };
    if map.get(version_key).and_then(Value::as_i64) != Some(version) {
        return format(format!("未対応の {version_key} です（対応しているのは {version}）"));
    }
    let Some(found) = map.get("model_digest").and_then(Value::as_str) else {
        return format("model_digest（文字列）が必要です");
    };
    if found == model.digest {
        return Ok((map, None));
    }
    if !allow_other_model {
        return Err(TraceError::DigestMismatch {
            expected: model.digest.clone(),
            found: found.to_string(),
        });
    }
    Ok((map, Some(found.to_string())))
}

/// 本体を読み、別のモデルに対する証拠なら、読めなかった理由にそのことを添える。
fn loaded<T>(other: Option<String>, body: impl FnOnce() -> Result<T, TraceError>) -> Result<Loaded<T>, TraceError> {
    match (body(), other) {
        (Ok(evidence), other_model_digest) => Ok(Loaded {
            evidence,
            other_model_digest,
        }),
        (Err(error), Some(found)) => Err(TraceError::OtherModel {
            found,
            error: Box::new(error),
        }),
        (Err(error), None) => Err(error),
    }
}

fn conditions_of(map: &Map<String, Value>, model: &Model) -> Result<Conditions, TraceError> {
    match map.get("conditions") {
        Some(c) => conditions_from_json(&model.names, c).map_err(TraceError::Format),
        None => format("conditions が必要です"),
    }
}

pub fn certificate_to_json(model: &Model, cert: &Certificate) -> Value {
    let states: Vec<Value> = cert
        .states
        .iter()
        .map(|s| {
            let names = &model.names;
            let row: Vec<Value> = names
                .state_types
                .iter()
                .enumerate()
                .map(|(i, ty)| value_to_json(names, ty, s.get(names.state_slots(i)).unwrap_or(&[])))
                .collect();
            Value::Array(row)
        })
        .collect();
    json!({
        "certificate_version": CERTIFICATE_VERSION,
        "model_digest": model.digest,
        "engine_version": ENGINE_VERSION,
        "conditions": conditions_to_json(&model.names, &cert.conditions),
        "states": states,
    })
}

/// 証明書を読む。状態は符号化列の辞書順に整列する。
/// 整列はここ（未検証）で行うが、証明書は判定ゲートが検査するので、誤りがあっても誤って受理されることはない。
pub fn certificate_from_json(model: &Model, json: &str) -> Result<Certificate, TraceError> {
    read_certificate(model, json, false).map(|l| l.evidence)
}

/// 証明書を読む。`allow_other_model` が真なら、`model_digest` が違う証明書も、このモデルの名前と型で読む。
pub fn read_certificate(model: &Model, json: &str, allow_other_model: bool) -> Result<Loaded<Certificate>, TraceError> {
    let root: Value = serde_json::from_str(json).map_err(|e| TraceError::Json(e.to_string()))?;
    let (map, other) = header(
        &root,
        model,
        "certificate_version",
        CERTIFICATE_VERSION,
        allow_other_model,
    )?;
    loaded(other, || certificate_body(model, map))
}

fn certificate_body(model: &Model, map: &Map<String, Value>) -> Result<Certificate, TraceError> {
    let conditions = conditions_of(map, model)?;
    let Some(rows) = map.get("states").and_then(Value::as_array) else {
        return format("states は状態の配列です");
    };
    let types = &model.names.state_types;
    let mut states = Vec::new();
    for (k, row) in rows.iter().enumerate() {
        let Some(row) = row.as_array() else {
            return format(format!("states[{k}] は値の配列です"));
        };
        if row.len() != types.len() {
            return format(format!("states[{k}] の値の個数が状態変数の個数と合いません"));
        }
        let mut state = Vec::new();
        for (v, ty) in row.iter().zip(types.iter()) {
            match value_from_json(&model.names.enums, ty, v) {
                Ok(x) => state.extend(x),
                Err(e) => return format(format!("states[{k}]: {e}")),
            }
        }
        states.push(state);
    }
    states.sort();
    states.dedup();
    Ok(Certificate { conditions, states })
}

/// トレース。開始状態、操作列、各ステップの出力と状態、末尾で起きる事象の主張、検査条件を持つ。
#[derive(Clone, Debug)]
pub struct Trace {
    pub conditions: Conditions,
    pub start: Vec<i64>,
    pub steps: Vec<TraceStep>,
    pub claim: Claim,
    pub seed: Option<u64>,
}

/// 評価エラーのJSON。範囲外更新には、値と、対象の型を付ける。
pub fn error_to_json(model: &Model, kind: &ErrKind, ty: Option<&fmspec_core::model::Type>) -> Value {
    match kind {
        ErrKind::Overflow => json!({"kind": "overflow"}),
        ErrKind::TypeMismatch => json!({"kind": "type_mismatch"}),
        ErrKind::Unbound => json!({"kind": "unbound"}),
        ErrKind::OutOfRange(x) => match ty {
            Some(ty) => json!({"kind": "out_of_range", "value": x, "type": core_type_to_json(&model.names, ty)}),
            None => json!({"kind": "out_of_range", "value": x}),
        },
        ErrKind::DivByZero => json!({"kind": "division_by_zero"}),
        ErrKind::Failed(code) => match failure_name(*code) {
            Some(name) => json!({"kind": name}),
            None => json!({"kind": "failed", "code": code}),
        },
    }
}

/// `Expr::Fail` の番号と、その名前。番号はIRの下ろし方が決める。
const FAILURES: [(i64, &str); 6] = [
    (fmspec_core::source::FAIL_NONE, "none"),
    (fmspec_core::source::FAIL_MISSING_KEY, "missing_key"),
    (fmspec_core::source::FAIL_INDEX, "index_out_of_range"),
    (fmspec_core::source::FAIL_FULL, "full"),
    (fmspec_core::source::FAIL_EMPTY, "empty"),
    (fmspec_core::source::FAIL_NOT_IN_DOMAIN, "not_in_domain"),
];

fn failure_name(code: i64) -> Option<&'static str> {
    FAILURES.iter().find(|(c, _)| *c == code).map(|(_, n)| *n)
}

fn error_from_json(v: Option<&Value>) -> Result<ErrKind, TraceError> {
    let Some(map) = v.and_then(Value::as_object) else {
        return format("claim.error はオブジェクトです");
    };
    match map.get("kind").and_then(Value::as_str) {
        Some("overflow") => Ok(ErrKind::Overflow),
        Some("type_mismatch") => Ok(ErrKind::TypeMismatch),
        Some("unbound") => Ok(ErrKind::Unbound),
        Some("out_of_range") => match map.get("value").and_then(Value::as_i64) {
            Some(x) => Ok(ErrKind::OutOfRange(x)),
            None => format("claim.error.value は整数です"),
        },
        Some("division_by_zero") => Ok(ErrKind::DivByZero),
        Some("failed") => match map.get("code").and_then(Value::as_i64) {
            Some(code) => Ok(ErrKind::Failed(code)),
            None => format("claim.error.code は整数です"),
        },
        Some(name) => match FAILURES.iter().find(|(_, n)| *n == name) {
            Some((code, _)) => Ok(ErrKind::Failed(*code)),
            None => format("claim.error.kind が不正です"),
        },
        None => format("claim.error.kind が不正です"),
    }
}

fn name_of(names: &[String], i: usize) -> Value {
    match names.get(i) {
        Some(n) => json!(n),
        None => json!(i),
    }
}

pub fn claim_to_json(model: &Model, claim: &Claim) -> Value {
    let names = &model.names;
    match claim {
        Claim::Invariant(i) => json!({"violation": "invariant", "name": name_of(&names.invariants, *i)}),
        Claim::Contract(k) => json!({"violation": "contract", "name": name_of(&names.contracts, *k)}),
        Claim::Deadlock => json!({"violation": "deadlock"}),
        Claim::InvariantError(i, e) => {
            json!({"error": error_to_json(model, e, None), "site": "invariant", "name": name_of(&names.invariants, *i)})
        }
        Claim::ContractError(k, e) => {
            json!({"error": error_to_json(model, e, None), "site": "contract", "name": name_of(&names.contracts, *k)})
        }
        Claim::TerminalError(e) => json!({"error": error_to_json(model, e, None), "site": "terminal"}),
        Claim::StepError(a, args, site, e) => {
            let (params, choices) = args_to_json(model, *a, args);
            let act = model.raw().actions.get(*a);
            let mut out = json!({
                "action": names.actions.get(*a).map(|n| n.name.as_str()).unwrap_or("?"),
                "args": params,
                "choices": choices,
            });
            let (site_name, ty) = match site {
                Site::Guard => ("guard", None),
                Site::Output => ("output", act.and_then(|a| a.output.as_ref()).map(|o| &o.ty)),
                Site::Update(u) => {
                    let owner = names.actions.get(*a).and_then(|n| n.updates.get(*u));
                    // 評価の失敗は、どのスロットでも同じ（最初のスロットで起きる）なので、
                    // スロットは範囲外更新にだけ付ける。
                    if let Some(o) = owner {
                        out["target"] = name_of(&names.states, o.var);
                        let wide = names.state_types.get(o.var).map(|t| t.width(&names.enums)).unwrap_or(1) > 1;
                        if wide && matches!(e, ErrKind::OutOfRange(_)) {
                            out["slot"] = json!(o.slot);
                        }
                    }
                    let target = act.and_then(|a| a.updates.get(*u)).map(|up| up.target);
                    ("update", target.and_then(|t| model.raw().state_types.get(t)))
                }
            };
            out["site"] = json!(site_name);
            out["error"] = error_to_json(model, e, ty);
            out
        }
    }
}

fn claim_from_json(model: &Model, v: Option<&Value>) -> Result<Claim, TraceError> {
    let Some(map) = v.and_then(Value::as_object) else {
        return format("claim はオブジェクトです");
    };
    let names = &model.names;
    let name = || map.get("name").and_then(Value::as_str).unwrap_or("");
    let invariant = || match names.invariant_index(name()) {
        Some(i) => Ok(i),
        None => format(format!("claim: 未定義の不変条件 {:?}", name())),
    };
    let contract = || match names.contract_index(name()) {
        Some(k) => Ok(k),
        None => format(format!("claim: 未定義の遷移契約 {:?}", name())),
    };
    if let Some(kind) = map.get("violation").and_then(Value::as_str) {
        return match kind {
            "invariant" => Ok(Claim::Invariant(invariant()?)),
            "contract" => Ok(Claim::Contract(contract()?)),
            "deadlock" => Ok(Claim::Deadlock),
            _ => format("claim.violation が不正です"),
        };
    }
    let kind = error_from_json(map.get("error"))?;
    match map.get("site").and_then(Value::as_str) {
        Some("invariant") => Ok(Claim::InvariantError(invariant()?, kind)),
        Some("contract") => Ok(Claim::ContractError(contract()?, kind)),
        Some("terminal") => Ok(Claim::TerminalError(kind)),
        Some(site @ ("guard" | "update" | "output")) => {
            let action_name = map.get("action").and_then(Value::as_str).unwrap_or("");
            let Some(a) = names.action_index(action_name) else {
                return format(format!("claim: 未定義の操作 {action_name:?}"));
            };
            let empty = json!({});
            let args = args_from_json(
                model,
                a,
                map.get("args").unwrap_or(&empty),
                map.get("choices").unwrap_or(&empty),
            )
            .map_err(TraceError::Format)?;
            let site = match site {
                "guard" => Site::Guard,
                "output" => Site::Output,
                _ => {
                    let target = map.get("target").and_then(Value::as_str).unwrap_or("");
                    // slot は範囲外更新にだけ付く。省略すると状態変数の最初のスロットとする。
                    let slot = match map.get("slot") {
                        None => 0,
                        Some(v) => match v.as_u64().and_then(|n| usize::try_from(n).ok()) {
                            Some(slot) => slot,
                            None => return format("claim.slot は0以上の整数です"),
                        },
                    };
                    let index = names.state_index(target);
                    let update = index.and_then(|t| {
                        names.actions[a]
                            .updates
                            .iter()
                            .position(|o| o.var == t && o.slot == slot)
                    });
                    match update {
                        Some(u) => Site::Update(u),
                        None => return format(format!("claim: 操作 {action_name:?} は {target:?} を更新しません")),
                    }
                }
            };
            Ok(Claim::StepError(a, args, site, kind))
        }
        _ => format("claim.site が不正です"),
    }
}

pub fn trace_to_json(model: &Model, trace: &Trace) -> Value {
    let steps: Vec<Value> = trace
        .steps
        .iter()
        .map(|st| {
            let (params, choices) = args_to_json(model, st.action, &st.args);
            json!({
                "action": model.names.actions.get(st.action).map(|n| n.name.as_str()).unwrap_or("?"),
                "args": params,
                "choices": choices,
                "output": output_to_json(model, st.action, st.output),
                "state": state_to_json(model, &st.state),
            })
        })
        .collect();
    json!({
        "trace_version": TRACE_VERSION,
        "model_digest": model.digest,
        "engine_version": ENGINE_VERSION,
        "seed": trace.seed,
        "conditions": conditions_to_json(&model.names, &trace.conditions),
        "initial": state_to_json(model, &trace.start),
        "steps": steps,
        "claim": claim_to_json(model, &trace.claim),
    })
}

pub fn trace_from_json(model: &Model, json: &str) -> Result<Trace, TraceError> {
    read_trace(model, json, false).map(|l| l.evidence)
}

/// トレースを読む。`allow_other_model` が真なら、`model_digest` が違うトレースも、このモデルの名前と型で読む。
pub fn read_trace(model: &Model, json: &str, allow_other_model: bool) -> Result<Loaded<Trace>, TraceError> {
    let root: Value = serde_json::from_str(json).map_err(|e| TraceError::Json(e.to_string()))?;
    let (map, other) = header(&root, model, "trace_version", TRACE_VERSION, allow_other_model)?;
    loaded(other, || trace_body(model, map))
}

fn trace_body(model: &Model, map: &Map<String, Value>) -> Result<Trace, TraceError> {
    let conditions = conditions_of(map, model)?;
    // 開始状態が初期状態の1つであることは、判定ゲートが検査する。
    // 初期状態が1つのモデルでは、initial を省略できる。
    let inits = model.checked().initials();
    let start = match map.get("initial") {
        Some(initial) => state_from_json(model, initial).map_err(|e| TraceError::Format(format!("initial: {e}")))?,
        None if inits.len() == 1 => inits[0].clone(),
        None => return format("初期状態が複数あるモデルでは initial が必要です"),
    };
    let Some(rows) = map.get("steps").and_then(Value::as_array) else {
        return format("steps はステップの配列です");
    };
    let mut steps = Vec::new();
    let empty = json!({});
    for (k, row) in rows.iter().enumerate() {
        let at = |e: String| TraceError::Format(format!("steps[{k}]: {e}"));
        let Some(row) = row.as_object() else {
            return format(format!("steps[{k}] はオブジェクトです"));
        };
        let name = row.get("action").and_then(Value::as_str).unwrap_or("");
        let Some(action) = model.names.action_index(name) else {
            return format(format!("steps[{k}]: 未定義の操作 {name:?}"));
        };
        let args = args_from_json(
            model,
            action,
            row.get("args").unwrap_or(&empty),
            row.get("choices").unwrap_or(&empty),
        )
        .map_err(at)?;
        let output = match row.get("output") {
            Some(o) => output_from_json(model, action, o).map_err(at)?,
            None => return format(format!("steps[{k}]: output が必要です")),
        };
        let state = match row.get("state") {
            Some(s) => state_from_json(model, s).map_err(at)?,
            None => return format(format!("steps[{k}]: state が必要です")),
        };
        steps.push(TraceStep {
            action,
            args,
            output,
            state,
        });
    }
    let claim = claim_from_json(model, map.get("claim"))?;
    // seed は表示と記録のためのもので、再生には使わない。省略と null は、seed なしとする。
    let seed = match map.get("seed") {
        None | Some(Value::Null) => None,
        Some(v) => match v.as_u64() {
            Some(seed) => Some(seed),
            None => return format("seed は null か0以上の整数です"),
        },
    };
    Ok(Trace {
        conditions,
        start,
        steps,
        claim,
        seed,
    })
}
