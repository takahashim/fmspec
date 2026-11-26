//! fmspec のJSONレベルのAPI（仕様書 §3.2）。
//!
//! モデル、検査のオプション、証拠、結果を、いずれもJSONで受け渡す。
//! CLIとnative extensionは同じ関数を呼ぶので、交換形式とそのテストを共有できる。
//!
//! 結果の形式は docs/ir.md にある。オプションの誤り（未定義の名前、未知のキーなど）は `Err` で返す。

mod human;
mod report;

use fmspec_core::evidence::Evidence;
use fmspec_core::gate::decide;
use fmspec_core::semantics::Conditions;
use fmspec_ir::{certificate_from_json, certificate_to_json, default_conditions, trace_from_json, LoadError};
use fmspec_search::{check as search_check, sample, BfsOptions, SimOptions, Status};
use serde_json::{json, Map, Value};
use std::time::Instant;

pub use fmspec_ir::{load, Model};
pub use human::human;

/// 中断要求の問い合わせ。真を返したら、探索を打ち切って `inconclusive` を返す。
pub type Interrupt<'a> = Option<&'a dyn Fn() -> bool>;

const CONDITION_KEYS: [&str; 4] = ["actions", "invariants", "contracts", "deadlock"];

fn options<'a>(v: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    let map = v.as_object().ok_or("オプションはオブジェクトです")?;
    for key in map.keys() {
        if !CONDITION_KEYS.contains(&key.as_str()) && !allowed.contains(&key.as_str()) {
            return Err(format!("未知のオプション {key:?}"));
        }
    }
    Ok(map)
}

fn select(
    mask: &mut [bool],
    wanted: Option<&Value>,
    what: &str,
    find: impl Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let Some(wanted) = wanted.filter(|v| !v.is_null()) else {
        return Ok(());
    };
    let names = wanted
        .as_array()
        .ok_or_else(|| format!("{what}の指定は名前の配列です"))?;
    mask.fill(false);
    for name in names {
        let name = name.as_str().ok_or_else(|| format!("{what}の指定は名前の配列です"))?;
        match find(name) {
            Some(i) => mask[i] = true,
            None => return Err(format!("未定義の{what} {name:?}")),
        }
    }
    Ok(())
}

/// オプションから検査条件を作る。省略した項目は、すべてが対象で、デッドロック検査は無効。
fn conditions(model: &Model, map: &Map<String, Value>) -> Result<Conditions, String> {
    let deadlock = match map.get("deadlock") {
        None | Some(Value::Null) => false,
        Some(Value::Bool(b)) => *b,
        Some(_) => return Err("deadlock は真偽値です".to_string()),
    };
    let mut c = default_conditions(model, deadlock);
    select(&mut c.actions, map.get("actions"), "操作", |n| {
        model.names.action_index(n)
    })?;
    select(&mut c.invariants, map.get("invariants"), "不変条件", |n| {
        model.names.invariant_index(n)
    })?;
    select(&mut c.contracts, map.get("contracts"), "遷移契約", |n| {
        model.names.contract_index(n)
    })?;
    Ok(c)
}

fn count(map: &Map<String, Value>, key: &str, min: u64) -> Result<Option<u64>, String> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(v) => match v.as_u64() {
            Some(n) if n >= min => Ok(Some(n)),
            _ => Err(format!("{key} は{min}以上の整数です（{v}）")),
        },
    }
}

fn flag(map: &Map<String, Value>, key: &str) -> Result<bool, String> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(false),
        Some(Value::Bool(b)) => Ok(*b),
        Some(_) => Err(format!("{key} は真偽値です")),
    }
}

/// 結果をJSON文字列にする。オプションの誤りは、結果と同じ形（`status` が `usage_error`）で表す。
pub fn to_text(result: Result<Value, String>) -> String {
    match result {
        Ok(body) => body.to_string(),
        Err(message) => json!({"status": "usage_error", "message": message}).to_string(),
    }
}

/// モデルの概要。IR検証を通ったことの報告に使う。
pub fn describe(model: &Model) -> Value {
    json!({
        "status": "valid",
        "model": model.names.model,
        "model_digest": model.digest,
        "states": model.names.states.len(),
        "actions": model.names.actions.len(),
        "invariants": model.names.invariants.len(),
        "contracts": model.names.contracts.len(),
    })
}

/// IRを読み込めなかったことの報告。
pub fn load_error(e: &LoadError) -> Value {
    json!({"status": "invalid_model", "message": e.to_string()})
}

/// 幅優先探索でモデルを検査する。
///
/// オプションは、検査条件（`actions`、`invariants`、`contracts`、`deadlock`）、`max_states`、
/// `certificate`（真なら、受理された証明書を結果に含める）。
pub fn check(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["max_states", "certificate"])?;
    let cond = conditions(model, map)?;
    let max_states = count(map, "max_states", 1)?.map(|n| usize::try_from(n).unwrap_or(usize::MAX));
    let outcome = search_check(model.checked(), &cond, &BfsOptions { max_states, interrupt });
    let mut body = report::check_report(model, &cond, &outcome);
    if let (true, Evidence::Certificate(cert), Status::Verified) =
        (flag(map, "certificate")?, &outcome.evidence, outcome.status)
    {
        body["certificate"] = certificate_to_json(model, cert);
    }
    Ok(body)
}

/// ランダムシミュレーションでモデルを検査する。
///
/// オプションは、検査条件、`seed`（既定は0）、`traces`（既定は100）、`max_steps`（既定は100）。
pub fn simulate(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["seed", "traces", "max_steps"])?;
    let cond = conditions(model, map)?;
    let seed = count(map, "seed", 0)?.unwrap_or(0);
    let traces = count(map, "traces", 1)?.unwrap_or(100);
    let max_steps = count(map, "max_steps", 0)?.unwrap_or(100);
    let sim = SimOptions {
        seed,
        traces: usize::try_from(traces).unwrap_or(usize::MAX),
        max_steps: usize::try_from(max_steps).unwrap_or(usize::MAX),
        interrupt,
    };
    let started = Instant::now();
    let sampled = sample(model.checked(), &cond, &sim);
    Ok(report::simulation_report(
        model,
        &cond,
        &sim,
        &sampled,
        started.elapsed(),
    ))
}

/// 提示された証明書を、オプションの検査条件で検査する。
pub fn verify_certificate(model: &Model, certificate: &str, opts: &Value) -> Result<Value, String> {
    let map = options(opts, &[])?;
    let cond = conditions(model, map)?;
    let cert = match certificate_from_json(model, certificate) {
        Ok(cert) => cert,
        Err(e) => return Ok(report::unreadable_evidence(model, &e.to_string())),
    };
    let evidence = Evidence::Certificate(cert);
    let verdict = decide(model.checked(), &cond, &evidence);
    Ok(report::evidence_report(model, &cond, &evidence, &verdict))
}

/// 提示されたトレースを、トレースに記録された検査条件で再生する。
pub fn replay(model: &Model, trace: &str) -> Value {
    let trace = match trace_from_json(model, trace) {
        Ok(trace) => trace,
        Err(e) => return report::unreadable_evidence(model, &e.to_string()),
    };
    let cond = trace.conditions.clone();
    let evidence = Evidence::Trace(trace.steps, trace.claim);
    let verdict = decide(model.checked(), &cond, &evidence);
    report::evidence_report(model, &cond, &evidence, &verdict)
}
