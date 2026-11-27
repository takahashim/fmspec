//! fmspec のJSONレベルのAPI（仕様書 §3.2）。
//!
//! モデル、検査のオプション、証拠、結果を、いずれもJSONで受け渡す。
//! CLIとnative extensionは同じ関数を呼ぶので、交換形式とそのテストを共有できる。
//!
//! 結果の形式は docs/ir.md にある。オプションの誤り（未定義の名前、未知のキーなど）は `Err` で返す。

mod coverage;
mod human;
mod inject;
mod options;
mod report;
mod session;

use fmspec_core::evidence::Evidence;
use fmspec_core::gate::decide;
use fmspec_core::gate::VerdictKind;
use fmspec_ir::{certificate_to_json, read_certificate, read_trace, LoadError, TraceError};
use fmspec_search::{
    check as search_check, judge, sample, shrink as search_shrink, BfsOptions, GateOptions, SimOptions, Status,
};
use options::{conditions, count, deadline, flag, keys, max_states, options, size};
use serde_json::{json, Value};
use std::time::Instant;

pub use coverage::{coverage, test_paths};
pub use fmspec_ir::{load, Model};
pub use human::human;
pub use session::Session;

/// 中断要求の問い合わせ。真を返したら、探索か証明書の検査を打ち切って `inconclusive` を返す。
pub type Interrupt<'a> = Option<&'a dyn Fn() -> bool>;

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
/// `max_depth`（深さ、つまり初期状態からの遷移数の上限）、`max_time_ms`（探索と証拠の検査の時間の上限）、
/// `max_check_cost`（判定ゲートが証拠の検査にかける評価回数の上限）、
/// `certificate`（真なら、受理された証明書を結果に含める）。
pub fn check(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(
        opts,
        &[
            "max_states",
            "max_depth",
            "max_time_ms",
            "max_check_cost",
            "certificate",
        ],
    )?;
    let cond = conditions(model, map)?;
    let opts = BfsOptions {
        max_states: max_states(map)?,
        interrupt,
        max_check_cost: count(map, "max_check_cost", 0)?,
        max_depth: count(map, "max_depth", 0)?.map(size),
        deadline: deadline(map)?,
    };
    let outcome = search_check(model.checked(), &cond, &opts);
    let mut body = report::check_report(model, &cond, &outcome);
    if let (true, Evidence::Certificate(cert), Status::Verified) =
        (flag(map, "certificate")?, &outcome.evidence, &outcome.status)
    {
        body["certificate"] = certificate_to_json(model, cert);
    }
    Ok(body)
}

/// ランダムシミュレーションでモデルを検査する。
///
/// オプションは、検査条件、`seed`（既定は0）、`traces`（既定は100）、`max_steps`（既定は100）、`max_time_ms`。
pub fn simulate(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["seed", "traces", "max_steps", "max_time_ms"])?;
    let cond = conditions(model, map)?;
    let seed = count(map, "seed", 0)?.unwrap_or(0);
    let traces = count(map, "traces", 1)?.unwrap_or(100);
    let max_steps = count(map, "max_steps", 0)?.unwrap_or(100);
    let sim = SimOptions {
        seed,
        traces: size(traces),
        max_steps: size(max_steps),
        interrupt,
        deadline: deadline(map)?,
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

/// 別のモデルに対する証拠を読むことを許すオプション（仕様書 §10）。
const ALLOW_OTHER_MODEL: &str = "allow_other_model";

/// 読めなかった証拠の報告。別のモデルに対する証拠なら、その digest を `evidence_model_digest` に記録する。
fn unreadable(model: &Model, e: &TraceError) -> Value {
    let mut body = report::unreadable_evidence(model, &e.to_string());
    if let TraceError::OtherModel { found, .. } = e {
        body["evidence_model_digest"] = json!(found);
    }
    body
}

/// 別のモデルに対する証拠を指定により読んだなら、その digest を結果に記録する。
fn mark_other_model(mut body: Value, other: Option<String>) -> Value {
    if let Some(found) = other {
        body["evidence_model_digest"] = json!(found);
    }
    body
}

/// 提示された証明書を、オプションの検査条件で検査する。
///
/// オプションは、検査条件、`max_check_cost`、`max_time_ms`、`allow_other_model`（真なら、`model_digest` が違う証明書も、
/// このモデルの名前と型で読んで検査する。省略時は偽で、別のモデルに対する証明書は読めない証拠として拒否する）。
pub fn verify_certificate(
    model: &Model,
    certificate: &str,
    opts: &Value,
    interrupt: Interrupt,
) -> Result<Value, String> {
    let map = options(opts, &["max_check_cost", "max_time_ms", ALLOW_OTHER_MODEL])?;
    let cond = conditions(model, map)?;
    let gate = GateOptions {
        max_cost: count(map, "max_check_cost", 0)?,
        interrupt,
        deadline: deadline(map)?,
    };
    let loaded = match read_certificate(model, certificate, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => loaded,
        Err(e) => return Ok(unreadable(model, &e)),
    };
    let (verdict, evidence) = judge(model.checked(), &cond, Evidence::Certificate(loaded.evidence), &gate);
    let body = report::evidence_report(model, &cond, &evidence, &verdict, None);
    Ok(mark_other_model(body, loaded.other_model_digest))
}

/// 提示されたトレースを、トレースに記録された検査条件で再生する。`replay_with` をオプションなしで呼ぶのと同じ。
pub fn replay(model: &Model, trace: &str) -> Value {
    // オプションが空なので、誤りにはならない。
    replay_with(model, trace, &json!({})).unwrap_or_else(|message| json!({"status": "usage_error", "message": message}))
}

/// 提示されたトレースを、トレースに記録された検査条件で再生する。
///
/// オプションは `allow_other_model`（`verify_certificate` と同じ）。
pub fn replay_with(model: &Model, trace: &str, opts: &Value) -> Result<Value, String> {
    let map = keys(opts, &[ALLOW_OTHER_MODEL])?;
    let loaded = match read_trace(model, trace, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => loaded,
        Err(e) => return Ok(unreadable(model, &e)),
    };
    let trace = loaded.evidence;
    let cond = trace.conditions.clone();
    let evidence = Evidence::Trace(trace.start, trace.steps, trace.claim);
    let verdict = decide(model.checked(), &cond, &evidence);
    let body = report::evidence_report(model, &cond, &evidence, &verdict, trace.seed);
    Ok(mark_other_model(body, loaded.other_model_digest))
}

/// 縮小で試す候補の数の、既定の上限。
const DEFAULT_SHRINK_ATTEMPTS: u64 = 10_000;

/// モデル違反のトレースを縮小する（仕様書 §10）。
///
/// 元のトレースを判定ゲートが受理しなければ、その拒否を報告する。
/// ステップの削除と、引数（公開引数と内部選択）を小さくする変更を試す。
/// 縮小結果は判定ゲートが同じ主張で受理したトレースで、元のステップ数を `original_steps` に記録する。
/// オプションは `attempts`（試す候補の数の上限。削除と引数の変更で共有する）と
/// `allow_other_model`（`verify_certificate` と同じ）。
pub fn shrink(model: &Model, trace: &str, opts: &Value) -> Result<Value, String> {
    let map = keys(opts, &["attempts", ALLOW_OTHER_MODEL])?;
    let attempts = count(map, "attempts", 1)?.unwrap_or(DEFAULT_SHRINK_ATTEMPTS);
    let (trace, other) = match read_trace(model, trace, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => (loaded.evidence, loaded.other_model_digest),
        Err(e) => return Ok(unreadable(model, &e)),
    };
    let cond = &trace.conditions;
    let original = trace.steps.len();
    // 元のトレースを判定ゲートに渡す。縮小の起点に使うので、トレースの部分は手元に残す。
    let evidence = Evidence::Trace(trace.start.clone(), trace.steps.clone(), trace.claim.clone());
    let verdict = decide(model.checked(), cond, &evidence);
    if !matches!(verdict.kind(), VerdictKind::Violated | VerdictKind::Error) {
        let body = report::evidence_report(model, cond, &evidence, &verdict, trace.seed);
        return Ok(mark_other_model(body, other));
    }
    let shrunk_steps = search_shrink(
        model.checked(),
        cond,
        &trace.start,
        &trace.steps,
        &trace.claim,
        size(attempts),
    );
    let shrunk = Evidence::Trace(trace.start.clone(), shrunk_steps, trace.claim.clone());
    let verdict = decide(model.checked(), cond, &shrunk);
    let mut body = report::evidence_report(model, cond, &shrunk, &verdict, trace.seed);
    body["original_steps"] = json!(original);
    Ok(mark_other_model(body, other))
}
