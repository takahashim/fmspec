//! 結果の機械可読JSONと、人間向けの表示。

use fmspec_core::evidence::{Claim, Evidence, Limit, Reject};
use fmspec_core::gate::{Verdict, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::typing::InvalidModel;
use fmspec_ir::{
    claim_to_json, conditions_to_json, state_to_json, trace_to_json, Model, Source, Trace, ENGINE_VERSION, IR_VERSION,
};
use fmspec_search::{Outcome, Status};
use serde_json::{json, Value};
use std::fmt::Write;

fn base(model: &Model, cond: &Conditions, status: &str) -> Value {
    json!({
        "status": status,
        "model": model.names.model,
        "model_digest": model.digest,
        "engine_version": ENGINE_VERSION,
        "ir_version": IR_VERSION,
        "conditions": conditions_to_json(&model.names, cond),
    })
}

fn limit_name(limit: Limit) -> &'static str {
    match limit {
        Limit::MaxStates => "max_states",
        Limit::Interrupted => "interrupted",
    }
}

fn source_json(source: &Option<Source>) -> Value {
    match source {
        Some(s) => json!({"file": s.file, "line": s.line}),
        None => Value::Null,
    }
}

/// 主張の対象の定義のソース位置。
fn claim_source(model: &Model, claim: &Claim) -> Value {
    let names = &model.names;
    match claim {
        Claim::Invariant(i) | Claim::InvariantError(i, _) => {
            source_json(names.invariant_sources.get(*i).unwrap_or(&None))
        }
        Claim::Contract(k) | Claim::ContractError(k, _) => source_json(names.contract_sources.get(*k).unwrap_or(&None)),
        Claim::StepError(a, _, _, _) => source_json(&names.actions.get(*a).and_then(|n| n.source.clone())),
        Claim::Deadlock | Claim::TerminalError(_) => Value::Null,
    }
}

/// 証拠を拒否した理由。証明書の状態は添字ではなく値で示す。
fn reject_json(model: &Model, evidence: &Evidence, reject: Reject) -> Value {
    let names = &model.names;
    let state = |k: usize| match evidence {
        Evidence::Certificate(cert) => cert
            .states
            .get(k)
            .map(|s| state_to_json(model, s))
            .unwrap_or(Value::Null),
        _ => Value::Null,
    };
    let action = |a: usize| names.actions.get(a).map(|n| json!(n.name)).unwrap_or(json!(a));
    match reject {
        Reject::ConditionMismatch => {
            json!({"reason": "condition_mismatch", "message": "証明書の検査条件が、要求された検査条件と一致しません"})
        }
        Reject::MissingInitial => json!({"reason": "missing_initial", "message": "証明書が初期状態を含みません"}),
        Reject::IllTypedState(k) => {
            json!({"reason": "ill_typed_state", "state": state(k), "message": "証明書の状態が状態型に従いません"})
        }
        Reject::InvariantNotHeld(k, i) => json!({
            "reason": "invariant_not_held", "state": state(k),
            "invariant": names.invariants.get(i),
            "message": "証明書の状態で不変条件が成立しません",
        }),
        Reject::StepFailed(k, a) => json!({
            "reason": "step_failed", "state": state(k), "action": action(a),
            "message": "証明書の状態で操作の評価が失敗します",
        }),
        Reject::MissingSuccessor(k, a) => json!({
            "reason": "missing_successor", "state": state(k), "action": action(a),
            "message": "証明書の状態からの遷移先が、証明書に含まれません",
        }),
        Reject::ContractNotHeld(k, c) => json!({
            "reason": "contract_not_held", "state": state(k),
            "contract": names.contracts.get(c),
            "message": "証明書の状態からの遷移で遷移契約が成立しません",
        }),
        Reject::Deadlock(k) => json!({
            "reason": "deadlock", "state": state(k),
            "message": "証明書の状態が非終端のデッドロックです",
        }),
        Reject::BadStep(j) => json!({
            "reason": "bad_step", "step": j + 1,
            "message": "トレースのステップの操作が対象外か、引数がドメインに従いません",
        }),
        Reject::StepMismatch(j) => json!({
            "reason": "step_mismatch", "step": j + 1,
            "message": "トレースのステップがモデルの遷移と一致しません",
        }),
        Reject::ClaimNotReproduced => json!({
            "reason": "claim_not_reproduced",
            "message": "トレースの末尾で、主張どおりの事象が起きません",
        }),
    }
}

fn attach_evidence(body: &mut Value, model: &Model, cond: &Conditions, evidence: &Evidence) {
    match evidence {
        Evidence::Certificate(cert) => {
            body["certificate_states"] = json!(cert.states.len());
        }
        Evidence::Trace(steps, claim) => {
            let trace = Trace {
                conditions: cond.clone(),
                steps: steps.clone(),
                claim: claim.clone(),
                seed: None,
            };
            body["property"] = claim_to_json(model, claim);
            body["property"]["source"] = claim_source(model, claim);
            body["trace"] = trace_to_json(model, &trace);
        }
        Evidence::Unavailable(limit) => {
            body["reason"] = json!(limit_name(*limit));
        }
    }
}

/// `check` の結果。探索器の報告（`search`）は検査済みの値ではない。
pub fn check_report(model: &Model, cond: &Conditions, outcome: &Outcome) -> Value {
    let status = match outcome.status {
        Status::Verified => "verified",
        Status::Violated => "violated",
        Status::Error => "error",
        Status::Inconclusive(_) => "inconclusive",
        Status::InternalError(_) => "internal_error",
    };
    let mut body = base(model, cond, status);
    body["strategy"] = json!("bfs");
    body["search"] = json!({
        "complete": outcome.stats.complete,
        "visited_states": outcome.stats.visited_states,
        "transitions": outcome.stats.transitions,
        "time_ms": outcome.search_time.as_secs_f64() * 1000.0,
    });
    body["gate"] = json!({"time_ms": outcome.gate_time.as_secs_f64() * 1000.0});
    attach_evidence(&mut body, model, cond, &outcome.evidence);
    if let Status::InternalError(reject) = outcome.status {
        body["rejected"] = reject_json(model, &outcome.evidence, reject);
        body["message"] = json!("探索器が生成した証拠を判定ゲートが拒否しました。fmspec の不具合です");
    }
    body
}

/// 外部から提示された証拠の検査結果。探索を行っていないので、探索統計は付けない。
pub fn evidence_report(model: &Model, cond: &Conditions, evidence: &Evidence, verdict: &Verdict) -> Value {
    let status = match verdict.kind() {
        VerdictKind::Verified => "verified",
        VerdictKind::Violated => "violated",
        VerdictKind::Error => "error",
        VerdictKind::Inconclusive => "inconclusive",
        VerdictKind::InvalidModel => "invalid_model",
        VerdictKind::Rejected => "rejected",
    };
    let mut body = base(model, cond, status);
    attach_evidence(&mut body, model, cond, evidence);
    if let Some(reject) = verdict.reject() {
        body["rejected"] = reject_json(model, evidence, reject);
    }
    if let Some(invalid) = verdict.invalid() {
        body["message"] = json!(invalid_message(invalid));
    }
    body
}

fn invalid_message(invalid: InvalidModel) -> String {
    format!("モデルが整形式ではありません（{invalid:?}）")
}

/// 形式が合わない、または別のモデルに対する証拠。
pub fn unreadable_evidence(model: &Model, message: &str) -> Value {
    json!({
        "status": "rejected",
        "model": model.names.model,
        "model_digest": model.digest,
        "engine_version": ENGINE_VERSION,
        "rejected": {"reason": "unreadable", "message": message},
    })
}

// ---- 人間向けの表示 ----

fn plain(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

fn pairs(v: &Value) -> String {
    match v.as_object() {
        Some(map) => map
            .iter()
            .map(|(k, v)| format!("{k}: {}", plain(v)))
            .collect::<Vec<_>>()
            .join(", "),
        None => plain(v),
    }
}

fn error_text(e: &Value) -> String {
    match e["kind"].as_str() {
        Some("overflow") => "符号付き64ビット整数のオーバーフロー".to_string(),
        Some("out_of_range") => {
            let range = match e["type"]["int"].as_object() {
                Some(r) => format!("、型 {}..{} の範囲外", r["min"], r["max"]),
                None => String::new(),
            };
            format!("範囲外更新（値 {}{range}）", e["value"])
        }
        Some("type_mismatch") => "型の不一致".to_string(),
        Some("unbound") => "未束縛の参照".to_string(),
        _ => e.to_string(),
    }
}

fn property_text(p: &Value) -> String {
    if let Some(kind) = p["violation"].as_str() {
        return match kind {
            "invariant" => format!("不変条件 {} の違反", plain(&p["name"])),
            "contract" => format!("遷移契約 {} の違反", plain(&p["name"])),
            _ => "非終端のデッドロック".to_string(),
        };
    }
    let error = error_text(&p["error"]);
    match p["site"].as_str() {
        Some("invariant") => format!("不変条件 {} の評価エラー: {error}", plain(&p["name"])),
        Some("contract") => format!("遷移契約 {} の評価エラー: {error}", plain(&p["name"])),
        Some("terminal") => format!("終端条件の評価エラー: {error}"),
        Some(site) => {
            let mut args = pairs(&p["args"]);
            let choices = pairs(&p["choices"]);
            if !choices.is_empty() {
                args = if args.is_empty() {
                    format!("内部選択 {choices}")
                } else {
                    format!("{args}; 内部選択 {choices}")
                };
            }
            let place = match site {
                "guard" => "guard".to_string(),
                "output" => "出力式".to_string(),
                _ => format!("更新式（{}）", plain(&p["target"])),
            };
            format!("操作 {}({args}) の{place}で評価エラー: {error}", plain(&p["action"]))
        }
        None => p.to_string(),
    }
}

fn trace_text(out: &mut String, trace: &Value) {
    let _ = writeln!(out, "  初期状態 {}", pairs(&trace["initial"]));
    let Some(steps) = trace["steps"].as_array() else {
        return;
    };
    for (i, st) in steps.iter().enumerate() {
        let mut line = format!("  {}. {}({})", i + 1, plain(&st["action"]), pairs(&st["args"]));
        let choices = pairs(&st["choices"]);
        if !choices.is_empty() {
            let _ = write!(line, " 内部選択 {choices}");
        }
        if let Some(v) = st["output"].get("value") {
            let _ = write!(line, " 出力 {}", plain(v));
        }
        let _ = writeln!(out, "{line} → {}", pairs(&st["state"]));
    }
    let _ = writeln!(out, "  （{} ステップ）", steps.len());
}

pub fn human(body: &Value, _model: Option<&Model>) -> String {
    let mut out = String::new();
    let status = body["status"].as_str().unwrap_or("?");
    let model = plain(&body["model"]);
    let headline = match status {
        "valid" => format!("Valid: {model}"),
        "verified" => format!("Verified: {model}"),
        "violated" => format!("Violated: {model} / {}", property_text(&body["property"])),
        "error" => format!("Error: {model} / {}", property_text(&body["property"])),
        "inconclusive" => format!("Inconclusive: {model}（{}）", plain(&body["reason"])),
        "internal_error" => format!("InternalError: {model}"),
        "rejected" => format!("Rejected: {model}"),
        other => format!("{other}: {model}"),
    };
    let _ = writeln!(out, "{headline}");
    if status == "valid" {
        let _ = writeln!(
            out,
            "  状態変数 {}、操作 {}、不変条件 {}、遷移契約 {}",
            body["states"], body["actions"], body["invariants"], body["contracts"]
        );
    }
    if let Some(source) = body["property"]["source"].as_object() {
        let _ = writeln!(out, "  定義: {}:{}", plain(&source["file"]), source["line"]);
    }
    if body.get("trace").is_some() {
        trace_text(&mut out, &body["trace"]);
    }
    if let Some(rejected) = body.get("rejected") {
        let _ = writeln!(out, "  拒否の理由: {}", plain(&rejected["message"]));
        for key in ["state", "action", "invariant", "contract", "step"] {
            if let Some(v) = rejected.get(key).filter(|v| !v.is_null()) {
                let _ = writeln!(out, "    {key}: {}", pairs(v));
            }
        }
    }
    if let Some(message) = body.get("message") {
        let _ = writeln!(out, "  {}", plain(message));
    }
    if let Some(n) = body.get("certificate_states") {
        let checked = if status == "verified" {
            "（判定ゲートが受理）"
        } else {
            ""
        };
        let _ = writeln!(out, "  証明書の状態数 {n}{checked}");
    }
    if let Some(search) = body.get("search") {
        let complete = if search["complete"] == json!(true) {
            "完走"
        } else {
            "未完走"
        };
        let _ = writeln!(
            out,
            "  探索: {complete}、訪問状態数 {}、遷移数 {}（探索器の報告）",
            search["visited_states"], search["transitions"]
        );
    }
    out
}
