//! 結果の機械可読JSON。

use fmspec_core::evidence::{Claim, Evidence, Limit, Reject};
use fmspec_core::gate::{Verdict, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::typing::InvalidModel;
use fmspec_ir::{
    claim_to_json, conditions_to_json, state_to_json, trace_to_json, Model, Source, Trace, ENGINE_VERSION, IR_VERSION,
};
use fmspec_search::{Outcome, Sampled, SimOptions, Status, PRNG_NAME};
use serde_json::{json, Value};
use std::time::Duration;

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

pub(crate) fn limit_name(limit: Limit) -> &'static str {
    match limit {
        Limit::MaxStates => "max_states",
        Limit::Interrupted => "interrupted",
        Limit::CheckBudget => "max_check_cost",
        Limit::AbstractFailed => "abstract_failed",
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
    let states = match evidence {
        Evidence::Certificate(cert) => Some(&cert.states),
        _ => None,
    };
    reject_json_in(model, states, reject)
}

/// 証拠を拒否した理由。`states` は証明書の状態の列（証明書でなければ `None`）。
pub(crate) fn reject_json_in(model: &Model, states: Option<&Vec<Vec<i64>>>, reject: Reject) -> Value {
    let names = &model.names;
    let state = |k: usize| {
        states
            .and_then(|ss| ss.get(k))
            .map(|s| state_to_json(model, s))
            .unwrap_or(Value::Null)
    };
    let action = |a: usize| names.actions.get(a).map(|n| json!(n.name)).unwrap_or(json!(a));
    match reject {
        Reject::ConditionMismatch => {
            json!({"reason": "condition_mismatch", "message": "証明書の検査条件が、要求された検査条件と一致しません"})
        }
        Reject::MissingInitial(_) => json!({"reason": "missing_initial", "message": "証明書が初期状態を含みません"}),
        Reject::BadStart => {
            json!({"reason": "bad_start", "message": "トレースの開始状態がモデルの初期状態ではありません"})
        }
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
        Reject::MappingFailed(k, _) => json!({
            "reason": "mapping_failed", "state": state(k),
            "message": "証明書の状態、またはその遷移先で、写像の評価が失敗します",
        }),
        Reject::StepNotMapped(k, a) => json!({
            "reason": "step_not_mapped", "state": state(k), "action": action(a),
            "message": "証明書の状態からの遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写りません",
        }),
        Reject::InitialMappingFailed(_, _) => json!({
            "reason": "initial_mapping_failed",
            "message": "初期状態で写像の評価が失敗します",
        }),
        Reject::InitialNotMapped(_) => json!({
            "reason": "initial_not_mapped",
            "message": "初期状態が、抽象モデルの初期状態に写りません",
        }),
        Reject::NotSymmetric(i) => json!({
            "reason": "not_symmetric", "swap": i,
            "message": "宣言した入れ替えが、モデルの対称性ではありません",
        }),
    }
}

fn attach_evidence(body: &mut Value, model: &Model, cond: &Conditions, evidence: &Evidence, seed: Option<u64>) {
    match evidence {
        Evidence::Certificate(cert) => {
            body["certificate_states"] = json!(cert.states.len());
        }
        Evidence::Trace(start, steps, claim) => {
            let trace = Trace {
                conditions: cond.clone(),
                start: start.clone(),
                steps: steps.clone(),
                claim: claim.clone(),
                seed,
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

fn status_name(status: Status) -> &'static str {
    match status {
        Status::Verified => "verified",
        Status::Violated => "violated",
        Status::Error => "error",
        Status::Inconclusive(_) => "inconclusive",
        Status::InternalError(_) => "internal_error",
    }
}

fn attach_internal_error(body: &mut Value, model: &Model, outcome: &Outcome) {
    if let Status::InternalError(reject) = outcome.status {
        body["rejected"] = reject_json(model, &outcome.evidence, reject);
        body["message"] = json!("探索器が生成した証拠を判定ゲートが拒否しました。fmspec の不具合です");
    }
}

/// `simulate` の結果。`sampled` は指定したサンプルの検査を完了しただけで、網羅性の主張はない。
pub fn simulation_report(
    model: &Model,
    cond: &Conditions,
    opts: &SimOptions,
    sampled: &Sampled,
    time: Duration,
) -> Value {
    let status = sampled
        .found
        .as_ref()
        .map(|o| status_name(o.status))
        .unwrap_or("sampled");
    let mut body = base(model, cond, status);
    body["strategy"] = json!("random");
    body["simulation"] = json!({
        "seed": opts.seed,
        "traces": opts.traces,
        "max_steps": opts.max_steps,
        "prng": PRNG_NAME,
        "completed_traces": sampled.stats.traces,
        "steps": sampled.stats.steps,
        "time_ms": time.as_secs_f64() * 1000.0,
    });
    if let Some(outcome) = &sampled.found {
        attach_evidence(&mut body, model, cond, &outcome.evidence, Some(opts.seed));
        attach_internal_error(&mut body, model, outcome);
    }
    body
}

/// `check` の結果。探索器の報告（`search`）は検査済みの値ではない。
pub fn check_report(model: &Model, cond: &Conditions, outcome: &Outcome) -> Value {
    let status = status_name(outcome.status);
    let mut body = base(model, cond, status);
    body["strategy"] = json!("bfs");
    body["search"] = json!({
        "complete": outcome.stats.complete,
        "visited_states": outcome.stats.visited_states,
        "transitions": outcome.stats.transitions,
        "time_ms": outcome.search_time.as_secs_f64() * 1000.0,
    });
    body["gate"] = json!({"time_ms": outcome.gate_time.as_secs_f64() * 1000.0});
    attach_evidence(&mut body, model, cond, &outcome.evidence, None);
    attach_internal_error(&mut body, model, outcome);
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
    attach_evidence(&mut body, model, cond, evidence, None);
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
