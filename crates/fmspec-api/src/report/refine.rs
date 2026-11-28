//! 詳細化の検査の結果の機械可読JSON（docs/ir.md の「詳細化」）。

use super::{attach_bfs, inconsistency_json, limit_name, reject_json_in, INCONSISTENCY_MESSAGE, REJECTED_MESSAGE};
use fmspec_core::kernel::evidence::TraceStep;
use fmspec_core::kernel::evidence::{RefClaim, RefEvidence};
use fmspec_core::kernel::refine::{map_state_of, Mapped};
use fmspec_core::kernel::semantics::Conditions;
use fmspec_ir::{
    args_to_json, claim_to_json, conditions_to_json, error_to_json, output_to_json, state_to_json, Refinement,
    ENGINE_VERSION, IR_VERSION,
};
use fmspec_search::{Internal, RefOutcome, RefStatus};
use serde_json::{json, Value};

fn status_name(status: &RefStatus) -> &'static str {
    match status {
        RefStatus::Refines => "refines",
        RefStatus::NotRefines => "not_refines",
        RefStatus::Error => "error",
        RefStatus::Inconclusive(_) => "inconclusive",
        RefStatus::InternalError(_) => "internal_error",
    }
}

/// 抽象モデルの状態の値。写像の評価が失敗すれば `null`。
fn mapped_json(r: &Refinement, state: &[i64]) -> Value {
    match map_state_of(
        r.concrete.checked(),
        r.abstract_model.checked(),
        &r.mapping,
        &state.to_vec(),
    ) {
        Mapped::Ok(x) => state_to_json(&r.abstract_model, &x),
        _ => Value::Null,
    }
}

fn claim_json(r: &Refinement, claim: &RefClaim, steps: &[TraceStep]) -> Value {
    let (b, a) = (&r.concrete, &r.abstract_model);
    match claim {
        RefClaim::Init => json!({
            "violation": "initial",
            "message": "初期状態が、抽象モデルの初期状態に写りません",
        }),
        RefClaim::Step => {
            let action = steps
                .last()
                .and_then(|st| b.names.actions.get(st.action))
                .map(|n| n.name.as_str());
            json!({
                "violation": "step",
                "action": action,
                "message": "最後の遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写りません",
            })
        }
        RefClaim::Map(slot, kind) => {
            let var = a.names.state_of_slot(*slot).map(|(v, _)| v);
            let ty = a.raw().state_types.get(*slot);
            json!({
                "violation": "mapping",
                "state": var.and_then(|v| a.names.states.get(v)),
                "error": error_to_json(a, kind, ty),
                "message": "末尾の状態で、写像の評価が失敗します",
            })
        }
        RefClaim::Model(c) => claim_to_json(b, c),
    }
}

fn trace_json(r: &Refinement, start: &[i64], steps: &[TraceStep]) -> Value {
    let b = &r.concrete;
    let steps_json: Vec<Value> = steps
        .iter()
        .map(|st| {
            let (params, choices) = args_to_json(b, st.action, &st.args);
            json!({
                "action": b.names.actions.get(st.action).map(|n| n.name.as_str()).unwrap_or("?"),
                "args": params,
                "choices": choices,
                "output": output_to_json(b, st.action, st.output),
                "state": state_to_json(b, &st.state),
                "abstract": mapped_json(r, &st.state),
            })
        })
        .collect();
    json!({
        "initial": state_to_json(b, start),
        "initial_abstract": mapped_json(r, start),
        "steps": steps_json,
    })
}

/// 詳細化の文書と2つのモデルの名前。
fn identity(r: &Refinement, status: &str) -> Value {
    json!({
        "status": status,
        "refinement": r.name,
        "refinement_digest": r.digest,
        "concrete": r.concrete.names.model,
        "abstract": r.abstract_model.names.model,
    })
}

/// 詳細化の文書の概要。
pub(crate) fn describe_refinement(r: &Refinement) -> Value {
    identity(r, "valid")
}

/// 詳細化の検査結果のJSON。
pub(crate) fn refine_report(r: &Refinement, cond: &Conditions, outcome: &RefOutcome) -> Value {
    let mut body = identity(r, status_name(&outcome.status));
    body["engine_version"] = json!(ENGINE_VERSION);
    body["ir_version"] = json!(IR_VERSION);
    body["conditions"] = conditions_to_json(&r.concrete.names, cond);
    attach_bfs(&mut body, &outcome.stats, outcome.search_time, outcome.gate_time);
    match &outcome.evidence {
        RefEvidence::Certificate(cert) => {
            body["certificate_states"] = json!(cert.states.len());
        }
        RefEvidence::Trace(start, steps, claim) => {
            body["property"] = claim_json(r, claim, steps);
            body["trace"] = trace_json(r, start, steps);
        }
        RefEvidence::Unavailable(limit) => {
            body["reason"] = json!(limit_name(*limit));
        }
    }
    match &outcome.status {
        RefStatus::InternalError(Internal::Rejected(reject)) => {
            // 証明書の状態は添字ではなく値で示す（`reject_json` と同じ）。
            let states = match &outcome.evidence {
                RefEvidence::Certificate(cert) => Some(&cert.states),
                _ => None,
            };
            body["rejected"] = reject_json_in(&r.concrete, states, *reject);
            body["message"] = json!(REJECTED_MESSAGE);
        }
        RefStatus::InternalError(Internal::Inconsistent(i)) => {
            body["inconsistency"] = inconsistency_json(&r.concrete, i);
            body["message"] = json!(INCONSISTENCY_MESSAGE);
            body.as_object_mut().map(|m| m.remove("reason"));
        }
        // 読み込みは写像の式の数を揃えるので、起きない。
        RefStatus::InternalError(Internal::InvalidMapping) => {
            body["message"] = json!("写像の式の数が、抽象モデルの状態のスロットの数と違います。fmspec の不具合です");
        }
        _ => {}
    }
    body
}
