//! 詳細化の検査（docs/ir.md の「詳細化」）。

use crate::options::{count, deadline, max_states, options, select, size};
use crate::report::{inconsistency_json, limit_name, reject_json_in, INCONSISTENCY_MESSAGE};
use crate::Interrupt;
use fmspec_core::evidence::TraceStep;
use fmspec_core::refine::{map_state, Mapped, RefClaim, RefEvidence};
use fmspec_core::semantics::Conditions;
use fmspec_ir::{
    args_to_json, claim_to_json, conditions_to_json, error_to_json, output_to_json, state_to_json, Model, Refinement,
    ENGINE_VERSION, IR_VERSION,
};
use fmspec_search::{refine as search_refine, BfsOptions, Internal, RefOutcome, RefStatus};
use serde_json::{json, Value};

/// 詳細化の検査条件。具体モデルの対象の操作だけを選ぶ。不変条件、遷移契約、デッドロックは検査しない。
fn ref_conditions(model: &Model, opts: &serde_json::Map<String, Value>) -> Result<Conditions, String> {
    let mut c = Conditions {
        actions: vec![true; model.names.actions.len()],
        invariants: vec![false; model.names.invariants.len()],
        contracts: vec![false; model.names.contracts.len()],
        deadlock: false,
    };
    select(&mut c.actions, opts.get("actions"), "操作", |n| {
        model.names.action_index(n)
    })?;
    Ok(c)
}

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
    let (b, a) = (r.concrete.raw(), r.abstract_model.raw());
    match map_state(b, a, &r.mapping, &state.to_vec()) {
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

/// 詳細化の検査結果のJSON。
pub(crate) fn refine_report(r: &Refinement, cond: &Conditions, outcome: &RefOutcome) -> Value {
    let mut body = json!({
        "status": status_name(&outcome.status),
        "refinement": r.name,
        "refinement_digest": r.digest,
        "concrete": r.concrete.names.model,
        "abstract": r.abstract_model.names.model,
        "engine_version": ENGINE_VERSION,
        "ir_version": IR_VERSION,
        "conditions": conditions_to_json(&r.concrete.names, cond),
        "strategy": "bfs",
        "search": {
            "complete": outcome.stats.complete,
            "visited_states": outcome.stats.visited_states,
            "transitions": outcome.stats.transitions,
            "time_ms": outcome.search_time.as_secs_f64() * 1000.0,
        },
        "gate": {"time_ms": outcome.gate_time.as_secs_f64() * 1000.0},
    });
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
            let states = match &outcome.evidence {
                RefEvidence::Certificate(cert) => Some(&cert.states),
                _ => None,
            };
            body["rejected"] = reject_json_in(&r.concrete, states, *reject);
            body["message"] = json!("探索器が生成した証拠を判定ゲートが拒否しました。fmspec の不具合です");
        }
        RefStatus::InternalError(Internal::Inconsistent(i)) => {
            body["inconsistency"] = inconsistency_json(&r.concrete, i);
            body["message"] = json!(INCONSISTENCY_MESSAGE);
            body.as_object_mut().map(|m| m.remove("reason"));
        }
        _ => {}
    }
    body
}

/// 具体モデルが写像のもとで抽象モデルを詳細化するかを検査する。
///
/// オプションは、`actions`（具体モデルの対象の操作の名前の配列。省略時はすべて）、`max_states`、`max_depth`、`max_time_ms`。
/// 抽象モデルの操作は、すべてを照合に使う。
pub fn refine(r: &Refinement, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["max_states", "max_depth", "max_time_ms"])?;
    for key in ["invariants", "contracts", "deadlock"] {
        if map.get(key).is_some_and(|v| !v.is_null()) {
            return Err(format!("詳細化の検査では {key} を指定できません"));
        }
    }
    let cond = ref_conditions(&r.concrete, map)?;
    let opts = BfsOptions {
        max_states: max_states(map)?,
        interrupt,
        max_check_cost: None,
        max_depth: count(map, "max_depth", 0)?.map(size),
        deadline: deadline(map)?,
    };
    let outcome = search_refine(
        r.concrete.checked(),
        &cond,
        r.abstract_model.checked(),
        &r.mapping,
        &opts,
    );
    Ok(refine_report(r, &cond, &outcome))
}

/// 詳細化の文書の概要。
pub fn describe_refinement(r: &Refinement) -> Value {
    json!({
        "status": "valid",
        "refinement": r.name,
        "refinement_digest": r.digest,
        "concrete": r.concrete.names.model,
        "abstract": r.abstract_model.names.model,
    })
}
