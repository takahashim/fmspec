//! 結果の機械可読JSON（docs/ir.md）。
//!
//! 結果の形は、ここと `refine`（詳細化の検査の結果）だけで決める。API の関数は、検査の結果と、
//! 結果に示す付帯の情報（`Provenance`、`CheckOutputs`、`ShrinkSummary`）を渡すだけで、項目を書き足さない。

mod refine;

pub(crate) use refine::{describe_refinement, refine_report};

use fmspec_core::evidence::{Claim, Evidence, Limit, RefReject, Reject};
use fmspec_core::gate::{Verdict, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::typing::InvalidModel;
use fmspec_ir::{
    certificate_to_json, claim_to_json, conditions_to_json, state_to_json, trace_to_json, Model, Source, Trace,
    TraceError, ENGINE_VERSION, IR_VERSION,
};
use fmspec_search::{Inconsistency, Internal, Outcome, Sampled, ShrinkStop, SimOptions, Stats, Status, PRNG_NAME};
use serde_json::{json, Value};
use std::time::Duration;

/// 判定ゲートが、探索器の生成した証拠を拒否したことを報告する `message`。
const REJECTED_MESSAGE: &str = "探索器が生成した証拠を判定ゲートが拒否しました。fmspec の不具合です";

/// オプションの誤りの結果。結果と同じ形（`status` が `usage_error`）で表す。
pub(crate) fn usage_error(message: &str) -> Value {
    json!({"status": "usage_error", "message": message})
}

/// モデルの概要。IR検証を通ったことの報告に使う。
pub(crate) fn describe(model: &Model) -> Value {
    json!({
        "status": "valid",
        "model": model.names.model,
        "model_digest": model.digest,
        "states": model.names.states.len(),
        "actions": model.names.actions.len(),
        // 対称性の像として加えた不変条件は数えない。
        "invariants": model.names.invariant_family.iter().enumerate().filter(|(j, f)| j == *f).count(),
        "contracts": model.names.contracts.len(),
    })
}

/// どの結果にもある項目。
fn header(model: &Model, status: &str) -> Value {
    json!({
        "status": status,
        "model": model.names.model,
        "model_digest": model.digest,
        "engine_version": ENGINE_VERSION,
    })
}

/// 検査条件のもとで判定した結果に共通の項目。
fn base(model: &Model, cond: &Conditions, status: &str) -> Value {
    let mut body = header(model, status);
    body["ir_version"] = json!(IR_VERSION);
    body["conditions"] = conditions_to_json(&model.names, cond);
    body
}

fn limit_name(limit: Limit) -> &'static str {
    match limit {
        Limit::MaxStates => "max_states",
        Limit::Interrupted => "interrupted",
        Limit::CheckBudget => "max_check_cost",
        Limit::MaxDepth => "max_depth",
        Limit::MaxTime => "max_time_ms",
        Limit::AbstractFailed => "abstract_failed",
    }
}

/// 主張の対象の定義のソース位置。
fn claim_source(model: &Model, claim: &Claim) -> Value {
    let names = &model.names;
    let source: Option<&Source> = match claim {
        Claim::Invariant(i) | Claim::InvariantError(i, _) => names.invariant_sources.get(*i).and_then(Option::as_ref),
        Claim::Contract(k) | Claim::ContractError(k, _) => names.contract_sources.get(*k).and_then(Option::as_ref),
        Claim::StepError(a, _, _, _) => names.actions.get(*a).and_then(|n| n.source.as_ref()),
        Claim::Deadlock | Claim::TerminalError(_) => None,
    };
    match source {
        Some(s) => json!({"file": s.file, "line": s.line}),
        None => Value::Null,
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
fn reject_json_in(model: &Model, states: Option<&Vec<Vec<i64>>>, reject: Reject) -> Value {
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
        Reject::Refine(RefReject::MappingFailed(k, _)) => json!({
            "reason": "mapping_failed", "state": state(k),
            "message": "証明書の状態、またはその遷移先で、写像の評価が失敗します",
        }),
        Reject::Refine(RefReject::StepNotMapped(k, a)) => json!({
            "reason": "step_not_mapped", "state": state(k), "action": action(a),
            "message": "証明書の状態からの遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写りません",
        }),
        Reject::Refine(RefReject::InitialMappingFailed(_, _)) => json!({
            "reason": "initial_mapping_failed",
            "message": "初期状態で写像の評価が失敗します",
        }),
        Reject::Refine(RefReject::InitialNotMapped(_)) => json!({
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

fn status_name(status: &Status) -> &'static str {
    match status {
        Status::Verified => "verified",
        Status::Violated => "violated",
        Status::Error => "error",
        Status::Inconclusive(_) => "inconclusive",
        Status::InternalError(_) => "internal_error",
    }
}

/// 探索器の内部の不整合を報告する `message`。
const INCONSISTENCY_MESSAGE: &str = "探索器の内部の不整合です。fmspec の不具合です";

/// 探索器の内部の不整合の内容。状態は符号化列（`encoded_state`）で示し、状態型に従うときだけ値（`state`）も示す。
fn inconsistency_json(model: &Model, inconsistency: &Inconsistency) -> Value {
    match inconsistency {
        Inconsistency::Successors { action, state } => {
            let names = &model.names;
            let decoded = if model.checked().state_ok(state) {
                state_to_json(model, state)
            } else {
                Value::Null
            };
            json!({
                "kind": "successors",
                "action": names.actions.get(*action).map(|n| json!(n.name)).unwrap_or(json!(action)),
                "state": decoded,
                "encoded_state": state,
                "message": "状態での操作の遷移を列挙できません。操作が未定義か、状態が状態型に従いません",
            })
        }
        Inconsistency::SymmetryTrace => json!({
            "kind": "symmetry_trace",
            "message": "対称性による削減で、代表元の経路から具体的なトレースを作れません",
        }),
    }
}

/// 探索器の内部の不整合を見つけ、結果を返せなかったことの報告。カバレッジとテスト経路が使う。
pub(crate) fn inconsistency_report(model: &Model, inconsistency: &Inconsistency) -> Value {
    let mut body = header(model, "internal_error");
    body["inconsistency"] = inconsistency_json(model, inconsistency);
    body["message"] = json!(INCONSISTENCY_MESSAGE);
    body
}

/// 判定ゲートを通した結果の証拠と、`internal_error` の内容。
/// 探索器の内部の不整合では、判定ゲートに渡した `Unavailable` に意味はないので、証拠の項目（`reason` など）は付けない。
fn attach_outcome(body: &mut Value, model: &Model, cond: &Conditions, outcome: &Outcome, seed: Option<u64>) {
    match &outcome.status {
        Status::InternalError(Internal::Inconsistent(inconsistency)) => {
            body["inconsistency"] = inconsistency_json(model, inconsistency);
            body["message"] = json!(INCONSISTENCY_MESSAGE);
        }
        Status::InternalError(Internal::Rejected(reject)) => {
            attach_evidence(body, model, cond, &outcome.evidence, seed);
            body["rejected"] = reject_json(model, &outcome.evidence, *reject);
            body["message"] = json!(REJECTED_MESSAGE);
        }
        // 検証済みのモデルに対する判定ゲートはモデルを拒否しない（証明済み）ので、起きない。
        Status::InternalError(Internal::InvalidModel(invalid)) => {
            attach_evidence(body, model, cond, &outcome.evidence, seed);
            body["message"] = json!(invalid_message(*invalid));
        }
        _ => attach_evidence(body, model, cond, &outcome.evidence, seed),
    }
}

/// `simulate` の結果。`sampled` は指定したサンプルの検査を完了しただけで、網羅性の主張はない。
pub(crate) fn simulation_report(
    model: &Model,
    cond: &Conditions,
    opts: &SimOptions,
    sampled: &Sampled,
    time: Duration,
) -> Value {
    let status = sampled
        .found
        .as_ref()
        .map(|o| status_name(&o.status))
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
        attach_outcome(&mut body, model, cond, outcome, Some(opts.seed));
    }
    body
}

/// 幅優先探索の報告（`strategy`、`search`、`gate`）。探索器の報告（`search`）は検査済みの値ではない。
fn attach_bfs(body: &mut Value, stats: &Stats, search_time: Duration, gate_time: Duration) {
    body["strategy"] = json!("bfs");
    body["search"] = json!({
        "complete": stats.complete,
        "visited_states": stats.visited_states,
        "transitions": stats.transitions,
        "time_ms": search_time.as_secs_f64() * 1000.0,
    });
    body["gate"] = json!({"time_ms": gate_time.as_secs_f64() * 1000.0});
}

/// `check` の結果に、指定により加える項目。
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CheckOutputs {
    /// 対称性による削減を使った。使った対称性（`symmetry`）を示す。
    pub symmetry: bool,
    /// 受理された証明書（`certificate`）を示す。`verified` のときだけ加える。
    pub certificate: bool,
}

/// `check` の結果。
pub(crate) fn check_report(model: &Model, cond: &Conditions, outcome: &Outcome, outputs: CheckOutputs) -> Value {
    let status = status_name(&outcome.status);
    let mut body = base(model, cond, status);
    attach_bfs(&mut body, &outcome.stats, outcome.search_time, outcome.gate_time);
    attach_outcome(&mut body, model, cond, outcome, None);
    if outputs.symmetry {
        body["symmetry"] = json!({"groups": model.names.symmetry_groups, "swaps": model.names.symmetry.len()});
    }
    if let (true, Evidence::Certificate(cert), Status::Verified) =
        (outputs.certificate, &outcome.evidence, &outcome.status)
    {
        body["certificate"] = certificate_to_json(model, cert);
    }
    body
}

/// 判定ゲートが、提示された証拠を判定した結果。
pub(crate) struct Judged<'a> {
    pub cond: &'a Conditions,
    pub evidence: &'a Evidence,
    pub verdict: &'a Verdict,
}

/// 提示された証拠の出所。結果にそのまま示す。
#[derive(Clone, Debug, Default)]
pub(crate) struct Provenance {
    /// 提示されたトレースに記録されていたseed。示すトレースにそのまま残す。
    pub seed: Option<u64>,
    /// 別のモデルに対する証拠を指定により読んだなら、その digest（`evidence_model_digest`）。
    pub other_model_digest: Option<String>,
}

impl Provenance {
    fn attach(&self, body: &mut Value) {
        if let Some(found) = &self.other_model_digest {
            body["evidence_model_digest"] = json!(found);
        }
    }
}

fn verdict_name(kind: VerdictKind) -> &'static str {
    match kind {
        VerdictKind::Verified => "verified",
        VerdictKind::Violated => "violated",
        VerdictKind::Error => "error",
        VerdictKind::Inconclusive => "inconclusive",
        VerdictKind::InvalidModel => "invalid_model",
        VerdictKind::Rejected => "rejected",
    }
}

/// 外部から提示された証拠の検査結果。探索を行っていないので、探索統計は付けない。
pub(crate) fn evidence_report(model: &Model, judged: &Judged, provenance: &Provenance) -> Value {
    let Judged {
        cond,
        evidence,
        verdict,
    } = *judged;
    let mut body = base(model, cond, verdict_name(verdict.kind()));
    attach_evidence(&mut body, model, cond, evidence, provenance.seed);
    if let Some(reject) = verdict.reject() {
        body["rejected"] = reject_json(model, evidence, reject);
    }
    if let Some(invalid) = verdict.invalid() {
        body["message"] = json!(invalid_message(invalid));
    }
    provenance.attach(&mut body);
    body
}

/// 縮小器の報告。検査済みの値ではない。
#[derive(Clone, Copy, Debug)]
pub(crate) struct ShrinkSummary {
    /// 元のトレースのステップ数。
    pub original_steps: usize,
    /// 試した候補の数。
    pub attempts: usize,
    /// 打ち切った理由。`None` なら打ち切らずに終わった。
    pub stopped: Option<ShrinkStop>,
}

/// 縮小したトレースの検査結果。提示された証拠の検査結果に、元のステップ数（`original_steps`）と、
/// 縮小器の報告（`shrink`。`complete` が偽なら、`limit` に打ち切った理由を書く）を加える。
pub(crate) fn shrink_report(model: &Model, judged: &Judged, provenance: &Provenance, summary: &ShrinkSummary) -> Value {
    let mut body = evidence_report(model, judged, provenance);
    body["original_steps"] = json!(summary.original_steps);
    let mut shrink = json!({"attempts": summary.attempts, "complete": summary.stopped.is_none()});
    match summary.stopped {
        None => {}
        Some(ShrinkStop::Attempts) => shrink["limit"] = json!("attempts"),
        Some(ShrinkStop::Limit(limit)) => shrink["limit"] = json!(limit_name(limit)),
    }
    body["shrink"] = shrink;
    body
}

fn invalid_message(invalid: InvalidModel) -> String {
    format!("モデルが整形式ではありません（{invalid:?}）")
}

/// 形式が合わない、または別のモデルに対する証拠。検査条件を読めていないので、`conditions` は付けない。
/// 別のモデルに対する証拠なら、その digest を `evidence_model_digest` に記録する。
pub(crate) fn unreadable_evidence(model: &Model, e: &TraceError) -> Value {
    let mut body = header(model, "rejected");
    body["rejected"] = json!({"reason": "unreadable", "message": e.to_string()});
    if let TraceError::OtherModel { found, .. } = e {
        body["evidence_model_digest"] = json!(found);
    }
    body
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{check_report, inconsistency_report, limit_name, simulation_report, CheckOutputs};
    use crate::human::human;
    use fmspec_core::evidence::{Certificate, Evidence, Limit};
    use fmspec_ir::{default_conditions, load, Model, ENGINE_VERSION};
    use fmspec_search::{
        check_evidence, Inconsistency, Internal, Outcome, Sampled, SimOptions, SimStats, Stats, Status,
    };
    use serde_json::{json, Value};

    const INCONSISTENCY: &str = "探索器の内部の不整合です。fmspec の不具合です";
    const SUCCESSORS: &str = "状態での操作の遷移を列挙できません。操作が未定義か、状態が状態型に従いません";

    /// 状態変数 `x`（`0..=3`、初期値0）と、`x` を1増やす操作 `inc` を持つモデル。
    fn counter() -> Model {
        let ir = json!({
            "ir_version": 1,
            "name": "counter",
            "states": [{"name": "x", "type": {"int": {"min": 0, "max": 3}}, "initial": {"int": 0}}],
            "actions": [{
                "name": "inc",
                "guard": {"lt": [{"var": 0}, {"int": 3}]},
                "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"int": 1}]}}]
            }]
        });
        load(&ir.to_string()).unwrap()
    }

    /// 探索器が内部の不整合を返したときの検査結果。`check` と同じく、判定ゲートには `Unavailable` を渡してある。
    fn inconsistent(m: &Model, inconsistency: Inconsistency) -> Outcome {
        let cond = default_conditions(m, false);
        let stats = Stats {
            visited_states: 2,
            transitions: 1,
            complete: false,
        };
        let mut o = check_evidence(m.checked(), &cond, Evidence::Unavailable(Limit::Interrupted), stats);
        o.status = Status::InternalError(Internal::Inconsistent(inconsistency));
        o
    }

    /// `a` に `b` の項目を加える。
    fn merged(mut a: Value, b: Value) -> Value {
        for (k, v) in b.as_object().unwrap() {
            a[k] = v.clone();
        }
        a
    }

    fn identity(m: &Model) -> Value {
        json!({"model": "counter", "model_digest": m.digest, "engine_version": ENGINE_VERSION})
    }

    #[test]
    fn an_inconsistency_is_reported_as_an_internal_error_without_a_reason() {
        let m = counter();
        let cond = default_conditions(&m, false);
        let o = inconsistent(
            &m,
            Inconsistency::Successors {
                action: 0,
                state: vec![1, 2],
            },
        );
        let body = check_report(&m, &cond, &o, CheckOutputs::default());
        let expected = merged(
            identity(&m),
            json!({
                "status": "internal_error",
                "ir_version": 1,
                "conditions": body["conditions"],
                "strategy": "bfs",
                "search": {"complete": false, "visited_states": 2, "transitions": 1, "time_ms": 0.0},
                "gate": {"time_ms": body["gate"]["time_ms"]},
                "inconsistency": {
                    "kind": "successors",
                    "action": "inc",
                    "state": null,
                    "encoded_state": [1, 2],
                    "message": SUCCESSORS,
                },
                "message": INCONSISTENCY,
            }),
        );
        assert_eq!(body, expected);
        assert_eq!(
            human(&body),
            format!(
                "InternalError: counter\n  不整合: {SUCCESSORS}\n    action: inc\n    encoded_state: [1,2]\n  {INCONSISTENCY}\n  探索: 未完走、訪問状態数 2、遷移数 1（探索器の報告）\n"
            )
        );
    }

    #[test]
    fn an_inconsistency_in_a_well_typed_state_shows_the_state_and_the_action_index() {
        let m = counter();
        let o = inconsistent(
            &m,
            Inconsistency::Successors {
                action: 5,
                state: vec![2],
            },
        );
        let body = check_report(&m, &default_conditions(&m, false), &o, CheckOutputs::default());
        assert_eq!(body["inconsistency"]["action"], json!(5));
        assert_eq!(body["inconsistency"]["state"], json!({"x": 2}));
        assert_eq!(body["inconsistency"]["encoded_state"], json!([2]));
        let text = human(&body);
        assert!(
            text.contains("    action: 5\n    state: x: 2\n    encoded_state: [2]\n"),
            "{text}"
        );
    }

    #[test]
    fn an_inconsistency_in_a_simulation_is_an_internal_error() {
        let m = counter();
        let cond = default_conditions(&m, false);
        let opts = SimOptions {
            seed: 3,
            traces: 1,
            max_steps: 1,
            interrupt: None,
            deadline: None,
        };
        let sampled = Sampled {
            found: Some(inconsistent(
                &m,
                Inconsistency::Successors {
                    action: 0,
                    state: vec![9],
                },
            )),
            stats: SimStats::default(),
        };
        let body = simulation_report(&m, &cond, &opts, &sampled, std::time::Duration::ZERO);
        assert_eq!(body["status"], "internal_error");
        assert_eq!(body["inconsistency"]["encoded_state"], json!([9]));
        assert_eq!(body["message"], INCONSISTENCY);
        assert!(body.get("reason").is_none(), "{body}");
        assert!(body.get("rejected").is_none(), "{body}");
    }

    #[test]
    fn an_inconsistency_in_the_graph_is_reported_in_place_of_the_coverage() {
        let m = counter();
        let body = inconsistency_report(
            &m,
            &Inconsistency::Successors {
                action: 0,
                state: vec![],
            },
        );
        let expected = merged(
            identity(&m),
            json!({
                "status": "internal_error",
                "inconsistency": {
                    "kind": "successors",
                    "action": "inc",
                    "state": null,
                    "encoded_state": [],
                    "message": SUCCESSORS,
                },
                "message": INCONSISTENCY,
            }),
        );
        assert_eq!(body, expected);
    }

    /// 判定ゲートが証拠を拒否した `internal_error` の出力は、不整合を区別する前と同じである。
    #[test]
    fn a_rejected_certificate_is_still_reported_with_its_reason() {
        let m = counter();
        let cond = default_conditions(&m, false);
        let cert = Evidence::Certificate(Certificate {
            conditions: cond.clone(),
            states: vec![vec![0]],
        });
        let o = check_evidence(m.checked(), &cond, cert, Stats::default());
        assert!(matches!(o.status, Status::InternalError(Internal::Rejected(_))));
        let body = check_report(&m, &cond, &o, CheckOutputs::default());
        assert_eq!(body["status"], "internal_error");
        assert_eq!(body["certificate_states"], json!(1));
        assert_eq!(
            body["rejected"],
            json!({
                "reason": "missing_successor", "state": {"x": 0}, "action": "inc",
                "message": "証明書の状態からの遷移先が、証明書に含まれません",
            })
        );
        let message = "探索器が生成した証拠を判定ゲートが拒否しました。fmspec の不具合です";
        assert_eq!(body["message"], message);
        assert!(body.get("inconsistency").is_none(), "{body}");
        assert_eq!(
            human(&body),
            format!(
                "InternalError: counter\n  拒否の理由: 証明書の状態からの遷移先が、証明書に含まれません\n    state: x: 0\n    action: inc\n  {message}\n  証明書の状態数 1\n  探索: 未完走、訪問状態数 0、遷移数 0（探索器の報告）\n"
            )
        );
    }

    /// `limit_name` が書くすべての理由に、人間向けの表示の文がある（キーの名前を括弧に添え、名前だけを示さない）。
    #[test]
    fn every_limit_has_a_reason_text() {
        let limits = [
            Limit::MaxStates,
            Limit::Interrupted,
            Limit::CheckBudget,
            Limit::MaxDepth,
            Limit::MaxTime,
            Limit::AbstractFailed,
        ];
        for limit in limits {
            // 理由を足したら、ここと human の `reason_text` に足す（`match` が網羅を強いる）。
            match limit {
                Limit::MaxStates
                | Limit::Interrupted
                | Limit::CheckBudget
                | Limit::MaxDepth
                | Limit::MaxTime
                | Limit::AbstractFailed => {}
            }
            let name = limit_name(limit);
            let body = json!({"status": "inconclusive", "model": "m", "reason": name});
            let text = human(&body);
            assert!(text.contains(&format!("（{name}）")), "{text}");
        }
    }
}
