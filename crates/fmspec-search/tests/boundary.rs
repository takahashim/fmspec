//! 仕様書 §17.1.1 の境界ケース。表の各行を独立したテストにする。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod common;

use common::*;
use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, Reject, TraceStep};
use fmspec_core::gate::{decide, decide_raw, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Site;
use fmspec_core::typing::InvalidModel;
use fmspec_ir::{parse, Model};
use fmspec_search::{check_evidence, Internal, Outcome, Stats, Status};
use serde_json::{json, Value};

fn accepted_again(m: &Model, o: &Outcome, deadlock: bool) -> VerdictKind {
    decide(m.checked(), &conditions(m, deadlock), &o.evidence).kind()
}

// ---- モデル検査の境界ケース ----

#[test]
fn tickets_is_verified() {
    let m = model(&tickets());
    let o = run_with(&m, false, Some(10_000));
    assert_eq!(o.status, Status::Verified);
    assert_eq!(certificate_states(&o), vec![vec![0], vec![1], vec![2], vec![3]]);
    assert_eq!(o.stats.visited_states, 4);
    assert!(o.stats.complete);
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Verified);
}

#[test]
fn removing_the_purchase_guard_gives_the_shortest_counterexample() {
    let m = model(&tickets_without_guard());
    let o = run(&m);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Invariant(0));
    assert_eq!(
        steps.iter().map(|s| (s.action, s.args.clone())).collect::<Vec<_>>(),
        vec![(0, vec![2]), (0, vec![2])]
    );
    assert_eq!(first_values(steps), vec![2, 4]);
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Violated);
}

#[test]
fn updating_to_a_constant_out_of_range_is_an_error() {
    let mut ir = tickets();
    ir["actions"][0]["updates"][0]["expr"] = json!({"int": 5});
    let m = model(&ir);
    let o = run(&m);
    assert_eq!(o.status, Status::Error);
    let (steps, claim) = trace(&o);
    assert!(steps.is_empty());
    assert_eq!(
        *claim,
        Claim::StepError(0, vec![1], Site::Update(0), ErrKind::OutOfRange(5))
    );
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Error);
    // 報告には、値5と型 0..4 を含める。
    let report = fmspec_ir::claim_to_json(&m, claim);
    assert_eq!(
        report["error"],
        json!({"kind": "out_of_range", "value": 5, "type": {"int": {"min": 0, "max": 4}}})
    );
    assert_eq!(report["target"], json!("sold"));
}

#[test]
fn a_violating_initial_state_is_a_zero_step_counterexample() {
    let mut ir = tickets();
    ir["states"][0]["initial"] = json!({"int": 4});
    let m = model(&ir);
    let o = run(&m);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert!(steps.is_empty());
    assert_eq!(*claim, Claim::Invariant(0));
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Violated);
}

/// 1状態で、同じ公開入力が内部選択に応じて success または forbidden を返す自己ループ。
fn responder() -> Value {
    let label = |v: &str| json!({"enum": {"type": "result", "variant": v}});
    json!({
        "ir_version": 1,
        "name": "responder",
        "enums": [{"name": "result", "variants": ["success", "forbidden"]}],
        "states": [{"name": "x", "type": {"int": {"min": 0, "max": 0}}, "initial": {"int": 0}}],
        "actions": [{
            "name": "request",
            "params": [{"name": "id", "type": {"int": {"min": 7, "max": 7}}}],
            "choices": [{"name": "allowed", "type": {"bool": {}}}],
            "updates": [],
            "output": {"type": {"enum": "result"}, "expr": {"ite": [{"choice": 0}, label("success"), label("forbidden")]}}
        }],
        "contracts": [{"name": "succeeds", "action": "request", "expr": {"eq": [{"output": {}}, label("success")]}}]
    })
}

#[test]
fn a_contract_violation_keeps_the_internal_choice_and_output() {
    let m = model(&responder());
    let o = run(&m);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Contract(0));
    // 公開引数 id=7、内部選択 allowed=false、出力 forbidden（ラベルの添字1）。
    assert_eq!(
        steps,
        &vec![TraceStep {
            action: 0,
            args: vec![7, 0],
            output: Some(1),
            state: vec![0]
        }]
    );
    let report = fmspec_ir::trace_to_json(
        &m,
        &fmspec_ir::Trace {
            conditions: conditions(&m, false),
            start: vec![0],
            steps: steps.clone(),
            claim: claim.clone(),
            seed: None,
        },
    );
    assert_eq!(report["steps"][0]["args"], json!({"id": 7}));
    assert_eq!(report["steps"][0]["choices"], json!({"allowed": false}));
    assert_eq!(report["steps"][0]["output"], json!({"value": "forbidden"}));
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Violated);

    // 証明書でも、この辺の契約違反を検出する。
    let cond = conditions(&m, false);
    let cert = Evidence::Certificate(Certificate {
        conditions: cond.clone(),
        states: vec![vec![0]],
    });
    let v = decide(m.checked(), &cond, &cert);
    assert_eq!(v.kind(), VerdictKind::Rejected);
    assert_eq!(v.reject(), Some(Reject::ContractNotHeld(0, 0)));
}

#[test]
fn a_stuck_initial_state_is_a_deadlock_unless_terminal() {
    let mut ir = counter(0, json!([]));
    ir["invariants"] = json!([{"name": "always", "expr": {"bool": true}}]);
    let m = model(&ir);
    let o = run_with(&m, true, None);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert!(steps.is_empty());
    assert_eq!(*claim, Claim::Deadlock);
    assert_eq!(accepted_again(&m, &o, true), VerdictKind::Violated);
    // デッドロック検査が無効なら、同じモデルは Verified。
    assert_eq!(run(&m).status, Status::Verified);

    ir["terminal"] = json!({"bool": true});
    let m = model(&ir);
    let o = run_with(&m, true, None);
    assert_eq!(o.status, Status::Verified);
    assert_eq!(accepted_again(&m, &o, true), VerdictKind::Verified);
}

#[test]
fn max_states_one_completes_on_a_self_loop_and_stops_at_a_new_state() {
    let m = model(&counter(1, json!([stay()])));
    let o = run_with(&m, false, Some(1));
    assert_eq!(o.status, Status::Verified);
    assert_eq!(o.stats.visited_states, 1);

    let m = model(&counter(1, json!([stay(), go("go", 0, 1)])));
    let o = run_with(&m, false, Some(1));
    assert_eq!(o.status, Status::Inconclusive(Limit::MaxStates));
    assert_eq!(o.stats.visited_states, 1);
    assert!(!o.stats.complete);
    // 上限が足りれば完走する。
    let o = run_with(&m, false, Some(2));
    assert_eq!(o.status, Status::Verified);
    assert_eq!(o.stats.visited_states, 2);
}

#[test]
fn a_certificate_may_be_a_superset_of_the_reachable_states() {
    let m = model(&counter(1, json!([stay()])));
    let cond = conditions(&m, false);
    let cert = Certificate {
        conditions: cond.clone(),
        states: vec![vec![0], vec![1]],
    };
    let v = decide(m.checked(), &cond, &Evidence::Certificate(cert.clone()));
    assert_eq!(v.kind(), VerdictKind::Verified);
    assert_eq!(cert.states.len(), 2);
    assert_eq!(run(&m).stats.visited_states, 1);
}

#[test]
fn certificates_missing_states_or_made_for_other_conditions_are_rejected() {
    let m = model(&counter(1, json!([go("go", 0, 1)])));
    let cond = conditions(&m, false);
    let decide_cert = |cert_cond: &Conditions, states: Vec<Vec<i64>>| {
        let cert = Certificate {
            conditions: cert_cond.clone(),
            states,
        };
        let v = decide(m.checked(), &cond, &Evidence::Certificate(cert));
        (v.kind(), v.reject())
    };
    assert_eq!(
        decide_cert(&cond, vec![vec![1]]),
        (VerdictKind::Rejected, Some(Reject::MissingInitial(0)))
    );
    assert_eq!(
        decide_cert(&cond, vec![vec![0]]),
        (VerdictKind::Rejected, Some(Reject::MissingSuccessor(0, 0)))
    );
    assert_eq!(
        decide_cert(&cond, vec![vec![0], vec![1]]),
        (VerdictKind::Verified, None)
    );
    // 別の対象操作で作成した証明書。状態集合が正しくても、検査条件の不一致で拒否する。
    let mut other = cond.clone();
    other.actions[0] = false;
    assert_eq!(
        decide_cert(&other, vec![vec![0], vec![1]]),
        (VerdictKind::Rejected, Some(Reject::ConditionMismatch))
    );
}

// ---- 式の境界ケース ----

fn status_of(invariant: Value) -> Status {
    let m = model(&big(invariant));
    let o = run(&m);
    match o.status {
        Status::Verified => assert_eq!(accepted_again(&m, &o, false), VerdictKind::Verified),
        Status::Violated => {
            let (steps, claim) = trace(&o);
            assert!(steps.is_empty());
            assert_eq!(*claim, Claim::Invariant(0));
            assert_eq!(accepted_again(&m, &o, false), VerdictKind::Violated);
        }
        Status::Error => {
            let (steps, claim) = trace(&o);
            assert!(steps.is_empty());
            assert_eq!(*claim, Claim::InvariantError(0, ErrKind::Overflow));
            assert_eq!(accepted_again(&m, &o, false), VerdictKind::Error);
        }
        other => panic!("想定外の結果: {other:?}"),
    }
    o.status
}

#[test]
fn ite_evaluates_only_the_chosen_branch() {
    let (e, t, f) = (overflowing(), json!({"bool": true}), json!({"bool": false}));
    assert_eq!(status_of(json!({"ite": [f, e, t]})), Status::Verified);
    assert_eq!(status_of(json!({"ite": [t, e, t]})), Status::Error);
}

#[test]
fn all_any_implies_stop_at_the_deciding_operand() {
    let (e, t, f) = (overflowing(), json!({"bool": true}), json!({"bool": false}));
    assert_eq!(status_of(json!({"all": [f, e]})), Status::Violated);
    assert_eq!(status_of(json!({"any": [t, e]})), Status::Verified);
    assert_eq!(status_of(json!({"implies": [f, e]})), Status::Verified);
}

#[test]
fn all_any_implies_evaluate_the_rest_otherwise() {
    let (e, t, f) = (overflowing(), json!({"bool": true}), json!({"bool": false}));
    assert_eq!(status_of(json!({"all": [t, e]})), Status::Error);
    assert_eq!(status_of(json!({"any": [f, e]})), Status::Error);
    assert_eq!(status_of(json!({"implies": [t, e]})), Status::Error);
}

#[test]
fn n_ary_all_and_any_evaluate_in_written_order() {
    let (e, t, f) = (overflowing(), json!({"bool": true}), json!({"bool": false}));
    assert_eq!(status_of(json!({"all": [t, t, f, e, t]})), Status::Violated);
    assert_eq!(status_of(json!({"all": [t, t, e, f, t]})), Status::Error);
    assert_eq!(status_of(json!({"any": [f, f, t, e, f]})), Status::Verified);
    assert_eq!(status_of(json!({"any": [f, f, e, t, f]})), Status::Error);
    assert_eq!(status_of(json!({"all": []})), Status::Verified);
    assert_eq!(status_of(json!({"any": []})), Status::Violated);
    assert_eq!(status_of(json!({"all": [t]})), Status::Verified);
    assert_eq!(status_of(json!({"any": [f]})), Status::Violated);
}

#[test]
fn updates_are_not_evaluated_when_the_guard_is_false() {
    let bump = |guard: bool| {
        let mut ir = big(json!({"ge": [{"var": 0}, {"int": 0}]}));
        ir["actions"] = json!([{
            "name": "bump",
            "guard": {"bool": guard},
            "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"int": 1}]}}]
        }]);
        model(&ir)
    };
    assert_eq!(run(&bump(false)).status, Status::Verified);
    let m = bump(true);
    let o = run(&m);
    assert_eq!(o.status, Status::Error);
    let (steps, claim) = trace(&o);
    assert!(steps.is_empty());
    assert_eq!(*claim, Claim::StepError(0, vec![], Site::Update(0), ErrKind::Overflow));
    assert_eq!(accepted_again(&m, &o, false), VerdictKind::Error);
}

// ---- 不具合を注入した探索器 ----

/// 購入の枚数のドメインを1枚だけに狭める。2枚購入を列挙し忘れる探索器が見るモデルに相当する。
fn only_single_purchase(mut ir: Value) -> Value {
    ir["actions"][0]["params"][0]["type"] = json!({"int": {"min": 1, "max": 1}});
    ir
}

#[test]
fn a_silently_truncated_search_is_an_internal_error() {
    let m = model(&tickets());
    let o = check_evidence(
        m.checked(),
        &conditions(&m, false),
        truncating_search(&m, 3),
        Stats::default(),
    );
    assert_eq!(certificate_states(&o), vec![vec![0], vec![1], vec![2]]);
    assert!(matches!(
        o.status,
        Status::InternalError(Internal::Rejected(Reject::MissingSuccessor(_, _)))
    ));
    assert_eq!(o.verdict.kind(), VerdictKind::Rejected);
}

#[test]
fn a_fabricated_counterexample_is_an_internal_error() {
    let m = model(&tickets());
    let cond = conditions(&m, false);
    // 販売数0からの購入で4に達する、存在しない遷移。
    let steps = vec![TraceStep {
        action: 0,
        args: vec![2],
        output: None,
        state: vec![4],
    }];
    let o = check_evidence(
        m.checked(),
        &cond,
        Evidence::Trace(vec![0], steps, Claim::Invariant(0)),
        Stats::default(),
    );
    assert_eq!(
        o.status,
        Status::InternalError(Internal::Rejected(Reject::StepMismatch(0)))
    );
}

#[test]
fn a_false_deadlock_report_is_an_internal_error() {
    let m = model(&tickets());
    let cond = conditions(&m, true);
    // 販売数3ではキャンセルが有効なので、デッドロックではない。
    let steps = vec![
        TraceStep {
            action: 0,
            args: vec![2],
            output: None,
            state: vec![2],
        },
        TraceStep {
            action: 0,
            args: vec![1],
            output: None,
            state: vec![3],
        },
    ];
    let o = check_evidence(
        m.checked(),
        &cond,
        Evidence::Trace(vec![0], steps, Claim::Deadlock),
        Stats::default(),
    );
    assert_eq!(
        o.status,
        Status::InternalError(Internal::Rejected(Reject::ClaimNotReproduced))
    );
}

#[test]
fn a_search_that_forgets_transitions_but_visits_every_state_is_still_verified() {
    let m = model(&tickets());
    // 2枚購入を列挙し忘れても、訪問済み集合は {0, 1, 2, 3} になる。
    let o = forgetful_search(&m, &model(&only_single_purchase(tickets())));
    assert_eq!(certificate_states(&o), vec![vec![0], vec![1], vec![2], vec![3]]);
    assert_eq!(o.status, Status::Verified);
}

#[test]
fn a_valid_but_longer_counterexample_is_accepted() {
    let m = model(&tickets_without_guard());
    let o = forgetful_search(&m, &model(&only_single_purchase(tickets_without_guard())));
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Invariant(0));
    assert_eq!(first_values(steps), vec![1, 2, 3, 4]);
    // 最短でないことは、不具合のない探索器との比較で検出する。
    assert_eq!(trace(&run(&m)).0.len(), 2);
}

#[test]
fn the_gate_rejects_a_model_that_skipped_validation() {
    let (mut raw, _, _) = parse(&tickets().to_string()).unwrap();
    let cond = Conditions {
        actions: vec![true, true],
        invariants: vec![true],
        contracts: vec![],
        deadlock: false,
    };
    // 状態変数の個数と、型の個数が一致しないモデル。
    raw.state_types.clear();
    let cert = Evidence::Certificate(Certificate {
        conditions: cond.clone(),
        states: vec![vec![0]],
    });
    let v = decide_raw(&raw, &cond, &cert);
    assert_eq!(v.kind(), VerdictKind::InvalidModel);
    assert_eq!(v.invalid(), Some(InvalidModel::Initial(0)));
}
