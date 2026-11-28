//! 判定ゲートの資源上限と中断。打ち切った検査は `inconclusive` になり、モデルについて何も主張しない。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, load, verify_certificate, Model};
use fmspec_core::kernel::evidence::{Evidence, Limit};
use fmspec_core::kernel::gate::VerdictKind;
use fmspec_ir::default_conditions;
use fmspec_search::{evidence_cost, judge, GateOptions};
use serde_json::{json, Value};
use std::cell::Cell;
use std::time::Instant;

/// `n`（0..=max）を1ずつ増やすモデル。不変条件 `slow` は、`width` × `width` 回の量化で評価する。
fn counter(max: i64, width: i64) -> Model {
    let n = json!({"var": 0});
    let range = json!({"int": {"min": 0, "max": width - 1}});
    let slow = json!({"forall": {"name": "x", "type": range, "body":
        {"forall": {"name": "y", "type": range, "body":
            {"ge": [{"add": [{"local": "x"}, {"add": [{"local": "y"}, n]}]}, {"int": 0}]}}}}});
    let ir = json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": max}}, "initial": {"int": 0}}],
        "actions": [{"name": "inc", "guard": {"lt": [n, {"int": max}]},
                     "updates": [{"target": 0, "expr": {"add": [n, {"int": 1}]}}]}],
        "invariants": [{"name": "slow", "expr": slow}]
    });
    load(&ir.to_string()).unwrap()
}

#[test]
fn the_cost_bound_grows_with_quantifiers_and_states() {
    let small = counter(3, 1);
    let wide = counter(3, 8);
    let cond = default_conditions(&small, false);
    let result = check(&small, &json!({"certificate": true}), None).unwrap();
    let cert = fmspec_ir::certificate_from_json(&small, &result["certificate"].to_string()).unwrap();
    let cost = evidence_cost(small.checked(), &cond, &Evidence::Certificate(cert.clone()));
    assert!(cost > 0);
    // 上限は証明書の状態の数に比例する。
    let mut half = cert.clone();
    half.states.truncate(2);
    assert_eq!(
        evidence_cost(small.checked(), &cond, &Evidence::Certificate(half)) * 2,
        cost
    );
    // 量化の範囲を縦横それぞれ8倍にすると、評価回数の上限は大きく増える。
    let wide_cost = evidence_cost(wide.checked(), &cond, &Evidence::Certificate(cert));
    assert!(wide_cost > 16 * cost, "{wide_cost} {cost}");
}

#[test]
fn evidence_over_the_budget_is_not_checked() {
    let m = counter(3, 4);
    let ok = check(&m, &json!({"certificate": true}), None).unwrap();
    assert_eq!(ok["status"], "verified", "{ok}");

    let limited = check(&m, &json!({"max_check_cost": 10}), None).unwrap();
    assert_eq!(limited["status"], "inconclusive", "{limited}");
    assert_eq!(limited["reason"], "max_check_cost");
    assert!(limited.get("certificate_states").is_none());

    let cert = ok["certificate"].to_string();
    let limited = verify_certificate(&m, &cert, &json!({"max_check_cost": 10}), None).unwrap();
    assert_eq!(limited["status"], "inconclusive", "{limited}");
    assert_eq!(limited["reason"], "max_check_cost");
    let enough = verify_certificate(&m, &cert, &json!({"max_check_cost": 1_000_000}), None).unwrap();
    assert_eq!(enough["status"], "verified", "{enough}");

    // 検査条件の違う証明書は、見積もりが上限を超えても、判定ゲートが検査条件の不一致で拒否する。
    for opts in [
        json!({"invariants": [], "max_check_cost": 10}),
        json!({"invariants": [], "max_time_ms": 0}),
    ] {
        let mismatch = verify_certificate(&m, &cert, &opts, None).unwrap();
        assert_eq!(mismatch["status"], "rejected", "{mismatch}");
        assert_eq!(mismatch["rejected"]["reason"], "condition_mismatch", "{mismatch}");
    }

    // 違反のトレースも、上限を超えれば検査しない。
    let bad = with_invariant(json!({"lt": [{"var": 0}, {"int": 2}]}));
    let violated = check(&bad, &json!({}), None).unwrap();
    assert_eq!(violated["status"], "violated", "{violated}");
    let limited = check(&bad, &json!({"max_check_cost": 1}), None).unwrap();
    assert_eq!(limited["status"], "inconclusive", "{limited}");
    assert!(limited.get("trace").is_none());
}

fn with_invariant(expr: Value) -> Model {
    let n = json!({"var": 0});
    let ir = json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": 3}}, "initial": {"int": 0}}],
        "actions": [{"name": "inc", "guard": {"lt": [n, {"int": 3}]},
                     "updates": [{"target": 0, "expr": {"add": [n, {"int": 1}]}}]}],
        "invariants": [{"name": "small", "expr": expr}]
    });
    load(&ir.to_string()).unwrap()
}

#[test]
fn a_certificate_check_stops_between_states_when_interrupted() {
    // 1状態の検査の見積もりが区切りの目安を超えるので、1状態ごとに中断要求を確かめる。
    let m = counter(3, 1024);
    let cond = default_conditions(&m, false);
    let cert = || {
        Evidence::Certificate(fmspec_core::kernel::evidence::Certificate {
            conditions: cond.clone(),
            states: (0..=3).map(|n| vec![n]).collect(),
        })
    };
    let asked = Cell::new(0);
    let interrupt = || {
        asked.set(asked.get() + 1);
        true
    };
    let opts = GateOptions {
        max_cost: None,
        interrupt: Some(&interrupt),
        deadline: None,
    };
    let (verdict, evidence) = judge(m.checked(), &cond, cert(), &opts);
    assert_eq!(verdict.kind(), VerdictKind::Inconclusive);
    assert_eq!(verdict.limit(), Some(Limit::Interrupted));
    assert!(matches!(evidence, Evidence::Unavailable(Limit::Interrupted)));
    assert_eq!(asked.get(), 1);

    // 中断を求めなければ、最後まで検査して受理する。
    let never = || false;
    let opts = GateOptions {
        max_cost: None,
        interrupt: Some(&never),
        deadline: None,
    };
    let (verdict, _) = judge(m.checked(), &cond, cert(), &opts);
    assert_eq!(verdict.kind(), VerdictKind::Verified);
}

#[test]
fn a_certificate_check_stops_between_states_at_the_deadline() {
    let m = counter(3, 1024);
    let cond = default_conditions(&m, false);
    let cert = Evidence::Certificate(fmspec_core::kernel::evidence::Certificate {
        conditions: cond.clone(),
        states: (0..=3).map(|n| vec![n]).collect(),
    });
    let opts = GateOptions {
        max_cost: None,
        interrupt: None,
        deadline: Some(Instant::now()),
    };
    let (verdict, evidence) = judge(m.checked(), &cond, cert, &opts);
    assert_eq!(verdict.kind(), VerdictKind::Inconclusive);
    assert_eq!(verdict.limit(), Some(Limit::MaxTime));
    assert!(matches!(evidence, Evidence::Unavailable(Limit::MaxTime)));
}

#[test]
fn the_depth_and_time_limits_are_reported_by_name() {
    let m = counter(3, 1);
    // 到達状態は深さ3まで。深さ3では完走し、深さ2では状態3が残る。
    let full = check(&m, &json!({"max_depth": 3}), None).unwrap();
    assert_eq!(full["status"], "verified", "{full}");
    let short = check(&m, &json!({"max_depth": 2}), None).unwrap();
    assert_eq!(short["status"], "inconclusive", "{short}");
    assert_eq!(short["reason"], "max_depth");
    assert_eq!(short["search"]["complete"], false);
    assert_eq!(short["search"]["visited_states"], 3);
    assert!(short.get("certificate_states").is_none());
    // 証明書を求めても、打ち切った探索の状態集合は含めない。
    let asked = check(&m, &json!({"max_depth": 2, "certificate": true}), None).unwrap();
    assert!(asked.get("certificate").is_none());

    let timed = check(&m, &json!({"max_time_ms": 0}), None).unwrap();
    assert_eq!(timed["status"], "inconclusive", "{timed}");
    assert_eq!(timed["reason"], "max_time_ms");
    let ample = check(&m, &json!({"max_time_ms": u64::MAX}), None).unwrap();
    assert_eq!(ample["status"], "verified", "{ample}");

    let sim = fmspec_api::simulate(&m, &json!({"max_time_ms": 0}), None).unwrap();
    assert_eq!(sim["status"], "inconclusive", "{sim}");
    assert_eq!(sim["reason"], "max_time_ms");

    let graph = fmspec_api::coverage(&m, &json!({"max_time_ms": 0}), None).unwrap();
    assert_eq!(graph["complete"], false, "{graph}");
    let paths = fmspec_api::test_paths(&m, &json!({"max_time_ms": 0}), None).unwrap();
    assert_eq!(paths["complete"], false, "{paths}");
    let paths = fmspec_api::test_paths(&m, &json!({"max_time_ms": 60_000}), None).unwrap();
    assert_eq!(paths["complete"], true, "{paths}");
}
