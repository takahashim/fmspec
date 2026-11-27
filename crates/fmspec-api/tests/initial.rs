//! 初期状態が複数あるモデルの検査。探索、シミュレーション、縮小、適合性検査のセッションを確かめる。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, load, replay, shrink, simulate, verify_certificate, Model, Session};
use serde_json::{json, Value};
use std::sync::Arc;

/// `n`（0..=4）の初期値を 0 か 3 とし、`inc` で1ずつ増やすモデル。`stay` は何も変えない。
fn counter(max: i64) -> Model {
    let n = json!({"var": 0});
    let ir = json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": 4}}, "initial_in": [{"int": 3}, {"int": 0}]}],
        "actions": [
            {"name": "inc", "guard": {"lt": [n, {"int": 4}]}, "updates": [{"target": 0, "expr": {"add": [n, {"int": 1}]}}]},
            {"name": "stay", "guard": {"bool": true}, "updates": []}
        ],
        "invariants": [{"name": "bounded", "expr": {"le": [n, {"int": max}]}}]
    });
    load(&ir.to_string()).unwrap()
}

#[test]
fn search_starts_from_every_initial_state() {
    let m = counter(3);
    let result = check(&m, &json!({}), None).unwrap();
    assert_eq!(result["status"], "violated", "{result}");
    assert_eq!(result["trace"]["initial"], json!({"n": 3}));
    assert_eq!(result["trace"]["steps"].as_array().unwrap().len(), 1);
    assert_eq!(replay(&m, &result["trace"].to_string())["status"], "violated");

    // 開始状態を初期状態でない状態に書き換えたトレースは拒否する。
    let mut forged = result["trace"].clone();
    forged["initial"] = json!({"n": 2});
    forged["steps"][0]["state"] = json!({"n": 3});
    forged["claim"] = json!({"violation": "deadlock"});
    let again = replay(&m, &forged.to_string());
    assert_eq!(again["status"], "rejected", "{again}");
    assert_eq!(again["rejected"]["reason"], "bad_start", "{again}");

    let m = counter(4);
    let result = check(&m, &json!({"certificate": true}), None).unwrap();
    assert_eq!(result["status"], "verified", "{result}");
    assert_eq!(result["search"]["visited_states"], 5);
    let again = verify_certificate(&m, &result["certificate"].to_string(), &json!({}), None).unwrap();
    assert_eq!(again["status"], "verified", "{again}");
}

#[test]
fn simulation_and_shrinking_keep_the_start_state() {
    let m = counter(3);
    let result = simulate(&m, &json!({"seed": 7, "traces": 50, "max_steps": 10}), None).unwrap();
    assert_eq!(result["status"], "violated", "{result}");
    assert_eq!(replay(&m, &result["trace"].to_string())["status"], "violated");

    let mut trace = check(&m, &json!({}), None).unwrap()["trace"].clone();
    let inc = trace["steps"][0].clone();
    let mut stay = inc.clone();
    stay["action"] = json!("stay");
    stay["state"] = json!({"n": 3});
    trace["steps"] = json!([stay, stay, inc]);
    let shrunk = shrink(&m, &trace.to_string(), &json!({}), None).unwrap();
    assert_eq!(shrunk["status"], "violated", "{shrunk}");
    assert_eq!(shrunk["original_steps"], 3);
    assert_eq!(shrunk["trace"]["initial"], json!({"n": 3}));
    assert_eq!(shrunk["trace"]["steps"].as_array().unwrap().len(), 1);
}

#[test]
fn a_session_starts_from_the_initial_states_matching_the_observation() {
    let m = Arc::new(counter(4));
    let mut session = Session::new(m.clone(), &json!({})).unwrap();
    let started = session.start(&json!({"n": 3})).unwrap();
    assert_eq!(started["status"], "continue", "{started}");

    let mut session = Session::new(m, &json!({})).unwrap();
    let failed: Value = session.start(&json!({"n": 2})).unwrap();
    assert_eq!(failed["status"], "conformance_failure", "{failed}");
    assert_eq!(failed["expected"], json!([{"state": {"n": 0}}, {"state": {"n": 3}}]));
}

/// 観測しない状態変数だけが違う初期状態は、初期観測の不適合の `expected` で1つにまとめる（照合後の不適合と同じ）。
#[test]
fn an_initial_conformance_failure_lists_each_expected_observation_once() {
    let ir = json!({
        "ir_version": 1,
        "name": "pair",
        "states": [
            {"name": "a", "type": {"int": {"min": 0, "max": 4}}, "initial_in": [{"int": 3}, {"int": 0}]},
            {"name": "b", "type": {"int": {"min": 0, "max": 1}}, "initial_in": [{"int": 0}, {"int": 1}]}
        ],
        "actions": []
    });
    let m = Arc::new(load(&ir.to_string()).unwrap());
    let mut session = Session::new(m, &json!({"observe": ["a"]})).unwrap();
    let failed = session.start(&json!({"a": 2})).unwrap();
    assert_eq!(failed["status"], "conformance_failure", "{failed}");
    assert_eq!(
        failed["expected"],
        json!([{"state": {"a": 0}}, {"state": {"a": 3}}]),
        "{failed}"
    );
    assert_eq!(failed["mismatch"], json!(["a"]));
}

#[test]
fn a_session_stops_when_the_initial_candidates_exceed_the_limit() {
    let m = Arc::new(counter(4));
    let mut session = Session::new(m, &json!({"observe": [], "max_candidates": 1})).unwrap();
    let started = session.start(&json!({})).unwrap();
    assert_eq!(started["status"], "inconclusive", "{started}");
    assert_eq!(started["reason"], "max_candidates");
}
