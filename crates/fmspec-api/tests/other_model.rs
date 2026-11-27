//! 別のモデルに対する証拠を、明示的な指定（`allow_other_model`）で検査する（仕様書 §10）。
//!
//! 指定がなければ、`model_digest` が違う証拠は読めない証拠として拒否する。
//! 指定があれば、証拠をこのモデルの名前と型で読み、判定ゲートがこのモデルに対して判定する。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, human, load, replay, replay_with, shrink, verify_certificate, Model};
use serde_json::{json, Value};

/// 状態変数 `x`（`0..=max`、初期値0）と、`x` を1増やす操作 `inc`、不変条件 `small`（`x <= bound`）を持つモデル。
/// `edit` でIRを書き換える。
fn counter(max: i64, bound: i64, edit: impl FnOnce(&mut Value)) -> Model {
    let mut ir = json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "x", "type": {"int": {"min": 0, "max": max}}, "initial": {"int": 0}}],
        "actions": [{
            "name": "inc",
            "guard": {"lt": [{"var": 0}, {"int": max}]},
            "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"int": 1}]}}]
        }],
        "invariants": [{"name": "small", "expr": {"le": [{"var": 0}, {"int": bound}]}}]
    });
    edit(&mut ir);
    load(&ir.to_string()).unwrap()
}

/// `x` を0に戻す操作 `reset` を加える。元のモデルの遷移はすべて残る。
fn with_reset(ir: &mut Value) {
    ir["actions"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name": "reset", "updates": [{"target": 0, "expr": {"int": 0}}]}));
}

fn allow() -> Value {
    json!({"allow_other_model": true})
}

/// `small` の違反に至るトレース（`x` が 0 → 1 → 2）。
fn violation(old: &Model) -> String {
    let body = check(old, &json!({}), None).unwrap();
    assert_eq!(body["status"], "violated");
    body["trace"].to_string()
}

#[test]
fn evidence_for_another_model_is_refused_unless_allowed() {
    let old = counter(3, 1, |_| {});
    let new = counter(3, 1, with_reset);
    assert_ne!(old.digest, new.digest);
    let trace = violation(&old);

    let refused = replay(&new, &trace);
    assert_eq!(refused["status"], "rejected");
    assert_eq!(refused["rejected"]["reason"], "unreadable");
    assert!(refused.get("evidence_model_digest").is_none(), "{refused}");
    for opts in [
        json!({}),
        json!({"allow_other_model": false}),
        json!({"allow_other_model": null}),
    ] {
        assert_eq!(replay_with(&new, &trace, &opts).unwrap(), refused);
        assert_eq!(shrink(&new, &trace, &opts, None).unwrap(), refused);
    }

    let body = replay_with(&new, &trace, &allow()).unwrap();
    assert_eq!(body["status"], "violated");
    assert_eq!(body["model_digest"], json!(new.digest));
    assert_eq!(body["evidence_model_digest"], json!(old.digest));
    // 結果のトレースは、判定ゲートがこのモデルで受理したもので、このモデルの digest を持つ。
    assert_eq!(body["trace"]["model_digest"], json!(new.digest));
    assert_eq!(replay(&new, &body["trace"].to_string())["status"], "violated");
    assert_eq!(
        human(&body).lines().nth(1).unwrap(),
        format!(
            "  別のモデルに対する証拠を、指定によりこのモデルで扱いました（証拠のdigestは {}）",
            old.digest
        )
    );

    // 同じモデルの証拠には、指定があっても evidence_model_digest を付けない。
    let same = replay_with(&old, &trace, &allow()).unwrap();
    assert_eq!(same, replay(&old, &trace));
    assert!(same.get("evidence_model_digest").is_none(), "{same}");
}

#[test]
fn the_gate_judges_the_evidence_against_the_current_model() {
    let old = counter(3, 1, |_| {});
    let trace = violation(&old);
    // 不変条件を直したモデルでは、元の反例はもう違反ではないので、主張どおりの事象が起きないとして拒否する。
    let fixed = counter(3, 2, |_| {});
    let body = replay_with(&fixed, &trace, &allow()).unwrap();
    assert_eq!(body["status"], "rejected");
    assert_eq!(body["rejected"]["reason"], "claim_not_reproduced", "{body}");
    assert_eq!(body["evidence_model_digest"], json!(old.digest));
    // 縮小も、判定ゲートが元のトレースを受理しなければ縮小しない。
    let shrunk = shrink(&fixed, &trace, &allow(), None).unwrap();
    assert_eq!(shrunk["status"], "rejected");
    assert!(shrunk.get("original_steps").is_none(), "{shrunk}");
    assert_eq!(shrunk["evidence_model_digest"], json!(old.digest));

    // guard を変えたモデルでは、トレースのステップがモデルの遷移と一致しない。
    let guarded = counter(3, 1, |ir| {
        ir["actions"][0]["guard"] = json!({"lt": [{"var": 0}, {"int": 1}]})
    });
    let body = replay_with(&guarded, &trace, &allow()).unwrap();
    assert_eq!(body["status"], "rejected");
    assert_ne!(body["rejected"]["reason"], "unreadable", "{body}");
}

#[test]
fn shrink_accepts_evidence_for_another_model_when_allowed() {
    let old = counter(3, 1, |_| {});
    let new = counter(3, 1, with_reset);
    // old の反例に、new の reset を挟んで遠回りにしたトレース。digest は old のまま。
    let mut trace: Value = serde_json::from_str(&violation(&old)).unwrap();
    let steps = trace["steps"].as_array().unwrap().clone();
    let reset = json!({"action": "reset", "args": {}, "choices": {}, "output": {"unit": true}, "state": {"x": 0}});
    trace["steps"] = json!([steps[0], reset, steps[0], steps[1]]);
    // 検査条件は名前で読む。reset も対象にする。
    trace["conditions"]["actions"] = json!(["inc", "reset"]);
    let body = shrink(&new, &trace.to_string(), &allow(), None).unwrap();
    assert_eq!(body["status"], "violated");
    assert_eq!(body["original_steps"], 4);
    assert_eq!(body["trace"]["steps"].as_array().unwrap().len(), 2);
    assert_eq!(body["trace"]["model_digest"], json!(new.digest));
    assert_eq!(body["evidence_model_digest"], json!(old.digest));
}

#[test]
fn evidence_that_does_not_fit_the_current_model_is_unreadable() {
    let old = counter(3, 1, |_| {});
    let trace = violation(&old);
    for (new, what) in [
        (counter(3, 1, |ir| ir["actions"][0]["name"] = json!("step")), "\"inc\""),
        (
            counter(3, 1, |ir| ir["invariants"][0]["name"] = json!("tiny")),
            "\"small\"",
        ),
        (counter(3, 1, |ir| ir["states"][0]["name"] = json!("y")), "initial"),
    ] {
        let body = replay_with(&new, &trace, &allow()).unwrap();
        assert_eq!(body["status"], "rejected");
        assert_eq!(body["rejected"]["reason"], "unreadable");
        assert_eq!(body["evidence_model_digest"], json!(old.digest));
        let message = body["rejected"]["message"].as_str().unwrap();
        let prefix = format!(
            "別のモデル（証拠のdigestは {}）に対する証拠を、このモデルでは読めません: ",
            old.digest
        );
        assert!(message.starts_with(&prefix), "{message}");
        assert!(message.contains(what), "{message}");
        // 読めない証拠には、読めていない検査条件を付けない。
        assert!(body.get("conditions").is_none(), "{body}");
        // 表示では、このモデルで扱ったとは書かず、digest は拒否の理由に1度だけ示す。
        assert_eq!(
            human(&body),
            format!("Rejected: counter\n  拒否の理由: {message}\n")
        );
    }
    // JSONとして読めない証拠と、版の誤りは、digest を読む前の誤りなので、そのまま報告する。
    let body = replay_with(&old, "{", &allow()).unwrap();
    assert!(body.get("evidence_model_digest").is_none(), "{body}");
}

#[test]
fn a_certificate_for_another_model_is_checked_against_the_current_model() {
    let opts = json!({"invariants": [], "certificate": true});
    let old = counter(3, 1, |_| {});
    let cert = check(&old, &opts, None).unwrap()["certificate"].to_string();
    let conditions = json!({"invariants": []});
    let mut allowed = conditions.clone();
    allowed["allow_other_model"] = json!(true);

    // 不変条件 small を変えたモデル。検査条件の対象外なので、証明書はそのまま成り立つ。
    let new = counter(3, 2, |_| {});
    let refused = verify_certificate(&new, &cert, &conditions, None).unwrap();
    assert_eq!(refused["rejected"]["reason"], "unreadable");
    let body = verify_certificate(&new, &cert, &allowed, None).unwrap();
    assert_eq!(body["status"], "verified");
    assert_eq!(body["evidence_model_digest"], json!(old.digest));

    // 検査条件は名前で比べる。操作 reset を加えたモデルの既定の検査条件は reset を含むので、
    // inc だけを対象にした証明書とは一致しない。
    let reset = counter(3, 1, with_reset);
    let body = verify_certificate(&reset, &cert, &allowed, None).unwrap();
    assert_eq!(body["rejected"]["reason"], "condition_mismatch");

    // 状態の範囲を広げると、証明書の状態 3 からの遷移先 4 が証明書にないので拒否する。
    let wider = counter(5, 1, |_| {});
    let body = verify_certificate(&wider, &cert, &allowed, None).unwrap();
    assert_eq!(body["status"], "rejected");
    assert_eq!(body["rejected"]["reason"], "missing_successor");
    assert_eq!(body["evidence_model_digest"], json!(old.digest));
}

#[test]
fn allow_other_model_is_a_boolean() {
    let m = counter(3, 1, |_| {});
    let trace = violation(&m);
    let expected = "allow_other_model は真偽値です（\"yes\"）";
    let bad = json!({"allow_other_model": "yes"});
    assert_eq!(replay_with(&m, &trace, &bad).unwrap_err(), expected);
    assert_eq!(shrink(&m, &trace, &bad, None).unwrap_err(), expected);
    assert_eq!(verify_certificate(&m, "{}", &bad, None).unwrap_err(), expected);
    assert_eq!(
        replay_with(&m, &trace, &json!({"attempts": 1})).unwrap_err(),
        "未知のオプション \"attempts\""
    );
    // check と simulate は証拠を読まないので、受け付けない。
    assert!(check(&m, &json!({"allow_other_model": true}), None).is_err());
}

/// 状態変数 `x`（`0..=4`、初期値0）と、`x` に引数 `d`（`0..=2`）を足す操作 `add`、不変条件 `small`（`x <= 2`）を持つモデル。
fn adder(edit: impl FnOnce(&mut Value)) -> Model {
    let mut ir = json!({
        "ir_version": 1,
        "name": "adder",
        "states": [{"name": "x", "type": {"int": {"min": 0, "max": 4}}, "initial": {"int": 0}}],
        "actions": [{
            "name": "add",
            "params": [{"name": "d", "type": {"int": {"min": 0, "max": 2}}}],
            "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"param": 0}]}}]
        }],
        "invariants": [{"name": "small", "expr": {"le": [{"var": 0}, {"int": 2}]}}]
    });
    edit(&mut ir);
    load(&ir.to_string()).unwrap()
}

#[test]
fn shrinking_evidence_for_another_model_also_makes_arguments_smaller() {
    let old = adder(|_| {});
    let new = adder(with_reset);
    assert_ne!(old.digest, new.digest);
    let step = |d: i64, x: i64| json!({"action": "add", "args": {"d": d}, "choices": {}, "output": {"unit": true}, "state": {"x": x}});
    let trace = json!({
        "trace_version": 1,
        "model_digest": old.digest,
        "seed": null,
        "conditions": {"actions": ["add"], "invariants": ["small"], "contracts": [], "deadlock": false},
        "initial": {"x": 0},
        "steps": [step(2, 2), step(2, 4)],
        "claim": {"violation": "invariant", "name": "small"}
    });
    // どちらのステップを削っても x は 2 以下だが、最初の引数を 1 にしても違反は残る。
    let body = shrink(&new, &trace.to_string(), &allow(), None).unwrap();
    assert_eq!(body["status"], "violated", "{body}");
    assert_eq!(body["trace"]["steps"], json!([step(1, 1), step(2, 3)]));
    assert_eq!(body["original_steps"], 2);
    assert_eq!(body["evidence_model_digest"], json!(old.digest));
    assert_eq!(body["trace"]["model_digest"], json!(new.digest));
}
