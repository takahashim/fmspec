//! 証明書、トレース、検査条件のJSONの読み込み。主張の往復と、形式の誤りの拒否。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim};
use fmspec_core::source::FAIL_MISSING_KEY;
use fmspec_core::step::Site;
use fmspec_ir::{
    certificate_from_json, certificate_to_json, claim_to_json, conditions_from_json, default_conditions, load,
    trace_from_json, trace_to_json, Model, Trace, TraceError,
};
use serde_json::{json, Value};

/// 2スロットの状態変数 `p` と1スロットの `n` を、操作 `move` が更新するモデル。
/// 更新のスロットは (p, 0)、(p, 1)、(n, 0) の順になる。
fn model() -> Model {
    let digit = json!({"int": {"min": 0, "max": 3}});
    let ir = json!({
        "ir_version": 1,
        "name": "evidence",
        "states": [
            {"name": "p", "type": {"tuple": [digit, digit]}, "initial": {"tuple": [{"int": 0}, {"int": 0}]}},
            {"name": "n", "type": digit, "initial": {"int": 0}}
        ],
        "actions": [{
            "name": "move",
            "updates": [
                {"target": 0, "expr": {"tuple": [{"int": 1}, {"int": 2}]}},
                {"target": 1, "expr": {"int": 3}}
            ]
        }],
        "invariants": [{"name": "small", "expr": {"le": [{"var": 1}, {"int": 3}]}}]
    });
    load(&ir.to_string()).unwrap_or_else(|e| panic!("{e}"))
}

fn trace(m: &Model, claim: Claim) -> Trace {
    Trace {
        conditions: default_conditions(m, false),
        start: vec![0, 0, 0],
        steps: vec![],
        claim,
        seed: None,
    }
}

fn trace_json(m: &Model, claim: Claim) -> Value {
    trace_to_json(m, &trace(m, claim))
}

fn read_back(m: &Model, json: &Value) -> Result<Trace, TraceError> {
    trace_from_json(m, &json.to_string())
}

fn format_error(m: &Model, json: &Value) -> String {
    match read_back(m, json) {
        Err(TraceError::Format(message)) => message,
        other => panic!("形式の誤りとして拒否されるはず: {other:?}"),
    }
}

#[test]
fn update_errors_name_the_target_and_the_slot_of_an_out_of_range_value() {
    let m = model();
    let claim = Claim::StepError(0, vec![], Site::Update(1), ErrKind::OutOfRange(4));
    let json = claim_to_json(&m, &claim);
    assert_eq!(
        (&json["target"], &json["slot"], &json["error"]["type"]),
        (&json!("p"), &json!(1), &json!({"int": {"min": 0, "max": 3}}))
    );
    assert_eq!(read_back(&m, &trace_json(&m, claim.clone())).unwrap().claim, claim);

    // 1スロットの状態変数には slot を付けない。
    let claim = Claim::StepError(0, vec![], Site::Update(2), ErrKind::OutOfRange(-1));
    let json = claim_to_json(&m, &claim);
    assert_eq!((&json["target"], json.get("slot")), (&json!("n"), None));
    assert_eq!(read_back(&m, &trace_json(&m, claim.clone())).unwrap().claim, claim);

    // 範囲外更新以外の評価の失敗は、どのスロットでも同じなので、状態変数の最初のスロットとして読む。
    let claim = Claim::StepError(0, vec![], Site::Update(1), ErrKind::Overflow);
    assert_eq!(claim_to_json(&m, &claim).get("slot"), None);
    assert_eq!(
        read_back(&m, &trace_json(&m, claim)).unwrap().claim,
        Claim::StepError(0, vec![], Site::Update(0), ErrKind::Overflow)
    );

    // 更新しない状態変数やスロットは拒否する。
    let mut json = trace_json(&m, Claim::StepError(0, vec![], Site::Update(1), ErrKind::OutOfRange(4)));
    json["claim"]["slot"] = json!(2);
    assert!(format_error(&m, &json).contains("\"p\" を更新しません"));
    // 2^32 + 1 は、32ビットで切り詰めると 1 になるが、そう読まない。
    json["claim"]["slot"] = json!(4_294_967_297u64);
    assert!(format_error(&m, &json).contains("を更新しません"));
    // 整数でない slot を、最初のスロットとして読まない。
    json["claim"]["slot"] = json!("1");
    assert!(format_error(&m, &json).contains("claim.slot"));
}

#[test]
fn failures_are_written_by_name_and_unknown_codes_by_number() {
    let m = model();
    for (kind, error) in [
        (ErrKind::Failed(FAIL_MISSING_KEY), json!({"kind": "missing_key"})),
        (ErrKind::Failed(99), json!({"kind": "failed", "code": 99})),
        (ErrKind::DivByZero, json!({"kind": "division_by_zero"})),
    ] {
        let claim = Claim::InvariantError(0, kind);
        let json = trace_json(&m, claim.clone());
        assert_eq!(json["claim"]["error"], error);
        assert_eq!(read_back(&m, &json).unwrap().claim, claim);
    }
    let mut json = trace_json(&m, Claim::TerminalError(ErrKind::Overflow));
    json["claim"]["error"] = json!({"kind": "explosion"});
    assert!(format_error(&m, &json).contains("claim.error.kind"));
    json["claim"]["error"] = json!({"kind": "out_of_range"});
    assert!(format_error(&m, &json).contains("claim.error.value"));
}

#[test]
fn malformed_traces_are_rejected_as_format_errors() {
    let m = model();
    let good = trace_json(&m, Claim::Invariant(0));
    let broken = |change: &dyn Fn(&mut Value)| {
        let mut json = good.clone();
        change(&mut json);
        format_error(&m, &json)
    };
    assert!(broken(&|j| j["trace_version"] = json!(2)).contains("trace_version"));
    assert!(broken(&|j| j["claim"]["name"] = json!("large")).contains("未定義の不変条件"));
    assert!(broken(&|j| j["claim"] = json!({"violation": "liveness"})).contains("claim.violation"));
    assert!(broken(&|j| j["steps"] = json!({})).contains("steps"));
    let step = json!({"action": "move", "args": {}, "choices": {}, "output": {"unit": true},
                      "state": {"p": [1, 2], "n": 3}});
    assert!(read_back(&m, &{
        let mut j = good.clone();
        j["steps"] = json!([step]);
        j
    })
    .is_ok());
    let without = |key: &str| {
        let mut s = step.clone();
        s.as_object_mut().unwrap().remove(key);
        json!([s])
    };
    assert!(broken(&|j| j["steps"] = without("output")).contains("steps[0]: output が必要"));
    assert!(broken(&|j| j["steps"] = without("state")).contains("steps[0]: state が必要"));
    assert!(broken(&|j| j["steps"] = json!([{"action": "jump"}])).contains("未定義の操作"));
    assert!(broken(&|j| j["initial"] = json!({"p": [0, 0]})).contains("initial"));
    assert!(matches!(trace_from_json(&m, "{"), Err(TraceError::Json(_))));
}

/// `model_digest` のない証拠は、別のモデルに対する証拠でなく、形式の誤りとして拒否する。
#[test]
fn evidence_without_a_model_digest_is_a_format_error() {
    let m = model();
    let mut json = trace_json(&m, Claim::Deadlock);
    json.as_object_mut().unwrap().remove("model_digest");
    assert!(format_error(&m, &json).contains("model_digest"));
    json["model_digest"] = json!(1);
    assert!(format_error(&m, &json).contains("model_digest"));

    let cert = Certificate {
        conditions: default_conditions(&m, false),
        states: vec![vec![0, 0, 0]],
    };
    let mut json = certificate_to_json(&m, &cert);
    json.as_object_mut().unwrap().remove("model_digest");
    match certificate_from_json(&m, &json.to_string()) {
        Err(TraceError::Format(message)) => assert!(message.contains("model_digest"), "{message}"),
        other => panic!("形式の誤りとして拒否されるはず: {other:?}"),
    }
}

#[test]
fn a_seed_is_null_or_a_non_negative_integer() {
    let m = model();
    let mut json = trace_json(&m, Claim::Deadlock);
    assert_eq!(json["seed"], Value::Null);
    assert_eq!(read_back(&m, &json).unwrap().seed, None);
    json.as_object_mut().unwrap().remove("seed");
    assert_eq!(read_back(&m, &json).unwrap().seed, None);
    json["seed"] = json!(u64::MAX);
    assert_eq!(read_back(&m, &json).unwrap().seed, Some(u64::MAX));
    for bad in [json!("7"), json!(-1), json!(1.5)] {
        json["seed"] = bad;
        assert!(format_error(&m, &json).contains("seed"));
    }
}

#[test]
fn certificates_are_deduplicated_and_rows_must_match_the_state_variables() {
    let m = model();
    let cert = Certificate {
        conditions: default_conditions(&m, false),
        states: vec![vec![1, 2, 3], vec![0, 0, 0], vec![1, 2, 3]],
    };
    let mut json = certificate_to_json(&m, &cert);
    assert_eq!(json["states"][0], json!([[1, 2], 3]));
    let back = certificate_from_json(&m, &json.to_string()).unwrap();
    assert_eq!(back.states, vec![vec![0, 0, 0], vec![1, 2, 3]]);

    json["states"][1] = json!([[0, 0]]);
    match certificate_from_json(&m, &json.to_string()) {
        Err(TraceError::Format(message)) => assert!(message.contains("states[1]"), "{message}"),
        other => panic!("{other:?}"),
    }
    json["states"][1] = json!([[0, 0], true]);
    assert!(matches!(
        certificate_from_json(&m, &json.to_string()),
        Err(TraceError::Format(_))
    ));
}

#[test]
fn conditions_name_defined_items_only() {
    let m = model();
    let names = &m.names;
    let ok = json!({"actions": ["move"], "invariants": [], "contracts": [], "deadlock": true});
    let c = conditions_from_json(names, &ok).unwrap();
    assert_eq!((c.actions, c.invariants, c.deadlock), (vec![true], vec![false], true));
    let with = |key: &str, v: Value| {
        let mut c = ok.clone();
        c[key] = v;
        conditions_from_json(names, &c).unwrap_err()
    };
    assert!(with("actions", json!(["jump"])).contains("未定義の名前 \"jump\""));
    assert!(with("invariants", json!("small")).contains("名前の配列"));
    assert!(with("deadlock", json!(null)).contains("deadlock"));
    assert!(with("fairness", json!(true)).contains("未知のキー"));
    // Setの要素の重複と同じく、名前の重複は形式の誤りとする。
    assert_eq!(
        with("actions", json!(["move", "move"])),
        "conditions.actions: 名前 \"move\" が重複しています"
    );
    assert!(with("invariants", json!(["small", "small"])).contains("重複"));
}

/// 証拠の状態にあるSetの要素の重複は、形式の誤りとして拒否する。
#[test]
fn duplicate_set_elements_in_evidence_states_are_format_errors() {
    let bit = json!({"int": {"min": 0, "max": 1}});
    let ir = json!({
        "ir_version": 1,
        "name": "evidence_set",
        "states": [{"name": "s", "type": {"set": bit}, "initial": {"set": {"of": bit, "items": []}}}],
        "actions": [{"name": "noop"}]
    });
    let m = load(&ir.to_string()).unwrap_or_else(|e| panic!("{e}"));
    let mut json = trace_json(&m, Claim::Deadlock);
    assert!(read_back(&m, &json).is_ok());
    json["initial"] = json!({"s": [1, 1]});
    assert_eq!(
        format_error(&m, &json),
        "initial: 状態変数 \"s\": 要素 1 が重複しています"
    );
    json["initial"] = json!({"s": []});
    json["steps"] = json!([{"action": "noop", "args": {}, "choices": {}, "output": {"unit": true},
                            "state": {"s": [0, 1, 0]}}]);
    let message = format_error(&m, &json);
    assert!(message.contains("状態変数 \"s\": 要素 0 が重複しています"), "{message}");

    let cert = Certificate {
        conditions: default_conditions(&m, false),
        states: vec![vec![0, 0]],
    };
    let mut json = certificate_to_json(&m, &cert);
    json["states"][0] = json!([[1, 1]]);
    match certificate_from_json(&m, &json.to_string()) {
        Err(TraceError::Format(message)) => assert_eq!(message, "states[0]: 要素 1 が重複しています"),
        other => panic!("形式の誤りとして拒否されるはず: {other:?}"),
    }
}

/// 証拠の各オブジェクトは、書けるキーが決まっている。書き間違いを黙って無視しないよう、未知のキーは形式の誤りとする。
#[test]
fn unknown_keys_in_evidence_are_format_errors() {
    let m = model();
    let step = json!({"action": "move", "args": {}, "choices": {}, "output": {"unit": true},
                      "state": {"p": [1, 2], "n": 3}});
    let mut good = trace_json(&m, Claim::Invariant(0));
    good["steps"] = json!([step]);
    assert!(read_back(&m, &good).is_ok());
    let broken = |change: &dyn Fn(&mut Value)| {
        let mut json = good.clone();
        change(&mut json);
        format_error(&m, &json)
    };
    // 初期状態が1つのモデルで initial を書き間違えても、初期状態から始めるトレースとして読まない。
    let typo = broken(&|j| {
        let initial = j.as_object_mut().unwrap().remove("initial").unwrap();
        j["intial"] = initial;
    });
    assert_eq!(typo, "トレース: 未知のキー \"intial\"");
    assert_eq!(
        broken(&|j| j["steps"][0]["stat"] = json!(1)),
        "steps[0]: 未知のキー \"stat\""
    );
    assert_eq!(broken(&|j| j["claim"]["note"] = json!(1)), "claim: 未知のキー \"note\"");
    // violation と error の両方を持つ主張を、violation の主張として読まない。
    let both = broken(&|j| {
        j["claim"]["error"] = json!({"kind": "overflow"});
        j["claim"]["site"] = json!("invariant");
    });
    assert!(both.starts_with("claim: 未知のキー"), "{both}");
    assert_eq!(
        broken(&|j| j["claim"] = json!({"violation": "deadlock", "name": "small"})),
        "claim: 未知のキー \"name\""
    );
    let mut error = trace_json(&m, Claim::TerminalError(ErrKind::Overflow));
    error["claim"]["error"]["value"] = json!(1);
    assert_eq!(format_error(&m, &error), "claim.error: 未知のキー \"value\"");
    // slot は update の主張にだけ書ける。
    let mut guard = trace_json(&m, Claim::StepError(0, vec![], Site::Guard, ErrKind::Overflow));
    assert!(read_back(&m, &guard).is_ok());
    guard["claim"]["slot"] = json!("x");
    assert_eq!(format_error(&m, &guard), "claim: 未知のキー \"slot\"");

    let cert = Certificate {
        conditions: default_conditions(&m, false),
        states: vec![vec![0, 0, 0]],
    };
    let mut json = certificate_to_json(&m, &cert);
    json["extra"] = json!(1);
    match certificate_from_json(&m, &json.to_string()) {
        Err(TraceError::Format(message)) => assert_eq!(message, "証明書: 未知のキー \"extra\""),
        other => panic!("形式の誤りとして拒否されるはず: {other:?}"),
    }
}

/// 名前は文字列である。文字列でない名前を空の名前として読まない。
#[test]
fn names_in_evidence_must_be_strings() {
    let m = model();
    let mut json = trace_json(&m, Claim::Invariant(0));
    json["steps"] = json!([{"action": 1, "output": {"unit": true}, "state": {"p": [1, 2], "n": 3}}]);
    assert_eq!(format_error(&m, &json), "steps[0].action は文字列です");
    let mut json = trace_json(&m, Claim::Invariant(0));
    json["claim"]["name"] = json!(0);
    assert_eq!(format_error(&m, &json), "claim.name は文字列です");
    let mut json = trace_json(&m, Claim::StepError(0, vec![], Site::Guard, ErrKind::Overflow));
    json["claim"]["action"] = Value::Null;
    assert_eq!(format_error(&m, &json), "claim.action は文字列です");
    let mut json = trace_json(&m, Claim::StepError(0, vec![], Site::Update(2), ErrKind::Overflow));
    json["claim"]["target"] = json!(1);
    assert_eq!(format_error(&m, &json), "claim.target は文字列です");
}

/// ステップと主張の args と choices は省略でき、省略すると {} とする。
#[test]
fn args_and_choices_may_be_omitted() {
    let m = model();
    let mut json = trace_json(&m, Claim::StepError(0, vec![], Site::Guard, ErrKind::Overflow));
    json["steps"] = json!([{"action": "move", "output": {"unit": true}, "state": {"p": [1, 2], "n": 3}}]);
    let claim = json["claim"].as_object_mut().unwrap();
    claim.remove("args");
    claim.remove("choices");
    let trace = read_back(&m, &json).unwrap();
    assert_eq!(trace.steps[0].state, vec![1, 2, 3]);
    assert_eq!(trace.claim, Claim::StepError(0, vec![], Site::Guard, ErrKind::Overflow));
}
