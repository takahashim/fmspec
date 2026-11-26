//! IRの読み込み。未知のバージョン・演算子、未定義参照、型不整合、重複定義を拒否する（仕様書 §6）。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, TraceStep};
use fmspec_core::step::Site;
use fmspec_core::typing::InvalidModel;
use fmspec_ir::{
    certificate_from_json, certificate_to_json, default_conditions, load, trace_from_json, trace_to_json, LoadError,
    Trace, TraceError,
};
use serde_json::{json, Value};

fn base() -> Value {
    json!({
        "ir_version": 1,
        "name": "m",
        "enums": [{"name": "color", "variants": ["red", "green"]}],
        "states": [
            {"id": 0, "name": "n", "type": {"int": {"min": 0, "max": 3}}, "initial": {"int": 0}},
            {"id": 1, "name": "on", "type": {"bool": {}}, "initial": {"bool": false}},
            {"id": 2, "name": "c", "type": {"enum": "color"}, "initial": {"enum": {"type": "color", "variant": "green"}}}
        ],
        "actions": [{
            "name": "inc",
            "params": [{"name": "d", "type": {"int": {"min": 1, "max": 2}}}],
            "choices": [{"name": "flip", "type": {"bool": {}}}],
            "guard": {"lt": [{"var": 0}, {"int": 3}]},
            "updates": [
                {"target": 0, "expr": {"add": [{"var": 0}, {"param": 0}]}},
                {"target": 1, "expr": {"choice": 0}}
            ],
            "output": {"type": {"enum": "color"}, "expr": {"var": 2}}
        }],
        "invariants": [{"name": "bounded", "expr": {"le": [{"var": 0}, {"int": 3}]}}],
        "contracts": [{"name": "grows", "action": "inc", "expr": {"gt": [{"next": 0}, {"var": 0}]}}],
        "terminal": {"eq": [{"var": 0}, {"int": 3}]}
    })
}

fn with(change: impl FnOnce(&mut Value)) -> Result<fmspec_ir::Model, LoadError> {
    let mut ir = base();
    change(&mut ir);
    load(&ir.to_string())
}

fn schema_error(change: impl FnOnce(&mut Value)) -> String {
    match with(change) {
        Err(LoadError::Schema { path, message }) => format!("{path}: {message}"),
        Err(other) => panic!("形式の誤りとして拒否されるはず: {other:?}"),
        Ok(_) => panic!("拒否されるはずのIRを受理した"),
    }
}

fn invalid(change: impl FnOnce(&mut Value)) -> InvalidModel {
    match with(change) {
        Err(LoadError::Invalid { reason, .. }) => reason,
        Err(other) => panic!("IR検証で拒否されるはず: {other:?}"),
        Ok(_) => panic!("拒否されるはずのIRを受理した"),
    }
}

#[test]
fn the_base_model_loads() {
    let m = with(|_| {}).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(m.names.states, vec!["n", "on", "c"]);
    assert_eq!(m.raw().inits, vec![vec![0, 0, 1]]);
    assert_eq!(m.raw().actions[0].n_params, 1);
    assert_eq!(m.raw().actions[0].domains.len(), 2);
}

#[test]
fn unknown_versions_operators_and_keys_are_rejected() {
    assert!(schema_error(|ir| ir["ir_version"] = json!(2)).contains("未対応のIRバージョン"));
    assert!(schema_error(|ir| ir["ir_version"] = json!("1")).contains("未対応のIRバージョン"));
    assert!(
        schema_error(|ir| ir["invariants"][0]["expr"] = json!({"xor": [{"bool": true}, {"bool": true}]}))
            .contains("未知の演算子")
    );
    assert!(schema_error(|ir| ir["extra"] = json!(1)).contains("未知のキー"));
    assert!(schema_error(|ir| ir["actions"][0]["gaurd"] = json!({"bool": true})).contains("未知のキー"));
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = json!({"le": [{"var": 0}]})).contains("オペランド"));
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = json!({"int": 1.5})).contains("整数"));
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = json!({"int": 9223372036854775808u64})).contains("整数"));
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = json!({"var": -1})).contains("添字"));
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = json!({"bool": true, "int": 1})).contains("1つだけ"));
    assert!(matches!(load("{"), Err(LoadError::Json(_))));
}

#[test]
fn undefined_names_are_rejected() {
    assert!(schema_error(|ir| ir["states"][2]["type"] = json!({"enum": "shape"})).contains("未定義の列挙型"));
    assert!(schema_error(|ir| ir["contracts"][0]["action"] = json!("dec")).contains("未定義の操作"));
    let bad_label = json!({"eq": [{"var": 2}, {"enum": {"type": "color", "variant": "blue"}}]});
    assert!(schema_error(|ir| ir["invariants"][0]["expr"] = bad_label).contains("未定義のラベル"));
}

#[test]
fn duplicate_definitions_are_rejected() {
    assert!(schema_error(|ir| ir["states"][1]["name"] = json!("n")).contains("重複"));
    assert!(schema_error(|ir| ir["enums"][0]["variants"] = json!(["red", "red"])).contains("重複"));
    assert!(schema_error(|ir| ir["actions"][0]["choices"][0]["name"] = json!("d")).contains("重複"));
    assert!(schema_error(|ir| {
        let copy = ir["invariants"][0].clone();
        ir["invariants"].as_array_mut().unwrap().push(copy);
    })
    .contains("重複"));
    assert!(schema_error(|ir| {
        let copy = ir["actions"][0].clone();
        ir["actions"].as_array_mut().unwrap().push(copy);
    })
    .contains("重複"));
    assert!(schema_error(|ir| ir["states"][1]["id"] = json!(2)).contains("添字"));
}

#[test]
fn type_errors_are_rejected() {
    assert!(schema_error(|ir| ir["states"][1]["initial"] = json!({"int": 0})).contains("初期値の型"));
    assert_eq!(
        invalid(|ir| ir["states"][0]["initial"] = json!({"int": 4})),
        InvalidModel::Initial(0)
    );
    assert_eq!(
        invalid(|ir| ir["states"][0]["type"] = json!({"int": {"min": 1, "max": 0}})),
        InvalidModel::StateType(0)
    );
    let empty = json!({"name": "empty", "variants": []});
    assert_eq!(
        invalid(|ir| ir["enums"].as_array_mut().unwrap().push(empty)),
        InvalidModel::EmptyEnum(1)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["guard"] = json!({"var": 0})),
        InvalidModel::Guard(0)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["guard"] = json!({"lt": [{"var": 5}, {"int": 3}]})),
        InvalidModel::Guard(0)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["guard"] = json!({"lt": [{"param": 1}, {"int": 3}]})),
        InvalidModel::Guard(0)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["updates"][1]["expr"] = json!({"param": 0})),
        InvalidModel::Update(0, 1)
    );
    let again = json!({"target": 0, "expr": {"int": 1}});
    assert_eq!(
        invalid(|ir| ir["actions"][0]["updates"][1] = again),
        InvalidModel::DuplicateUpdate(0, 1)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["updates"][1]["target"] = json!(3)),
        InvalidModel::Update(0, 1)
    );
    assert_eq!(
        invalid(|ir| ir["actions"][0]["output"]["expr"] = json!({"var": 0})),
        InvalidModel::Output(0)
    );
    assert_eq!(
        invalid(|ir| ir["invariants"][0]["expr"] = json!({"eq": [{"var": 0}, {"var": 1}]})),
        InvalidModel::Invariant(0)
    );
    assert_eq!(
        invalid(|ir| ir["invariants"][0]["expr"] = json!({"eq": [{"next": 0}, {"int": 1}]})),
        InvalidModel::Invariant(0)
    );
    assert_eq!(
        invalid(|ir| ir["invariants"][0]["expr"] = json!({"all": [{"var": 0}]})),
        InvalidModel::Invariant(0)
    );
    assert_eq!(
        invalid(|ir| ir["contracts"][0]["expr"] = json!({"eq": [{"output": {}}, {"int": 1}]})),
        InvalidModel::Contract(0)
    );
    assert_eq!(invalid(|ir| ir["terminal"] = json!({"int": 1})), InvalidModel::Terminal);
    // エラーには、名前を使った説明が付く。
    let message = with(|ir| ir["actions"][0]["guard"] = json!({"var": 0}))
        .err()
        .unwrap()
        .to_string();
    assert!(message.contains("\"inc\""), "{message}");
}

#[test]
fn the_digest_ignores_key_order_and_source_locations() {
    let m = with(|_| {}).unwrap();
    let reordered = r#"{"name": "m", "ir_version": 1, "states": []}"#;
    let plain = r#"{"ir_version": 1, "name": "m", "states": []}"#;
    assert_eq!(load(reordered).unwrap().digest, load(plain).unwrap().digest);
    let located = with(|ir| ir["invariants"][0]["source"] = json!({"file": "spec/tickets.rb", "line": 12})).unwrap();
    assert_eq!(located.digest, m.digest);
    assert_eq!(located.names.invariant_sources[0].as_ref().unwrap().line, 12);
    let changed = with(|ir| ir["invariants"][0]["expr"] = json!({"le": [{"var": 0}, {"int": 2}]})).unwrap();
    assert_ne!(changed.digest, m.digest);
    assert!(m.digest.starts_with("sha256:") && m.digest.len() == 7 + 64);
}

#[test]
fn traces_round_trip_through_json() {
    let m = with(|_| {}).unwrap();
    let steps = vec![TraceStep {
        action: 0,
        args: vec![2, 1],
        output: Some(1),
        state: vec![2, 1, 1],
    }];
    for claim in [
        Claim::Invariant(0),
        Claim::Contract(0),
        Claim::Deadlock,
        Claim::InvariantError(0, ErrKind::Overflow),
        Claim::ContractError(0, ErrKind::TypeMismatch),
        Claim::TerminalError(ErrKind::Unbound),
        Claim::StepError(0, vec![2, 0], Site::Guard, ErrKind::Overflow),
        Claim::StepError(0, vec![2, 0], Site::Update(1), ErrKind::OutOfRange(4)),
        Claim::StepError(0, vec![1, 1], Site::Output, ErrKind::OutOfRange(-1)),
    ] {
        let trace = Trace {
            conditions: default_conditions(&m, true),
            start: vec![0, 0, 1],
            steps: steps.clone(),
            claim,
            seed: Some(42),
        };
        let json = trace_to_json(&m, &trace);
        let back = trace_from_json(&m, &json.to_string()).unwrap_or_else(|e| panic!("{e}\n{json}"));
        assert_eq!(
            (back.start, back.steps, back.claim, back.seed),
            (trace.start, trace.steps, trace.claim, trace.seed)
        );
        assert_eq!(back.conditions, trace.conditions);
    }
    let trace = Trace {
        conditions: default_conditions(&m, false),
        start: vec![0, 0, 1],
        steps,
        claim: Claim::Deadlock,
        seed: None,
    };
    let json = trace_to_json(&m, &trace);
    assert_eq!(json["initial"], json!({"n": 0, "on": false, "c": "green"}));
    assert_eq!(json["steps"][0]["args"], json!({"d": 2}));
    assert_eq!(json["steps"][0]["choices"], json!({"flip": true}));
    assert_eq!(json["steps"][0]["output"], json!({"value": "green"}));
    assert_eq!(json["steps"][0]["state"], json!({"n": 2, "on": true, "c": "green"}));
}

#[test]
fn evidence_for_another_model_is_refused() {
    let m = with(|_| {}).unwrap();
    let other = with(|ir| ir["states"][0]["initial"] = json!({"int": 1})).unwrap();
    let cert = Certificate {
        conditions: default_conditions(&m, false),
        states: vec![vec![3, 1, 0], vec![0, 0, 1]],
    };
    let json = certificate_to_json(&m, &cert).to_string();
    // 読み込みで、状態を符号化列の辞書順に整列する。
    assert_eq!(
        certificate_from_json(&m, &json).unwrap().states,
        vec![vec![0, 0, 1], vec![3, 1, 0]]
    );
    assert!(matches!(
        certificate_from_json(&other, &json),
        Err(TraceError::DigestMismatch { .. })
    ));
    let trace = Trace {
        conditions: default_conditions(&m, false),
        start: vec![0, 0, 1],
        steps: vec![],
        claim: Claim::Deadlock,
        seed: None,
    };
    let json = trace_to_json(&m, &trace).to_string();
    assert!(matches!(
        trace_from_json(&other, &json),
        Err(TraceError::DigestMismatch { .. })
    ));
    assert!(matches!(trace_from_json(&m, "[]"), Err(TraceError::Format(_))));
}

#[test]
fn initial_states_are_the_filtered_product_of_candidates() {
    let set_initial = |ir: &mut Value, i: usize, candidates: Value| {
        let state = ir["states"][i].as_object_mut().unwrap();
        state.remove("initial");
        state.insert("initial_in".to_string(), candidates);
    };
    let m = with(|ir| {
        set_initial(ir, 0, json!([{"int": 2}, {"int": 0}, {"int": 1}, {"int": 0}]));
        set_initial(
            ir,
            2,
            json!([{"enum": {"type": "color", "variant": "green"}}, {"enum": {"type": "color", "variant": "red"}}]),
        );
        ir["initial_constraint"] = json!({"ne": [{"var": 0}, {"int": 1}]});
    })
    .unwrap();
    // 候補の重複を除き、符号化列の辞書順に並べる。
    assert_eq!(
        m.raw().inits,
        vec![vec![0, 0, 0], vec![0, 0, 1], vec![2, 0, 0], vec![2, 0, 1]]
    );

    // 初期状態が複数あるモデルのトレースは、開始状態を initial に記録する。
    let trace = Trace {
        conditions: default_conditions(&m, false),
        start: vec![2, 0, 0],
        steps: vec![],
        claim: Claim::Deadlock,
        seed: None,
    };
    let mut json = trace_to_json(&m, &trace);
    assert_eq!(json["initial"], json!({"n": 2, "on": false, "c": "red"}));
    assert_eq!(trace_from_json(&m, &json.to_string()).unwrap().start, vec![2, 0, 0]);
    json.as_object_mut().unwrap().remove("initial");
    assert!(trace_from_json(&m, &json.to_string()).is_err());

    let m = with(|ir| ir["initial_constraint"] = Value::Null).unwrap();
    assert_eq!(m.raw().inits, vec![vec![0, 0, 1]]);
    assert!(schema_error(|ir| set_initial(ir, 0, json!([]))).contains("空でない"));
    assert!(schema_error(|ir| ir["states"][0]["initial_in"] = json!([{"int": 0}])).contains("どちらか一方"));
    assert!(schema_error(|ir| ir["initial_constraint"] = json!({"int": 0})).contains("初期条件"));
    assert!(schema_error(|ir| ir["initial_constraint"] = json!({"bool": false})).contains("初期状態がありません"));
    assert!(schema_error(|ir| ir["initial_constraint"] = json!({"param": 0})).contains("初期条件"));
    assert_eq!(
        invalid(|ir| set_initial(ir, 0, json!([{"int": 0}, {"int": 4}]))),
        InvalidModel::Initial(1)
    );
}
