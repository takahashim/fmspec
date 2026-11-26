//! カバレッジの分母（到達可能な状態と遷移）と、テスト経路の生成。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{coverage, load, test_paths, Model};
use serde_json::{json, Value};

/// 販売数 0..3。purchase(1..2) と cancel。遷移は purchase が5本、cancel が3本。
fn tickets() -> Model {
    let sold = json!({"var": 0});
    let qty = json!({"param": 0});
    let ir = json!({
        "ir_version": 1,
        "name": "tickets",
        "states": [{"name": "sold", "type": {"int": {"min": 0, "max": 4}}, "initial": {"int": 0}}],
        "actions": [
            {"name": "purchase", "params": [{"name": "quantity", "type": {"int": {"min": 1, "max": 2}}}],
             "guard": {"le": [{"add": [sold, qty]}, {"int": 3}]},
             "updates": [{"target": 0, "expr": {"add": [sold, qty]}}]},
            {"name": "cancel", "guard": {"gt": [sold, {"int": 0}]},
             "updates": [{"target": 0, "expr": {"sub": [sold, {"int": 1}]}}]}
        ]
    });
    load(&ir.to_string()).unwrap()
}

#[test]
fn the_denominator_is_every_reachable_state_and_transition() {
    let m = tickets();
    let none = coverage(&m, &json!({}), None).unwrap();
    assert_eq!(none["complete"], true);
    assert_eq!(none["states"], json!({"reachable": 4, "covered": 0}));
    assert_eq!(none["transitions"], json!({"reachable": 8, "covered": 0}));
    assert_eq!(none["uncovered_count"], 8);
    assert_eq!(
        none["actions"],
        json!([{"name": "purchase", "reachable": 5, "covered": 0}, {"name": "cancel", "reachable": 3, "covered": 0}])
    );

    // 状態0から purchase(2) で2へ。状態0と2、遷移1本を覆った。
    let seen = json!({"states": [[0], [2]], "transitions": [[[0], 0, [2]]]});
    let some = coverage(&m, &json!({"seen": seen}), None).unwrap();
    assert_eq!(some["states"]["covered"], 2);
    assert_eq!(some["transitions"]["covered"], 1);
    assert_eq!(some["actions"][0]["covered"], 1);

    // 対象の操作を絞ると、分母もその操作の遷移だけになる。
    let cancel_only = coverage(&m, &json!({"actions": ["cancel"]}), None).unwrap();
    assert_eq!(cancel_only["states"]["reachable"], 1);
    assert_eq!(cancel_only["transitions"]["reachable"], 0);

    let limited = coverage(&m, &json!({"max_states": 2}), None).unwrap();
    assert_eq!(limited["complete"], false);
    assert_eq!(limited["states"]["reachable"], 2);

    assert!(coverage(&m, &json!({"seen": {"transitions": [[0, 0]]}}), None).is_err());
}

fn inputs(path: &Value) -> Vec<(String, Value)> {
    path["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| (i["action"].as_str().unwrap().to_string(), i["args"].clone()))
        .collect()
}

#[test]
fn test_paths_cover_every_reachable_state_and_input() {
    let m = tickets();
    let found = test_paths(&m, &json!({}), None).unwrap();
    assert_eq!(found["targets"], 8);
    assert_eq!(found["covered"], 8);
    let paths = found["paths"].as_array().unwrap();
    // 最初の経路は、探索順で最初の組（状態0の purchase(1)）から、覆っていない組を貪欲にたどる。
    assert_eq!(
        inputs(&paths[0])[..2],
        [
            ("purchase".to_string(), json!({"quantity": 1})),
            ("purchase".to_string(), json!({"quantity": 1}))
        ]
    );
    assert!(paths.iter().all(|p| p["start"] == json!({"sold": 0})));

    let short = test_paths(&m, &json!({"max_steps": 1}), None).unwrap();
    assert_eq!(short["covered"], 2);
    assert_eq!(short["paths"].as_array().unwrap().len(), 2);
    for p in short["paths"].as_array().unwrap() {
        assert_eq!(p["inputs"].as_array().unwrap().len(), 1);
    }

    let two = test_paths(&m, &json!({"max_steps": 2}), None).unwrap();
    assert!(two["paths"]
        .as_array()
        .unwrap()
        .iter()
        .all(|p| p["inputs"].as_array().unwrap().len() <= 2));
    // 状態3は初期状態から2入力なので、状態3からの cancel だけは3入力の経路が要る。
    assert_eq!(two["covered"], 7);

    assert!(test_paths(&m, &json!({"max_steps": 0}), None).is_err());
    assert!(test_paths(&m, &json!({"inject": {"cancel": ["nothing"]}}), None).is_err());
}
