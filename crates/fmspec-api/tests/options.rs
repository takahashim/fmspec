//! オプションの誤り。CLI と Ruby の拡張は、この文をそのまま利用者に示す。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, coverage, load, shrink, simulate, to_text, Model, Session};
use serde_json::{json, Value};
use std::sync::Arc;

fn counter() -> Model {
    let n = json!({"var": 0});
    let ir = json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": 2}}, "initial": {"int": 0}}],
        "actions": [{"name": "inc", "guard": {"lt": [n, {"int": 2}]},
                     "updates": [{"target": 0, "expr": {"add": [n, {"int": 1}]}}]}],
        "invariants": [{"name": "small", "expr": {"le": [n, {"int": 2}]}}]
    });
    load(&ir.to_string()).unwrap()
}

fn check_error(opts: Value) -> String {
    check(&counter(), &opts, None).unwrap_err()
}

#[test]
fn condition_errors() {
    assert_eq!(check_error(json!([])), "オプションはオブジェクトです");
    assert_eq!(check_error(json!({"bogus": 1})), "未知のオプション \"bogus\"");
    assert_eq!(check_error(json!({"deadlock": 1})), "deadlock は真偽値です");
    assert_eq!(check_error(json!({"actions": "inc"})), "操作の指定は名前の配列です");
    assert_eq!(
        check_error(json!({"invariants": [1]})),
        "不変条件の指定は名前の配列です"
    );
    assert_eq!(check_error(json!({"contracts": ["c"]})), "未定義の遷移契約 \"c\"");
    assert_eq!(
        check_error(json!({"max_states": 0})),
        "max_states は1以上の整数です（0）"
    );
    assert_eq!(check_error(json!({"certificate": 1})), "certificate は真偽値です");
    assert_eq!(
        check_error(json!({"max_depth": -1})),
        "max_depth は0以上の整数です（-1）"
    );
    assert_eq!(
        check_error(json!({"max_time_ms": 1.5})),
        "max_time_ms は0以上の整数です（1.5）"
    );
    let ok = check(
        &counter(),
        &json!({"deadlock": null, "actions": null, "max_states": null, "max_depth": null, "max_time_ms": null}),
        None,
    )
    .unwrap();
    assert_eq!(ok["status"], "verified", "{ok}");
}

#[test]
fn each_function_accepts_only_its_keys() {
    let m = counter();
    let err = simulate(&m, &json!({"max_states": 1}), None).unwrap_err();
    assert_eq!(err, "未知のオプション \"max_states\"");
    let err = simulate(&m, &json!({"traces": -1}), None).unwrap_err();
    assert_eq!(err, "traces は1以上の整数です（-1）");
    // shrink は検査条件をトレースから読むので、検査条件のキーも受け付けない。
    let err = shrink(&m, "{}", &json!({"deadlock": true}), None).unwrap_err();
    assert_eq!(err, "未知のオプション \"deadlock\"");
    let err = shrink(&m, "{}", &json!(1), None).unwrap_err();
    assert_eq!(err, "オプションはオブジェクトです");
    let err = coverage(&m, &json!({"seen": {"edges": []}}), None).unwrap_err();
    assert_eq!(err, "seen の未知のキー \"edges\"");
    let err = Session::new(Arc::new(counter()), &json!({"deadlock": "yes"}))
        .err()
        .unwrap();
    assert_eq!(err, "deadlock は真偽値です");
}

#[test]
fn usage_errors_have_the_shape_of_a_result() {
    let text = to_text(check(&counter(), &json!({"bogus": 1}), None));
    assert_eq!(
        text,
        r#"{"message":"未知のオプション \"bogus\"","status":"usage_error"}"#
    );
}

#[test]
fn option_errors_are_found_before_the_search() {
    // 探索は状態を取り出すごとに中断要求を確かめる。誤った指定なら、探索を始めずに誤りを返す。
    let asked = std::cell::Cell::new(0);
    let interrupt = || {
        asked.set(asked.get() + 1);
        false
    };
    for opts in [json!({"certificate": 1}), json!({"certificate": "yes", "max_depth": 1})] {
        let err = check(&counter(), &opts, Some(&interrupt)).unwrap_err();
        assert!(err.starts_with("certificate は真偽値です"), "{err}");
    }
    assert_eq!(asked.get(), 0);
    // 正しい指定なら探索する。
    check(&counter(), &json!({"certificate": true}), Some(&interrupt)).unwrap();
    assert!(asked.get() > 0);
}
