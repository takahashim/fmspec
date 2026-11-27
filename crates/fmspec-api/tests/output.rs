//! 結果のJSONの項目と、人間向けの表示。CLI と Ruby の `Fmspec::Result` は、どちらもそのまま使う。
//!
//! 違反のトレースと `Sampled` の表示は crates/fmspec-cli/tests/cli.rs が、
//! 証明書つきの `Verified` の表示は test/check_test.rb が固定している。ここではそれ以外を固定する。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, describe, human, load, replay, shrink, simulate, verify_certificate, Model};
use serde_json::{json, Value};

/// 支払い回数 `charges`（0..2）。`pay(id)` は内部選択 `ok` が真なら1回増やし、
/// success か forbidden を返す。`double` は2回増やす。
fn orders() -> Model {
    let charges = json!({"var": 0});
    let ok = json!({"choice": 0});
    let answer = |v: &str| json!({"enum": {"type": "answer", "variant": v}});
    let ir = json!({
        "ir_version": 1,
        "name": "orders",
        "enums": [{"name": "answer", "variants": ["success", "forbidden"]}],
        "states": [
            {"name": "charges", "type": {"int": {"min": 0, "max": 2}}, "initial": {"int": 0}},
            {"name": "open", "type": {"bool": {}}, "initial": {"bool": true}}
        ],
        "actions": [
            {"name": "pay", "params": [{"name": "id", "type": {"int": {"min": 0, "max": 1}}}],
             "choices": [{"name": "ok", "type": {"bool": {}}}],
             "guard": {"lt": [charges, {"int": 2}]},
             "updates": [{"target": 0, "expr": {"ite": [ok, {"add": [charges, {"int": 1}]}, charges]}}],
             "output": {"type": {"enum": "answer"}, "expr": {"ite": [ok, answer("success"), answer("forbidden")]}}},
            {"name": "double", "updates": [{"target": 0, "expr": {"add": [charges, {"int": 2}]}}]}
        ],
        "invariants": [{"name": "single", "expr": {"le": [charges, {"int": 1}]}}]
    });
    load(&ir.to_string()).unwrap()
}

fn keys(body: &Value) -> Vec<&str> {
    body.as_object().unwrap().keys().map(String::as_str).collect()
}

/// 不変条件を外し、pay だけを対象にすると、到達できる3状態で成り立つ。
fn pay_only() -> Value {
    json!({"actions": ["pay"], "invariants": []})
}

#[test]
fn each_kind_of_result_has_its_own_set_of_keys() {
    let m = orders();
    let identity = ["engine_version", "model", "model_digest", "status"];
    let judged = [
        "conditions",
        "engine_version",
        "ir_version",
        "model",
        "model_digest",
        "status",
    ];
    let with = |base: &[&'static str], extra: &[&'static str]| {
        let mut all: Vec<&str> = base.iter().chain(extra).copied().collect();
        all.sort_unstable();
        all
    };

    let mut opts = pay_only();
    opts["certificate"] = json!(true);
    let verified = check(&m, &opts, None).unwrap();
    assert_eq!(
        keys(&verified),
        with(
            &judged,
            &["certificate", "certificate_states", "gate", "search", "strategy"]
        )
    );
    let violated = check(&m, &json!({"actions": ["pay"]}), None).unwrap();
    assert_eq!(
        keys(&violated),
        with(&judged, &["gate", "property", "search", "strategy", "trace"])
    );
    assert_eq!(violated["property"]["source"], Value::Null);
    let limited = check(&m, &json!({"max_states": 1}), None).unwrap();
    assert_eq!(keys(&limited), with(&judged, &["gate", "reason", "search", "strategy"]));
    let sampled = simulate(&m, &pay_only(), None).unwrap();
    assert_eq!(keys(&sampled), with(&judged, &["simulation", "strategy"]));

    // 提示された証拠の検査は探索をしないので、search、gate、strategy を付けない。
    let cert = verified["certificate"].to_string();
    let again = verify_certificate(&m, &cert, &pay_only(), None).unwrap();
    assert_eq!(keys(&again), with(&judged, &["certificate_states"]));
    let replayed = replay(&m, &violated["trace"].to_string());
    assert_eq!(keys(&replayed), with(&judged, &["property", "trace"]));
    let shrunk = shrink(&m, &violated["trace"].to_string(), &json!({})).unwrap();
    assert_eq!(keys(&shrunk), with(&judged, &["original_steps", "property", "trace"]));

    // 読めない証拠には、読めていない検査条件を付けない。
    for unreadable in [
        replay(&m, "{}"),
        verify_certificate(&m, "[]", &json!({}), None).unwrap(),
        shrink(&m, "not json", &json!({})).unwrap(),
    ] {
        assert_eq!(keys(&unreadable), with(&identity, &["rejected"]), "{unreadable}");
        assert_eq!(unreadable["status"], "rejected");
        assert_eq!(unreadable["rejected"]["reason"], "unreadable");
        assert!(unreadable["rejected"]["message"].is_string(), "{unreadable}");
    }
}

#[test]
fn results_read_as_text() {
    let m = orders();
    assert_eq!(
        human(&describe(&m)),
        "Valid: orders\n  状態変数 2、操作 2、不変条件 1、遷移契約 0\n"
    );
    assert_eq!(
        human(&check(&m, &json!({"max_states": 1}), None).unwrap()),
        "Inconclusive: orders（max_states）\n  探索: 未完走、訪問状態数 1、遷移数 2（探索器の報告）\n"
    );

    // 内部選択と出力のあるトレース。縮小しても短くならない。
    let violated = check(&m, &json!({"actions": ["pay"]}), None).unwrap();
    let trace = "  初期状態 charges: 0, open: true\n\
                 \x20 1. pay(id: 0) 内部選択 ok: true 出力 success → charges: 1, open: true\n\
                 \x20 2. pay(id: 0) 内部選択 ok: true 出力 success → charges: 2, open: true\n\
                 \x20 （2 ステップ）\n";
    let shrunk = shrink(&m, &violated["trace"].to_string(), &json!({})).unwrap();
    assert_eq!(
        human(&shrunk),
        format!("Violated: orders / 不変条件 single の違反\n{trace}  縮小前は 2 ステップ\n")
    );

    // 主張を差し替えたトレースは拒否する。拒否してもトレースは示す。
    let mut forged = violated["trace"].clone();
    forged["claim"] = json!({"violation": "deadlock"});
    assert_eq!(
        human(&replay(&m, &forged.to_string())),
        format!("Rejected: orders\n{trace}  拒否の理由: トレースの末尾で、主張どおりの事象が起きません\n")
    );

    // 拒否した証明書は、拒否の理由の状態と操作を示し、受理したとは書かない。
    let mut opts = pay_only();
    opts["certificate"] = json!(true);
    let mut cert = check(&m, &opts, None).unwrap()["certificate"].clone();
    cert["states"].as_array_mut().unwrap().pop();
    let rejected = verify_certificate(&m, &cert.to_string(), &pay_only(), None).unwrap();
    assert_eq!(
        human(&rejected),
        "Rejected: orders\n\
         \x20 拒否の理由: 証明書の状態からの遷移先が、証明書に含まれません\n\
         \x20   state: charges: 1, open: true\n\
         \x20   action: pay\n\
         \x20 証明書の状態数 2\n"
    );
    assert_eq!(
        human(&replay(&m, "{}")),
        "Rejected: orders\n  拒否の理由: 未対応の trace_version です（対応しているのは 1）\n"
    );
}

#[test]
fn every_kind_of_property_reads_as_text() {
    let headline = |status: &str, property: Value| {
        let text = human(&json!({"status": status, "model": "m", "property": property}));
        text.lines().next().unwrap().to_string()
    };
    let int = json!({"int": {"min": 0, "max": 2}});
    let cases = [
        (
            "violated",
            json!({"violation": "contract", "name": "kept"}),
            "Violated: m / 遷移契約 kept の違反",
        ),
        (
            "violated",
            json!({"violation": "deadlock"}),
            "Violated: m / 非終端のデッドロック",
        ),
        (
            "error",
            json!({"site": "invariant", "name": "small", "error": {"kind": "division_by_zero"}}),
            "Error: m / 不変条件 small の評価エラー: 0による除算",
        ),
        (
            "error",
            json!({"site": "contract", "name": "kept", "error": {"kind": "overflow"}}),
            "Error: m / 遷移契約 kept の評価エラー: 符号付き64ビット整数のオーバーフロー",
        ),
        (
            "error",
            json!({"site": "terminal", "error": {"kind": "none"}}),
            "Error: m / 終端条件の評価エラー: 空の option の取り出し",
        ),
        (
            "error",
            json!({"site": "guard", "action": "pay", "args": {}, "choices": {"ok": true},
                   "error": {"kind": "missing_key"}}),
            "Error: m / 操作 pay(内部選択 ok: true) のguardで評価エラー: map にないキーの参照",
        ),
        (
            "error",
            json!({"site": "output", "action": "pay", "args": {"id": 0}, "choices": {"ok": false},
                   "error": {"kind": "index_out_of_range"}}),
            "Error: m / 操作 pay(id: 0; 内部選択 ok: false) の出力式で評価エラー: list の範囲外の添字",
        ),
        (
            "error",
            json!({"site": "update", "action": "double", "args": {}, "choices": {}, "target": "charges",
                   "error": {"kind": "out_of_range", "value": 3, "type": int}}),
            "Error: m / 操作 double() の更新式（charges）で評価エラー: 範囲外更新（値 3、型 0..2 の範囲外）",
        ),
    ];
    for (status, property, expected) in cases {
        assert_eq!(headline(status, property), expected);
    }
}
