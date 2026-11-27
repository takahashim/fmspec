//! 詳細化の検査。写像の下ろし（複合型、列挙型の共有）と、判定と、文書の読み込みの誤り。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{load_refinement, refine};
use serde_json::{json, Value};

fn item(label: &str) -> Value {
    json!({"enum": {"type": "item", "variant": label}})
}

/// 品物の集合に入れたり出したりする具体モデル。
fn basket() -> Value {
    let items = json!({"var": 0});
    let x = json!({"param": 0});
    json!({
        "ir_version": 1,
        "name": "basket",
        "enums": [{"name": "item", "variants": ["apple", "bread", "milk"]}],
        "states": [
            {"name": "basket", "type": {"set": {"enum": "item"}}, "initial": {"set": {"of": {"enum": "item"}, "items": []}}},
            {"name": "last", "type": {"enum": "item"}, "initial": item("apple")}
        ],
        "actions": [
            {
                "name": "add",
                "params": [{"name": "x", "type": {"enum": "item"}}],
                "guard": {"not": [{"contains": [items, x]}]},
                "updates": [{"target": 0, "expr": {"insert": [items, x]}}, {"target": 1, "expr": x}]
            },
            {
                "name": "remove",
                "params": [{"name": "x", "type": {"enum": "item"}}],
                "guard": {"contains": [items, x]},
                "updates": [{"target": 0, "expr": {"remove": [items, x]}}]
            }
        ]
    })
}

/// 個数だけを数える抽象モデル。`dec` がなければ、品物を出す遷移は写らない。
fn counter(with_dec: bool) -> Value {
    let n = json!({"var": 0});
    let mut actions = vec![json!({
        "name": "inc",
        "guard": {"lt": [n, {"int": 3}]},
        "updates": [{"target": 0, "expr": {"add": [n, {"int": 1}]}}]
    })];
    if with_dec {
        actions.push(json!({
            "name": "dec",
            "guard": {"gt": [n, {"int": 0}]},
            "updates": [{"target": 0, "expr": {"sub": [n, {"int": 1}]}}]
        }));
    }
    json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": 3}}, "initial": {"int": 0}}],
        "actions": actions
    })
}

fn doc(concrete: Value, abs: Value, mapping: Value) -> String {
    json!({"ir_version": 1, "name": "r", "concrete": concrete, "abstract": abs, "mapping": mapping}).to_string()
}

fn size_map() -> Value {
    json!([{"state": "n", "expr": {"size": [{"var": 0}]}}])
}

fn run(text: &str) -> Value {
    let r = load_refinement(text).unwrap_or_else(|e| panic!("読み込めません: {e}"));
    refine(&r, &json!({}), None).unwrap()
}

#[test]
fn the_size_of_a_set_refines_a_counter() {
    let r = run(&doc(basket(), counter(true), size_map()));
    assert_eq!(r["status"], "refines", "{r}");
    // 品物の集合は8通り、最後に入れた品物は3通り。
    assert!(r["certificate_states"].as_u64().unwrap() > 8, "{r}");
}

#[test]
fn removing_an_item_does_not_refine_a_counter_that_only_counts_up() {
    let r = run(&doc(basket(), counter(false), size_map()));
    assert_eq!(r["status"], "not_refines", "{r}");
    assert_eq!(r["property"]["violation"], "step");
    assert_eq!(r["property"]["action"], "remove");
    let steps = r["trace"]["steps"].as_array().unwrap();
    assert_eq!(steps.len(), 2, "{r}");
    assert_eq!(r["trace"]["initial_abstract"], json!({"n": 0}));
    assert_eq!(steps[0]["abstract"], json!({"n": 1}));
    assert_eq!(steps[1]["abstract"], json!({"n": 0}));
}

#[test]
fn composite_values_and_shared_enumerations_are_mapped() {
    // 抽象モデルの列挙型は別の順に並べ、使わない列挙型を前に置く。読み込みで具体モデルの番号に揃う。
    let abs = json!({
        "ir_version": 1,
        "name": "free",
        "enums": [
            {"name": "color", "variants": ["red", "green"]},
            {"name": "item", "variants": ["apple", "bread", "milk"]}
        ],
        "states": [
            {"name": "summary", "type": {"tuple": [{"int": {"min": 0, "max": 3}}, {"bool": {}}]},
             "initial": {"tuple": [{"int": 0}, {"bool": false}]}},
            {"name": "last", "type": {"enum": "item"}, "initial": item("apple")}
        ],
        "actions": [{
            "name": "jump",
            "params": [
                {"name": "p", "type": {"tuple": [{"int": {"min": 0, "max": 3}}, {"bool": {}}]}},
                {"name": "q", "type": {"enum": "item"}}
            ],
            "updates": [{"target": 0, "expr": {"param": 0}}, {"target": 1, "expr": {"param": 1}}]
        }]
    });
    let mapping = json!([
        {"state": "last", "expr": {"var": 1}},
        {"state": "summary", "expr": {"tuple": [{"size": [{"var": 0}]}, {"contains": [{"var": 0}, item("milk")]}]}}
    ]);
    let r = run(&doc(basket(), abs, mapping));
    assert_eq!(r["status"], "refines", "{r}");
    assert_eq!(r["trace"], Value::Null);
}

#[test]
fn the_document_is_checked_when_loaded() {
    let err = |text: String| match load_refinement(&text) {
        Ok(_) => panic!("読み込めてしまった"),
        Err(e) => e.to_string(),
    };
    assert!(err(doc(basket(), counter(true), json!([]))).contains("\"n\" の写像がありません"));
    assert!(err(doc(
        basket(),
        counter(true),
        json!([{"state": "n", "expr": {"int": 0}}, {"state": "n", "expr": {"int": 0}}])
    ))
    .contains("重複"));
    assert!(err(doc(
        basket(),
        counter(true),
        json!([{"state": "m", "expr": {"int": 0}}])
    ))
    .contains("\"m\" はありません"));
    let bad = err(doc(
        basket(),
        counter(true),
        json!([{"state": "n", "expr": {"contains": [{"var": 0}, item("milk")]}}]),
    ));
    assert!(
        bad.contains("$.mapping[0].expr") && bad.contains("写像の式の型"),
        "{bad}"
    );
    let mut clash = counter(true);
    clash["enums"] = json!([{"name": "item", "variants": ["apple"]}]);
    assert!(err(doc(basket(), clash, size_map())).contains("ラベルが"));
    let mut broken = basket();
    broken["states"][0]["name"] = json!(3);
    assert!(err(doc(broken, counter(true), size_map())).contains("$.concrete.states[0].name"));
}

#[test]
fn invariants_and_contracts_cannot_be_selected() {
    let r = load_refinement(&doc(basket(), counter(true), size_map())).unwrap();
    // 検査しない検査条件は、ほかのAPIの受け付けないオプションと同じく、未知のオプションとして拒否する。
    for key in ["invariants", "contracts", "deadlock"] {
        let err = refine(&r, &json!({key: null}), None).unwrap_err();
        assert_eq!(err, format!("未知のオプション {key:?}"));
    }
    assert!(refine(&r, &json!({"actions": ["nope"]}), None).is_err());
    let only_add = refine(&r, &json!({"actions": ["add"]}), None).unwrap();
    assert_eq!(only_add["status"], "refines", "{only_add}");
    let limited = refine(&r, &json!({"max_states": 1}), None).unwrap();
    assert_eq!(limited["status"], "inconclusive");
    assert_eq!(limited["reason"], "max_states");
}
