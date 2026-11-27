//! 複合型、量化、let、除算のモデル検査。IRの下ろし方を、検査の結果とトレースで確かめる。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, load, replay, verify_certificate, Model};
use serde_json::{json, Value};

fn model(ir: &Value) -> Model {
    load(&ir.to_string()).unwrap_or_else(|e| panic!("モデルを読み込めません: {e}"))
}

fn run(ir: &Value) -> Value {
    check(&model(ir), &json!({"certificate": true}), None).unwrap()
}

fn base(states: Value, actions: Value, invariants: Value) -> Value {
    json!({
        "ir_version": 1,
        "name": "m",
        "enums": [{"name": "item", "variants": ["apple", "bread", "milk"]}],
        "states": states,
        "actions": actions,
        "invariants": invariants
    })
}

fn item(label: &str) -> Value {
    json!({"enum": {"type": "item", "variant": label}})
}

/// 証明書を検査し直し、トレースを再生し直す。
fn recheck(ir: &Value, result: &Value) {
    let m = model(ir);
    match result["status"].as_str().unwrap() {
        "verified" => {
            let cert = result["certificate"].to_string();
            let again = verify_certificate(&m, &cert, &json!({}), None).unwrap();
            assert_eq!(again["status"], "verified", "{again}");
        }
        "violated" | "error" => {
            let again = replay(&m, &result["trace"].to_string());
            assert_eq!(again["status"], result["status"], "{again}");
        }
        _ => {}
    }
}

fn basket() -> Value {
    let items = json!({"var": 0});
    let x = json!({"param": 0});
    base(
        json!([{"name": "basket", "type": {"set": {"enum": "item"}}, "initial": {"set": {"of": {"enum": "item"}, "items": []}}}]),
        json!([
            {
                "name": "add",
                "params": [{"name": "x", "type": {"enum": "item"}}],
                "guard": {"not": [{"contains": [items, x]}]},
                "updates": [{"target": 0, "expr": {"insert": [items, x]}}]
            },
            {
                "name": "drop",
                "params": [{"name": "x", "type": {"enum": "item"}}],
                "guard": {"contains": [items, x]},
                "updates": [{"target": 0, "expr": {"remove": [items, x]}}]
            }
        ]),
        json!([
            {"name": "small", "expr": {"le": [{"size": [items]}, {"int": 3}]}},
            {"name": "no_milk_alone", "expr": {"implies": [
                {"contains": [items, item("milk")]},
                {"exists": {"name": "y", "in": items, "body": {"ne": [{"local": "y"}, item("milk")]}}}
            ]}}
        ]),
    )
}

#[test]
fn sets_are_explored_as_values() {
    let mut ir = basket();
    ir["invariants"].as_array_mut().unwrap().remove(1);
    let r = run(&ir);
    assert_eq!(r["status"], "verified", "{r}");
    assert_eq!(r["search"]["visited_states"], 8);
    recheck(&ir, &r);
}

#[test]
fn set_traces_use_element_lists() {
    let ir = basket();
    let r = run(&ir);
    assert_eq!(r["status"], "violated", "{r}");
    assert_eq!(r["property"]["name"], "no_milk_alone");
    let steps = r["trace"]["steps"].as_array().unwrap();
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0]["args"], json!({"x": "milk"}));
    assert_eq!(steps[0]["state"], json!({"basket": ["milk"]}));
    recheck(&ir, &r);
}

fn wallet(limit: i64) -> Value {
    let m = json!({"var": 0});
    let k = json!({"param": 0});
    let current = json!({"ite": [{"has_key": [m, k]}, {"get": [m, k]}, {"int": 0}]});
    base(
        json!([{
            "name": "balance",
            "type": {"map": {"key": {"enum": "item"}, "value": {"int": {"min": 0, "max": 2}}}},
            "initial": {"map": {"key": {"enum": "item"}, "value": {"int": {"min": 0, "max": 2}}, "items": [[item("bread"), {"int": 1}]]}}
        }]),
        json!([{
            "name": "deposit",
            "params": [{"name": "k", "type": {"enum": "item"}}],
            "guard": {"lt": [current, {"int": limit}]},
            "updates": [{"target": 0, "expr": {"put": [m, k, {"add": [current, {"int": 1}]}]}}]
        }, {
            "name": "close",
            "params": [{"name": "k", "type": {"enum": "item"}}],
            "guard": {"has_key": [m, k]},
            "updates": [{"target": 0, "expr": {"delete": [m, k]}}]
        }]),
        json!([{"name": "bounded", "expr": {"forall": {"name": "x", "in": {"keys": [m]}, "body": {"le": [{"get": [m, {"local": "x"}]}, {"int": 2}]}}}}]),
    )
}

#[test]
fn maps_hold_values_per_key() {
    let ir = wallet(2);
    let r = run(&ir);
    assert_eq!(r["status"], "verified", "{r}");
    // キーごとに、なし、1、2 の3通り（0 は put でしか作れないが、作る遷移はない）。
    assert_eq!(r["search"]["visited_states"], 27);
    recheck(&ir, &r);
}

#[test]
fn storing_a_value_outside_the_type_is_an_error() {
    let ir = wallet(3);
    let r = run(&ir);
    assert_eq!(r["status"], "error", "{r}");
    assert_eq!(r["property"]["site"], "update");
    assert_eq!(r["property"]["target"], "balance");
    assert_eq!(r["property"]["error"], json!({"kind": "not_in_domain"}));
    assert_eq!(r["trace"]["initial"], json!({"balance": [["bread", 1]]}));
    recheck(&ir, &r);
}

fn lock(peek_guard: Value) -> Value {
    let holder = json!({"var": 0});
    let mut ir = base(
        json!([{"name": "holder", "type": {"option": {"enum": "item"}}, "initial": {"none": {"enum": "item"}}}]),
        json!([
            {
                "name": "acquire",
                "params": [{"name": "u", "type": {"enum": "item"}}],
                "guard": {"is_none": [holder]},
                "updates": [{"target": 0, "expr": {"some": [{"param": 0}]}}]
            },
            {
                "name": "release",
                "guard": {"is_some": [holder]},
                "updates": [{"target": 0, "expr": {"none": {"enum": "item"}}}]
            },
            {
                "name": "peek",
                "guard": peek_guard,
                "output": {"type": {"enum": "item"}, "expr": {"unwrap": [holder]}}
            }
        ]),
        json!([]),
    );
    ir["contracts"] =
        json!([{"name": "kept", "action": "acquire", "expr": {"eq": [{"next": 0}, {"some": [{"param": 0}]}]}}]);
    ir
}

#[test]
fn options_and_unwrap() {
    let ir = lock(json!({"is_some": [{"var": 0}]}));
    let r = run(&ir);
    assert_eq!(r["status"], "verified", "{r}");
    assert_eq!(r["search"]["visited_states"], 4);
    recheck(&ir, &r);

    let ir = lock(json!({"bool": true}));
    let r = run(&ir);
    assert_eq!(r["status"], "error", "{r}");
    assert_eq!(r["property"]["site"], "output");
    assert_eq!(r["property"]["error"], json!({"kind": "none"}));
    assert_eq!(r["trace"]["initial"], json!({"holder": null}));
    recheck(&ir, &r);
}

fn queue() -> Value {
    let q = json!({"var": 0});
    let mut ir = base(
        json!([{"name": "q", "type": {"list": {"of": {"int": {"min": 0, "max": 3}}, "max": 2}}, "initial": {"list": {"of": {"int": {"min": 0, "max": 3}}, "max": 2, "items": []}}}]),
        json!([
            {
                "name": "enqueue",
                "params": [{"name": "x", "type": {"int": {"min": 0, "max": 3}}}],
                "guard": {"lt": [{"size": [q]}, {"int": 2}]},
                "updates": [{"target": 0, "expr": {"push": [q, {"param": 0}]}}]
            },
            {
                "name": "dequeue",
                "guard": {"gt": [{"size": [q]}, {"int": 0}]},
                "updates": [{"target": 0, "expr": {"shift": [q]}}],
                "output": {"type": {"int": {"min": 0, "max": 3}}, "expr": {"first": [q]}}
            }
        ]),
        json!([{"name": "ordered", "expr": {"forall": {"name": "x", "in": q, "body": {"le": [{"local": "x"}, {"int": 3}]}}}}]),
    );
    ir["contracts"] = json!([
        {"name": "last", "action": "enqueue", "expr": {"eq": [{"last": [{"next": 0}]}, {"param": 0}]}},
        {"name": "fifo", "action": "dequeue", "expr": {"eq": [{"output": {}}, {"at": [q, {"int": 0}]}]}}
    ]);
    ir
}

#[test]
fn lists_behave_as_queues() {
    let ir = queue();
    let r = run(&ir);
    assert_eq!(r["status"], "verified", "{r}");
    assert_eq!(r["search"]["visited_states"], 1 + 4 + 16);
    recheck(&ir, &r);
}

#[test]
fn a_full_list_is_an_error() {
    let mut ir = queue();
    ir["actions"][0]["guard"] = json!({"bool": true});
    let r = run(&ir);
    assert_eq!(r["status"], "error", "{r}");
    assert_eq!(r["property"]["error"], json!({"kind": "full"}));
    assert_eq!(r["trace"]["steps"].as_array().unwrap().len(), 2);
    recheck(&ir, &r);
}

#[test]
fn composite_arguments_enumerate_only_canonical_values() {
    let ir = base(
        json!([{"name": "last", "type": {"option": {"int": {"min": 0, "max": 2}}}, "initial": {"none": {"int": {"min": 0, "max": 2}}}}]),
        json!([{
            "name": "set",
            "params": [{"name": "p", "type": {"option": {"int": {"min": 0, "max": 2}}}}],
            "updates": [{"target": 0, "expr": {"param": 0}}]
        }]),
        json!([]),
    );
    let r = run(&ir);
    assert_eq!(r["status"], "verified", "{r}");
    assert_eq!(r["search"]["visited_states"], 4);
    // 各状態で、引数は none、some(0)、some(1)、some(2) の4通り。
    assert_eq!(r["search"]["transitions"], 16);
    recheck(&ir, &r);
}

fn invariant(expr: Value) -> Value {
    base(
        json!([{"name": "n", "type": {"int": {"min": 0, "max": 0}}, "initial": {"int": 0}}]),
        json!([]),
        json!([{"name": "p", "expr": expr}]),
    )
}

#[test]
fn division_follows_ruby() {
    let x = json!({"local": "x"});
    let law = json!({"forall": {"name": "x", "type": {"int": {"min": -7, "max": 7}}, "body": {"forall": {"name": "y", "type": {"int": {"min": -3, "max": 3}}, "body": {"implies": [
        {"ne": [{"local": "y"}, {"int": 0}]},
        {"let": {"name": "q", "value": {"div": [x, {"local": "y"}]}, "body": {"let": {"name": "r", "value": {"mod": [x, {"local": "y"}]}, "body": {"all": [
            {"eq": [{"add": [{"mul": [{"local": "q"}, {"local": "y"}]}, {"local": "r"}]}, x]},
            {"implies": [{"gt": [{"local": "y"}, {"int": 0}]}, {"all": [{"ge": [{"local": "r"}, {"int": 0}]}, {"lt": [{"local": "r"}, {"local": "y"}]}]}]},
            {"implies": [{"lt": [{"local": "y"}, {"int": 0}]}, {"all": [{"le": [{"local": "r"}, {"int": 0}]}, {"gt": [{"local": "r"}, {"local": "y"}]}]}]}
        ]}}}}}
    ]}}}}});
    assert_eq!(run(&invariant(law))["status"], "verified");
    let cases = [
        ((-7, 2), (-4, 1)),
        ((-7, -2), (3, -1)),
        ((7, -2), (-4, -1)),
        ((7, 2), (3, 1)),
    ];
    for ((a, b), (q, r)) in cases {
        let e = json!({"all": [
            {"eq": [{"div": [{"int": a}, {"int": b}]}, {"int": q}]},
            {"eq": [{"mod": [{"int": a}, {"int": b}]}, {"int": r}]}
        ]});
        assert_eq!(run(&invariant(e))["status"], "verified", "{a} / {b}");
    }
    let r = run(&invariant(
        json!({"eq": [{"div": [{"int": 1}, {"var": 0}]}, {"int": 0}]}),
    ));
    assert_eq!(r["status"], "error");
    assert_eq!(r["property"]["error"], json!({"kind": "division_by_zero"}));
    let min = json!({"sub": [{"int": -9223372036854775807i64}, {"int": 1}]});
    let r = run(&invariant(json!({"eq": [{"div": [min, {"int": -1}]}, {"int": 0}]})));
    assert_eq!(r["property"]["error"], json!({"kind": "overflow"}));
    let r = run(&invariant(json!({"eq": [{"mod": [min, {"int": -1}]}, {"int": 0}]})));
    assert_eq!(r["status"], "verified");
}

#[test]
fn evaluation_order_and_short_circuits_are_preserved() {
    let none = json!({"none": {"int": {"min": 0, "max": 1}}});
    let boom = json!({"unwrap": [none]});
    let overflow = json!({"add": [{"int": 9223372036854775807i64}, {"int": 1}]});
    let tuple = |a: &Value, b: &Value| json!({"tuple": [a, b]});
    let int = |n: i64| json!({"int": n});
    let status = |e: Value| {
        let r = run(&invariant(e));
        (
            r["status"].as_str().unwrap().to_string(),
            r["property"]["error"]["kind"].clone(),
        )
    };
    // 打ち切られた部分式は評価しない。
    assert_eq!(
        status(json!({"all": [{"bool": false}, {"eq": [boom, {"int": 0}]}]})).0,
        "violated"
    );
    assert_eq!(
        status(json!({"ite": [{"bool": true}, {"bool": true}, {"eq": [tuple(&boom, &boom), tuple(&boom, &boom)]}]})).0,
        "verified"
    );
    // 複合型の値の部分式は左から評価し、最初の失敗を報告する。
    assert_eq!(
        status(json!({"eq": [tuple(&overflow, &boom), tuple(&int(0), &int(0))]})).1,
        json!("overflow")
    );
    assert_eq!(
        status(json!({"eq": [tuple(&boom, &overflow), tuple(&int(0), &int(0))]})).1,
        json!("none")
    );
    // 比較が途中で偽と決まっても、両辺の評価は終える。
    assert_eq!(
        status(json!({"eq": [tuple(&int(1), &boom), tuple(&int(0), &int(0))]})).1,
        json!("none")
    );
    // 選ばれなかった枝は評価しない。複合型の ite でも同じ。
    let pick = |c: bool| json!({"eq": [{"ite": [{"bool": c}, tuple(&int(1), &int(2)), tuple(&boom, &int(2))]}, tuple(&int(1), &int(2))]});
    assert_eq!(status(pick(true)).0, "verified");
    assert_eq!(status(pick(false)).1, json!("none"));
    // 量化は正規順にたどり、最初に偽になった時点で打ち切る。
    let set = json!({"set": {"of": {"int": {"min": 0, "max": 3}}, "items": [{"int": 2}, {"int": 0}]}});
    let e = json!({"forall": {"name": "x", "in": set, "body": {"eq": [{"div": [{"int": 1}, {"sub": [{"local": "x"}, {"int": 2}]}]}, {"int": 0}]}}});
    assert_eq!(status(e).0, "violated");
}

#[test]
fn records_tuples_and_constants() {
    let mut ir = base(
        json!([{
            "name": "pos",
            "type": {"record": [{"name": "x", "type": {"int": {"min": 0, "max": 2}}}, {"name": "y", "type": {"int": {"min": 0, "max": 2}}}]},
            "initial": {"const": "origin"}
        }]),
        json!([{
            "name": "step",
            "params": [{"name": "d", "type": {"tuple": [{"int": {"min": 0, "max": 1}}, {"int": {"min": 0, "max": 1}}]}}],
            "guard": {"let": {"name": "p", "value": {"var": 0}, "body": {"all": [
                {"lt": [{"add": [{"field": {"of": {"local": "p"}, "name": "x"}}, {"nth": {"of": {"param": 0}, "index": 0}}]}, {"int": 3}]},
                {"lt": [{"add": [{"field": {"of": {"local": "p"}, "name": "y"}}, {"nth": {"of": {"param": 0}, "index": 1}}]}, {"int": 3}]}
            ]}}},
            "updates": [{"target": 0, "expr": {"record": [
                {"name": "x", "expr": {"add": [{"field": {"of": {"var": 0}, "name": "x"}}, {"nth": {"of": {"param": 0}, "index": 0}}]}},
                {"name": "y", "expr": {"add": [{"field": {"of": {"var": 0}, "name": "y"}}, {"nth": {"of": {"param": 0}, "index": 1}}]}}
            ]}}]
        }]),
        json!([{"name": "not_corner", "expr": {"ne": [{"var": 0}, {"record": [{"name": "x", "expr": {"int": 2}}, {"name": "y", "expr": {"int": 2}}]}]}}]),
    );
    ir["constants"] = json!([{
        "name": "origin",
        "type": {"record": [{"name": "x", "type": {"int": {"min": 0, "max": 2}}}, {"name": "y", "type": {"int": {"min": 0, "max": 2}}}]},
        "value": {"record": [{"name": "x", "expr": {"int": 0}}, {"name": "y", "expr": {"int": 0}}]}
    }]);
    let r = run(&ir);
    assert_eq!(r["status"], "violated", "{r}");
    assert_eq!(r["trace"]["steps"].as_array().unwrap().len(), 2);
    assert_eq!(r["trace"]["steps"][0]["args"], json!({"d": [1, 1]}));
    assert_eq!(r["trace"]["steps"][1]["state"], json!({"pos": {"x": 2, "y": 2}}));
    recheck(&ir, &r);
}

#[test]
fn type_errors_name_the_definition() {
    let load_err = |ir: Value| load(&ir.to_string()).err().unwrap().to_string();
    let mut ir = basket();
    ir["invariants"][0]["expr"] = json!({"contains": [{"var": 0}, {"int": 1}]});
    let message = load_err(ir);
    assert!(
        message.contains("\"small\"") && message.contains("enum item"),
        "{message}"
    );
    let mut ir = basket();
    ir["states"][0]["type"] = json!({"set": {"int": {"min": 0, "max": 100000}}});
    assert!(load_err(ir).contains("値の数"));
    let mut ir = basket();
    ir["states"][0]["type"] = json!({"set": {"set": {"bool": {}}}});
    assert!(load_err(ir).contains("set、map、list を含まない"));
}

#[test]
fn map_get_reports_missing_key_before_using_the_payload() {
    let key = json!({"enum": "item"});
    let value = json!({"option": {"bool": {}}});
    let map = json!({"map": {"key": key, "value": value}});
    let ir = base(
        json!([
            {"name": "items", "type": map,
             "initial": {"map": {"key": key, "value": value, "items": [[item("bread"), {"some": [{"bool": true}]}]]}}},
            {"name": "last", "type": value, "initial": {"none": {"bool": {}}}}
        ]),
        json!([{"name": "read", "updates": [{"target": 1, "expr": {"get": [{"var": 0}, item("apple")]}}]}]),
        json!([]),
    );

    let result = run(&ir);
    assert_eq!(result["status"], "error", "{result}");
    assert_eq!(result["property"]["site"], "update");
    assert_eq!(result["property"]["target"], "last");
    assert_eq!(result["property"]["error"], json!({"kind": "missing_key"}));
    recheck(&ir, &result);
}
