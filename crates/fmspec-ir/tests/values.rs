//! 値のJSON表現（`value_to_json` と `value_from_json`）。正規形への変換と、型に合わない値の拒否。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_ir::{load, value_from_json, value_to_json, Model, SType};
use serde_json::{json, Value};

/// 状態変数の型だけを使うモデル。状態変数 `v` の型を `ty` とし、初期値を `initial` とする。
fn model_of(ty: Value, initial: Value) -> Model {
    let ir = json!({
        "ir_version": 1,
        "name": "values",
        "enums": [{"name": "color", "variants": ["red", "green", "blue"]}],
        "states": [{"name": "v", "type": ty, "initial": initial}],
    });
    load(&ir.to_string()).unwrap_or_else(|e| panic!("{e}"))
}

fn ty(m: &Model) -> &SType {
    &m.names.state_types[0]
}

fn from(m: &Model, v: Value) -> Result<Vec<i64>, String> {
    value_from_json(&m.names.enums, ty(m), &v)
}

fn color_set() -> Model {
    model_of(
        json!({"set": {"enum": "color"}}),
        json!({"set": {"of": {"enum": "color"}, "items": []}}),
    )
}

fn color_map() -> Model {
    let bit = json!({"int": {"min": 0, "max": 1}});
    model_of(
        json!({"map": {"key": {"enum": "color"}, "value": bit}}),
        json!({"map": {"key": {"enum": "color"}, "value": bit, "items": []}}),
    )
}

#[test]
fn composite_values_round_trip_through_their_canonical_json() {
    let small = json!({"int": {"min": -1, "max": 2}});
    let ty = json!({"tuple": [
        {"record": [{"name": "on", "type": {"bool": {}}}, {"name": "c", "type": {"enum": "color"}}]},
        {"option": small},
        {"set": small},
        {"map": {"key": {"option": {"enum": "color"}}, "value": small}},
        {"list": {"of": {"enum": "color"}, "max": 3}}
    ]});
    let initial = json!({"tuple": [
        {"record": [{"name": "on", "expr": {"bool": false}}, {"name": "c", "expr": {"enum": {"type": "color", "variant": "red"}}}]},
        {"none": small},
        {"set": {"of": small, "items": []}},
        {"map": {"key": {"option": {"enum": "color"}}, "value": small, "items": []}},
        {"list": {"of": {"enum": "color"}, "max": 3, "items": []}}
    ]});
    let m = model_of(ty, initial);
    let value = json!([
        {"on": true, "c": "blue"},
        {"some": -1},
        [-1, 0, 2],
        [[null, 2], [{"some": "green"}, -1]],
        ["green", "green"]
    ]);
    let slots = from(&m, value.clone()).unwrap();
    assert_eq!(slots.len(), m.names.state_slots(0).len());
    assert_eq!(value_to_json(&m.names, &m.names.state_types[0], &slots), value);
    // 初期値（既定値ばかりの値）も、同じ表現で読み書きできる。
    let initial = &m.raw().inits[0];
    let json = value_to_json(&m.names, &m.names.state_types[0], initial);
    assert_eq!(json, json!([{"on": false, "c": "red"}, null, [], [], []]));
    assert_eq!(&from(&m, json).unwrap(), initial);
}

#[test]
fn sets_and_maps_are_read_in_any_order_and_written_in_canonical_order() {
    let m = color_set();
    let slots = from(&m, json!(["blue", "red"])).unwrap();
    assert_eq!(slots, vec![1, 0, 1]);
    assert_eq!(value_to_json(&m.names, ty(&m), &slots), json!(["red", "blue"]));

    let m = color_map();
    let slots = from(&m, json!([["blue", 1], ["red", 0]])).unwrap();
    assert_eq!(slots, vec![1, 0, 0, 0, 1, 1]);
    assert_eq!(
        value_to_json(&m.names, ty(&m), &slots),
        json!([["red", 0], ["blue", 1]])
    );
}

/// Setの要素とMapのキーの重複は拒否する。Setの値の表現は重複を含まない要素の配列で、
/// Mapのキーの重複は、値が同じでも拒否するのとそろえる。
#[test]
fn duplicate_set_elements_and_duplicate_map_keys_are_rejected() {
    let m = color_set();
    assert_eq!(
        from(&m, json!(["green", "green"])).unwrap_err(),
        "要素 \"green\" が重複しています"
    );
    assert_eq!(
        from(&m, json!(["green", "red", "green"])).unwrap_err(),
        "要素 \"green\" が重複しています"
    );
    // 番号に変換して同じになる要素も重複とする。
    let m = model_of(
        json!({"set": {"option": {"enum": "color"}}}),
        json!({"set": {"of": {"option": {"enum": "color"}}, "items": []}}),
    );
    assert_eq!(
        from(&m, json!([null, {"some": "red"}, null])).unwrap_err(),
        "要素 null が重複しています"
    );

    let m = color_map();
    assert_eq!(
        from(&m, json!([["red", 0], ["red", 1]])).unwrap_err(),
        "キー \"red\" が重複しています"
    );
    assert_eq!(
        from(&m, json!([["red", 0], ["red", 0]])).unwrap_err(),
        "キー \"red\" が重複しています"
    );
}

#[test]
fn values_that_do_not_fit_the_type_are_rejected() {
    let m = model_of(json!({"int": {"min": 0, "max": 3}}), json!({"int": 0}));
    assert!(from(&m, json!(1.5)).unwrap_err().contains("整数"));
    assert!(from(&m, json!(9223372036854775808u64)).unwrap_err().contains("整数"));
    // 状態変数の整数の範囲は、ここでは検査しない（判定ゲートが検査する）。
    assert_eq!(from(&m, json!(7)).unwrap(), vec![7]);

    let m = model_of(
        json!({"enum": "color"}),
        json!({"enum": {"type": "color", "variant": "red"}}),
    );
    assert!(from(&m, json!("purple")).unwrap_err().contains("未定義のラベル"));
    assert!(from(&m, json!(0)).unwrap_err().contains("ラベルの文字列"));

    let bit = json!({"int": {"min": 0, "max": 1}});
    let m = model_of(
        json!({"record": [{"name": "a", "type": bit}, {"name": "b", "type": bit}]}),
        json!({"record": [{"name": "a", "expr": {"int": 0}}, {"name": "b", "expr": {"int": 0}}]}),
    );
    assert!(from(&m, json!({"a": 0})).unwrap_err().contains("2 個"));
    assert!(from(&m, json!({"a": 0, "c": 0}))
        .unwrap_err()
        .contains("\"b\" がありません"));

    let m = model_of(json!({"option": bit}), json!({"none": bit}));
    assert!(from(&m, json!(0)).unwrap_err().contains("some"));
    assert!(from(&m, json!({"some": 0, "extra": 1})).unwrap_err().contains("some"));

    let m = model_of(
        json!({"list": {"of": bit, "max": 1}}),
        json!({"list": {"of": bit, "max": 1, "items": []}}),
    );
    assert!(from(&m, json!([0, 1])).unwrap_err().contains("上限 1"));

    // Setの要素とMapのキーは番号にするので、範囲外の整数は型に属さないとして拒否する。
    let m = model_of(json!({"set": bit}), json!({"set": {"of": bit, "items": []}}));
    assert!(from(&m, json!([2])).unwrap_err().contains("属しません"));
    let m = color_map();
    assert!(from(&m, json!([["red"]])).unwrap_err().contains("[キー, 値]"));
}

/// 公開の `value_from_json` には、読み込みで拒否する型（キー型でない要素の型のSetやMap）も渡せる。
/// そのときは panic せず、誤りを返す。
#[test]
fn sets_and_maps_of_non_key_types_are_errors_not_panics() {
    let wide = SType::Int(0, 1 << 20);
    let set = SType::Set(Box::new(wide.clone()));
    assert!(value_from_json(&[], &set, &json!([5])).unwrap_err().contains("キー型"));
    let map = SType::Map(Box::new(wide), Box::new(SType::Bool));
    assert!(value_from_json(&[], &map, &json!([[5, true]]))
        .unwrap_err()
        .contains("キー型"));
    let nested = SType::Set(Box::new(SType::Set(Box::new(SType::Bool))));
    assert!(value_from_json(&[], &nested, &json!([[true]])).is_err());
}
