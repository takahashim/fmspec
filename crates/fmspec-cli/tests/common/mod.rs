//! テスト用のモデル。
//!
//! チケット例は crates/fmspec-search/tests/common にも同じものがある（テスト用の補助コードは crate 間で共有できないので、小さいものは重複させる）。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use serde_json::{json, Value};

/// 仕様書 §4.1 のチケット例。
pub fn tickets() -> Value {
    json!({
        "ir_version": 1,
        "name": "tickets",
        "states": [{"id": 0, "name": "sold", "type": {"int": {"min": 0, "max": 4}}, "initial": {"int": 0}}],
        "actions": [
            {
                "name": "purchase",
                "params": [{"name": "quantity", "type": {"int": {"min": 1, "max": 2}}}],
                "choices": [],
                "guard": {"le": [{"add": [{"var": 0}, {"param": 0}]}, {"int": 3}]},
                "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"param": 0}]}}]
            },
            {
                "name": "cancel",
                "guard": {"gt": [{"var": 0}, {"int": 0}]},
                "updates": [{"target": 0, "expr": {"sub": [{"var": 0}, {"int": 1}]}}]
            }
        ],
        "invariants": [{"name": "capacity_respected", "expr": {"le": [{"var": 0}, {"int": 3}]}}]
    })
}

/// チケット例から購入の guard だけを削除したもの。
pub fn tickets_without_guard() -> Value {
    let mut ir = tickets();
    ir["actions"][0].as_object_mut().unwrap().remove("guard");
    ir
}
