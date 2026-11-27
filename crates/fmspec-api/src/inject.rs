//! 注入する内部選択の指定と、入力のJSON。セッションとテスト経路の生成が共有する。
//!
//! 入力のJSON（`{"action", "args", "choices"}`）の読み取り（`parse_input`）と書き出し（`input_json`）は、
//! 互いに逆の変換なので、ここに並べて置く。

use fmspec_ir::{value_from_json, value_to_json, Model};
use serde_json::{json, Map, Value};

/// `inject` オプション（操作名から、注入する内部選択の名前の配列へのオブジェクト）を、
/// 操作ごとの内部選択の添字（昇順）にする。
pub(crate) fn parse_inject(model: &Model, v: Option<&Value>) -> Result<Vec<Vec<usize>>, String> {
    let mut injected: Vec<Vec<usize>> = vec![Vec::new(); model.names.actions.len()];
    let Some(v) = v.filter(|v| !v.is_null()) else {
        return Ok(injected);
    };
    let message = || format!("inject は、操作名から内部選択の名前の配列へのオブジェクトです（{v}）");
    for (action_name, choices) in v.as_object().ok_or_else(message)? {
        let a = model
            .names
            .action_index(action_name)
            .ok_or(format!("未定義の操作 {action_name:?}"))?;
        for choice in choices.as_array().ok_or_else(message)? {
            let choice = choice.as_str().ok_or_else(message)?;
            let k = model.names.actions[a]
                .choices
                .iter()
                .position(|n| n == choice)
                .ok_or(format!("操作 {action_name:?} に内部選択 {choice:?} はありません"))?;
            if !injected[a].contains(&k) {
                injected[a].push(k);
            }
        }
        injected[a].sort_unstable();
    }
    Ok(injected)
}

/// 注入する内部選択の、引数の列（公開引数に続けて内部選択）での添字。
pub(crate) fn inject_slots(model: &Model, injected: &[Vec<usize>]) -> Vec<Vec<usize>> {
    injected
        .iter()
        .enumerate()
        .map(|(a, ks)| {
            let act = &model.names.actions[a];
            ks.iter()
                .flat_map(|k| {
                    let i = act.params.len() + k;
                    let start = act.arg_offsets[i];
                    start..start + act.arg_types[i].width(&model.names.enums)
                })
                .collect()
        })
        .collect()
}

/// 入力（公開引数に、注入する選択の値を続けた列）を、公開引数（`args`）と注入する選択（`choices`）の
/// 名前付きのJSONにする。
pub(crate) fn input_json(model: &Model, injected: &[Vec<usize>], action: usize, values: &[i64]) -> Value {
    let enums = &model.names.enums;
    let names = &model.names.actions[action];
    let mut args = Map::new();
    let mut choices = Map::new();
    let mut at = 0;
    let order = (0..names.params.len()).chain(injected[action].iter().map(|k| names.params.len() + k));
    for i in order {
        let ty = &names.arg_types[i];
        let w = ty.width(enums);
        let v = value_to_json(&model.names, ty, values.get(at..at + w).unwrap_or(&[]));
        at += w;
        if i < names.params.len() {
            args.insert(names.params[i].clone(), v);
        } else {
            choices.insert(names.choices[i - names.params.len()].clone(), v);
        }
    }
    json!({"action": names.name, "args": args, "choices": choices})
}

/// 入力のJSON（`{"action", "args", "choices"}`）を、操作の添字と、入力（公開引数に、注入する選択の値を続けた列）にする。
/// `choices` は注入する選択の値で、`input_json` の逆である。ほかのキー（`output` など）は見ない。
pub(crate) fn parse_input(model: &Model, injected: &[Vec<usize>], v: &Value) -> Result<(usize, Vec<i64>), String> {
    let map = v.as_object().ok_or("入力はオブジェクトです")?;
    let name = map
        .get("action")
        .and_then(Value::as_str)
        .ok_or("action は操作の名前です")?;
    let action = model.names.action_index(name).ok_or(format!("未定義の操作 {name:?}"))?;
    let empty = Map::new();
    let named = |key: &str| match map.get(key) {
        None => Ok(&empty),
        Some(v) => v.as_object().ok_or(format!("{key} はオブジェクトです")),
    };
    let args = named("args")?;
    let choices = named("choices")?;
    let names = &model.names.actions[action];
    let injected = &injected[action];
    if args.len() != names.params.len() || choices.len() != injected.len() {
        return Err(format!("操作 {name:?} の引数または注入する選択の個数が合いません"));
    }
    let read = |given: &Map<String, Value>, binding: &String, index: usize| -> Result<Vec<i64>, String> {
        let v = given.get(binding).ok_or(format!("引数 {binding:?} がありません"))?;
        value_from_json(&model.names.enums, &names.arg_types[index], v).map_err(|e| format!("引数 {binding:?}: {e}"))
    };
    let mut values = Vec::new();
    for (i, param) in names.params.iter().enumerate() {
        values.extend(read(args, param, i)?);
    }
    for k in injected {
        values.extend(read(choices, &names.choices[*k], names.params.len() + k)?);
    }
    Ok((action, values))
}
