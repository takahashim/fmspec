//! 符号化した値と、型に応じたJSON表現の変換。
//!
//! Bool は真偽値、Int は数値、Enum はラベルの文字列で表す。読み込みは宣言した型に従って行う。

use crate::model::{EnumNames, Model, Names};
use fmspec_core::model::Type;
use serde_json::{json, Map, Value};

pub fn type_to_json(names: &Names, ty: &Type) -> Value {
    match ty {
        Type::Bool => json!({"bool": {}}),
        Type::Int(min, max) => json!({"int": {"min": min, "max": max}}),
        Type::Enum(id) => json!({"enum": names.enums.get(*id).map(|e| e.name.as_str()).unwrap_or("?")}),
    }
}

pub fn value_to_json(names: &Names, ty: &Type, x: i64) -> Value {
    match ty {
        Type::Bool => Value::Bool(x != 0),
        Type::Int(_, _) => json!(x),
        Type::Enum(id) => {
            let label = usize::try_from(x)
                .ok()
                .and_then(|k| names.enums.get(*id)?.variants.get(k));
            match label {
                Some(label) => json!(label),
                None => json!(x),
            }
        }
    }
}

pub(crate) fn value_from_json(enums: &[EnumNames], ty: &Type, v: &Value) -> Result<i64, String> {
    match ty {
        Type::Bool => v
            .as_bool()
            .map(i64::from)
            .ok_or_else(|| format!("真偽値が必要です（{v}）")),
        Type::Int(_, _) => match v.as_i64() {
            Some(x) if v.is_i64() || v.is_u64() => Ok(x),
            _ => Err(format!("符号付き64ビット整数が必要です（{v}）")),
        },
        Type::Enum(id) => {
            let label = v.as_str().ok_or_else(|| format!("ラベルの文字列が必要です（{v}）"))?;
            let e = enums.get(*id).ok_or_else(|| "未定義の列挙型".to_string())?;
            match e.variants.iter().position(|x| x == label) {
                Some(k) => Ok(k as i64),
                None => Err(format!("列挙型 {:?} に未定義のラベル {label:?}", e.name)),
            }
        }
    }
}

pub fn state_to_json(model: &Model, state: &[i64]) -> Value {
    let mut map = Map::new();
    for (i, x) in state.iter().enumerate() {
        match (model.names.states.get(i), model.raw().state_types.get(i)) {
            (Some(name), Some(ty)) => map.insert(name.clone(), value_to_json(&model.names, ty, *x)),
            _ => map.insert(format!("#{i}"), json!(x)),
        };
    }
    Value::Object(map)
}

pub(crate) fn state_from_json(model: &Model, v: &Value) -> Result<Vec<i64>, String> {
    let map = v.as_object().ok_or("状態はオブジェクトです")?;
    if map.len() != model.names.states.len() {
        return Err("状態変数の個数がモデルと合いません".to_string());
    }
    let mut state = Vec::new();
    for (name, ty) in model.names.states.iter().zip(model.raw().state_types.iter()) {
        let x = map.get(name).ok_or_else(|| format!("状態変数 {name:?} がありません"))?;
        state.push(value_from_json(&model.names.enums, ty, x).map_err(|e| format!("状態変数 {name:?}: {e}"))?);
    }
    Ok(state)
}

/// 操作の引数の列を、公開引数と内部選択のJSONに分ける。
pub fn args_to_json(model: &Model, action: usize, args: &[i64]) -> (Value, Value) {
    let mut params = Map::new();
    let mut choices = Map::new();
    let (Some(act), Some(names)) = (model.raw().actions.get(action), model.names.actions.get(action)) else {
        return (Value::Object(params), Value::Object(choices));
    };
    let all = names.params.iter().chain(names.choices.iter());
    for (i, ((name, ty), x)) in all.zip(act.domains.iter()).zip(args.iter()).enumerate() {
        let v = value_to_json(&model.names, ty, *x);
        if i < act.n_params {
            params.insert(name.clone(), v);
        } else {
            choices.insert(name.clone(), v);
        }
    }
    (Value::Object(params), Value::Object(choices))
}

pub(crate) fn args_from_json(
    model: &Model,
    action: usize,
    params: &Value,
    choices: &Value,
) -> Result<Vec<i64>, String> {
    let act = &model.raw().actions[action];
    let names = &model.names.actions[action];
    let params = params.as_object().ok_or("args はオブジェクトです")?;
    let choices = choices.as_object().ok_or("choices はオブジェクトです")?;
    if params.len() != names.params.len() || choices.len() != names.choices.len() {
        return Err(format!("操作 {:?} の引数の個数が合いません", names.name));
    }
    let mut args = Vec::new();
    let all = names
        .params
        .iter()
        .map(|n| (n, params))
        .chain(names.choices.iter().map(|n| (n, choices)));
    for ((name, map), ty) in all.zip(act.domains.iter()) {
        let x = map.get(name).ok_or_else(|| format!("引数 {name:?} がありません"))?;
        args.push(value_from_json(&model.names.enums, ty, x).map_err(|e| format!("引数 {name:?}: {e}"))?);
    }
    Ok(args)
}

/// 出力のJSON。出力宣言のない操作は `{"unit": true}`。
pub fn output_to_json(model: &Model, action: usize, output: Option<i64>) -> Value {
    let ty = model
        .raw()
        .actions
        .get(action)
        .and_then(|a| a.output.as_ref())
        .map(|o| &o.ty);
    match (ty, output) {
        (Some(ty), Some(x)) => json!({"value": value_to_json(&model.names, ty, x)}),
        (None, Some(x)) => json!({"value": x}),
        (_, None) => json!({"unit": true}),
    }
}

pub(crate) fn output_from_json(model: &Model, action: usize, v: &Value) -> Result<Option<i64>, String> {
    let map = v.as_object().ok_or("output はオブジェクトです")?;
    if map.len() != 1 {
        return Err("output は unit か value のどちらか1つを持ちます".to_string());
    }
    if map.get("unit") == Some(&Value::Bool(true)) {
        return Ok(None);
    }
    let x = map
        .get("value")
        .ok_or("output は unit か value のどちらか1つを持ちます")?;
    let ty = model.raw().actions[action]
        .output
        .as_ref()
        .map(|o| &o.ty)
        .ok_or_else(|| format!("操作 {:?} は出力を宣言していません", model.names.actions[action].name))?;
    value_from_json(&model.names.enums, ty, x)
        .map(Some)
        .map_err(|e| format!("output: {e}"))
}
