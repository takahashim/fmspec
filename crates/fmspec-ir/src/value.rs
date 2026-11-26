//! 値のスロットと、型に応じたJSON表現の変換。
//!
//! | 型 | JSON |
//! |---|---|
//! | Bool | 真偽値 |
//! | Int | 数値 |
//! | Enum | ラベルの文字列 |
//! | Tuple | 要素の配列 |
//! | Record | フィールド名をキーとするオブジェクト |
//! | Option | 空なら `null`、そうでなければ `{"some": 値}` |
//! | Set | 要素の配列。正規順に並べる |
//! | Map | `[キー, 値]` の配列。キーの正規順に並べる |
//! | List | 要素の配列 |
//!
//! 読み込みは宣言した型に従って行う。整数の範囲は検査しない（判定ゲートが状態の型を検査する）。
//! ただし、Setの要素とMapのキーは番号に変換するので、型に属さなければ誤りとする。

use crate::model::{EnumNames, Model, Names};
use crate::types::SType;
use fmspec_core::map_encoding::encode_map_rows;
use fmspec_core::model::Type;
use serde_json::{json, Map, Value};

fn enum_name(names: &Names, id: usize) -> &str {
    names.enums.get(id).map(|e| e.name.as_str()).unwrap_or("?")
}

/// 中核の型のJSON。
pub fn core_type_to_json(names: &Names, ty: &Type) -> Value {
    match ty {
        Type::Bool => json!({"bool": {}}),
        Type::Int(min, max) => json!({"int": {"min": min, "max": max}}),
        Type::Enum(id) => json!({"enum": enum_name(names, *id)}),
    }
}

pub fn type_to_json(names: &Names, ty: &SType) -> Value {
    match ty {
        SType::Bool => json!({"bool": {}}),
        SType::Int(min, max) => json!({"int": {"min": min, "max": max}}),
        SType::Enum(id) => json!({"enum": enum_name(names, *id)}),
        SType::Tuple(ts) => json!({"tuple": ts.iter().map(|t| type_to_json(names, t)).collect::<Vec<_>>()}),
        SType::Record(fs) => json!({"record": fs
            .iter()
            .map(|(n, t)| json!({"name": n, "type": type_to_json(names, t)}))
            .collect::<Vec<_>>()}),
        SType::Option(t) => json!({"option": type_to_json(names, t)}),
        SType::Set(t) => json!({"set": type_to_json(names, t)}),
        SType::Map(k, v) => json!({"map": {"key": type_to_json(names, k), "value": type_to_json(names, v)}}),
        SType::List(t, n) => json!({"list": {"of": type_to_json(names, t), "max": n}}),
    }
}

fn parts<'s>(enums: &[EnumNames], tys: impl Iterator<Item = &'s SType>, slots: &[i64]) -> Vec<(&'s SType, Vec<i64>)> {
    let mut at = 0;
    tys.map(|t| {
        let w = t.width(enums);
        let part = slots.get(at..at + w).map(<[i64]>::to_vec).unwrap_or_default();
        at += w;
        (t, part)
    })
    .collect()
}

/// スロットの列を、型に応じたJSONにする。
pub fn value_to_json(names: &Names, ty: &SType, slots: &[i64]) -> Value {
    let enums = &names.enums;
    let x = slots.first().copied().unwrap_or(0);
    match ty {
        SType::Bool => Value::Bool(x != 0),
        SType::Int(_, _) => json!(x),
        SType::Enum(id) => {
            let label = usize::try_from(x)
                .ok()
                .and_then(|k| names.enums.get(*id)?.variants.get(k));
            match label {
                Some(label) => json!(label),
                None => json!(x),
            }
        }
        SType::Tuple(ts) => Value::Array(
            parts(enums, ts.iter(), slots)
                .iter()
                .map(|(t, s)| value_to_json(names, t, s))
                .collect(),
        ),
        SType::Record(fs) => {
            let values = parts(enums, fs.iter().map(|(_, t)| t), slots);
            let mut map = Map::new();
            for ((name, _), (t, s)) in fs.iter().zip(&values) {
                map.insert(name.clone(), value_to_json(names, t, s));
            }
            Value::Object(map)
        }
        SType::Option(t) => {
            if x == 0 {
                Value::Null
            } else {
                json!({"some": value_to_json(names, t, slots.get(1..).unwrap_or(&[]))})
            }
        }
        SType::Set(t) => {
            let mut out = Vec::new();
            for (r, bit) in slots.iter().enumerate() {
                if *bit != 0 {
                    let mut codes = Vec::new();
                    t.unrank(enums, r as u64, &mut codes);
                    out.push(value_to_json(names, t, &codes));
                }
            }
            Value::Array(out)
        }
        SType::Map(k, v) => {
            let w = 1 + v.width(enums);
            let mut out = Vec::new();
            for (r, entry) in slots.chunks(w).enumerate() {
                if entry.first().copied().unwrap_or(0) != 0 {
                    let mut codes = Vec::new();
                    k.unrank(enums, r as u64, &mut codes);
                    out.push(json!([
                        value_to_json(names, k, &codes),
                        value_to_json(names, v, &entry[1..])
                    ]));
                }
            }
            Value::Array(out)
        }
        SType::List(t, _) => {
            let w = t.width(enums);
            let len = usize::try_from(x).unwrap_or(0);
            Value::Array(
                slots
                    .get(1..)
                    .unwrap_or(&[])
                    .chunks(w.max(1))
                    .take(len)
                    .map(|s| value_to_json(names, t, s))
                    .collect(),
            )
        }
    }
}

/// 型に応じて、JSONの値をスロットの列（正規形）にする。型に合わない値は `Err`。
pub fn value_from_json(enums: &[EnumNames], ty: &SType, v: &Value) -> Result<Vec<i64>, String> {
    let mut out = Vec::new();
    encode(enums, ty, v, &mut out)?;
    Ok(out)
}

fn encode(enums: &[EnumNames], ty: &SType, v: &Value, out: &mut Vec<i64>) -> Result<(), String> {
    match ty {
        SType::Bool => out.push(
            v.as_bool()
                .map(i64::from)
                .ok_or_else(|| format!("真偽値が必要です（{v}）"))?,
        ),
        SType::Int(_, _) => match v.as_i64() {
            Some(x) if v.is_i64() || v.is_u64() => out.push(x),
            _ => return Err(format!("符号付き64ビット整数が必要です（{v}）")),
        },
        SType::Enum(id) => {
            let label = v.as_str().ok_or_else(|| format!("ラベルの文字列が必要です（{v}）"))?;
            let e = enums.get(*id).ok_or_else(|| "未定義の列挙型".to_string())?;
            match e.variants.iter().position(|x| x == label) {
                Some(k) => out.push(k as i64),
                None => return Err(format!("列挙型 {:?} に未定義のラベル {label:?}", e.name)),
            }
        }
        SType::Tuple(ts) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            if items.len() != ts.len() {
                return Err(format!("要素が {} 個必要です（{v}）", ts.len()));
            }
            for (t, x) in ts.iter().zip(items) {
                encode(enums, t, x, out)?;
            }
        }
        SType::Record(fs) => {
            let map = v.as_object().ok_or_else(|| format!("オブジェクトが必要です（{v}）"))?;
            if map.len() != fs.len() {
                return Err(format!("フィールドが {} 個必要です（{v}）", fs.len()));
            }
            for (name, t) in fs {
                let x = map
                    .get(name)
                    .ok_or_else(|| format!("フィールド {name:?} がありません"))?;
                encode(enums, t, x, out)?;
            }
        }
        SType::Option(t) => {
            if v.is_null() {
                out.push(0);
                t.defaults(enums, out);
            } else {
                let inner = v
                    .as_object()
                    .filter(|m| m.len() == 1)
                    .and_then(|m| m.get("some"))
                    .ok_or_else(|| format!("null か {{\"some\": 値}} が必要です（{v}）"))?;
                out.push(1);
                encode(enums, t, inner, out)?;
            }
        }
        SType::Set(t) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            let n = t.keys(enums).unwrap_or(0) as usize;
            let mut bits = vec![0i64; n];
            for x in items {
                let r = key_rank(enums, t, x)?;
                bits[r] = 1;
            }
            out.extend(bits);
        }
        SType::Map(k, val) => {
            let items = v
                .as_array()
                .ok_or_else(|| format!("[キー, 値] の配列が必要です（{v}）"))?;
            let n = k.keys(enums).unwrap_or(0) as usize;
            let mut entries: Vec<Option<Vec<i64>>> = vec![None; n];
            for item in items {
                let pair = item
                    .as_array()
                    .filter(|p| p.len() == 2)
                    .ok_or_else(|| format!("[キー, 値] が必要です（{item}）"))?;
                let r = key_rank(enums, k, &pair[0])?;
                if entries[r].is_some() {
                    return Err(format!("キー {} が重複しています", pair[0]));
                }
                let mut codes = Vec::new();
                encode(enums, val, &pair[1], &mut codes)?;
                entries[r] = Some(codes);
            }
            let mut default = Vec::new();
            val.defaults(enums, &mut default);
            let flat =
                encode_map_rows(&entries, &default).ok_or_else(|| "Mapの値スロット数が型と一致しません".to_string())?;
            out.extend(flat);
        }
        SType::List(t, max) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            if items.len() > *max {
                return Err(format!("要素が {} 個あり、上限 {max} を超えます", items.len()));
            }
            out.push(items.len() as i64);
            for x in items {
                encode(enums, t, x, out)?;
            }
            for _ in items.len()..*max {
                t.defaults(enums, out);
            }
        }
    }
    Ok(())
}

fn key_rank(enums: &[EnumNames], t: &SType, x: &Value) -> Result<usize, String> {
    let mut codes = Vec::new();
    encode(enums, t, x, &mut codes)?;
    match t.rank(enums, &codes) {
        Some(r) => Ok(r as usize),
        None => Err(format!("{x} は要素の型に属しません")),
    }
}

pub fn state_to_json(model: &Model, state: &[i64]) -> Value {
    let names = &model.names;
    let mut map = Map::new();
    for (i, (name, ty)) in names.states.iter().zip(&names.state_types).enumerate() {
        let slots = state.get(names.state_slots(i)).unwrap_or(&[]);
        map.insert(name.clone(), value_to_json(names, ty, slots));
    }
    Value::Object(map)
}

pub(crate) fn state_from_json(model: &Model, v: &Value) -> Result<Vec<i64>, String> {
    let names = &model.names;
    let map = v.as_object().ok_or("状態はオブジェクトです")?;
    if map.len() != names.states.len() {
        return Err("状態変数の個数がモデルと合いません".to_string());
    }
    let mut state = Vec::new();
    for (name, ty) in names.states.iter().zip(&names.state_types) {
        let x = map.get(name).ok_or_else(|| format!("状態変数 {name:?} がありません"))?;
        state.extend(value_from_json(&names.enums, ty, x).map_err(|e| format!("状態変数 {name:?}: {e}"))?);
    }
    Ok(state)
}

/// 操作の引数の列を、公開引数と内部選択のJSONに分ける。
pub fn args_to_json(model: &Model, action: usize, args: &[i64]) -> (Value, Value) {
    let mut params = Map::new();
    let mut choices = Map::new();
    let Some(act) = model.names.actions.get(action) else {
        return (Value::Object(params), Value::Object(choices));
    };
    for (i, (name, ty)) in act.arg_names().zip(&act.arg_types).enumerate() {
        let start = act.arg_offsets[i];
        let slots = args.get(start..start + ty.width(&model.names.enums)).unwrap_or(&[]);
        let v = value_to_json(&model.names, ty, slots);
        if i < act.params.len() {
            params.insert(name.clone(), v);
        } else {
            choices.insert(name.clone(), v);
        }
    }
    (Value::Object(params), Value::Object(choices))
}

/// 公開引数と内部選択のJSONを、操作の引数の列にする。
pub fn args_from_json(model: &Model, action: usize, params: &Value, choices: &Value) -> Result<Vec<i64>, String> {
    let names = &model.names.actions[action];
    let params = params.as_object().ok_or("args はオブジェクトです")?;
    let choices = choices.as_object().ok_or("choices はオブジェクトです")?;
    if params.len() != names.params.len() || choices.len() != names.choices.len() {
        return Err(format!("操作 {:?} の引数の個数が合いません", names.name));
    }
    let mut args = Vec::new();
    for (i, (name, ty)) in names.arg_names().zip(&names.arg_types).enumerate() {
        let map = if i < names.params.len() { params } else { choices };
        let x = map.get(name).ok_or_else(|| format!("引数 {name:?} がありません"))?;
        args.extend(value_from_json(&model.names.enums, ty, x).map_err(|e| format!("引数 {name:?}: {e}"))?);
    }
    Ok(args)
}

/// 出力のJSON。出力宣言のない操作は `{"unit": true}`。
pub fn output_to_json(model: &Model, action: usize, output: Option<i64>) -> Value {
    let ty = model.names.actions.get(action).and_then(|a| a.output.as_ref());
    match (ty, output) {
        (Some(ty), Some(x)) => json!({"value": value_to_json(&model.names, ty, &[x])}),
        (None, Some(x)) => json!({"value": x}),
        (_, None) => json!({"unit": true}),
    }
}

/// 出力の値のJSONを符号にする。
pub fn output_value_from_json(model: &Model, action: usize, v: &Value) -> Result<i64, String> {
    let names = &model.names.actions[action];
    let ty = names
        .output
        .as_ref()
        .ok_or_else(|| format!("操作 {:?} は出力を宣言していません", names.name))?;
    let codes = value_from_json(&model.names.enums, ty, v)?;
    codes.first().copied().ok_or_else(|| "出力の値が不正です".to_string())
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
    output_value_from_json(model, action, x)
        .map(Some)
        .map_err(|e| format!("output: {e}"))
}
