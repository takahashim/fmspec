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
//! | Set | 要素の配列。正規順に並べ、重複を含めない |
//! | Map | `[キー, 値]` の配列。キーの正規順に並べる |
//! | List | 要素の配列 |
//!
//! JSONと符号の列の間は、値の木（中核の `Val`）を通す。ここではJSONと値の木の形の対応だけを扱い、
//! 値の木と符号の列の変換は、中核の検証済みの関数（`SType::encode`、`SType::decode`）で行う。
//!
//! 読み込みは宣言した型に従って行う。整数の範囲は検査しない（判定ゲートが状態の型を検査する）。
//! ただし、Setの要素とMapのキーは番号に変換するので、型に属さなければ誤りとする。
//! 読み込みでは順序を問わないが、番号に変換して同じになるSetの要素やMapのキーが重複していれば誤りとする。

use crate::model::{EnumNames, Model, Names};
use crate::types::SType;
use fmspec_core::kernel::model::Type;
use fmspec_core::value::val_codec::Val;
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

/// スロットの列を、型に応じたJSONにする。正規形の符号化でなければ `{"invalid_slots": [...]}`。
pub fn value_to_json(names: &Names, ty: &SType, slots: &[i64]) -> Value {
    match ty.decode(&names.enums, slots) {
        Some(v) => val_to_json(names, ty, &v),
        None => json!({ "invalid_slots": slots }),
    }
}

/// 値の木のJSON。
fn val_to_json(names: &Names, ty: &SType, v: &Val) -> Value {
    match (ty, v) {
        (SType::Bool, Val::Bool(b)) => Value::Bool(*b),
        (SType::Int(_, _), Val::Int(x)) => json!(x),
        (SType::Enum(id), Val::Enum(k)) => {
            let label = usize::try_from(*k)
                .ok()
                .and_then(|k| names.enums.get(*id)?.variants.get(k));
            match label {
                Some(label) => json!(label),
                None => json!(k),
            }
        }
        (SType::Tuple(ts), Val::Tuple(vs)) => {
            Value::Array(ts.iter().zip(vs).map(|(t, v)| val_to_json(names, t, v)).collect())
        }
        (SType::Record(fs), Val::Tuple(vs)) => {
            let mut map = Map::new();
            for ((name, t), v) in fs.iter().zip(vs) {
                map.insert(name.clone(), val_to_json(names, t, v));
            }
            Value::Object(map)
        }
        (SType::Option(_), Val::None) => Value::Null,
        (SType::Option(t), Val::Some(w)) => json!({"some": val_to_json(names, t, w)}),
        (SType::Set(t), Val::Set(es)) => Value::Array(es.iter().map(|e| val_to_json(names, t, e)).collect()),
        (SType::Map(k, x), Val::Map(ks, vs)) => Value::Array(
            ks.iter()
                .zip(vs)
                .map(|(kv, vv)| json!([val_to_json(names, k, kv), val_to_json(names, x, vv)]))
                .collect(),
        ),
        (SType::List(t, _), Val::List(items)) => Value::Array(items.iter().map(|x| val_to_json(names, t, x)).collect()),
        // 中核の decode は型に合う木だけを返す。
        _ => Value::Null,
    }
}

/// 型に応じて、JSONの値をスロットの列（正規形）にする。型に合わない値は `Err`。
pub fn value_from_json(enums: &[EnumNames], ty: &SType, v: &Value) -> Result<Vec<i64>, String> {
    let val = val_from_json(enums, ty, v)?;
    ty.encode(enums, &val)
        .ok_or_else(|| format!("{v} を型の符号の列にできません"))
}

/// 型に応じて、JSONの値を値の木にする。形の誤りと、Setの要素とMapのキーの誤り（型に属さない、重複）は `Err`。
fn val_from_json(enums: &[EnumNames], ty: &SType, v: &Value) -> Result<Val, String> {
    Ok(match ty {
        SType::Bool => Val::Bool(v.as_bool().ok_or_else(|| format!("真偽値が必要です（{v}）"))?),
        SType::Int(_, _) => match v.as_i64() {
            Some(x) if v.is_i64() || v.is_u64() => Val::Int(x),
            _ => return Err(format!("符号付き64ビット整数が必要です（{v}）")),
        },
        SType::Enum(id) => {
            let label = v.as_str().ok_or_else(|| format!("ラベルの文字列が必要です（{v}）"))?;
            let e = enums.get(*id).ok_or_else(|| "未定義の列挙型".to_string())?;
            match e.variants.iter().position(|x| x == label) {
                Some(k) => Val::Enum(k as i64),
                None => return Err(format!("列挙型 {:?} に未定義のラベル {label:?}", e.name)),
            }
        }
        SType::Tuple(ts) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            if items.len() != ts.len() {
                return Err(format!("要素が {} 個必要です（{v}）", ts.len()));
            }
            Val::Tuple(
                ts.iter()
                    .zip(items)
                    .map(|(t, x)| val_from_json(enums, t, x))
                    .collect::<Result<_, _>>()?,
            )
        }
        SType::Record(fs) => {
            let map = v.as_object().ok_or_else(|| format!("オブジェクトが必要です（{v}）"))?;
            if map.len() != fs.len() {
                return Err(format!("フィールドが {} 個必要です（{v}）", fs.len()));
            }
            let mut vs = Vec::new();
            for (name, t) in fs {
                let x = map
                    .get(name)
                    .ok_or_else(|| format!("フィールド {name:?} がありません"))?;
                vs.push(val_from_json(enums, t, x)?);
            }
            Val::Tuple(vs)
        }
        SType::Option(t) => {
            if v.is_null() {
                Val::None
            } else {
                let inner = v
                    .as_object()
                    .filter(|m| m.len() == 1)
                    .and_then(|m| m.get("some"))
                    .ok_or_else(|| format!("null か {{\"some\": 値}} が必要です（{v}）"))?;
                Val::Some(Box::new(val_from_json(enums, t, inner)?))
            }
        }
        SType::Set(t) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            let mut seen = vec![false; key_count(enums, t)?];
            let mut es = Vec::new();
            for x in items {
                let e = val_from_json(enums, t, x)?;
                let r = key_rank(enums, t, &e, x, seen.len())?;
                if std::mem::replace(&mut seen[r], true) {
                    return Err(format!("要素 {x} が重複しています"));
                }
                es.push(e);
            }
            Val::Set(es)
        }
        SType::Map(k, val) => {
            let items = v
                .as_array()
                .ok_or_else(|| format!("[キー, 値] の配列が必要です（{v}）"))?;
            let mut seen = vec![false; key_count(enums, k)?];
            let (mut ks, mut vs) = (Vec::new(), Vec::new());
            for item in items {
                let pair = item
                    .as_array()
                    .filter(|p| p.len() == 2)
                    .ok_or_else(|| format!("[キー, 値] が必要です（{item}）"))?;
                let kv = val_from_json(enums, k, &pair[0])?;
                let r = key_rank(enums, k, &kv, &pair[0], seen.len())?;
                if std::mem::replace(&mut seen[r], true) {
                    return Err(format!("キー {} が重複しています", pair[0]));
                }
                ks.push(kv);
                vs.push(val_from_json(enums, val, &pair[1])?);
            }
            Val::Map(ks, vs)
        }
        SType::List(t, max) => {
            let items = v.as_array().ok_or_else(|| format!("配列が必要です（{v}）"))?;
            if items.len() > *max {
                return Err(format!("要素が {} 個あり、上限 {max} を超えます", items.len()));
            }
            Val::List(
                items
                    .iter()
                    .map(|x| val_from_json(enums, t, x))
                    .collect::<Result<_, _>>()?,
            )
        }
    })
}

/// キー型の値の数。読み込みはキー型でない要素の型のSetやMapを拒否するが、
/// 公開の `value_from_json` には渡せるので、そのときは誤りとする。
fn key_count(enums: &[EnumNames], t: &SType) -> Result<usize, String> {
    t.keys(enums)
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| "Setの要素とMapのキーの型がキー型ではありません".to_string())
}

/// Setの要素とMapのキーの番号（誤りの報告のため。符号の列は `SType::encode` が作る）。
fn key_rank(enums: &[EnumNames], t: &SType, e: &Val, x: &Value, n: usize) -> Result<usize, String> {
    let rank = t
        .encode(enums, e)
        .and_then(|codes| t.rank(enums, &codes))
        .and_then(|r| usize::try_from(r).ok());
    match rank {
        Some(r) if r < n => Ok(r),
        _ => Err(format!("{x} は要素の型に属しません")),
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
