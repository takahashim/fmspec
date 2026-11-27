//! IRのJSONを読むための補助関数。

use crate::model::{LoadError, Source};
use serde_json::{Map, Value};
use std::collections::HashSet;

pub(crate) type Res<T> = Result<T, LoadError>;

pub(crate) fn schema<T>(path: &str, message: impl Into<String>) -> Res<T> {
    Err(LoadError::Schema {
        path: path.to_string(),
        message: message.into(),
    })
}

pub(crate) fn object<'a>(v: &'a Value, path: &str, allowed: &[&str]) -> Res<&'a Map<String, Value>> {
    let Some(map) = v.as_object() else {
        return schema(path, "オブジェクトが必要です");
    };
    for key in map.keys() {
        if !allowed.contains(&key.as_str()) {
            return schema(path, format!("未知のキー {key:?}"));
        }
    }
    Ok(map)
}

pub(crate) fn required<'a>(map: &'a Map<String, Value>, path: &str, key: &str) -> Res<&'a Value> {
    match map.get(key) {
        Some(v) => Ok(v),
        None => schema(path, format!("キー {key:?} が必要です")),
    }
}

pub(crate) fn array<'a>(v: &'a Value, path: &str) -> Res<&'a Vec<Value>> {
    match v.as_array() {
        Some(a) => Ok(a),
        None => schema(path, "配列が必要です"),
    }
}

pub(crate) fn optional_array<'a>(map: &'a Map<String, Value>, path: &str, key: &str) -> Res<&'a [Value]> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(&[]),
        Some(v) => Ok(array(v, &format!("{path}.{key}"))?),
    }
}

pub(crate) fn string(v: &Value, path: &str) -> Res<String> {
    match v.as_str() {
        Some(s) => Ok(s.to_string()),
        None => schema(path, "文字列が必要です"),
    }
}

pub(crate) fn int(v: &Value, path: &str) -> Res<i64> {
    match v.as_i64() {
        Some(i) if v.is_i64() || v.is_u64() => Ok(i),
        _ => schema(path, "符号付き64ビット整数が必要です"),
    }
}

pub(crate) fn index(v: &Value, path: &str) -> Res<usize> {
    match v.as_u64().and_then(|i| usize::try_from(i).ok()) {
        Some(i) => Ok(i),
        None => schema(path, "0以上の整数の添字が必要です"),
    }
}

pub(crate) fn unique(seen: &mut HashSet<String>, name: &str, path: &str, what: &str) -> Res<()> {
    if seen.insert(name.to_string()) {
        Ok(())
    } else {
        schema(path, format!("{what} {name:?} の定義が重複しています"))
    }
}

pub(crate) fn source(map: &Map<String, Value>, path: &str) -> Res<Option<Source>> {
    let Some(v) = map.get("source") else {
        return Ok(None);
    };
    if v.is_null() {
        return Ok(None);
    }
    let path = format!("{path}.source");
    let map = object(v, &path, &["file", "line"])?;
    let file = string(required(map, &path, "file")?, &format!("{path}.file"))?;
    let line = match required(map, &path, "line")?.as_u64() {
        Some(n) => n,
        None => return schema(&format!("{path}.line"), "0以上の整数が必要です"),
    };
    Ok(Some(Source { file, line }))
}

/// キーを1つだけ持つオブジェクトの、そのキーと値。
pub(crate) fn single<'a>(map: &'a Map<String, Value>, path: &str, message: &str) -> Res<(&'a String, &'a Value)> {
    match (map.iter().next(), map.len()) {
        (Some(entry), 1) => Ok(entry),
        _ => schema(path, message),
    }
}

pub(crate) fn operands<'a>(body: &'a Value, path: &str, n: usize) -> Res<&'a Vec<Value>> {
    let items = array(body, path)?;
    if items.len() != n {
        return schema(path, format!("オペランドは{n}個必要です（{}個あります）", items.len()));
    }
    Ok(items)
}
