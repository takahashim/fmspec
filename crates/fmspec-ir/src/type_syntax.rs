//! IRの型の構文の読み取りと、型の名前。

use crate::json::{array, int, object, required, schema, single, string, unique, Res};
use crate::model::EnumNames;
use crate::types::{SType, XType, MAX_KEYS, MAX_LIST, MAX_WIDTH};
use serde_json::Value;
use std::collections::HashSet;

fn int_range(v: &Value, path: &str) -> Res<(i64, i64)> {
    let range = object(v, path, &["min", "max"])?;
    let min = int(required(range, path, "min")?, &format!("{path}.min"))?;
    let max = int(required(range, path, "max")?, &format!("{path}.max"))?;
    Ok((min, max))
}

fn enum_id(enums: &[EnumNames], v: &Value, path: &str) -> Res<usize> {
    let name = string(v, path)?;
    match enums.iter().position(|e| e.name == name) {
        Some(id) => Ok(id),
        None => schema(path, format!("未定義の列挙型 {name:?}")),
    }
}

/// 型を読む。Setの要素とMapのキーは、値の数が `MAX_KEYS` 以下の、Set、Map、Listを含まない型に限る。
pub(crate) fn parse_type(v: &Value, path: &str, enums: &[EnumNames]) -> Res<SType> {
    let ty = parse_type_inner(v, path, enums)?;
    if ty.width(enums) > MAX_WIDTH {
        return schema(path, format!("型のスロット数が上限 {MAX_WIDTH} を超えます"));
    }
    Ok(ty)
}

fn parse_type_inner(v: &Value, path: &str, enums: &[EnumNames]) -> Res<SType> {
    let map = object(
        v,
        path,
        &["bool", "int", "enum", "tuple", "record", "option", "set", "map", "list"],
    )?;
    let (key, body) = single(
        map,
        path,
        "型は bool、int、enum、tuple、record、option、set、map、list のいずれか1つのキーを持つオブジェクトです",
    )?;
    let path = format!("{path}.{key}");
    let keyable = |t: &SType, what: &str| -> Res<()> {
        if t.keys(enums).is_none() {
            return schema(
                &path,
                format!("{what}の型は、値の数が {MAX_KEYS} 以下で、set、map、list を含まない型に限ります"),
            );
        }
        Ok(())
    };
    match key.as_str() {
        "bool" => {
            object(body, &path, &[])?;
            Ok(SType::Bool)
        }
        "int" => {
            let (min, max) = int_range(body, &path)?;
            Ok(SType::Int(min, max))
        }
        "enum" => Ok(SType::Enum(enum_id(enums, body, &path)?)),
        "tuple" => {
            let items = array(body, &path)?;
            if items.is_empty() {
                return schema(&path, "tuple は1つ以上の要素を持ちます");
            }
            let ts = items
                .iter()
                .enumerate()
                .map(|(i, t)| parse_type_inner(t, &format!("{path}[{i}]"), enums))
                .collect::<Res<Vec<_>>>()?;
            Ok(SType::Tuple(ts))
        }
        "record" => {
            let items = array(body, &path)?;
            if items.is_empty() {
                return schema(&path, "record は1つ以上のフィールドを持ちます");
            }
            let mut seen = HashSet::new();
            let mut fields = Vec::new();
            for (i, item) in items.iter().enumerate() {
                let path = format!("{path}[{i}]");
                let f = object(item, &path, &["name", "type"])?;
                let name = string(required(f, &path, "name")?, &format!("{path}.name"))?;
                unique(&mut seen, &name, &path, "フィールド")?;
                fields.push((
                    name,
                    parse_type_inner(required(f, &path, "type")?, &format!("{path}.type"), enums)?,
                ));
            }
            Ok(SType::Record(fields))
        }
        "option" => Ok(SType::Option(Box::new(parse_type_inner(body, &path, enums)?))),
        "set" => {
            let t = parse_type_inner(body, &path, enums)?;
            keyable(&t, "set の要素")?;
            Ok(SType::Set(Box::new(t)))
        }
        "map" => {
            let m = object(body, &path, &["key", "value"])?;
            let k = parse_type_inner(required(m, &path, "key")?, &format!("{path}.key"), enums)?;
            keyable(&k, "map のキー")?;
            let v = parse_type_inner(required(m, &path, "value")?, &format!("{path}.value"), enums)?;
            Ok(SType::Map(Box::new(k), Box::new(v)))
        }
        _ => {
            let m = object(body, &path, &["of", "max"])?;
            let t = parse_type_inner(required(m, &path, "of")?, &format!("{path}.of"), enums)?;
            let max = match required(m, &path, "max")?.as_u64() {
                Some(n) if n as usize <= MAX_LIST => n as usize,
                _ => return schema(&format!("{path}.max"), format!("0以上 {MAX_LIST} 以下の整数が必要です")),
            };
            Ok(SType::List(Box::new(t), max))
        }
    }
}

pub(crate) fn type_name(enums: &[EnumNames], t: &XType) -> String {
    match t {
        XType::Bool => "bool".to_string(),
        XType::Int => "int".to_string(),
        XType::Enum(id) => format!("enum {}", enums.get(*id).map(|e| e.name.as_str()).unwrap_or("?")),
        XType::Tuple(ts) => format!(
            "tuple({})",
            ts.iter().map(|t| type_name(enums, t)).collect::<Vec<_>>().join(", ")
        ),
        XType::Record(fs) => format!(
            "record({})",
            fs.iter()
                .map(|(n, t)| format!("{n}: {}", type_name(enums, t)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        XType::Option(t) => format!("option({})", type_name(enums, t)),
        XType::Set(t) => format!("set({})", type_name(enums, &t.xtype())),
        XType::Map(k, v) => format!(
            "map({}, {})",
            type_name(enums, &k.xtype()),
            type_name(enums, &v.xtype())
        ),
        XType::List(t, n) => format!("list({}, max {n})", type_name(enums, &t.xtype())),
    }
}
