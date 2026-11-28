//! 詳細化の検査の文書（docs/ir.md の「詳細化」）。
//!
//! 具体モデル、抽象モデル、写像を1つのJSONにまとめる。
//!
//! ```json
//! {"ir_version": 1, "name": "payments_refine_ledger",
//!  "concrete": {...}, "abstract": {...},
//!  "mapping": [{"state": "balance", "expr": {...}}]}
//! ```
//!
//! 写像は、抽象モデルの状態変数ごとに1つ、具体モデルの状態の上の式で書く。
//! 2つのモデルは列挙型を名前で共有する。同じ名前の列挙型はラベルも同じでなければならない。
//! 読み込むときは、両方のモデルの列挙型を、具体モデルの列挙型に抽象モデルにしかないものを続けた列に揃える。
//! これで、写像の値の列挙型の番号が、2つのモデルで一致する。

use crate::canonical;
use crate::json::{array, object, required, schema, string, Res};
use crate::model::{checked_model, parse_value, LoadError, MapSource, Model};
use crate::IR_VERSION;
use fmspec_core::kernel::model::Expr;
use serde_json::{Map, Value};
use std::collections::HashSet;

/// 読み込んだ詳細化の検査の文書。
pub struct Refinement {
    pub name: String,
    pub digest: String,
    /// 具体モデル。
    pub concrete: Model,
    /// 抽象モデル。
    pub abstract_model: Model,
    /// 写像。抽象モデルの状態のスロットごとの、具体モデルの状態の上の中核の式。
    pub mapping: Vec<Expr>,
}

fn enums_of<'a>(model: &'a Map<String, Value>, path: &str) -> Res<Vec<(&'a str, &'a Value)>> {
    let mut out = Vec::new();
    if let Some(list) = model.get("enums").filter(|v| !v.is_null()) {
        for (i, e) in array(list, &format!("{path}.enums"))?.iter().enumerate() {
            let p = format!("{path}.enums[{i}]");
            let obj = object(e, &p, &["name", "variants"])?;
            let name = required(obj, &p, "name")?.as_str().ok_or_else(|| LoadError::Schema {
                path: format!("{p}.name"),
                message: "文字列が必要です".to_string(),
            })?;
            out.push((name, required(obj, &p, "variants")?));
        }
    }
    Ok(out)
}

/// 2つのモデルの列挙型を揃えた列。
fn merged_enums(concrete: &Map<String, Value>, abs: &Map<String, Value>) -> Res<Vec<Value>> {
    let mut merged: Vec<(&str, &Value)> = enums_of(concrete, "$.concrete")?;
    for (name, variants) in enums_of(abs, "$.abstract")? {
        match merged.iter().find(|(n, _)| *n == name) {
            Some((_, v)) if *v == variants => {}
            Some(_) => {
                return schema(
                    "$.abstract.enums",
                    format!("列挙型 {name:?} のラベルが、具体モデルと抽象モデルで違います"),
                )
            }
            None => merged.push((name, variants)),
        }
    }
    Ok(merged
        .into_iter()
        .map(|(name, variants)| serde_json::json!({"name": name, "variants": variants}))
        .collect())
}

fn with_enums(model: &Map<String, Value>, enums: &[Value]) -> Value {
    let mut m = model.clone();
    m.insert("enums".to_string(), Value::Array(enums.to_vec()));
    Value::Object(m)
}

/// 詳細化の検査の文書を読み込む。2つのモデルは、それぞれ中核のIR検証を通す。
pub fn load_refinement(json: &str) -> Result<Refinement, LoadError> {
    let root: Value = serde_json::from_str(json).map_err(|e| LoadError::Json(e.to_string()))?;
    let map = object(&root, "$", &["ir_version", "name", "concrete", "abstract", "mapping"])?;
    let version = required(map, "$", "ir_version")?;
    if version.as_i64() != Some(IR_VERSION) {
        return schema(
            "$.ir_version",
            format!("未対応のIRバージョン {version}（対応しているのは {IR_VERSION}）"),
        );
    }
    let name = string(required(map, "$", "name")?, "$.name")?;
    let concrete = required(map, "$", "concrete")?
        .as_object()
        .ok_or_else(|| LoadError::Schema {
            path: "$.concrete".to_string(),
            message: "モデルのオブジェクトが必要です".to_string(),
        })?;
    let abs = required(map, "$", "abstract")?
        .as_object()
        .ok_or_else(|| LoadError::Schema {
            path: "$.abstract".to_string(),
            message: "モデルのオブジェクトが必要です".to_string(),
        })?;
    let enums = merged_enums(concrete, abs)?;
    let concrete_root = with_enums(concrete, &enums);
    let abs_root = with_enums(abs, &enums);

    let at = |path: &str, e: LoadError| match e {
        LoadError::Schema { path: p, message } => LoadError::Schema {
            path: p.replacen('$', path, 1),
            message,
        },
        e => e,
    };
    let (raw_a, names_a, _) = parse_value(&abs_root, &[]).map_err(|e| at("$.abstract", e))?;
    let abstract_model =
        checked_model(raw_a, names_a, canonical::digest(&abs_root)).map_err(|e| at("$.abstract", e))?;

    // 写像を、抽象モデルの状態変数の順に並べる。
    let abs_states = abs_root["states"].as_array().cloned().unwrap_or_default();
    let mut entries: Vec<Option<(usize, &Value)>> = vec![None; abs_states.len()];
    let mut seen = HashSet::new();
    for (i, item) in array(required(map, "$", "mapping")?, "$.mapping")?.iter().enumerate() {
        let path = format!("$.mapping[{i}]");
        let m = object(item, &path, &["state", "expr"])?;
        let state = string(required(m, &path, "state")?, &format!("{path}.state"))?;
        let Some(j) = abstract_model.names.state_index(&state) else {
            return schema(
                &format!("{path}.state"),
                format!("抽象モデルに状態変数 {state:?} はありません"),
            );
        };
        if !seen.insert(state.clone()) {
            return schema(
                &format!("{path}.state"),
                format!("状態変数 {state:?} の写像が重複しています"),
            );
        }
        entries[j] = Some((i, required(m, &path, "expr")?));
    }
    let mut maps = Vec::new();
    for (j, entry) in entries.iter().enumerate() {
        let Some((i, expr)) = entry else {
            return schema(
                "$.mapping",
                format!(
                    "抽象モデルの状態変数 {:?} の写像がありません",
                    abstract_model.names.states[j]
                ),
            );
        };
        maps.push(MapSource {
            path: format!("$.mapping[{i}].expr"),
            expr,
            ty: &abs_states[j]["type"],
        });
    }
    let (raw_b, names_b, mapping) = parse_value(&concrete_root, &maps).map_err(|e| match e {
        LoadError::Schema { ref path, .. } if path.starts_with("$.mapping") => e,
        e => at("$.concrete", e),
    })?;
    let concrete_model =
        checked_model(raw_b, names_b, canonical::digest(&concrete_root)).map_err(|e| at("$.concrete", e))?;
    Ok(Refinement {
        name,
        digest: canonical::digest(&root),
        concrete: concrete_model,
        abstract_model,
        mapping,
    })
}
