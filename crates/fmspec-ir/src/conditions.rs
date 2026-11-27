//! 検査条件のJSON表現。対象の操作、不変条件、遷移契約を名前で並べる。

use crate::model::{Model, Names};
use fmspec_core::semantics::Conditions;
use serde_json::{json, Value};

/// すべての操作、不変条件、遷移契約を対象とする検査条件。
pub fn default_conditions(model: &Model, deadlock: bool) -> Conditions {
    Conditions {
        actions: vec![true; model.names.actions.len()],
        invariants: vec![true; model.names.invariants.len()],
        contracts: vec![true; model.names.contracts.len()],
        deadlock,
    }
}

fn selected<'a>(mask: &[bool], names: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    names
        .enumerate()
        .filter(|(i, _)| mask.get(*i).copied().unwrap_or(false))
        .map(|(_, n)| n)
        .collect()
}

pub fn conditions_to_json(names: &Names, c: &Conditions) -> Value {
    json!({
        "actions": selected(&c.actions, names.actions.iter().map(|a| a.name.as_str())),
        "invariants": selected(&c.invariants, names.invariants.iter().map(String::as_str)),
        "contracts": selected(&c.contracts, names.contracts.iter().map(String::as_str)),
        "deadlock": c.deadlock,
    })
}

fn mask(v: Option<&Value>, what: &str, len: usize, find: impl Fn(&str) -> Option<usize>) -> Result<Vec<bool>, String> {
    let items = v
        .and_then(Value::as_array)
        .ok_or_else(|| format!("conditions.{what} は名前の配列です"))?;
    let mut mask = vec![false; len];
    for item in items {
        let name = item
            .as_str()
            .ok_or_else(|| format!("conditions.{what} は名前の配列です"))?;
        let i = find(name).ok_or_else(|| format!("conditions.{what}: 未定義の名前 {name:?}"))?;
        mask[i] = true;
    }
    Ok(mask)
}

pub fn conditions_from_json(names: &Names, v: &Value) -> Result<Conditions, String> {
    let map = v.as_object().ok_or("conditions はオブジェクトです")?;
    for key in map.keys() {
        if !["actions", "invariants", "contracts", "deadlock"].contains(&key.as_str()) {
            return Err(format!("conditions: 未知のキー {key:?}"));
        }
    }
    Ok(Conditions {
        actions: mask(map.get("actions"), "actions", names.actions.len(), |n| {
            names.action_index(n)
        })?,
        invariants: mask(map.get("invariants"), "invariants", names.invariants.len(), |n| {
            names.invariant_index(n)
        })?,
        contracts: mask(map.get("contracts"), "contracts", names.contracts.len(), |n| {
            names.contract_index(n)
        })?,
        deadlock: map
            .get("deadlock")
            .and_then(Value::as_bool)
            .ok_or("conditions.deadlock は真偽値です")?,
    })
}
