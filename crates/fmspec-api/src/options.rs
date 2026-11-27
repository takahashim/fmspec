//! オプションのJSONの読み取り。誤りは利用者に向けた文で `Err` にする。

use fmspec_core::semantics::Conditions;
use fmspec_ir::{default_conditions, Model};
use serde_json::{Map, Value};

/// 検査条件のキー。検査条件を受け取る関数は、これらを常に受け付ける。
const CONDITION_KEYS: [&str; 4] = ["actions", "invariants", "contracts", "deadlock"];

/// オプションのオブジェクトを取り出す。`accepts` が受け付けないキーがあれば `Err`。
fn object(v: &Value, accepts: impl Fn(&str) -> bool) -> Result<&Map<String, Value>, String> {
    let map = v.as_object().ok_or("オプションはオブジェクトです")?;
    match map.keys().find(|k| !accepts(k)) {
        Some(key) => Err(format!("未知のオプション {key:?}")),
        None => Ok(map),
    }
}

/// `allowed` のキーだけを受け付けるオプションのオブジェクトを取り出す。
pub(crate) fn keys<'a>(v: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    object(v, |k| allowed.contains(&k))
}

/// 検査条件と `allowed` のキーを受け付けるオプションのオブジェクトを取り出す。
pub(crate) fn options<'a>(v: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    object(v, |k| CONDITION_KEYS.contains(&k) || allowed.contains(&k))
}

fn select(
    mask: &mut [bool],
    wanted: Option<&Value>,
    what: &str,
    find: impl Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let Some(wanted) = wanted.filter(|v| !v.is_null()) else {
        return Ok(());
    };
    let not_names = || format!("{what}の指定は名前の配列です");
    let names = wanted.as_array().ok_or_else(not_names)?;
    mask.fill(false);
    for name in names {
        let name = name.as_str().ok_or_else(not_names)?;
        match find(name) {
            Some(i) => mask[i] = true,
            None => return Err(format!("未定義の{what} {name:?}")),
        }
    }
    Ok(())
}

/// オプションから検査条件を作る。省略した項目は、すべてが対象で、デッドロック検査は無効。
pub(crate) fn conditions(model: &Model, map: &Map<String, Value>) -> Result<Conditions, String> {
    let mut c = default_conditions(model, flag(map, "deadlock")?);
    select(&mut c.actions, map.get("actions"), "操作", |n| {
        model.names.action_index(n)
    })?;
    select(&mut c.invariants, map.get("invariants"), "不変条件", |n| {
        model.names.invariant_index(n)
    })?;
    model.names.spread_invariants(&mut c.invariants);
    select(&mut c.contracts, map.get("contracts"), "遷移契約", |n| {
        model.names.contract_index(n)
    })?;
    Ok(c)
}

/// `min` 以上の整数のオプション。省略または `null` なら `None`。
pub(crate) fn count(map: &Map<String, Value>, key: &str, min: u64) -> Result<Option<u64>, String> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(v) => match v.as_u64() {
            Some(n) if n >= min => Ok(Some(n)),
            _ => Err(format!("{key} は{min}以上の整数です（{v}）")),
        },
    }
}

/// `count` の値を `usize` にする。収まらない値は `usize::MAX` に丸める（上限として使うので意味は変わらない）。
pub(crate) fn size(n: u64) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

/// 状態数の上限 `max_states`（1以上）。
pub(crate) fn max_states(map: &Map<String, Value>) -> Result<Option<usize>, String> {
    Ok(count(map, "max_states", 1)?.map(size))
}

/// 真偽値のオプション。省略または `null` なら偽。
pub(crate) fn flag(map: &Map<String, Value>, key: &str) -> Result<bool, String> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(false),
        Some(Value::Bool(b)) => Ok(*b),
        Some(_) => Err(format!("{key} は真偽値です")),
    }
}
