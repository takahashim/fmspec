//! オプションのJSONの読み取り。誤りは利用者に向けた文で `Err` にする。
//!
//! オプションのJSONを、探索器と判定ゲートのオプション（`BfsOptions`、`GateOptions`）にする変換もここに置く。

use crate::Interrupt;
use fmspec_core::kernel::semantics::Conditions;
use fmspec_ir::{default_conditions, Model};
use fmspec_search::{BfsOptions, GateOptions};
use serde_json::{Map, Value};
use std::time::{Duration, Instant};

/// 検査条件のキー。検査条件を受け取る関数は、これらを常に受け付ける。
const CONDITION_KEYS: [&str; 4] = ["actions", "invariants", "contracts", "deadlock"];

/// オブジェクトを取り出す。`accepts` が受け付けないキーがあれば `Err`。
/// `not_object` はオブジェクトでないときの文、`unknown` は受け付けないキーの文を作る。
fn object<'a>(
    v: &'a Value,
    accepts: impl Fn(&str) -> bool,
    not_object: &str,
    unknown: impl Fn(&str) -> String,
) -> Result<&'a Map<String, Value>, String> {
    let map = v.as_object().ok_or(not_object)?;
    match map.keys().find(|k| !accepts(k)) {
        Some(key) => Err(unknown(key)),
        None => Ok(map),
    }
}

/// `allowed` のキーだけを受け付けるオプションのオブジェクトを取り出す。
/// 検査条件の一部しか使わない関数は、使う検査条件のキーだけを `allowed` に含めて、使わないキーを拒否する。
/// 含めなかった検査条件は、`conditions` の既定（すべてが対象で、デッドロック検査は無効）になる。
pub(crate) fn options_only<'a>(v: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    object(
        v,
        |k| allowed.contains(&k),
        "オプションはオブジェクトです",
        |key| format!("未知のオプション {key:?}"),
    )
}

/// 検査条件のキーすべてと、`allowed` のキーを受け付けるオプションのオブジェクトを取り出す。
pub(crate) fn options_with_conditions<'a>(v: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    options_only(v, &[&CONDITION_KEYS[..], allowed].concat())
}

/// オプションの中の、`name` という名前のオブジェクトを取り出す。`allowed` のキーだけを受け付ける。
pub(crate) fn nested_object<'a>(v: &'a Value, name: &str, allowed: &[&str]) -> Result<&'a Map<String, Value>, String> {
    object(
        v,
        |k| allowed.contains(&k),
        &format!("{name} はオブジェクトです"),
        |key| format!("{name} の未知のキー {key:?}"),
    )
}

/// 名前の配列を、`find` で添字の列（指定の順で、重複を除く）にする。
/// `not_names` は配列でないか、名前でない要素があるときの文。未定義の名前の文は `what`（「操作」など）で始める。
pub(crate) fn indices(
    wanted: &Value,
    what: &str,
    not_names: impl Fn() -> String,
    find: impl Fn(&str) -> Option<usize>,
) -> Result<Vec<usize>, String> {
    let mut out = Vec::new();
    for name in wanted.as_array().ok_or_else(&not_names)? {
        let name = name.as_str().ok_or_else(&not_names)?;
        let i = find(name).ok_or_else(|| format!("未定義の{what} {name:?}"))?;
        if !out.contains(&i) {
            out.push(i);
        }
    }
    Ok(out)
}

/// 名前の配列の指定で、`mask` の対象を選ぶ。省略または `null` なら `mask` を変えない。
/// 誤りの文は `what`（「操作」など）で始め、型の誤りには指定の値を添える。
pub(crate) fn select(
    mask: &mut [bool],
    wanted: Option<&Value>,
    what: &str,
    find: impl Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let Some(wanted) = wanted.filter(|v| !v.is_null()) else {
        return Ok(());
    };
    let chosen = indices(
        wanted,
        what,
        || format!("{what}の指定は名前の配列です（{wanted}）"),
        find,
    )?;
    mask.fill(false);
    for i in chosen {
        mask[i] = true;
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

/// 時間の上限 `max_time_ms`（0以上のミリ秒）を、呼び出した時刻からの期限にする。
/// 時刻として表せないほど大きな値は、上限なしとする。
pub(crate) fn deadline(map: &Map<String, Value>) -> Result<Option<Instant>, String> {
    Ok(count(map, "max_time_ms", 0)?.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms))))
}

/// 真偽値のオプション。省略または `null` なら `None`。
pub(crate) fn optional_flag(map: &Map<String, Value>, key: &str) -> Result<Option<bool>, String> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::Bool(b)) => Ok(Some(*b)),
        Some(v) => Err(format!("{key} は真偽値です（{v}）")),
    }
}

/// 真偽値のオプション。省略または `null` なら偽。
pub(crate) fn flag(map: &Map<String, Value>, key: &str) -> Result<bool, String> {
    Ok(optional_flag(map, key)?.unwrap_or(false))
}

/// 幅優先探索のオプション。`max_states`、`max_depth`、`max_time_ms` を読む。
/// 判定ゲートの評価回数の上限は、呼び出し側が受け付けるかを決めるので、読んだ値を `max_check_cost` で渡す。
pub(crate) fn bfs_options<'a>(
    map: &Map<String, Value>,
    interrupt: Interrupt<'a>,
    max_check_cost: Option<u64>,
) -> Result<BfsOptions<'a>, String> {
    Ok(BfsOptions {
        max_states: max_states(map)?,
        interrupt,
        max_check_cost,
        max_depth: count(map, "max_depth", 0)?.map(size),
        deadline: deadline(map)?,
    })
}

/// 判定ゲートのオプション。`max_check_cost` を読む。
pub(crate) fn gate_options<'a>(
    map: &Map<String, Value>,
    interrupt: Interrupt<'a>,
    deadline: Option<Instant>,
) -> Result<GateOptions<'a>, String> {
    Ok(GateOptions {
        max_cost: count(map, "max_check_cost", 0)?,
        interrupt,
        deadline,
    })
}

/// トレースの検査の判定ゲートのオプション。トレースの検査は区切らないので、中断要求と時間の上限は渡さない。
pub(crate) fn trace_gate_options(map: &Map<String, Value>) -> Result<GateOptions<'static>, String> {
    gate_options(map, None, None)
}
