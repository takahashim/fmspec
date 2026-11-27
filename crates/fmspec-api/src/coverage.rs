//! Model-Based Testing のカバレッジと、テスト経路の生成（仕様書 §11.3）。
//!
//! どちらも、到達可能な状態と遷移のグラフ（`fmspec_search::explore`）を分母にする。
//! モデルの検査ではないので、判定ゲートを通さず、`Verified` などの判定も返さない。

use crate::inject::{inject_slots, input_json, parse_inject};
use crate::options::{conditions, count, max_states, options, size};
use crate::report::inconsistency_report;
use crate::Interrupt;
use fmspec_ir::{args_to_json, state_to_json, Model};
use fmspec_search::{explore, test_paths as search_paths};
use serde_json::{json, Value};
use std::collections::HashSet;

/// 報告に含める、覆っていない遷移の数の上限。
const MAX_UNCOVERED: usize = 20;

/// 経路の最大入力数の既定値。
const DEFAULT_MAX_STEPS: u64 = 20;

fn codes(v: &Value, what: &str) -> Result<Vec<i64>, String> {
    v.as_array()
        .and_then(|xs| xs.iter().map(Value::as_i64).collect::<Option<Vec<i64>>>())
        .ok_or_else(|| format!("{what}は整数の配列です"))
}

/// 遷移の符号（遷移元の状態、操作、引数）。
type TransitionCode = (Vec<i64>, usize, Vec<i64>);

/// `seen` オプションを、状態の符号の集合と遷移の符号の列にする。
fn parse_seen(v: Option<&Value>) -> Result<(HashSet<Vec<i64>>, Vec<TransitionCode>), String> {
    let empty = serde_json::Map::new();
    let seen = match v {
        None | Some(Value::Null) => &empty,
        Some(v) => v.as_object().ok_or("seen はオブジェクトです")?,
    };
    if let Some(key) = seen.keys().find(|k| !["states", "transitions"].contains(&k.as_str())) {
        return Err(format!("seen の未知のキー {key:?}"));
    }
    let list = |key: &str| -> Result<&[Value], String> {
        match seen.get(key) {
            None | Some(Value::Null) => Ok(&[]),
            Some(v) => v
                .as_array()
                .map(Vec::as_slice)
                .ok_or_else(|| format!("seen の {key} は配列です")),
        }
    };
    let mut states = HashSet::new();
    for s in list("states")? {
        states.insert(codes(s, "seen の状態")?);
    }
    let mut transitions = Vec::new();
    for t in list("transitions")? {
        let parts = t
            .as_array()
            .filter(|p| p.len() == 3)
            .ok_or("seen の遷移は [状態, 操作, 引数] です")?;
        let action = parts[1]
            .as_u64()
            .and_then(|a| usize::try_from(a).ok())
            .ok_or("seen の遷移の操作は添字です")?;
        transitions.push((
            codes(&parts[0], "seen の状態")?,
            action,
            codes(&parts[2], "seen の引数")?,
        ));
    }
    Ok((states, transitions))
}

/// テストで確実に通った状態と遷移（セッションの応答の `covered`）を、到達可能な状態と遷移と比べる。
///
/// オプションは、検査条件、`max_states`、`seen`（`{"states": [状態の符号], "transitions": [[状態の符号, 操作, 引数の符号]]}`）。
pub fn coverage(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["max_states", "seen"])?;
    let cond = conditions(model, map)?;
    let (states, seen_transitions) = parse_seen(map.get("seen"))?;
    let transitions: HashSet<(&[i64], usize, &[i64])> = seen_transitions
        .iter()
        .map(|(s, a, x)| (s.as_slice(), *a, x.as_slice()))
        .collect();

    let g = explore(model.checked(), &cond, max_states(map)?, interrupt);
    // 探索器の内部の不整合で集めきれなかったグラフは、分母にしない。
    if let Some(inconsistency) = &g.inconsistency {
        return Ok(inconsistency_report(model, inconsistency));
    }
    let covered_states = g.states.iter().filter(|s| states.contains(*s)).count();
    let n_actions = model.names.actions.len();
    let mut per_action = vec![(0usize, 0usize); n_actions];
    let mut uncovered = Vec::new();
    let mut n_uncovered = 0;
    for e in &g.edges {
        let key = (g.states[e.from].as_slice(), e.action, e.args.as_slice());
        per_action[e.action].0 += 1;
        if transitions.contains(&key) {
            per_action[e.action].1 += 1;
        } else {
            n_uncovered += 1;
            if uncovered.len() < MAX_UNCOVERED {
                let (args, choices) = args_to_json(model, e.action, &e.args);
                uncovered.push(json!({
                    "state": state_to_json(model, &g.states[e.from]),
                    "action": model.names.actions[e.action].name,
                    "args": args,
                    "choices": choices,
                }));
            }
        }
    }
    let actions: Vec<Value> = (0..n_actions)
        .filter(|a| cond.actions.get(*a).copied().unwrap_or(false))
        .map(|a| {
            json!({
                "name": model.names.actions[a].name,
                "reachable": per_action[a].0,
                "covered": per_action[a].1,
            })
        })
        .collect();
    let covered_transitions: usize = per_action.iter().map(|(_, c)| c).sum();
    Ok(json!({
        "status": "ok",
        "complete": g.complete,
        "states": {"reachable": g.states.len(), "covered": covered_states},
        "transitions": {"reachable": g.edges.len(), "covered": covered_transitions},
        "actions": actions,
        "uncovered": uncovered,
        "uncovered_count": n_uncovered,
    }))
}

/// 到達可能な状態と入力の組を覆うテスト経路を作る。
///
/// オプションは、検査条件、`max_states`、`max_steps`（1経路の最大入力数、既定は20）、
/// `inject`（セッションと同じ、注入する内部選択）。
pub fn test_paths(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options(opts, &["max_states", "max_steps", "inject"])?;
    let cond = conditions(model, map)?;
    let max_steps = size(count(map, "max_steps", 1)?.unwrap_or(DEFAULT_MAX_STEPS));
    let injected = parse_inject(model, map.get("inject"))?;
    let slots = inject_slots(model, &injected);
    let found = search_paths(model.checked(), &cond, &slots, max_states(map)?, max_steps, interrupt);
    if let Some(inconsistency) = &found.graph.inconsistency {
        return Ok(inconsistency_report(model, inconsistency));
    }
    let paths: Vec<Value> = found
        .paths
        .iter()
        .map(|p| {
            let inputs: Vec<Value> = p
                .inputs
                .iter()
                .map(|(a, x)| input_json(model, &injected, *a, x))
                .collect();
            json!({"start": state_to_json(model, &found.graph.states[p.start]), "inputs": inputs})
        })
        .collect();
    Ok(json!({
        "status": "ok",
        "complete": found.graph.complete,
        "targets": found.targets,
        "covered": found.covered,
        "paths": paths,
    }))
}
