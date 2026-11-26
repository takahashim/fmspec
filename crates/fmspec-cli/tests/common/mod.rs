//! テスト用のモデルと補助関数。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
#![allow(dead_code)]

use fmspec_core::evidence::{Claim, Evidence, TraceStep};
use fmspec_core::semantics::Conditions;
use fmspec_ir::{default_conditions, load, Model};
use fmspec_search::{check, check_evidence, BfsOptions, Outcome, Stats};
use serde_json::{json, Value};
use std::collections::{HashSet, VecDeque};

pub const MAX: i64 = i64::MAX;

pub fn model(ir: &Value) -> Model {
    match load(&ir.to_string()) {
        Ok(m) => m,
        Err(e) => panic!("モデルを読み込めません: {e}"),
    }
}

/// 仕様書 §4.1 のチケット例。
pub fn tickets() -> Value {
    json!({
        "ir_version": 1,
        "name": "tickets",
        "states": [{"id": 0, "name": "sold", "type": {"int": {"min": 0, "max": 4}}, "initial": {"int": 0}}],
        "actions": [
            {
                "name": "purchase",
                "params": [{"name": "quantity", "type": {"int": {"min": 1, "max": 2}}}],
                "choices": [],
                "guard": {"le": [{"add": [{"var": 0}, {"param": 0}]}, {"int": 3}]},
                "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"param": 0}]}}]
            },
            {
                "name": "cancel",
                "guard": {"gt": [{"var": 0}, {"int": 0}]},
                "updates": [{"target": 0, "expr": {"sub": [{"var": 0}, {"int": 1}]}}]
            }
        ],
        "invariants": [{"name": "capacity_respected", "expr": {"le": [{"var": 0}, {"int": 3}]}}]
    })
}

/// チケット例から購入の guard だけを削除したもの。
pub fn tickets_without_guard() -> Value {
    let mut ir = tickets();
    ir["actions"][0].as_object_mut().unwrap().remove("guard");
    ir
}

/// 1つの状態変数 `x`（`0..=max`、初期値0）を持つモデル。
pub fn counter(max: i64, actions: Value) -> Value {
    json!({
        "ir_version": 1,
        "name": "counter",
        "states": [{"name": "x", "type": {"int": {"min": 0, "max": max}}, "initial": {"int": 0}}],
        "actions": actions,
    })
}

pub fn stay() -> Value {
    json!({"name": "stay", "updates": [{"target": 0, "expr": {"var": 0}}]})
}

/// `x` が `from` のときだけ有効で、`x` を `to` にする操作。
pub fn go(name: &str, from: i64, to: i64) -> Value {
    json!({
        "name": name,
        "guard": {"eq": [{"var": 0}, {"int": from}]},
        "updates": [{"target": 0, "expr": {"int": to}}]
    })
}

/// i64 の最大値を持つ状態変数 `big` と、不変条件 `p` を持つモデル。
pub fn big(invariant: Value) -> Value {
    json!({
        "ir_version": 1,
        "name": "big",
        "states": [{"name": "big", "type": {"int": {"min": 0, "max": MAX}}, "initial": {"int": MAX}}],
        "invariants": [{"name": "p", "expr": invariant}]
    })
}

/// 「i64最大値を持つ状態変数に1を加え、その値が正か判定する」式。評価するとオーバーフローする。
pub fn overflowing() -> Value {
    json!({"gt": [{"add": [{"var": 0}, {"int": 1}]}, {"int": 0}]})
}

pub fn conditions(m: &Model, deadlock: bool) -> Conditions {
    default_conditions(m, deadlock)
}

pub fn run(m: &Model) -> Outcome {
    check(m.checked(), &conditions(m, false), &BfsOptions::default())
}

pub fn run_with(m: &Model, deadlock: bool, max_states: Option<usize>) -> Outcome {
    check(
        m.checked(),
        &conditions(m, deadlock),
        &BfsOptions {
            max_states,
            interrupt: None,
        },
    )
}

/// 不具合のある探索器。状態数が `limit` に達すると、新しい状態を黙って捨て、完走したものとして証明書を出す。
pub fn truncating_search(m: &Model, limit: usize) -> Evidence {
    let cond = conditions(m, false);
    let init = m.checked().initial();
    let mut visited: HashSet<Vec<i64>> = HashSet::from([init.clone()]);
    let mut queue = VecDeque::from([init]);
    while let Some(state) = queue.pop_front() {
        for a in 0..m.raw().actions.len() {
            let Some(fmspec_core::step::Enumerated::Ok(ts)) = m.checked().successors(a, &state) else {
                panic!("このテストのモデルでは評価エラーは起きない");
            };
            for t in ts {
                if visited.len() < limit && visited.insert(t.state.clone()) {
                    queue.push_back(t.state);
                }
            }
        }
    }
    let mut states: Vec<Vec<i64>> = visited.into_iter().collect();
    states.sort();
    Evidence::Certificate(fmspec_core::evidence::Certificate {
        conditions: cond,
        states,
    })
}

/// 不具合のある探索器。`forgetful` を探索して得た証拠を、そのまま `m` の証拠として判定ゲートに渡す。
/// `forgetful` は `m` の引数ドメインを狭めたモデルで、一部の遷移を列挙し忘れた探索器に相当する。
pub fn forgetful_search(m: &Model, forgetful: &Model) -> Outcome {
    let cond = conditions(m, false);
    let found = fmspec_search::bfs(forgetful.checked(), &cond, &BfsOptions::default());
    check_evidence(m.checked(), &cond, found.evidence, Stats::default())
}

pub fn trace(o: &Outcome) -> (&Vec<TraceStep>, &Claim) {
    match &o.evidence {
        Evidence::Trace(steps, claim) => (steps, claim),
        other => panic!("トレースではありません: {other:?}"),
    }
}

/// トレースの各ステップ後の、最初の状態変数の値。
pub fn first_values(steps: &[TraceStep]) -> Vec<i64> {
    steps.iter().map(|s| s.state[0]).collect()
}

pub fn certificate_states(o: &Outcome) -> Vec<Vec<i64>> {
    match &o.evidence {
        Evidence::Certificate(cert) => cert.states.clone(),
        other => panic!("証明書ではありません: {other:?}"),
    }
}
