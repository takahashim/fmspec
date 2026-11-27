//! 探索の深さと時間の上限（仕様書 §8.1、§8.3）。
//!
//! 上限で打ち切った探索は証明書を出さず、`Inconclusive` になる。上限の内側で見つけた違反と評価エラーは報告する。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod common;

use common::*;
use fmspec_core::evidence::{Claim, Evidence, Limit};
use fmspec_core::gate::VerdictKind;
use fmspec_ir::Model;
use fmspec_search::{check, sample, BfsOptions, Outcome, SimOptions, Status};
use serde_json::json;
use std::time::{Duration, Instant};

fn with_depth(m: &Model, deadlock: bool, max_depth: usize) -> Outcome {
    let opts = BfsOptions {
        max_depth: Some(max_depth),
        ..BfsOptions::default()
    };
    check(m.checked(), &conditions(m, deadlock), &opts)
}

fn depth_limited(o: &Outcome) {
    assert_eq!(o.status, Status::Inconclusive(Limit::MaxDepth));
    assert_eq!(o.verdict.kind(), VerdictKind::Inconclusive);
    assert!(matches!(o.evidence, Evidence::Unavailable(Limit::MaxDepth)));
    assert!(!o.stats.complete);
}

#[test]
fn a_search_within_the_depth_is_verified_and_one_level_short_is_not() {
    // チケット例の到達状態は 0、1、2（深さ1）、3（深さ2）。深さ2の状態3からの遷移は、訪問済みの2に戻る。
    let m = model(&tickets());
    let o = with_depth(&m, false, 2);
    assert_eq!(o.status, Status::Verified);
    assert_eq!(certificate_states(&o), vec![vec![0], vec![1], vec![2], vec![3]]);
    assert!(o.stats.complete);

    // 深さ1では、状態1から未訪問の状態3への遷移が残る。訪問した状態だけの証明書は出さない。
    let o = with_depth(&m, false, 1);
    depth_limited(&o);
    assert_eq!(o.stats.visited_states, 3);

    // 上限なしの結果は、十分な深さの上限の結果と同じである。
    assert_eq!(run(&m).status, Status::Verified);
}

#[test]
fn depth_zero_checks_only_the_initial_states() {
    let m = model(&counter(1, json!([stay()])));
    assert_eq!(with_depth(&m, false, 0).status, Status::Verified);

    let m = model(&counter(1, json!([stay(), go("go", 0, 1)])));
    let o = with_depth(&m, false, 0);
    depth_limited(&o);
    assert_eq!(o.stats.visited_states, 1);
}

#[test]
fn a_violation_within_the_depth_is_reported() {
    // 購入の guard がなければ、2回の購入（深さ2）で不変条件に違反する。
    let m = model(&tickets_without_guard());
    let o = with_depth(&m, false, 2);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Invariant(0));
    assert_eq!(steps.len(), 2);

    // 違反の状態が上限より深ければ、訪問しないので報告しない。
    depth_limited(&with_depth(&m, false, 1));
}

#[test]
fn a_contract_violation_beyond_the_depth_is_not_reported() {
    let mut ir = counter(1, json!([go("go", 0, 1)]));
    ir["contracts"] = json!([{"name": "never", "action": "go", "expr": {"bool": false}}]);
    let m = model(&ir);
    // 深さ0の状態からの遷移の違反は、1ステップのトレースになり、上限を超える。
    depth_limited(&with_depth(&m, false, 0));

    let o = with_depth(&m, false, 1);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Contract(0));
    assert_eq!(steps.len(), 1);
}

#[test]
fn a_deadlock_and_an_error_at_the_depth_are_reported() {
    // 状態1（深さ1）は有効な遷移を持たない。トレースは1ステップで、上限の内側である。
    let m = model(&counter(1, json!([go("go", 0, 1)])));
    let o = with_depth(&m, true, 1);
    assert_eq!(o.status, Status::Violated);
    let (steps, claim) = trace(&o);
    assert_eq!(*claim, Claim::Deadlock);
    assert_eq!(steps.len(), 1);
    depth_limited(&with_depth(&m, true, 0));

    // 初期状態での更新の評価エラーは、0ステップのトレースで報告する。
    let mut ir = tickets();
    ir["actions"][0]["updates"][0]["expr"] = json!({"int": 5});
    let o = with_depth(&model(&ir), false, 0);
    assert_eq!(o.status, Status::Error);
    assert!(trace(&o).0.is_empty());
}

#[test]
fn the_depth_and_the_state_limits_are_told_apart() {
    let m = model(&tickets());
    // 深さの上限で打ち切る遷移は、状態を保持しないので、状態数の上限に数えない。
    let opts = BfsOptions {
        max_depth: Some(1),
        max_states: Some(3),
        ..BfsOptions::default()
    };
    assert_eq!(
        check(m.checked(), &conditions(&m, false), &opts).status,
        Status::Inconclusive(Limit::MaxDepth)
    );
    let opts = BfsOptions {
        max_depth: Some(2),
        max_states: Some(3),
        ..BfsOptions::default()
    };
    assert_eq!(
        check(m.checked(), &conditions(&m, false), &opts).status,
        Status::Inconclusive(Limit::MaxStates)
    );
}

#[test]
fn a_passed_deadline_stops_the_search_and_is_not_an_interrupt() {
    let m = model(&tickets());
    let opts = BfsOptions {
        deadline: Some(Instant::now()),
        ..BfsOptions::default()
    };
    let o = check(m.checked(), &conditions(&m, false), &opts);
    assert_eq!(o.status, Status::Inconclusive(Limit::MaxTime));
    assert!(matches!(o.evidence, Evidence::Unavailable(Limit::MaxTime)));
    assert!(!o.stats.complete);

    // 中断要求もあれば、中断を理由にする。
    let opts = BfsOptions {
        deadline: Some(Instant::now()),
        interrupt: Some(&|| true),
        ..BfsOptions::default()
    };
    let o = check(m.checked(), &conditions(&m, false), &opts);
    assert_eq!(o.status, Status::Inconclusive(Limit::Interrupted));

    // 期限が先なら、完走して判定ゲートが証明書を受理する。
    let opts = BfsOptions {
        deadline: Instant::now().checked_add(Duration::from_secs(3600)),
        ..BfsOptions::default()
    };
    assert_eq!(
        check(m.checked(), &conditions(&m, false), &opts).status,
        Status::Verified
    );
}

#[test]
fn a_violation_in_the_initial_state_is_found_before_the_deadline_is_checked() {
    let m = model(&big(overflowing()));
    let opts = BfsOptions {
        deadline: Some(Instant::now()),
        ..BfsOptions::default()
    };
    assert_eq!(check(m.checked(), &conditions(&m, false), &opts).status, Status::Error);
}

#[test]
fn a_passed_deadline_stops_the_simulation() {
    let m = model(&tickets());
    let opts = SimOptions {
        seed: 0,
        traces: 10,
        max_steps: 10,
        interrupt: None,
        deadline: Some(Instant::now()),
    };
    let sampled = sample(m.checked(), &conditions(&m, false), &opts);
    let o = sampled.found.unwrap();
    assert_eq!(o.status, Status::Inconclusive(Limit::MaxTime));
    assert_eq!(sampled.stats.traces, 0);
}
