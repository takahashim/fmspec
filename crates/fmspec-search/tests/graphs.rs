//! 手作りの有限グラフでの探索の検査（仕様書 §14 の表、§14.1.1）。
//!
//! 探索器は証明の対象外なので、訪問状態、最短性、上限の扱いをここで検査する。
//! 比較の相手は、辺の一覧を直接たどる独立した全列挙である。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_core::evidence::{Claim, Evidence, Limit};
use fmspec_core::gate::{validate, CheckedModel};
use fmspec_core::model::{Action, BinOp, Contract, Expr, RawModel, Type, Update, Value};
use fmspec_core::semantics::Conditions;
use fmspec_search::{check, BfsOptions, Outcome, Status};
use std::collections::{BTreeSet, VecDeque};

fn int(x: i64) -> Expr {
    Expr::Const(Value::Int(x))
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Bin(BinOp::Eq, Box::new(a), Box::new(b))
}

/// 頂点 `0..n` と辺の一覧を持つグラフを、1つの状態変数 `x` のモデルにする。
/// 辺ごとに操作を1つ作り、不変条件は「`x` は `bad` のどれでもない」とする。
fn graph(n: i64, edges: &[(i64, i64)], bad: &[i64]) -> CheckedModel {
    let actions = edges
        .iter()
        .map(|(from, to)| Action {
            n_params: 0,
            domains: vec![],
            guard: eq(Expr::Var(0), int(*from)),
            updates: vec![Update {
                target: 0,
                expr: int(*to),
            }],
            output: None,
        })
        .collect();
    let invariants = bad
        .iter()
        .map(|b| Expr::Bin(BinOp::Ne, Box::new(Expr::Var(0)), Box::new(int(*b))))
        .collect();
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, n - 1)],
        init: vec![0],
        actions,
        invariants,
        contracts: vec![],
        terminal: None,
    };
    validate(raw).expect("整形式のモデル")
}

fn conditions(m: &CheckedModel, deadlock: bool) -> Conditions {
    Conditions {
        actions: vec![true; m.raw().actions.len()],
        invariants: vec![true; m.raw().invariants.len()],
        contracts: vec![true; m.raw().contracts.len()],
        deadlock,
    }
}

fn run(m: &CheckedModel, deadlock: bool, max_states: Option<usize>) -> Outcome {
    check(
        m,
        &conditions(m, deadlock),
        &BfsOptions {
            max_states,
            interrupt: None,
        },
    )
}

/// 辺の一覧を直接たどって、頂点0からの最短距離を求める。
fn distances(n: i64, edges: &[(i64, i64)]) -> Vec<Option<usize>> {
    let mut dist = vec![None; n as usize];
    dist[0] = Some(0);
    let mut queue = VecDeque::from([0i64]);
    while let Some(u) = queue.pop_front() {
        for (from, to) in edges {
            if *from == u && dist[*to as usize].is_none() {
                dist[*to as usize] = dist[u as usize].map(|d| d + 1);
                queue.push_back(*to);
            }
        }
    }
    dist
}

/// 決まった種から作る、小さな擬似乱数のグラフ。
fn random_graph(seed: u64, n: i64, m: usize) -> Vec<(i64, i64)> {
    let mut x = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        (x % n as u64) as i64
    };
    (0..m).map(|_| (next(), next())).collect()
}

#[test]
fn visited_states_match_an_independent_enumeration() {
    for seed in 0..200 {
        let n = 2 + (seed % 9) as i64;
        let edges = random_graph(seed, n, (seed % 14) as usize);
        let m = graph(n, &edges, &[]);
        let o = run(&m, false, None);
        assert_eq!(o.status, Status::Verified, "seed {seed}");
        let expected: BTreeSet<i64> = distances(n, &edges)
            .iter()
            .enumerate()
            .filter(|(_, d)| d.is_some())
            .map(|(v, _)| v as i64)
            .collect();
        let Evidence::Certificate(cert) = &o.evidence else {
            panic!("seed {seed}")
        };
        let visited: BTreeSet<i64> = cert.states.iter().map(|s| s[0]).collect();
        assert_eq!(visited, expected, "seed {seed}");
        assert_eq!(o.stats.visited_states, expected.len(), "seed {seed}");
        // 検査した遷移の数は、到達できる頂点から出る辺の数に等しい。
        let reachable_edges = edges.iter().filter(|(from, _)| expected.contains(from)).count();
        assert_eq!(o.stats.transitions, reachable_edges, "seed {seed}");
    }
}

#[test]
fn counterexamples_to_state_invariants_are_shortest() {
    let mut checked = 0;
    for seed in 0..300 {
        let n = 3 + (seed % 8) as i64;
        let edges = random_graph(seed, n, 3 + (seed % 12) as usize);
        let bad = [n - 1, n - 2];
        let dist = distances(n, &edges);
        let shortest = bad.iter().filter_map(|b| dist[*b as usize]).min();
        let m = graph(n, &edges, &bad);
        let o = run(&m, false, None);
        match shortest {
            None => assert_eq!(o.status, Status::Verified, "seed {seed}"),
            Some(d) => {
                assert_eq!(o.status, Status::Violated, "seed {seed}");
                let Evidence::Trace(steps, claim) = &o.evidence else {
                    panic!("seed {seed}")
                };
                assert_eq!(steps.len(), d, "seed {seed}");
                assert!(matches!(claim, Claim::Invariant(_)));
                // トレースは実際の辺をたどっている。
                let mut at = 0;
                for st in steps {
                    assert_eq!(edges[st.action], (at, st.state[0]), "seed {seed}");
                    at = st.state[0];
                }
                assert!(bad.contains(&at));
                checked += 1;
            }
        }
    }
    assert!(checked > 50, "反例のあるグラフが少なすぎる: {checked}");
}

#[test]
fn a_known_shortest_path_is_found_among_longer_ones() {
    // 0 → 1 → 2 → 3 → 4 の長い道と、0 → 5 → 4 の短い道。定義順は長い道が先。
    let edges = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 4)];
    let o = run(&graph(6, &edges, &[4]), false, None);
    let Evidence::Trace(steps, _) = &o.evidence else {
        panic!()
    };
    assert_eq!(steps.iter().map(|s| s.state[0]).collect::<Vec<_>>(), vec![5, 4]);
}

#[test]
fn ties_between_shortest_counterexamples_follow_the_definition_order() {
    // 長さ2の反例が2つある。操作の定義順で先に見つかるほうを返す。
    let edges = [(0, 2), (0, 1), (1, 3), (2, 3)];
    let o = run(&graph(4, &edges, &[3]), false, None);
    let Evidence::Trace(steps, _) = &o.evidence else {
        panic!()
    };
    assert_eq!(steps.iter().map(|s| s.state[0]).collect::<Vec<_>>(), vec![2, 3]);
}

#[test]
fn the_state_limit_counts_distinct_states_including_the_initial_one() {
    // 0 → 1 → 2 → 0 の閉路。状態は3つ。
    let m = graph(3, &[(0, 1), (1, 2), (2, 0)], &[]);
    for (max, visited) in [(1, 1), (2, 2)] {
        let o = run(&m, false, Some(max));
        assert_eq!(o.status, Status::Inconclusive(Limit::MaxStates), "max_states {max}");
        assert_eq!(o.stats.visited_states, visited);
        assert!(!o.stats.complete);
    }
    // 上限ちょうどなら完走する。既訪問の状態への辺 2 → 0 も検査している。
    let o = run(&m, false, Some(3));
    assert_eq!(o.status, Status::Verified);
    assert_eq!(
        (o.stats.visited_states, o.stats.transitions, o.stats.complete),
        (3, 3, true)
    );
}

#[test]
fn a_violation_on_an_edge_to_a_visited_state_is_found_at_the_state_limit() {
    // 自己ループ 0 → 0 に契約違反がある。状態数の上限が1でも、既訪問の状態への辺として検査する。
    let mut raw = graph(2, &[(0, 0)], &[]).raw().clone();
    raw.contracts = vec![Contract {
        action: 0,
        expr: Expr::Bin(BinOp::Ne, Box::new(Expr::Next(0)), Box::new(Expr::Var(0))),
    }];
    let m = validate(raw).unwrap();
    let o = run(&m, false, Some(1));
    assert_eq!(o.status, Status::Violated);
    let Evidence::Trace(steps, claim) = &o.evidence else {
        panic!()
    };
    assert_eq!((steps.len(), claim), (1, &Claim::Contract(0)));
}

#[test]
fn violations_in_the_initial_state_midway_on_an_edge_and_deadlocks_are_distinguished() {
    let edges = [(0, 1), (1, 2)];
    let claim_of = |o: &Outcome| match &o.evidence {
        Evidence::Trace(steps, claim) => (steps.len(), claim.clone()),
        other => panic!("{other:?}"),
    };
    // 初期状態の違反。
    assert_eq!(
        claim_of(&run(&graph(3, &edges, &[0]), true, None)),
        (0, Claim::Invariant(0))
    );
    // 途中の状態の違反。
    assert_eq!(
        claim_of(&run(&graph(3, &edges, &[1]), true, None)),
        (1, Claim::Invariant(0))
    );
    // 違反がなければ、行き止まりの状態2がデッドロック。
    let o = run(&graph(3, &edges, &[]), true, None);
    assert_eq!(o.status, Status::Violated);
    assert_eq!(claim_of(&o), (2, Claim::Deadlock));
    // デッドロック検査が無効なら Verified。
    assert_eq!(run(&graph(3, &edges, &[]), false, None).status, Status::Verified);
    // 遷移契約の違反は、その辺を最後のステップとするトレースになる。
    let mut raw = graph(3, &edges, &[]).raw().clone();
    raw.contracts = vec![Contract {
        action: 1,
        expr: eq(Expr::Next(0), Expr::Var(0)),
    }];
    let o = run(&validate(raw).unwrap(), true, None);
    assert_eq!(claim_of(&o), (2, Claim::Contract(0)));
}

#[test]
fn an_interrupt_request_stops_the_search() {
    let m = graph(3, &[(0, 1), (1, 2)], &[]);
    let o = check(
        &m,
        &conditions(&m, false),
        &BfsOptions {
            max_states: None,
            interrupt: Some(&|| true),
        },
    );
    assert_eq!(o.status, Status::Inconclusive(Limit::Interrupted));
}

#[test]
fn a_larger_state_space_is_explored_completely() {
    // 3つのカウンタ（0..=19）を1ずつ増やせるモデル。到達可能な状態は 20^3 = 8000 個。
    let inc = |i: usize| Action {
        n_params: 0,
        domains: vec![],
        guard: Expr::Bin(BinOp::Lt, Box::new(Expr::Var(i)), Box::new(int(19))),
        updates: vec![Update {
            target: i,
            expr: Expr::Bin(BinOp::Add, Box::new(Expr::Var(i)), Box::new(int(1))),
        }],
        output: None,
    };
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, 19); 3],
        init: vec![0, 0, 0],
        actions: vec![inc(0), inc(1), inc(2)],
        invariants: vec![],
        contracts: vec![],
        terminal: None,
    };
    let m = validate(raw).unwrap();
    let o = run(&m, false, None);
    assert_eq!(o.status, Status::Verified);
    assert_eq!(o.stats.visited_states, 8000);
    assert_eq!(o.stats.transitions, 3 * 19 * 20 * 20);
    assert_eq!(
        run(&m, false, Some(7999)).status,
        Status::Inconclusive(Limit::MaxStates)
    );
    assert_eq!(run(&m, false, Some(8000)).status, Status::Verified);
}
