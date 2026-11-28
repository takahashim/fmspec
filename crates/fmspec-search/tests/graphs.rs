//! 手作りの有限グラフでの探索の検査（仕様書 §14 の表、§14.1.1）。
//!
//! 探索器は証明の対象外なので、訪問状態、最短性、上限の扱いをここで検査する。
//! 比較の相手は、辺の一覧を直接たどる独立した全列挙である。
//! シミュレーション、縮小、状態と遷移のグラフも、同じグラフで検査する。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_core::checked::{validate, CheckedModel};
use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::{decide, VerdictKind};
use fmspec_core::model::{Action, BinOp, Contract, Expr, RawModel, Type, Update, Value};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Site;
use fmspec_search::{
    check, explore, sample, shrink, simulate, test_paths, BfsOptions, Outcome, ShrinkOptions, ShrinkStop, SimOptions,
    Status,
};
use std::cell::Cell;
use std::collections::{BTreeSet, VecDeque};
use std::time::{Duration, Instant};

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
        inits: vec![vec![0]],
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
            max_check_cost: None,
            ..BfsOptions::default()
        },
    )
}

/// 辺の一覧を直接たどって、頂点0からの最短距離を求める。
fn distances(n: i64, edges: &[(i64, i64)]) -> Vec<Option<usize>> {
    distances_from(0, n, edges)
}

/// 辺の一覧を直接たどって、頂点 `source` からの最短距離を求める。
fn distances_from(source: i64, n: i64, edges: &[(i64, i64)]) -> Vec<Option<usize>> {
    let mut dist = vec![None; n as usize];
    dist[source as usize] = Some(0);
    let mut queue = VecDeque::from([source]);
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
                let Evidence::Trace(_, steps, claim) = &o.evidence else {
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
    let Evidence::Trace(_, steps, _) = &o.evidence else {
        panic!()
    };
    assert_eq!(steps.iter().map(|s| s.state[0]).collect::<Vec<_>>(), vec![5, 4]);
}

#[test]
fn ties_between_shortest_counterexamples_follow_the_definition_order() {
    // 長さ2の反例が2つある。操作の定義順で先に見つかるほうを返す。
    let edges = [(0, 2), (0, 1), (1, 3), (2, 3)];
    let o = run(&graph(4, &edges, &[3]), false, None);
    let Evidence::Trace(_, steps, _) = &o.evidence else {
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
    let Evidence::Trace(_, steps, claim) = &o.evidence else {
        panic!()
    };
    assert_eq!((steps.len(), claim), (1, &Claim::Contract(0)));
}

#[test]
fn violations_in_the_initial_state_midway_on_an_edge_and_deadlocks_are_distinguished() {
    let edges = [(0, 1), (1, 2)];
    let claim_of = |o: &Outcome| match &o.evidence {
        Evidence::Trace(_, steps, claim) => (steps.len(), claim.clone()),
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
            max_check_cost: None,
            ..BfsOptions::default()
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
        inits: vec![vec![0, 0, 0]],
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

// ---- ランダムシミュレーション（仕様書 §9）----

/// 比較の相手の SplitMix64。探索器の実装を使わずに、標準のアルゴリズムをここに書く。
struct Mix(u64);

impl Mix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = n as u64;
        let threshold = n.wrapping_neg() % n;
        loop {
            let x = self.next();
            if x >= threshold {
                return (x % n) as usize;
            }
        }
    }
}

/// 期待するシミュレーションの結果。見つけた違反（開始頂点、たどった辺の添字、主張）と、完了したトレース数、総ステップ数。
type Expected = (Option<(i64, Vec<usize>, Claim)>, usize, usize);

/// 辺の一覧を直接たどる、独立したシミュレーション。
/// 初期状態が複数なら乱数で1つ選び、各ステップでは、定義順に並べた出る辺から1つを一様に選ぶ。
fn expected_simulation(
    inits: &[i64],
    edges: &[(i64, i64)],
    bad: &[i64],
    deadlock: bool,
    opts: &SimOptions,
) -> Expected {
    let mut rng = Mix(opts.seed);
    let (mut completed, mut total) = (0, 0);
    let violated = |v: i64| bad.iter().position(|b| *b == v).map(Claim::Invariant);
    for _ in 0..opts.traces {
        let start = if inits.len() > 1 {
            inits[rng.below(inits.len())]
        } else {
            inits[0]
        };
        if let Some(claim) = violated(start) {
            return (Some((start, vec![], claim)), completed, total);
        }
        let (mut at, mut taken) = (start, Vec::new());
        for _ in 0..opts.max_steps {
            let out: Vec<usize> = (0..edges.len()).filter(|e| edges[*e].0 == at).collect();
            if out.is_empty() {
                if deadlock {
                    return (Some((start, taken, Claim::Deadlock)), completed, total);
                }
                break;
            }
            let e = out[rng.below(out.len())];
            total += 1;
            taken.push(e);
            at = edges[e].1;
            if let Some(claim) = violated(at) {
                return (Some((start, taken, claim)), completed, total);
            }
        }
        completed += 1;
    }
    (None, completed, total)
}

fn with_inits(m: &CheckedModel, inits: &[i64]) -> CheckedModel {
    let mut raw = m.raw().clone();
    raw.inits = inits.iter().map(|v| vec![*v]).collect();
    validate(raw).unwrap()
}

#[test]
fn simulations_follow_the_seed_like_an_independent_sampler() {
    let mut found = 0;
    for seed in 0..300u64 {
        let n = 3 + (seed % 8) as i64;
        let edges = random_graph(seed, n, 3 + (seed % 12) as usize);
        let bad: Vec<i64> = if seed % 3 == 0 { vec![] } else { vec![n - 1, n - 2] };
        // 初期状態が1つのモデルは乱数を消費しない。2つのモデルは、トレースごとに1回消費する。
        let inits: Vec<i64> = if seed % 2 == 0 { vec![0] } else { vec![0, 1] };
        let deadlock = seed % 5 == 0;
        let m = with_inits(&graph(n, &edges, &bad), &inits);
        let cond = conditions(&m, deadlock);
        let opts = SimOptions {
            seed: seed.wrapping_mul(0x2545_F491_4F6C_DD1D),
            traces: 1 + (seed % 4) as usize,
            max_steps: (seed % 9) as usize,
            interrupt: None,
            deadline: None,
        };
        let (expected, completed, total) = expected_simulation(&inits, &edges, &bad, deadlock, &opts);
        let result = simulate(&m, &cond, &opts);
        assert_eq!(
            (result.stats.traces, result.stats.steps),
            (completed, total),
            "seed {seed}"
        );
        match (&expected, &result.evidence) {
            (None, Ok(None)) => {}
            (Some((start, taken, claim)), Ok(Some(Evidence::Trace(s, steps, c)))) => {
                assert_eq!((s, c), (&vec![*start], claim), "seed {seed}");
                assert_eq!(
                    steps.iter().map(|st| st.action).collect::<Vec<_>>(),
                    *taken,
                    "seed {seed}"
                );
                found += 1;
            }
            (e, r) => panic!("seed {seed}: expected {e:?}, got {r:?}"),
        }
        // 判定ゲートは、見つけたトレースをすべて受理する。
        let sampled = sample(&m, &cond, &opts);
        assert_eq!(sampled.stats, result.stats, "seed {seed}");
        let status = sampled.found.map(|o| o.status);
        assert_eq!(status, expected.map(|_| Status::Violated), "seed {seed}");
    }
    assert!(found > 50, "違反を見つけたシミュレーションが少なすぎる: {found}");
}

#[test]
fn an_interrupt_request_stops_the_simulation() {
    let m = graph(3, &[(0, 1), (1, 0)], &[]);
    let opts = SimOptions {
        seed: 0,
        traces: 10,
        max_steps: 10,
        interrupt: Some(&|| true),
        deadline: None,
    };
    let sampled = sample(&m, &conditions(&m, false), &opts);
    let o = sampled.found.unwrap();
    assert_eq!(o.status, Status::Inconclusive(Limit::Interrupted));
    assert_eq!(sampled.stats.traces, 0);
}

#[test]
fn an_interrupt_request_stops_a_simulation_without_steps() {
    // 最大ステップ数が0でも、トレースごとに中断要求を確かめる。完了したトレースを数えるだけで止まらない、ということがない。
    let m = graph(3, &[(0, 1), (1, 0)], &[]);
    let opts = SimOptions {
        seed: 0,
        traces: 10,
        max_steps: 0,
        interrupt: Some(&|| true),
        deadline: None,
    };
    let result = simulate(&m, &conditions(&m, false), &opts);
    assert!(matches!(
        result.evidence,
        Ok(Some(Evidence::Unavailable(Limit::Interrupted)))
    ));
    assert_eq!(result.stats.traces, 0);
}

// ---- トレースの縮小（仕様書 §10）----

/// 辺の添字の列を、開始頂点から再実行したトレースのステップ。無効な辺があれば `None`。
fn walk(edges: &[(i64, i64)], start: i64, taken: &[usize]) -> Option<Vec<TraceStep>> {
    let mut at = start;
    let mut steps = Vec::new();
    for e in taken {
        if edges[*e].0 != at {
            return None;
        }
        at = edges[*e].1;
        steps.push(TraceStep {
            action: *e,
            args: vec![],
            output: None,
            state: vec![at],
        });
    }
    Some(steps)
}

#[test]
fn shrunk_traces_keep_the_claim_and_no_single_step_can_be_removed() {
    let mut shrunk = 0;
    for seed in 0..300u64 {
        let n = 4 + (seed % 7) as i64;
        let edges = random_graph(seed, n, 6 + (seed % 10) as usize);
        let bad = [n - 1];
        let m = graph(n, &edges, &bad);
        let cond = conditions(&m, false);
        let opts = SimOptions {
            seed,
            traces: 20,
            max_steps: 30,
            interrupt: None,
            deadline: None,
        };
        let Ok(Some(Evidence::Trace(start, steps, claim))) = simulate(&m, &cond, &opts).evidence else {
            continue;
        };
        // 試す候補がなければ、元のトレースを返す。
        assert_eq!(
            shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(0)).steps,
            steps,
            "seed {seed}"
        );

        let best = shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(10_000)).steps;
        let accepted = |steps: Vec<TraceStep>| {
            decide(&m, &cond, &Evidence::Trace(start.clone(), steps, claim.clone())).kind() == VerdictKind::Violated
        };
        assert!(accepted(best.clone()), "seed {seed}");
        let shortest = distances_from(start[0], n, &edges)[bad[0] as usize].unwrap();
        assert!(shortest <= best.len() && best.len() <= steps.len(), "seed {seed}");
        // 局所最小：どの1ステップを除いても、同じ主張のトレースにならない。
        let taken: Vec<usize> = best.iter().map(|s| s.action).collect();
        for i in 0..taken.len() {
            let mut fewer = taken.clone();
            fewer.remove(i);
            if let Some(candidate) = walk(&edges, start[0], &fewer) {
                assert!(!accepted(candidate), "seed {seed}: step {i} of {taken:?}");
            }
        }
        if best.len() < steps.len() {
            shrunk += 1;
        }
    }
    assert!(shrunk > 30, "縮小できたトレースが少なすぎる: {shrunk}");
}

/// 引数と内部選択を持つグラフ。辺 `(from, to)` ごとに操作を1つ作り、公開引数 `d`（0から2）と内部選択 `c`（真偽値）を持たせる。
/// `x == from` で有効になり、`x` を `(to + d + (c ? 1 : 0)) mod n` にする。
/// ただし、`d` は添字が偶数の辺でだけ、`c` は添字が3の倍数の辺でだけ遷移先に効く（`uses`）。不変条件は `graph` と同じ。
fn graph_with_args(n: i64, edges: &[(i64, i64)], bad: &[i64]) -> CheckedModel {
    let bin = |op, a, b| Expr::Bin(op, Box::new(a), Box::new(b));
    let actions = edges
        .iter()
        .enumerate()
        .map(|(e, (from, to))| {
            let d = if uses(e, 0) { Expr::Arg(0) } else { int(0) };
            let c = if uses(e, 1) {
                Expr::Ite(Box::new(Expr::Arg(1)), Box::new(int(1)), Box::new(int(0)))
            } else {
                int(0)
            };
            let sum = bin(BinOp::Add, bin(BinOp::Add, int(*to), d), c);
            Action {
                n_params: 1,
                domains: vec![Type::Int(0, 2), Type::Bool],
                guard: eq(Expr::Var(0), int(*from)),
                updates: vec![Update {
                    target: 0,
                    expr: bin(BinOp::Mod, sum, int(n)),
                }],
                output: None,
            }
        })
        .collect();
    let invariants = bad
        .iter()
        .map(|b| Expr::Bin(BinOp::Ne, Box::new(Expr::Var(0)), Box::new(int(*b))))
        .collect();
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, n - 1)],
        inits: vec![vec![0]],
        actions,
        invariants,
        contracts: vec![],
        terminal: None,
    };
    validate(raw).expect("整形式のモデル")
}

/// 辺 `e` の `j` 番目の引数が遷移先に効くか。
fn uses(e: usize, j: usize) -> bool {
    if j == 0 {
        e.is_multiple_of(2)
    } else {
        e.is_multiple_of(3)
    }
}

/// 辺の添字と引数（`d`、`c` を 0/1 で）の列を、開始頂点から直接たどったトレースのステップ。無効な辺があれば `None`。
fn walk_with_args(n: i64, edges: &[(i64, i64)], start: i64, taken: &[(usize, Vec<i64>)]) -> Option<Vec<TraceStep>> {
    let mut at = start;
    let mut steps = Vec::new();
    for (e, args) in taken {
        if edges[*e].0 != at {
            return None;
        }
        let effect = |j: usize| if uses(*e, j) { args[j] } else { 0 };
        at = (edges[*e].1 + effect(0) + effect(1)) % n;
        steps.push(TraceStep {
            action: *e,
            args: args.clone(),
            output: None,
            state: vec![at],
        });
    }
    Some(steps)
}

#[test]
fn shrunk_traces_keep_the_claim_and_no_single_step_or_argument_can_be_reduced() {
    let mut lowered = 0;
    for seed in 0..300u64 {
        let n = 4 + (seed % 7) as i64;
        let edges = random_graph(seed, n, 3 + (seed % 8) as usize);
        let bad = [n - 1];
        let m = graph_with_args(n, &edges, &bad);
        let cond = conditions(&m, false);
        let opts = SimOptions {
            seed,
            traces: 20,
            max_steps: 30,
            interrupt: None,
            deadline: None,
        };
        let Ok(Some(Evidence::Trace(start, steps, claim))) = simulate(&m, &cond, &opts).evidence else {
            continue;
        };
        assert_eq!(
            shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(0)).steps,
            steps,
            "seed {seed}"
        );

        let best = shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(10_000)).steps;
        let accepted = |steps: Vec<TraceStep>| {
            decide(&m, &cond, &Evidence::Trace(start.clone(), steps, claim.clone())).kind() == VerdictKind::Violated
        };
        assert!(accepted(best.clone()), "seed {seed}");
        assert!(best.len() <= steps.len(), "seed {seed}");
        // 結果は、独立にたどり直したトレースと一致する（状態は再計算されている）。
        let taken: Vec<(usize, Vec<i64>)> = best.iter().map(|s| (s.action, s.args.clone())).collect();
        assert_eq!(
            walk_with_args(n, &edges, start[0], &taken),
            Some(best.clone()),
            "seed {seed}"
        );
        // 局所最小：どの1ステップを除いても、同じ主張のトレースにならない。
        for i in 0..taken.len() {
            let mut fewer = taken.clone();
            fewer.remove(i);
            if let Some(candidate) = walk_with_args(n, &edges, start[0], &fewer) {
                assert!(!accepted(candidate), "seed {seed}: step {i} of {taken:?}");
            }
        }
        // 局所最小：どの1ステップの1つの引数を、より小さい値に変えても、同じ主張のトレースにならない。
        for i in 0..taken.len() {
            for j in 0..2 {
                for v in 0..taken[i].1[j] {
                    let mut other = taken.clone();
                    other[i].1[j] = v;
                    if let Some(candidate) = walk_with_args(n, &edges, start[0], &other) {
                        assert!(!accepted(candidate), "seed {seed}: step {i} arg {j} = {v} of {taken:?}");
                    }
                }
            }
        }
        // 遷移先に効かない引数は、ドメインの最小の値まで小さくなる。
        for (e, args) in &taken {
            for j in 0..2 {
                assert!(uses(*e, j) || args[j] == 0, "seed {seed}: {taken:?}");
            }
        }
        if steps
            .iter()
            .any(|s| (0..2).any(|j| !uses(s.action, j) && s.args[j] != 0))
        {
            lowered += 1;
        }
    }
    assert!(lowered > 30, "効かない引数が0でないトレースが少なすぎる: {lowered}");
}

/// `x` を `d`（0から3）だけ増やす操作 `add` だけを持つモデル。不変条件は `x < bound`。
fn adder(bound: i64) -> CheckedModel {
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, bound + 3)],
        inits: vec![vec![0]],
        actions: vec![Action {
            n_params: 1,
            domains: vec![Type::Int(0, 3)],
            guard: Expr::Bin(BinOp::Lt, Box::new(Expr::Var(0)), Box::new(int(bound))),
            updates: vec![Update {
                target: 0,
                expr: Expr::Bin(BinOp::Add, Box::new(Expr::Var(0)), Box::new(Expr::Arg(0))),
            }],
            output: None,
        }],
        invariants: vec![Expr::Bin(BinOp::Lt, Box::new(Expr::Var(0)), Box::new(int(bound)))],
        contracts: vec![],
        terminal: None,
    };
    validate(raw).expect("整形式のモデル")
}

/// `adder` で、`d` が `ds` のステップを並べたトレース。
fn adds(ds: &[i64]) -> Vec<TraceStep> {
    ds.iter()
        .scan(0, |x, d| {
            *x += d;
            Some(TraceStep {
                action: 0,
                args: vec![*d],
                output: None,
                state: vec![*x],
            })
        })
        .collect()
}

#[test]
fn shrinking_a_long_trace_stops_at_the_deadline_with_an_accepted_trace() {
    // どのステップを除いても、どの引数を小さくしても違反しないので、局所最小を確かめるには長さの2乗に比例する時間がかかる。
    let m = adder(3000);
    let cond = conditions(&m, false);
    let steps = adds(&[1; 3000]);
    let claim = Claim::Invariant(0);
    let accepted = |steps: &[TraceStep]| {
        decide(&m, &cond, &Evidence::Trace(vec![0], steps.to_vec(), claim.clone())).kind() == VerdictKind::Violated
    };
    assert!(accepted(&steps));
    let started = Instant::now();
    let opts = ShrinkOptions {
        attempts: 10_000,
        interrupt: None,
        deadline: started.checked_add(Duration::from_millis(100)),
    };
    let shrunk = shrink(&m, &cond, &[0], &steps, &claim, &opts);
    assert!(started.elapsed() < Duration::from_secs(2), "{:?}", started.elapsed());
    assert_eq!(shrunk.stopped, Some(ShrinkStop::Limit(Limit::MaxTime)));
    assert!(shrunk.attempts < 10_000);
    assert_eq!(shrunk.steps, steps);
    assert!(accepted(&shrunk.steps));
}

#[test]
fn an_interrupt_request_stops_the_shrinking_with_the_last_accepted_trace() {
    let m = adder(6);
    let cond = conditions(&m, false);
    let claim = Claim::Invariant(0);
    let steps = adds(&[1, 0, 3, 2]);
    let full = shrink(&m, &cond, &[0], &steps, &claim, &ShrinkOptions::attempts(10_000));
    assert_eq!(full.stopped, None);
    assert_eq!(full.steps, adds(&[1, 3, 2]));
    for k in 0..full.attempts {
        let asked = Cell::new(0);
        let interrupt = || {
            asked.set(asked.get() + 1);
            asked.get() > k
        };
        let opts = ShrinkOptions {
            attempts: 10_000,
            interrupt: Some(&interrupt),
            deadline: None,
        };
        let part = shrink(&m, &cond, &[0], &steps, &claim, &opts);
        assert_eq!(
            (part.attempts, part.stopped),
            (k, Some(ShrinkStop::Limit(Limit::Interrupted)))
        );
        // 打ち切った時点の結果は、判定ゲートが同じ主張で受理したトレースである。
        let kind = decide(&m, &cond, &Evidence::Trace(vec![0], part.steps.clone(), claim.clone())).kind();
        assert_eq!(kind, VerdictKind::Violated, "k = {k}");
        assert!(part.steps.len() >= full.steps.len());
    }
}

#[test]
fn removals_and_argument_changes_share_the_attempts_and_a_spent_budget_leaves_an_accepted_trace() {
    let mut both = 0;
    for seed in 0..100u64 {
        let n = 4 + (seed % 7) as i64;
        let edges = random_graph(seed, n, 3 + (seed % 8) as usize);
        let bad = [n - 1];
        let m = graph_with_args(n, &edges, &bad);
        let cond = conditions(&m, false);
        let opts = SimOptions {
            seed,
            traces: 20,
            max_steps: 30,
            interrupt: None,
            deadline: None,
        };
        let Ok(Some(Evidence::Trace(start, steps, claim))) = simulate(&m, &cond, &opts).evidence else {
            continue;
        };
        let full = shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(10_000));
        assert_eq!(full.stopped, None, "seed {seed}");
        // 上限がちょうど試した候補（削除と引数の変更を合わせた数）の数なら、上限なしと同じ結果に終わる。
        let exact = shrink(
            &m,
            &cond,
            &start,
            &steps,
            &claim,
            &ShrinkOptions::attempts(full.attempts),
        );
        assert_eq!(exact, full, "seed {seed}");
        let lowered = steps.iter().zip(&full.steps).any(|(s, t)| s.args != t.args);
        if lowered && full.steps.len() < steps.len() {
            both += 1;
        }
        for budget in 0..full.attempts {
            let part = shrink(&m, &cond, &start, &steps, &claim, &ShrinkOptions::attempts(budget));
            assert_eq!(
                (part.attempts, part.stopped),
                (budget, Some(ShrinkStop::Attempts)),
                "seed {seed}"
            );
            let kind = decide(
                &m,
                &cond,
                &Evidence::Trace(start.clone(), part.steps.clone(), claim.clone()),
            )
            .kind();
            assert_eq!(kind, VerdictKind::Violated, "seed {seed}, budget {budget}");
            assert!(
                full.steps.len() <= part.steps.len() && part.steps.len() <= steps.len(),
                "seed {seed}"
            );
        }
    }
    assert!(both > 10, "削除と引数の変更の両方で縮んだトレースが少なすぎる: {both}");
}

/// 操作 `set(d)`（`x := d`、`d` は0から1_000_000）と `tick(e)`（`y := y + 1`、`e` は0か1で遷移先に効かない）を持つモデル。
/// 不変条件は「`x >= 500000` かつ `y >= 3` でない」。
fn wide() -> CheckedModel {
    let bin = |op, a, b| Expr::Bin(op, Box::new(a), Box::new(b));
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, 1_000_000), Type::Int(0, 3)],
        inits: vec![vec![0, 0]],
        actions: vec![
            Action {
                n_params: 1,
                domains: vec![Type::Int(0, 1_000_000)],
                guard: Expr::Const(Value::Bool(true)),
                updates: vec![Update {
                    target: 0,
                    expr: Expr::Arg(0),
                }],
                output: None,
            },
            Action {
                n_params: 1,
                domains: vec![Type::Int(0, 1)],
                guard: bin(BinOp::Lt, Expr::Var(1), int(3)),
                updates: vec![Update {
                    target: 1,
                    expr: bin(BinOp::Add, Expr::Var(1), int(1)),
                }],
                output: None,
            },
        ],
        invariants: vec![Expr::Not(Box::new(Expr::And(
            Box::new(bin(BinOp::Ge, Expr::Var(0), int(500_000))),
            Box::new(bin(BinOp::Ge, Expr::Var(1), int(3))),
        )))],
        contracts: vec![],
        terminal: None,
    };
    validate(raw).expect("整形式のモデル")
}

#[test]
fn a_wide_domain_does_not_spend_the_attempts_before_other_arguments_are_lowered() {
    let m = wide();
    let cond = conditions(&m, false);
    let claim = Claim::Invariant(0);
    let step = |action, arg, state: [i64; 2]| TraceStep {
        action,
        args: vec![arg],
        output: None,
        state: state.to_vec(),
    };
    let steps = vec![
        step(0, 700_000, [700_000, 0]),
        step(1, 1, [700_000, 1]),
        step(1, 1, [700_000, 2]),
        step(1, 1, [700_000, 3]),
    ];
    let shrunk = shrink(&m, &cond, &[0, 0], &steps, &claim, &ShrinkOptions::attempts(10_000));
    let kind = decide(
        &m,
        &cond,
        &Evidence::Trace(vec![0, 0], shrunk.steps.clone(), claim.clone()),
    )
    .kind();
    assert_eq!(kind, VerdictKind::Violated);
    // d は二分探索で、違反に要る最小の値まで小さくなり、遷移先に効かない e は0になる。
    let expected = vec![
        step(0, 500_000, [500_000, 0]),
        step(1, 0, [500_000, 1]),
        step(1, 0, [500_000, 2]),
        step(1, 0, [500_000, 3]),
    ];
    assert_eq!(shrunk.steps, expected);
    // d より前の値をすべて試して局所最小を確かめるには候補が足りないので、打ち切ったことを報告する。
    assert_eq!((shrunk.attempts, shrunk.stopped), (10_000, Some(ShrinkStop::Attempts)));
}

/// 公開引数 `d`（0から3）と、遷移先に効かない内部選択 `e`（0から3）を持つ操作 `add` だけのモデル。`add` は `x` を `d` だけ増やす。
fn add_with_choice(guard: Expr, contracts: Vec<Contract>) -> CheckedModel {
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, 10)],
        inits: vec![vec![0]],
        actions: vec![Action {
            n_params: 1,
            domains: vec![Type::Int(0, 3), Type::Int(0, 3)],
            guard,
            updates: vec![Update {
                target: 0,
                expr: Expr::Bin(BinOp::Add, Box::new(Expr::Var(0)), Box::new(Expr::Arg(0))),
            }],
            output: None,
        }],
        invariants: vec![],
        contracts,
        terminal: None,
    };
    validate(raw).expect("整形式のモデル")
}

/// `add_with_choice` で、引数 `(d, e)` の列を初期状態からたどったトレース。
fn adds_with_choice(args: &[(i64, i64)]) -> Vec<TraceStep> {
    args.iter()
        .scan(0, |x, (d, e)| {
            *x += d;
            Some(TraceStep {
                action: 0,
                args: vec![*d, *e],
                output: None,
                state: vec![*x],
            })
        })
        .collect()
}

/// 主張が不変条件でない違反と評価エラーでも、引数を小さくし、後続のステップを再実行する。
#[test]
fn arguments_are_lowered_for_contract_deadlock_and_step_error_claims() {
    let bin = |op, a, b| Expr::Bin(op, Box::new(a), Box::new(b));
    let below_five = bin(BinOp::Lt, Expr::Var(0), int(5));
    // 遷移契約：1回の遷移で2以上増えない。
    let small_steps = Contract {
        action: 0,
        expr: bin(BinOp::Lt, bin(BinOp::Sub, Expr::Next(0), Expr::Var(0)), int(2)),
    };
    // x = 5 で guard の評価が0除算になる。x < 5 では真、x > 5 では偽。
    let fails_at_five = bin(
        BinOp::Ge,
        bin(BinOp::Div, int(10), bin(BinOp::Sub, int(5), Expr::Var(0))),
        int(0),
    );
    let cases = [
        (
            add_with_choice(Expr::Const(Value::Bool(true)), vec![small_steps]),
            false,
            Claim::Contract(0),
            adds_with_choice(&[(1, 1), (3, 2)]),
            // 前のステップを除き、d は違反する最小の2に、e は0になる。
            adds_with_choice(&[(2, 0)]),
        ),
        (
            add_with_choice(below_five, vec![]),
            true,
            Claim::Deadlock,
            adds_with_choice(&[(3, 1), (3, 1)]),
            // 1つ目の d を2にすると、2つ目のステップの遷移先が5になり、そこで止まる。
            adds_with_choice(&[(2, 0), (3, 0)]),
        ),
        (
            add_with_choice(fails_at_five, vec![]),
            false,
            Claim::StepError(0, vec![0, 0], Site::Guard, ErrKind::DivByZero),
            adds_with_choice(&[(2, 3), (3, 1)]),
            adds_with_choice(&[(2, 0), (3, 0)]),
        ),
    ];
    for (m, deadlock, claim, steps, expected) in cases {
        let cond = conditions(&m, deadlock);
        let accepted = |steps: &[TraceStep]| {
            let kind = decide(&m, &cond, &Evidence::Trace(vec![0], steps.to_vec(), claim.clone())).kind();
            matches!(kind, VerdictKind::Violated | VerdictKind::Error)
        };
        assert!(accepted(&steps), "{claim:?}");
        let shrunk = shrink(&m, &cond, &[0], &steps, &claim, &ShrinkOptions::attempts(10_000));
        assert_eq!(shrunk.stopped, None, "{claim:?}");
        assert_eq!(shrunk.steps, expected, "{claim:?}");
        assert!(accepted(&shrunk.steps), "{claim:?}");
    }
}

// ---- 状態と遷移のグラフ（仕様書 §11.3）----

#[test]
fn the_explored_graph_matches_an_independent_enumeration() {
    for seed in 0..200u64 {
        let n = 2 + (seed % 9) as i64;
        let edges = random_graph(seed, n, (seed % 14) as usize);
        let m = graph(n, &edges, &[]);
        let cond = conditions(&m, false);
        let dist = distances(n, &edges);
        let reachable: BTreeSet<i64> = (0..n).filter(|v| dist[*v as usize].is_some()).collect();
        let reachable_edges = edges.iter().filter(|(from, _)| reachable.contains(from)).count();

        let g = explore(&m, &cond, None, None, None);
        assert!(g.complete, "seed {seed}");
        assert_eq!(g.states[0], vec![0], "seed {seed}");
        assert_eq!(
            g.states.iter().map(|s| s[0]).collect::<BTreeSet<_>>(),
            reachable,
            "seed {seed}"
        );
        assert_eq!(g.edges.len(), reachable_edges, "seed {seed}");
        for (id, s) in g.states.iter().enumerate() {
            assert_eq!(g.index[s], id, "seed {seed}");
            // 最初に到達した遷移の列は、最短の経路である。
            let path = g.path_to(id);
            assert_eq!(Some(path.len()), dist[s[0] as usize], "seed {seed}");
            assert_eq!(g.root(id), 0, "seed {seed}");
        }
        for e in &g.edges {
            let (from, to) = edges[e.action];
            assert_eq!(
                (g.states[e.from][0], e.to.map(|t| g.states[t][0])),
                (from, Some(to)),
                "seed {seed}"
            );
        }

        // 状態数の上限では、幅優先の訪問順の先頭だけを保持し、保持しない状態への辺は遷移先を持たない。
        if g.states.len() > 1 {
            let max = g.states.len() - 1;
            let limited = explore(&m, &cond, Some(max), None, None);
            assert!(!limited.complete, "seed {seed}");
            assert_eq!(limited.states, g.states[..max], "seed {seed}");
            assert!(limited.edges.iter().any(|e| e.to.is_none()), "seed {seed}");
        }

        // テスト経路は、到達できるすべての状態と入力の組を覆う。各経路は実際の辺をたどる。
        let max_steps = n as usize + 2;
        let p = test_paths(&m, &cond, &vec![vec![]; edges.len()], None, max_steps, None, None);
        assert_eq!(
            (p.targets, p.covered),
            (reachable_edges, reachable_edges),
            "seed {seed}"
        );
        for path in &p.paths {
            assert_eq!(path.start, 0, "seed {seed}");
            assert!(!path.inputs.is_empty() && path.inputs.len() <= max_steps, "seed {seed}");
            let taken: Vec<usize> = path.inputs.iter().map(|(a, _)| *a).collect();
            assert!(walk(&edges, 0, &taken).is_some(), "seed {seed}: {taken:?}");
        }
        // 1入力の経路で覆えるのは、初期状態から出る辺だけである。
        let p = test_paths(&m, &cond, &vec![vec![]; edges.len()], None, 1, None, None);
        assert_eq!(
            p.covered,
            edges.iter().filter(|(from, _)| *from == 0).count(),
            "seed {seed}"
        );
    }
}

#[test]
fn an_interrupt_request_leaves_the_graph_incomplete() {
    let m = graph(3, &[(0, 1), (1, 2)], &[]);
    let g = explore(&m, &conditions(&m, false), None, Some(&|| true), None);
    assert!(!g.complete);
    assert!(g.edges.is_empty());
}
