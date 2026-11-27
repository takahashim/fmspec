//! 対称性による削減を使う幅優先探索（docs/plans/refinement_symmetry_constants.md の3）。
//!
//! 状態を入れ替えで正規化した代表元だけを訪問する。証明書は代表元の集合である。
//! 違反を見つけたら、代表元の経路から、入れ替えを逆にたどって具体的なトレースを作り、
//! 判定ゲートには普通のトレースとして渡す。どちらも判定ゲート（`decide_symmetric`）が検査し直す。

use crate::bfs::{BfsOptions, Stats};
use crate::check::{inconsistent, status_of, Outcome};
use crate::inconsistency::{successors, Inconsistency};
use crate::stop::stopped;
use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::{decide_symmetric, CheckedModel};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use fmspec_core::sym::{canonicalize, SwapMaps};
use std::collections::{HashMap, VecDeque};
use std::time::Instant;

struct Node {
    /// 代表元。
    state: Vec<i64>,
    /// 初期状態からの遷移数。
    depth: usize,
    /// 親の添字、親の代表元からの遷移（操作と引数）、遷移先を代表元に移す入れ替えの列。
    /// 根では、初期状態と、初期状態を代表元に移す入れ替えの列。
    from: From,
}

enum From {
    Root(Vec<i64>, Vec<usize>),
    Edge(usize, usize, Vec<i64>, Vec<usize>),
}

/// 代表元で見つけた事象。具体的なトレースの末尾で、改めて評価して主張にする。
enum Found {
    Invariant,
    Step(usize),
    Contract(usize, Vec<i64>),
    Deadlock,
}

/// 入れ替えの列 `u` を施した状態での操作 `a` に対応する、元の状態での操作。各入れ替えは対合なので、逆順にたどる。
fn unmap_action(sw: &[SwapMaps], u: &[usize], a: usize) -> usize {
    u.iter().rev().fold(a, |b, &i| sw[i].act[b])
}

/// 根から `id` までの代表元の経路を、具体的なトレースにする。
/// 末尾の具体的な状態と、それを代表元に移す入れ替えの列も返す。
fn concretize(
    model: &CheckedModel,
    sw: &[SwapMaps],
    nodes: &[Node],
    id: usize,
) -> Option<(Vec<i64>, Vec<TraceStep>, Vec<usize>)> {
    let mut chain = Vec::new();
    let mut cur = id;
    loop {
        chain.push(cur);
        match &nodes[cur].from {
            From::Root(..) => break,
            From::Edge(parent, ..) => cur = *parent,
        }
    }
    chain.reverse();
    let From::Root(start, w0) = &nodes[chain[0]].from else {
        return None;
    };
    let mut state = start.clone();
    let mut u = w0.clone();
    let mut steps = Vec::new();
    for &n in &chain[1..] {
        let From::Edge(_, a, args, w) = &nodes[n].from else {
            return None;
        };
        let b = unmap_action(sw, &u, *a);
        let Some(Enumerated::Ok(ts)) = model.successors(b, &state) else {
            return None;
        };
        let t = ts.into_iter().find(|t| &t.args == args)?;
        steps.push(TraceStep {
            action: b,
            args: t.args,
            output: t.output,
            state: t.state.clone(),
        });
        state = t.state;
        u.extend_from_slice(w);
    }
    Some((start.clone(), steps, u))
}

fn property_claim(
    index: usize,
    value: Result<bool, ErrKind>,
    violated: fn(usize) -> Claim,
    failed: fn(usize, ErrKind) -> Claim,
) -> Claim {
    match value {
        Err(e) => failed(index, e),
        Ok(_) => violated(index),
    }
}

/// 代表元 `id` で見つけた事象を、具体的なトレースの証拠にする。
fn evidence_for(
    model: &CheckedModel,
    cond: &Conditions,
    sw: &[SwapMaps],
    nodes: &[Node],
    id: usize,
    found: Found,
) -> Result<Evidence, Inconsistency> {
    let Some((start, mut steps, u)) = concretize(model, sw, nodes, id) else {
        return Err(Inconsistency::SymmetryTrace);
    };
    let last = steps.last().map_or(start.clone(), |s| s.state.clone());
    // 対応する具体的な事象が見つからなければ、任意の主張を付ける。判定ゲートが拒否し、探索器の不具合として報告される。
    let fallback = Claim::Deadlock;
    let claim = match found {
        Found::Invariant => match model.invariants(cond, &last) {
            Some((i, v)) => property_claim(i, v, Claim::Invariant, Claim::InvariantError),
            None => fallback,
        },
        Found::Step(a) => {
            let b = unmap_action(sw, &u, a);
            match model.successors(b, &last) {
                Some(Enumerated::Fail(args, site, kind)) => Claim::StepError(b, args, site, kind),
                _ => fallback,
            }
        }
        Found::Contract(a, args) => {
            let b = unmap_action(sw, &u, a);
            let next = match model.successors(b, &last) {
                Some(Enumerated::Ok(ts)) => ts.into_iter().find(|t| t.args == args),
                _ => None,
            };
            match next {
                Some(t) => {
                    let violation = model.contracts(cond, b, &last, &t.args, &t.state, &t.output);
                    steps.push(TraceStep {
                        action: b,
                        args: t.args,
                        output: t.output,
                        state: t.state,
                    });
                    match violation {
                        Some((k, v)) => property_claim(k, v, Claim::Contract, Claim::ContractError),
                        None => fallback,
                    }
                }
                None => fallback,
            }
        }
        Found::Deadlock => match model.terminal(&last) {
            Err(e) => Claim::TerminalError(e),
            Ok(_) => Claim::Deadlock,
        },
    };
    Ok(Evidence::Trace(start, steps, claim))
}

/// 対称性による削減を使う幅優先探索で、証拠を生成する。`sw` は判定ゲートの `symmetry` が返した入れ替え。
pub fn bfs_sym(
    model: &CheckedModel,
    cond: &Conditions,
    sw: &Vec<SwapMaps>,
    opts: &BfsOptions,
) -> (Result<Evidence, Inconsistency>, Stats) {
    let n_actions = model.raw().actions.len();
    let mut stats = Stats::default();
    let mut nodes: Vec<Node> = Vec::new();
    let mut seen: HashMap<Vec<i64>, usize> = HashMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();

    for init in model.initials() {
        let (rep, w) = canonicalize(sw, init);
        if seen.contains_key(&rep) {
            continue;
        }
        if opts.max_states.is_some_and(|max| seen.len() >= max) {
            return (Ok(Evidence::Unavailable(Limit::MaxStates)), stats);
        }
        let id = nodes.len();
        let bad = model.invariants(cond, &rep).is_some();
        seen.insert(rep.clone(), id);
        nodes.push(Node {
            state: rep,
            depth: 0,
            from: From::Root(init.clone(), w),
        });
        stats.visited_states = seen.len();
        if bad {
            return (evidence_for(model, cond, sw, &nodes, id, Found::Invariant), stats);
        }
        queue.push_back(id);
    }

    // 深さの上限で、未訪問の状態への遷移か、上限を超えるトレースの違反を残したか（`bfs` と同じ）。
    let mut truncated = false;
    while let Some(cur) = queue.pop_front() {
        if let Some(limit) = stopped(opts.interrupt, opts.deadline) {
            return (Ok(Evidence::Unavailable(limit)), stats);
        }
        let state = nodes[cur].state.clone();
        let depth = nodes[cur].depth;
        let at_limit = opts.max_depth.is_some_and(|max| depth >= max);
        let mut enabled = false;
        for a in 0..n_actions {
            if !cond.actions.get(a).copied().unwrap_or(false) {
                continue;
            }
            let transitions = match successors(model, a, &state) {
                Err(inconsistency) => return (Err(inconsistency), stats),
                Ok(Enumerated::Fail(..)) => {
                    return (evidence_for(model, cond, sw, &nodes, cur, Found::Step(a)), stats);
                }
                Ok(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                enabled = true;
                stats.transitions += 1;
                if model.contracts(cond, a, &state, &t.args, &t.state, &t.output).is_some() {
                    if at_limit {
                        truncated = true;
                        continue;
                    }
                    return (
                        evidence_for(model, cond, sw, &nodes, cur, Found::Contract(a, t.args)),
                        stats,
                    );
                }
                let (rep, w) = canonicalize(sw, &t.state);
                if seen.contains_key(&rep) {
                    continue;
                }
                if at_limit {
                    truncated = true;
                    continue;
                }
                if opts.max_states.is_some_and(|max| seen.len() >= max) {
                    return (Ok(Evidence::Unavailable(Limit::MaxStates)), stats);
                }
                let id = nodes.len();
                let bad = model.invariants(cond, &rep).is_some();
                seen.insert(rep.clone(), id);
                nodes.push(Node {
                    state: rep,
                    depth: depth + 1,
                    from: From::Edge(cur, a, t.args, w),
                });
                stats.visited_states = seen.len();
                if bad {
                    return (evidence_for(model, cond, sw, &nodes, id, Found::Invariant), stats);
                }
                queue.push_back(id);
            }
        }
        if cond.deadlock && !enabled && model.terminal(&state) != Ok(true) {
            return (evidence_for(model, cond, sw, &nodes, cur, Found::Deadlock), stats);
        }
    }

    if truncated {
        return (Ok(Evidence::Unavailable(Limit::MaxDepth)), stats);
    }
    stats.complete = true;
    let mut states: Vec<Vec<i64>> = nodes.into_iter().map(|n| n.state).collect();
    states.sort();
    (
        Ok(Evidence::Certificate(Certificate {
            conditions: cond.clone(),
            states,
        })),
        stats,
    )
}

/// 対称性による削減を使ってモデルを検査する。`swaps` はモデルの入れ替え（スロットの置換）の列。
/// 入れ替えが対称性でなければ、その添字を `Err` で返す。
pub fn check_sym(
    model: &CheckedModel,
    cond: &Conditions,
    swaps: &Vec<Vec<usize>>,
    opts: &BfsOptions,
) -> Result<Outcome, usize> {
    let sw = fmspec_core::sym::symmetry(model.raw(), cond, swaps)?;
    let started = Instant::now();
    let (found, stats) = bfs_sym(model, cond, &sw, opts);
    let search_time = started.elapsed();
    let mut outcome = match found {
        Ok(evidence) => {
            let started = Instant::now();
            let verdict = decide_symmetric(model, cond, swaps, &evidence);
            Outcome {
                status: status_of(&verdict),
                verdict,
                evidence,
                stats,
                search_time,
                gate_time: started.elapsed(),
            }
        }
        Err(inconsistency) => inconsistent(model, cond, inconsistency, stats),
    };
    outcome.search_time = search_time;
    Ok(outcome)
}
