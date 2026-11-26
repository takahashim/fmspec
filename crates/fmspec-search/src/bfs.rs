//! 幅優先探索（仕様書 §8.1）。
//!
//! 操作は定義順、引数は辞書順に列挙する。したがって、状態不変条件の違反は遷移回数が最小の
//! トレースで見つかり、同じ長さのトレースのうちでは、この列挙順で最初に見つかるものを返す。

use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use std::collections::{HashMap, VecDeque};

#[derive(Default)]
pub struct BfsOptions<'a> {
    /// 保持する異なる状態の数の上限。初期状態を含む。
    pub max_states: Option<usize>,
    /// 中断要求の問い合わせ。真を返したら探索を打ち切る。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
}

/// 探索器の報告。検査済みの値ではない（仕様書 §14.1.1）。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// 訪問した異なる状態の数。
    pub visited_states: usize,
    /// 検査した有効な遷移の数。
    pub transitions: usize,
    /// 探索が完走したか。
    pub complete: bool,
}

pub struct SearchResult {
    pub evidence: Evidence,
    pub stats: Stats,
}

struct Node {
    state: Vec<i64>,
    /// 親の添字と、親からの遷移。
    parent: Option<(usize, usize, Vec<i64>, Option<i64>)>,
}

/// 初期状態から `id` の状態までのトレースを復元する。
fn path(nodes: &[Node], mut id: usize) -> Vec<TraceStep> {
    let mut steps = Vec::new();
    while let Some((parent, action, args, output)) = &nodes[id].parent {
        steps.push(TraceStep {
            action: *action,
            args: args.clone(),
            output: *output,
            state: nodes[id].state.clone(),
        });
        id = *parent;
    }
    steps.reverse();
    steps
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

/// 幅優先探索で証拠を生成する。
pub fn bfs(model: &CheckedModel, cond: &Conditions, opts: &BfsOptions) -> SearchResult {
    let n_actions = model.raw().actions.len();
    let mut stats = Stats::default();
    let init = model.initial();
    let mut nodes: Vec<Node> = vec![Node {
        state: init.clone(),
        parent: None,
    }];
    let mut visited: HashMap<Vec<i64>, usize> = HashMap::new();
    visited.insert(init.clone(), 0);
    stats.visited_states = 1;

    let finish = |evidence: Evidence, stats: Stats| SearchResult { evidence, stats };

    if let Some((i, v)) = model.invariants(cond, &init) {
        return finish(
            Evidence::Trace(
                Vec::new(),
                property_claim(i, v, Claim::Invariant, Claim::InvariantError),
            ),
            stats,
        );
    }

    let mut queue: VecDeque<usize> = VecDeque::from([0]);
    while let Some(cur) = queue.pop_front() {
        if opts.interrupt.is_some_and(|requested| requested()) {
            return finish(Evidence::Unavailable(Limit::Interrupted), stats);
        }
        let state = nodes[cur].state.clone();
        let mut enabled = false;
        for a in 0..n_actions {
            if !cond.actions.get(a).copied().unwrap_or(false) {
                continue;
            }
            let transitions = match model.successors(a, &state) {
                // 訪問済みの状態は型に従い、操作の添字は範囲内なので、ここには来ない。
                None => return finish(Evidence::Unavailable(Limit::Interrupted), stats),
                Some(Enumerated::Fail(args, site, kind)) => {
                    return finish(
                        Evidence::Trace(path(&nodes, cur), Claim::StepError(a, args, site, kind)),
                        stats,
                    );
                }
                Some(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                enabled = true;
                stats.transitions += 1;
                if let Some((k, v)) = model.contracts(cond, a, &state, &t.args, &t.state, &t.output) {
                    let mut steps = path(&nodes, cur);
                    steps.push(TraceStep {
                        action: a,
                        args: t.args,
                        output: t.output,
                        state: t.state,
                    });
                    return finish(
                        Evidence::Trace(steps, property_claim(k, v, Claim::Contract, Claim::ContractError)),
                        stats,
                    );
                }
                if visited.contains_key(&t.state) {
                    continue;
                }
                if opts.max_states.is_some_and(|max| visited.len() >= max) {
                    return finish(Evidence::Unavailable(Limit::MaxStates), stats);
                }
                let id = nodes.len();
                visited.insert(t.state.clone(), id);
                stats.visited_states = visited.len();
                let violation = model.invariants(cond, &t.state);
                nodes.push(Node {
                    state: t.state,
                    parent: Some((cur, a, t.args, t.output)),
                });
                if let Some((i, v)) = violation {
                    return finish(
                        Evidence::Trace(
                            path(&nodes, id),
                            property_claim(i, v, Claim::Invariant, Claim::InvariantError),
                        ),
                        stats,
                    );
                }
                queue.push_back(id);
            }
        }
        if cond.deadlock && !enabled {
            match model.terminal(&state) {
                Ok(true) => {}
                Ok(false) => return finish(Evidence::Trace(path(&nodes, cur), Claim::Deadlock), stats),
                Err(e) => return finish(Evidence::Trace(path(&nodes, cur), Claim::TerminalError(e)), stats),
            }
        }
    }

    stats.complete = true;
    // 証明書の状態集合は、符号化列を辞書順に整列した列とする（仕様書 §7.3）。
    let mut states: Vec<Vec<i64>> = nodes.into_iter().map(|n| n.state).collect();
    states.sort();
    finish(
        Evidence::Certificate(Certificate {
            conditions: cond.clone(),
            states,
        }),
        stats,
    )
}
