//! 幅優先探索（仕様書 §8.1）。
//!
//! 初期状態は与えられた順に起点とし、操作は定義順、引数は辞書順に列挙する。したがって、状態不変条件の違反は遷移回数が最小の
//! トレースで見つかり、同じ長さのトレースのうちでは、この列挙順で最初に見つかるものを返す。

use crate::claim::{contract_claim, deadlock_claim, invariant_claim, selected};
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use hashbrown::HashTable;
use rustc_hash::FxBuildHasher;
use std::collections::VecDeque;
use std::hash::BuildHasher;

#[derive(Default)]
pub struct BfsOptions<'a> {
    /// 保持する異なる状態の数の上限。初期状態を含む。
    pub max_states: Option<usize>,
    /// 中断要求の問い合わせ。真を返したら探索を打ち切る。証明書の検査の途中でも確かめる。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
    /// 判定ゲートが証拠の検査にかける評価回数の上限（`gate::evidence_cost` の見積もり）。
    pub max_check_cost: Option<u64>,
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
    /// 親からの遷移。初期状態は `None`。
    parent: Option<Parent>,
}

/// 親の節点と、親からの遷移。
struct Parent {
    node: usize,
    action: usize,
    args: Vec<i64>,
    output: Option<i64>,
}

fn hash_state(s: &[i64]) -> u64 {
    FxBuildHasher.hash_one(s)
}

/// 訪問済みの状態の集合。状態は節点の列 `nodes` にだけ置き、表には節点の添字を入れる。
/// 同じハッシュ値の状態は、符号化列の一致で確かめる。ハッシュ値だけで状態を同一視しない。
/// 状態のハッシュ値は呼び出し元が `hash_state` で一度だけ計算し、問い合わせと追加の両方に渡す。
#[derive(Default)]
struct Visited {
    table: HashTable<usize>,
}

impl Visited {
    fn len(&self) -> usize {
        self.table.len()
    }

    /// ハッシュ値 `hash` の状態 `s` を訪問済みか。
    fn contains(&self, nodes: &[Node], hash: u64, s: &[i64]) -> bool {
        self.table.find(hash, |&id| nodes[id].state == s).is_some()
    }

    /// 節点を加え、その添字を返す。呼び出し元は、`hash` が節点の状態のハッシュ値で、その状態が未訪問であることを確かめておく。
    fn push(&mut self, nodes: &mut Vec<Node>, hash: u64, node: Node) -> usize {
        let id = nodes.len();
        nodes.push(node);
        self.table.insert_unique(hash, id, |&j| hash_state(&nodes[j].state));
        id
    }
}

/// 初期状態から `id` の状態までのトレースを復元し、主張を付けて証拠にする。
fn trace(nodes: &[Node], id: usize, claim: Claim) -> Evidence {
    let (start, steps) = path(nodes, id);
    Evidence::Trace(start, steps, claim)
}

/// 初期状態から `id` の状態までの開始状態とステップを復元する。
fn path(nodes: &[Node], mut id: usize) -> (Vec<i64>, Vec<TraceStep>) {
    let mut steps = Vec::new();
    while let Some(parent) = &nodes[id].parent {
        steps.push(TraceStep {
            action: parent.action,
            args: parent.args.clone(),
            output: parent.output,
            state: nodes[id].state.clone(),
        });
        id = parent.node;
    }
    steps.reverse();
    (nodes[id].state.clone(), steps)
}

/// 幅優先探索で証拠を生成する。
pub fn bfs(model: &CheckedModel, cond: &Conditions, opts: &BfsOptions) -> SearchResult {
    let n_actions = model.raw().actions.len();
    let mut stats = Stats::default();
    let mut nodes: Vec<Node> = Vec::new();
    let mut visited = Visited::default();
    let mut queue: VecDeque<usize> = VecDeque::new();

    let finish = |evidence: Evidence, stats: Stats| SearchResult { evidence, stats };
    let full = |visited: &Visited| opts.max_states.is_some_and(|max| visited.len() >= max);

    // 初期状態は、与えられた順に探索の起点にする。
    for init in model.initials() {
        let hash = hash_state(init);
        if visited.contains(&nodes, hash, init) {
            continue;
        }
        if full(&visited) {
            return finish(Evidence::Unavailable(Limit::MaxStates), stats);
        }
        let node = Node {
            state: init.clone(),
            parent: None,
        };
        let id = visited.push(&mut nodes, hash, node);
        stats.visited_states = visited.len();
        if let Some(claim) = invariant_claim(model, cond, init) {
            return finish(trace(&nodes, id, claim), stats);
        }
        queue.push_back(id);
    }

    while let Some(cur) = queue.pop_front() {
        if opts.interrupt.is_some_and(|requested| requested()) {
            return finish(Evidence::Unavailable(Limit::Interrupted), stats);
        }
        let state = nodes[cur].state.clone();
        let mut enabled = false;
        for a in 0..n_actions {
            if !selected(&cond.actions, a) {
                continue;
            }
            let transitions = match model.successors(a, &state) {
                // 訪問済みの状態は型に従い、操作の添字は範囲内なので、ここには来ない。
                None => return finish(Evidence::Unavailable(Limit::Interrupted), stats),
                Some(Enumerated::Fail(args, site, kind)) => {
                    return finish(trace(&nodes, cur, Claim::StepError(a, args, site, kind)), stats);
                }
                Some(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                enabled = true;
                stats.transitions += 1;
                if let Some(claim) = contract_claim(model, cond, a, &state, &t.args, &t.state, &t.output) {
                    let (start, mut steps) = path(&nodes, cur);
                    steps.push(TraceStep {
                        action: a,
                        args: t.args,
                        output: t.output,
                        state: t.state,
                    });
                    return finish(Evidence::Trace(start, steps, claim), stats);
                }
                let hash = hash_state(&t.state);
                if visited.contains(&nodes, hash, &t.state) {
                    continue;
                }
                if full(&visited) {
                    return finish(Evidence::Unavailable(Limit::MaxStates), stats);
                }
                let violation = invariant_claim(model, cond, &t.state);
                let node = Node {
                    state: t.state,
                    parent: Some(Parent {
                        node: cur,
                        action: a,
                        args: t.args,
                        output: t.output,
                    }),
                };
                let id = visited.push(&mut nodes, hash, node);
                stats.visited_states = visited.len();
                if let Some(claim) = violation {
                    return finish(trace(&nodes, id, claim), stats);
                }
                queue.push_back(id);
            }
        }
        if cond.deadlock && !enabled {
            if let Some(claim) = deadlock_claim(model, &state) {
                return finish(trace(&nodes, cur, claim), stats);
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
