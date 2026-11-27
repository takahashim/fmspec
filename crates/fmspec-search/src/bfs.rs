//! 幅優先探索（仕様書 §8.1）。
//!
//! 初期状態は与えられた順に起点とし、操作は定義順、引数は辞書順に列挙する。したがって、状態不変条件の違反は遷移回数が最小の
//! トレースで見つかり、同じ長さのトレースのうちでは、この列挙順で最初に見つかるものを返す。
//!
//! 深さの上限 `max_depth` を指定すると、深さ（初期状態からの遷移数）が上限の状態からは新たな状態を訪問しない。
//! 上限の深さの状態からも遷移は列挙し、遷移の評価エラーとデッドロック（終端条件の評価エラーを含む。どちらもトレースは
//! 上限以下のステップ）は報告する。その遷移が未訪問の状態に至るか、遷移契約を満たさないか、遷移契約の評価がエラーになる
//! （トレースが上限を超える）ときは、報告せずに打ち切りを記録し（未訪問の遷移先の不変条件は評価しない）、
//! 探索の終わりに証明書の代わりに `Unavailable(MaxDepth)` を返す。網羅していない探索の状態集合は証明書にしない。

use crate::claim::{contract_claim, deadlock_claim, invariant_claim, selected};
use crate::inconsistency::{successors, Inconsistency};
use crate::stop::stopped;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, TraceStep};
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use hashbrown::HashTable;
use rustc_hash::FxBuildHasher;
use std::collections::VecDeque;
use std::hash::BuildHasher;
use std::time::Instant;

#[derive(Default)]
pub struct BfsOptions<'a> {
    /// 保持する異なる状態の数の上限。初期状態を含む。
    pub max_states: Option<usize>,
    /// 中断要求の問い合わせ。真を返したら探索を打ち切る。証明書の検査の途中でも確かめる。
    pub interrupt: Option<&'a dyn Fn() -> bool>,
    /// 判定ゲートが証拠の検査にかける評価回数の上限（`evidence_cost` の見積もり）。
    pub max_check_cost: Option<u64>,
    /// 深さ（初期状態からの遷移数）の上限。報告するトレースのステップ数は、この上限以下である。
    pub max_depth: Option<usize>,
    /// 時間の上限の時刻。探索の状態ごとと、証明書の検査の区切りごとに確かめる。
    pub deadline: Option<Instant>,
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
    /// 生成した証拠。探索器の内部の不整合を見つけたら、証拠の代わりに不整合（`Err`）。
    pub evidence: Result<Evidence, Inconsistency>,
    pub stats: Stats,
}

struct Node {
    state: Vec<i64>,
    /// 初期状態からの遷移数。
    depth: usize,
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
    search(model, cond, opts, |a, s| successors(model, a, s))
}

/// `bfs` の本体。遷移の列挙 `successors` を引数に取るのは、列挙の不整合を探索が返すことをテストするためである。
fn search<F>(model: &CheckedModel, cond: &Conditions, opts: &BfsOptions, successors: F) -> SearchResult
where
    F: Fn(usize, &Vec<i64>) -> Result<Enumerated, Inconsistency>,
{
    let n_actions = model.raw().actions.len();
    let mut stats = Stats::default();
    let mut nodes: Vec<Node> = Vec::new();
    let mut visited = Visited::default();
    let mut queue: VecDeque<usize> = VecDeque::new();

    let finish = |evidence: Evidence, stats: Stats| SearchResult {
        evidence: Ok(evidence),
        stats,
    };
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
            depth: 0,
            parent: None,
        };
        let id = visited.push(&mut nodes, hash, node);
        stats.visited_states = visited.len();
        if let Some(claim) = invariant_claim(model, cond, init) {
            return finish(trace(&nodes, id, claim), stats);
        }
        queue.push_back(id);
    }

    // 深さの上限で、未訪問の状態への遷移か、上限を超えるトレースの違反を残したか。
    let mut truncated = false;
    while let Some(cur) = queue.pop_front() {
        if let Some(limit) = stopped(opts.interrupt, opts.deadline) {
            return finish(Evidence::Unavailable(limit), stats);
        }
        let state = nodes[cur].state.clone();
        let depth = nodes[cur].depth;
        // 上限の深さの状態からの遷移は、トレースを上限より長くする。
        let at_limit = opts.max_depth.is_some_and(|max| depth >= max);
        let mut enabled = false;
        for a in 0..n_actions {
            if !selected(&cond.actions, a) {
                continue;
            }
            let transitions = match successors(a, &state) {
                // 訪問済みの状態は型に従い、操作の添字は範囲内なので、ここには来ないはずである。
                // 来たら中断とは報告せず、不整合として返す。
                Err(inconsistency) => {
                    return SearchResult {
                        evidence: Err(inconsistency),
                        stats,
                    }
                }
                Ok(Enumerated::Fail(args, site, kind)) => {
                    return finish(trace(&nodes, cur, Claim::StepError(a, args, site, kind)), stats);
                }
                Ok(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                enabled = true;
                stats.transitions += 1;
                // 上限の深さの状態からの遷移は、何も報告せず、打ち切りを記録するだけである。
                // 打ち切りが決まっていれば、遷移契約と訪問済みかを確かめる必要はない。
                if at_limit && truncated {
                    continue;
                }
                if let Some(claim) = contract_claim(model, cond, a, &state, &t.args, &t.state, &t.output) {
                    if at_limit {
                        truncated = true;
                        continue;
                    }
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
                if at_limit {
                    truncated = true;
                    continue;
                }
                if full(&visited) {
                    return finish(Evidence::Unavailable(Limit::MaxStates), stats);
                }
                let violation = invariant_claim(model, cond, &t.state);
                let node = Node {
                    state: t.state,
                    depth: depth + 1,
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

    if truncated {
        return finish(Evidence::Unavailable(Limit::MaxDepth), stats);
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

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{bfs, search, BfsOptions};
    use crate::inconsistency::tests::counter;
    use crate::inconsistency::{successors, Inconsistency};
    use fmspec_core::evidence::Evidence;
    use fmspec_ir::default_conditions;

    #[test]
    fn an_inconsistent_enumeration_is_returned_instead_of_evidence() {
        let m = counter();
        let cond = default_conditions(&m, false);
        // 状態 x = 2 で、列挙が状態を受け付けなかったものとする。
        let found = search(m.checked(), &cond, &BfsOptions::default(), |a, s| {
            if s == &vec![2] {
                Err(Inconsistency::Successors {
                    action: a,
                    state: s.clone(),
                })
            } else {
                successors(m.checked(), a, s)
            }
        });
        assert_eq!(
            found.evidence.err(),
            Some(Inconsistency::Successors {
                action: 0,
                state: vec![2]
            })
        );
        assert!(!found.stats.complete);
        assert_eq!(found.stats.visited_states, 3);
    }

    #[test]
    fn a_consistent_search_returns_evidence() {
        let m = counter();
        let found = bfs(m.checked(), &default_conditions(&m, false), &BfsOptions::default());
        assert!(matches!(found.evidence, Ok(Evidence::Certificate(_))));
        assert!(found.stats.complete);
    }
}
