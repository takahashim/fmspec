//! 到達可能な状態と遷移のグラフ（仕様書 §11.3）。
//!
//! Model-Based Testing のカバレッジの分母と、テスト経路の生成に使う。
//! 探索の順序は幅優先探索（`bfs`）と同じで、初期状態は与えられた順、操作は定義順、引数は辞書順である。
//! 性質は検査しない。モデルの検査は `check` が判定ゲートを通して行う。

use crate::claim::selected;
use crate::inconsistency::{successors, Inconsistency};
use fmspec_core::gate::CheckedModel;
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use std::collections::HashMap;

/// 有効な遷移。`to` は遷移先の状態の添字で、状態数の上限で保持しなかった状態なら `None`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge {
    pub from: usize,
    pub action: usize,
    pub args: Vec<i64>,
    pub output: Option<i64>,
    pub to: Option<usize>,
}

pub struct Graph {
    /// 状態。幅優先探索で訪問した順に並ぶ。
    pub states: Vec<Vec<i64>>,
    pub index: HashMap<Vec<i64>, usize>,
    /// 各状態に最初に到達した遷移（`edges` の添字）。初期状態は `None`。
    pub parent: Vec<Option<usize>>,
    /// 遷移。遷移元の訪問順、操作の定義順、引数の辞書順に並ぶ。
    pub edges: Vec<Edge>,
    /// 到達できるすべての状態と遷移を集めたか。状態数の上限、評価エラー、中断、内部の不整合で集めきれなければ偽。
    pub complete: bool,
    /// 探索器の内部の不整合。見つけたら探索をやめる。このグラフをカバレッジの分母やテスト経路に使ってはならない。
    pub inconsistency: Option<Inconsistency>,
}

/// 到達可能な状態と遷移を集める。評価エラーになる遷移は集めない。
pub fn explore(
    model: &CheckedModel,
    cond: &Conditions,
    max_states: Option<usize>,
    interrupt: Option<&dyn Fn() -> bool>,
) -> Graph {
    collect(model, cond, max_states, interrupt, |a, s| successors(model, a, s))
}

/// `explore` の本体。遷移の列挙 `successors` を引数に取るのは、列挙の不整合を記録することをテストするためである。
fn collect<F>(
    model: &CheckedModel,
    cond: &Conditions,
    max_states: Option<usize>,
    interrupt: Option<&dyn Fn() -> bool>,
    successors: F,
) -> Graph
where
    F: Fn(usize, &Vec<i64>) -> Result<Enumerated, Inconsistency>,
{
    let mut g = Graph {
        states: Vec::new(),
        index: HashMap::new(),
        parent: Vec::new(),
        edges: Vec::new(),
        complete: true,
        inconsistency: None,
    };
    let full = |g: &Graph| max_states.is_some_and(|max| g.states.len() >= max);
    for init in model.initials() {
        if g.index.contains_key(init) {
            continue;
        }
        if full(&g) {
            g.complete = false;
            break;
        }
        g.add(init.clone(), None);
    }
    let mut cur = 0;
    while cur < g.states.len() {
        if interrupt.is_some_and(|requested| requested()) {
            g.complete = false;
            return g;
        }
        let state = g.states[cur].clone();
        for a in 0..model.raw().actions.len() {
            if !selected(&cond.actions, a) {
                continue;
            }
            let ts = match successors(a, &state) {
                Ok(Enumerated::Ok(ts)) => ts,
                // 評価エラーになる遷移は集めず、残りの遷移を集める。
                Ok(Enumerated::Fail(..)) => {
                    g.complete = false;
                    continue;
                }
                // 集めた状態は型に従い、操作の添字は範囲内なので、ここには来ないはずである。
                // 来たら、評価エラーと区別して記録し、探索をやめる。
                Err(inconsistency) => {
                    g.complete = false;
                    g.inconsistency = Some(inconsistency);
                    return g;
                }
            };
            for t in ts {
                let to = match g.index.get(&t.state) {
                    Some(id) => Some(*id),
                    None if full(&g) => {
                        g.complete = false;
                        None
                    }
                    None => {
                        let parent = g.edges.len();
                        Some(g.add(t.state, Some(parent)))
                    }
                };
                g.edges.push(Edge {
                    from: cur,
                    action: a,
                    args: t.args,
                    output: t.output,
                    to,
                });
            }
        }
        cur += 1;
    }
    g
}

/// 遷移の引数の列から、入力（公開引数と、注入する選択の値）を取り出す。
/// `injected` は操作ごとの、注入する選択の引数の列での添字である。
pub fn input_of(model: &CheckedModel, injected: &[Vec<usize>], action: usize, args: &[i64]) -> Vec<i64> {
    let n = model.raw().actions[action].n_params.min(args.len());
    let mut input = args[..n].to_vec();
    if let Some(slots) = injected.get(action) {
        input.extend(slots.iter().filter_map(|i| args.get(*i)));
    }
    input
}

impl Graph {
    /// 未訪問の状態を加え、その添字を返す。`parent` は最初に到達した遷移（`edges` の添字）である。
    fn add(&mut self, state: Vec<i64>, parent: Option<usize>) -> usize {
        let id = self.states.len();
        self.index.insert(state.clone(), id);
        self.states.push(state);
        self.parent.push(parent);
        id
    }

    /// 初期状態から状態 `id` までの、最初に到達した遷移の列（`edges` の添字）。
    pub fn path_to(&self, mut id: usize) -> Vec<usize> {
        let mut path = Vec::new();
        while let Some(e) = self.parent[id] {
            path.push(e);
            id = self.edges[e].from;
        }
        path.reverse();
        path
    }

    /// 状態 `id` に至る経路の起点の初期状態。
    pub fn root(&self, mut id: usize) -> usize {
        while let Some(e) = self.parent[id] {
            id = self.edges[e].from;
        }
        id
    }
}

/// テスト経路。起点の初期状態と、入力（操作と、公開引数に注入する選択の値を続けた列）の列。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestPath {
    pub start: usize,
    pub inputs: Vec<(usize, Vec<i64>)>,
}

/// テスト経路で覆う対象。状態と入力の組と、その最初の遷移の遷移先。
struct Target {
    from: usize,
    action: usize,
    input: Vec<i64>,
    to: usize,
}

pub struct Paths {
    pub graph: Graph,
    pub paths: Vec<TestPath>,
    /// 経路で覆う対象の数。状態と入力の組で、有効な遷移があるもの。
    pub targets: usize,
    /// 経路が覆った対象の数。
    pub covered: usize,
}

/// 到達可能な状態と入力の組を覆うテスト経路を作る。
///
/// まだ覆っていない組を探索順に1つずつ取り、その遷移元への最短の経路にその入力を続ける。
/// さらに、遷移先から覆っていない組を貪欲にたどって延ばす。各経路は `max_steps` 入力以下である。
/// 入力に複数の遷移がある組（注入しない内部選択がある操作など）では、最初に列挙した遷移の遷移先をたどる。
pub fn test_paths(
    model: &CheckedModel,
    cond: &Conditions,
    injected: &[Vec<usize>],
    max_states: Option<usize>,
    max_steps: usize,
    interrupt: Option<&dyn Fn() -> bool>,
) -> Paths {
    let graph = explore(model, cond, max_states, interrupt);
    // 状態と入力の組ごとに、最初の遷移。`target_of` は、各遷移の組（`targets` の添字）である。
    let mut targets: Vec<Target> = Vec::new();
    let mut target_of: Vec<Option<usize>> = vec![None; graph.edges.len()];
    let mut seen: HashMap<(usize, usize, Vec<i64>), usize> = HashMap::new();
    let mut by_state: Vec<Vec<usize>> = vec![Vec::new(); graph.states.len()];
    for (i, e) in graph.edges.iter().enumerate() {
        let Some(to) = e.to else { continue };
        let input = input_of(model, injected, e.action, &e.args);
        let k = *seen.entry((e.from, e.action, input.clone())).or_insert_with(|| {
            by_state[e.from].push(targets.len());
            targets.push(Target {
                from: e.from,
                action: e.action,
                input,
                to,
            });
            targets.len() - 1
        });
        target_of[i] = Some(k);
    }
    let mut covered = vec![false; targets.len()];
    let mut paths = Vec::new();
    for t in 0..targets.len() {
        if covered[t] {
            continue;
        }
        let prefix = graph.path_to(targets[t].from);
        if prefix.len() + 1 > max_steps {
            continue;
        }
        // 最初に到達した遷移は遷移先を持つので、その組がある。
        let mut inputs = Vec::new();
        for k in prefix.into_iter().filter_map(|e| target_of[e]) {
            covered[k] = true;
            inputs.push((targets[k].action, targets[k].input.clone()));
        }
        let mut next = Some(t);
        while let Some(k) = next {
            covered[k] = true;
            let target = &targets[k];
            inputs.push((target.action, target.input.clone()));
            next = if inputs.len() < max_steps {
                by_state[target.to].iter().copied().find(|j| !covered[*j])
            } else {
                None
            };
        }
        paths.push(TestPath {
            start: graph.root(targets[t].from),
            inputs,
        });
    }
    let n = targets.len();
    let done = covered.iter().filter(|c| **c).count();
    Paths {
        graph,
        paths,
        targets: n,
        covered: done,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{collect, explore};
    use crate::inconsistency::tests::counter;
    use crate::inconsistency::{successors, Inconsistency};
    use fmspec_ir::default_conditions;

    #[test]
    fn an_inconsistent_enumeration_is_recorded_and_stops_the_exploration() {
        let m = counter();
        let cond = default_conditions(&m, false);
        let g = collect(m.checked(), &cond, None, None, |a, s| {
            if s == &vec![1] {
                Err(Inconsistency::Successors {
                    action: a,
                    state: s.clone(),
                })
            } else {
                successors(m.checked(), a, s)
            }
        });
        assert!(!g.complete);
        assert_eq!(
            g.inconsistency,
            Some(Inconsistency::Successors {
                action: 0,
                state: vec![1]
            })
        );
        assert_eq!(g.states, vec![vec![0], vec![1]]);
    }

    #[test]
    fn a_consistent_exploration_records_no_inconsistency() {
        let m = counter();
        let g = explore(m.checked(), &default_conditions(&m, false), None, None);
        assert!(g.complete);
        assert_eq!(g.inconsistency, None);
        assert_eq!(g.states.len(), 4);
    }
}
