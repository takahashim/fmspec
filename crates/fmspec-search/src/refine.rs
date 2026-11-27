//! 詳細化の検査の探索器（docs/plans/refinement_symmetry_constants.md の2）。
//!
//! 具体モデルを幅優先で探索し、各状態を写像で写して、初期状態と各遷移を抽象モデルと照合する。
//! 最初に見つけた食い違いをトレースにし、見つからなければ訪問した状態の集合を証明書にする。
//! どちらも判定ゲート（`decide_refinement`）が検査し直すので、ここは未検証である。

use crate::bfs::{BfsOptions, Stats};
use fmspec_core::evidence::{Certificate, Claim, Limit, Reject, TraceStep};
use fmspec_core::gate::CheckedModel;
use fmspec_core::model::Expr;
use fmspec_core::refine::{
    decide_refinement, find_move, map_state, Mapped, Move, RefClaim, RefEvidence, RefVerdict, RefVerdictKind,
};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Enumerated;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

/// 詳細化の検査結果の分類。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefStatus {
    /// 判定ゲートが証明書を受理した。
    Refines,
    /// 判定ゲートが、詳細化の破れるトレースを受理した。
    NotRefines,
    /// 判定ゲートが、写像か具体モデルの評価エラーに至るトレースを受理した。
    Error,
    /// 資源上限、中断、または抽象モデルの遷移列挙の失敗で、証拠を得られなかった。
    Inconclusive(Limit),
    /// 探索器が生成した証拠を判定ゲートが拒否した。探索器の不具合を示す。
    InternalError(Reject),
}

pub struct RefOutcome {
    pub status: RefStatus,
    pub verdict: RefVerdict,
    pub evidence: RefEvidence,
    /// 探索器の報告。検査済みの値ではない。
    pub stats: Stats,
    pub search_time: Duration,
    pub gate_time: Duration,
}

struct Node {
    state: Vec<i64>,
    parent: Option<(usize, usize, Vec<i64>, Option<i64>)>,
}

fn path(nodes: &[Node], mut id: usize) -> (Vec<i64>, Vec<TraceStep>) {
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
    (nodes[id].state.clone(), steps)
}

/// 具体モデルを探索して、詳細化の証拠を作る。
fn search(
    b: &CheckedModel,
    cb: &Conditions,
    a: &CheckedModel,
    f: &Vec<Expr>,
    opts: &BfsOptions,
) -> (RefEvidence, Stats) {
    let (bm, am) = (b.raw(), a.raw());
    let mut stats = Stats::default();
    let mut nodes: Vec<Node> = Vec::new();
    // 状態から、節点の添字と、写した抽象モデルの状態へ。
    let mut seen: HashMap<Vec<i64>, (usize, Vec<i64>)> = HashMap::new();
    let mut queue: VecDeque<usize> = VecDeque::new();

    for init in b.initials() {
        if seen.contains_key(init) {
            continue;
        }
        if opts.max_states.is_some_and(|max| seen.len() >= max) {
            return (RefEvidence::Unavailable(Limit::MaxStates), stats);
        }
        let x = match map_state(bm, am, f, init) {
            Mapped::Ok(x) => x,
            Mapped::Fail(slot, kind) => {
                return (
                    RefEvidence::Trace(init.clone(), Vec::new(), RefClaim::Map(slot, kind)),
                    stats,
                )
            }
            Mapped::Arity => return (RefEvidence::Unavailable(Limit::Interrupted), stats),
        };
        if !a.initials().contains(&x) {
            return (RefEvidence::Trace(init.clone(), Vec::new(), RefClaim::Init), stats);
        }
        let id = nodes.len();
        nodes.push(Node {
            state: init.clone(),
            parent: None,
        });
        seen.insert(init.clone(), (id, x));
        stats.visited_states = seen.len();
        queue.push_back(id);
    }

    while let Some(cur) = queue.pop_front() {
        if opts.interrupt.is_some_and(|requested| requested()) {
            return (RefEvidence::Unavailable(Limit::Interrupted), stats);
        }
        let state = nodes[cur].state.clone();
        let x = seen[&state].1.clone();
        for ac in 0..bm.actions.len() {
            if !cb.actions.get(ac).copied().unwrap_or(false) {
                continue;
            }
            let transitions = match b.successors(ac, &state) {
                None => return (RefEvidence::Unavailable(Limit::Interrupted), stats),
                Some(Enumerated::Fail(args, site, kind)) => {
                    let (start, steps) = path(&nodes, cur);
                    let claim = RefClaim::Model(Claim::StepError(ac, args, site, kind));
                    return (RefEvidence::Trace(start, steps, claim), stats);
                }
                Some(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                stats.transitions += 1;
                let with_step = |nodes: &[Node], t: &fmspec_core::step::Transition| {
                    let (start, mut steps) = path(nodes, cur);
                    steps.push(TraceStep {
                        action: ac,
                        args: t.args.clone(),
                        output: t.output,
                        state: t.state.clone(),
                    });
                    (start, steps)
                };
                let y = match seen.get(&t.state) {
                    Some((_, y)) => y.clone(),
                    None => match map_state(bm, am, f, &t.state) {
                        Mapped::Ok(y) => y,
                        Mapped::Fail(slot, kind) => {
                            let (start, steps) = with_step(&nodes, &t);
                            return (RefEvidence::Trace(start, steps, RefClaim::Map(slot, kind)), stats);
                        }
                        Mapped::Arity => return (RefEvidence::Unavailable(Limit::Interrupted), stats),
                    },
                };
                match find_move(am, &x, &y) {
                    Move::Yes => {}
                    Move::No => {
                        let (start, steps) = with_step(&nodes, &t);
                        return (RefEvidence::Trace(start, steps, RefClaim::Step), stats);
                    }
                    Move::Unknown(_) => return (RefEvidence::Unavailable(Limit::AbstractFailed), stats),
                }
                if seen.contains_key(&t.state) {
                    continue;
                }
                if opts.max_states.is_some_and(|max| seen.len() >= max) {
                    return (RefEvidence::Unavailable(Limit::MaxStates), stats);
                }
                let id = nodes.len();
                seen.insert(t.state.clone(), (id, y));
                nodes.push(Node {
                    state: t.state,
                    parent: Some((cur, ac, t.args, t.output)),
                });
                stats.visited_states = seen.len();
                queue.push_back(id);
            }
        }
    }

    stats.complete = true;
    let mut states: Vec<Vec<i64>> = nodes.into_iter().map(|n| n.state).collect();
    states.sort();
    (
        RefEvidence::Certificate(Certificate {
            conditions: cb.clone(),
            states,
        }),
        stats,
    )
}

/// 判定ゲートの判定を、検査結果に分類する。
pub fn ref_status(verdict: &RefVerdict) -> RefStatus {
    match verdict.kind() {
        RefVerdictKind::Refines => RefStatus::Refines,
        RefVerdictKind::NotRefines => RefStatus::NotRefines,
        RefVerdictKind::Error => RefStatus::Error,
        RefVerdictKind::Inconclusive => RefStatus::Inconclusive(verdict.limit().unwrap_or(Limit::Interrupted)),
        RefVerdictKind::Rejected => RefStatus::InternalError(verdict.reject().unwrap_or(Reject::ClaimNotReproduced)),
        // 読み込みは写像の式の数を揃えるので、ここには来ない。
        RefVerdictKind::InvalidModel => RefStatus::InternalError(Reject::ClaimNotReproduced),
    }
}

/// 具体モデル `b` が、写像 `f` のもとで抽象モデル `a` を詳細化するかを検査する。
/// 探索器で証拠を作り、判定ゲートを通してから結果を返す。
pub fn refine(b: &CheckedModel, cb: &Conditions, a: &CheckedModel, f: &Vec<Expr>, opts: &BfsOptions) -> RefOutcome {
    let started = Instant::now();
    let (evidence, stats) = search(b, cb, a, f, opts);
    let search_time = started.elapsed();
    let started = Instant::now();
    let verdict = decide_refinement(b, cb, a, f, &evidence);
    let gate_time = started.elapsed();
    RefOutcome {
        status: ref_status(&verdict),
        verdict,
        evidence,
        stats,
        search_time,
        gate_time,
    }
}
