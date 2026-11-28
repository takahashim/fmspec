//! 詳細化の検査の探索器（docs/plans/refinement_symmetry_constants.md の2）。
//!
//! 具体モデルを幅優先で探索し、各状態を写像で写して、初期状態と各遷移を抽象モデルと照合する。
//! 最初に見つけた食い違いをトレースにし、見つからなければ訪問した状態の集合を証明書にする。
//! どちらも判定ゲート（`decide_refinement`）が検査し直すので、ここは未検証である。

use crate::bfs::{BfsOptions, Stats};
use crate::check::Internal;
use crate::inconsistency::{successors, Inconsistency};
use crate::stop::stopped;
use fmspec_core::kernel::checked::CheckedModel;
use fmspec_core::kernel::evidence::{Certificate, Claim, Limit, TraceStep};
use fmspec_core::kernel::evidence::{RefClaim, RefEvidence};
use fmspec_core::kernel::model::Expr;
use fmspec_core::kernel::refine::{
    decide_refinement, find_move_of, map_state_of, Mapped, Move, RefVerdict, RefVerdictOutcome,
};
use fmspec_core::kernel::semantics::Conditions;
use fmspec_core::kernel::step::Enumerated;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

/// 詳細化の検査結果の分類。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefStatus {
    /// 判定ゲートが証明書を受理した。
    Refines,
    /// 判定ゲートが、詳細化の破れるトレースを受理した。
    NotRefines,
    /// 判定ゲートが、写像か具体モデルの評価エラーに至るトレースを受理した。
    Error,
    /// 資源上限、中断、または抽象モデルの遷移列挙の失敗で、証拠を得られなかった。
    Inconclusive(Limit),
    /// 探索器が生成した証拠を判定ゲートが拒否したか、探索器の内部の不整合。fmspec の不具合を示す。
    InternalError(Internal),
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
    /// 初期状態からの遷移数。
    depth: usize,
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
) -> (Result<RefEvidence, Inconsistency>, Stats) {
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
            return (Ok(RefEvidence::Unavailable(Limit::MaxStates)), stats);
        }
        let x = match map_state_of(b, a, f, init) {
            Mapped::Ok(x) => x,
            Mapped::Fail(slot, kind) => {
                return (
                    Ok(RefEvidence::Trace(init.clone(), Vec::new(), RefClaim::Map(slot, kind))),
                    stats,
                )
            }
            Mapped::Arity => return (Ok(RefEvidence::Unavailable(Limit::Interrupted)), stats),
        };
        if !a.initials().contains(&x) {
            return (Ok(RefEvidence::Trace(init.clone(), Vec::new(), RefClaim::Init)), stats);
        }
        let id = nodes.len();
        nodes.push(Node {
            state: init.clone(),
            depth: 0,
            parent: None,
        });
        seen.insert(init.clone(), (id, x));
        stats.visited_states = seen.len();
        queue.push_back(id);
    }

    // 深さの上限で、未訪問の状態への遷移か、上限を超えるトレースの食い違いを残したか（`bfs` と同じ扱い）。
    let mut truncated = false;
    while let Some(cur) = queue.pop_front() {
        if let Some(limit) = stopped(opts.interrupt, opts.deadline) {
            return (Ok(RefEvidence::Unavailable(limit)), stats);
        }
        let state = nodes[cur].state.clone();
        let depth = nodes[cur].depth;
        let at_limit = opts.max_depth.is_some_and(|max| depth >= max);
        let x = seen[&state].1.clone();
        for ac in 0..b.n_actions() {
            if !cb.actions.get(ac).copied().unwrap_or(false) {
                continue;
            }
            let transitions = match successors(b, ac, &state) {
                Err(inconsistency) => return (Err(inconsistency), stats),
                Ok(Enumerated::Fail(args, site, kind)) => {
                    let (start, steps) = path(&nodes, cur);
                    let claim = RefClaim::Model(Claim::StepError(ac, args, site, kind));
                    return (Ok(RefEvidence::Trace(start, steps, claim)), stats);
                }
                Ok(Enumerated::Ok(ts)) => ts,
            };
            for t in transitions {
                stats.transitions += 1;
                let with_step = |nodes: &[Node], t: &fmspec_core::kernel::step::Transition| {
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
                    None => match map_state_of(b, a, f, &t.state) {
                        Mapped::Ok(y) => y,
                        Mapped::Fail(_, _) if at_limit => {
                            truncated = true;
                            continue;
                        }
                        Mapped::Fail(slot, kind) => {
                            let (start, steps) = with_step(&nodes, &t);
                            return (Ok(RefEvidence::Trace(start, steps, RefClaim::Map(slot, kind))), stats);
                        }
                        Mapped::Arity => return (Ok(RefEvidence::Unavailable(Limit::Interrupted)), stats),
                    },
                };
                match find_move_of(a, &x, &y) {
                    Move::Yes => {}
                    Move::No if at_limit => {
                        truncated = true;
                        continue;
                    }
                    Move::No => {
                        let (start, steps) = with_step(&nodes, &t);
                        return (Ok(RefEvidence::Trace(start, steps, RefClaim::Step)), stats);
                    }
                    Move::Unknown(_) => return (Ok(RefEvidence::Unavailable(Limit::AbstractFailed)), stats),
                }
                if seen.contains_key(&t.state) {
                    continue;
                }
                if at_limit {
                    truncated = true;
                    continue;
                }
                if opts.max_states.is_some_and(|max| seen.len() >= max) {
                    return (Ok(RefEvidence::Unavailable(Limit::MaxStates)), stats);
                }
                let id = nodes.len();
                seen.insert(t.state.clone(), (id, y));
                nodes.push(Node {
                    state: t.state,
                    depth: depth + 1,
                    parent: Some((cur, ac, t.args, t.output)),
                });
                stats.visited_states = seen.len();
                queue.push_back(id);
            }
        }
    }

    if truncated {
        return (Ok(RefEvidence::Unavailable(Limit::MaxDepth)), stats);
    }
    stats.complete = true;
    let mut states: Vec<Vec<i64>> = nodes.into_iter().map(|n| n.state).collect();
    states.sort();
    (
        Ok(RefEvidence::Certificate(Certificate {
            conditions: cb.clone(),
            states,
        })),
        stats,
    )
}

/// 判定ゲートの判定を、検査結果に分類する。
pub fn ref_status(verdict: &RefVerdict) -> RefStatus {
    match verdict.outcome() {
        RefVerdictOutcome::Refines => RefStatus::Refines,
        RefVerdictOutcome::NotRefines => RefStatus::NotRefines,
        RefVerdictOutcome::Error => RefStatus::Error,
        RefVerdictOutcome::Inconclusive(limit) => RefStatus::Inconclusive(limit),
        RefVerdictOutcome::Rejected(reject) => RefStatus::InternalError(Internal::Rejected(reject)),
        // 具体モデルと抽象モデルは検証済みなので、写像の式の数が違うときに限る。読み込みは写像の式の数を揃えるので、起きない。
        RefVerdictOutcome::InvalidModel => RefStatus::InternalError(Internal::InvalidMapping),
    }
}

/// 具体モデル `b` が、写像 `f` のもとで抽象モデル `a` を詳細化するかを検査する。
/// 探索器で証拠を作り、判定ゲートを通してから結果を返す。
pub fn refine(b: &CheckedModel, cb: &Conditions, a: &CheckedModel, f: &Vec<Expr>, opts: &BfsOptions) -> RefOutcome {
    let started = Instant::now();
    let (found, stats) = search(b, cb, a, f, opts);
    let search_time = started.elapsed();
    // 探索器の内部の不整合では、判定ゲートに証拠がないことを渡す。判定は Inconclusive で、分類を InternalError にする。
    let (evidence, inconsistency) = match found {
        Ok(evidence) => (evidence, None),
        Err(i) => (RefEvidence::Unavailable(Limit::Interrupted), Some(i)),
    };
    let started = Instant::now();
    let verdict = decide_refinement(b, cb, a, f, &evidence);
    let gate_time = started.elapsed();
    let status = match inconsistency {
        Some(i) => RefStatus::InternalError(Internal::Inconsistent(i)),
        None => ref_status(&verdict),
    };
    RefOutcome {
        status,
        verdict,
        evidence,
        stats,
        search_time,
        gate_time,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{refine, RefStatus};
    use crate::bfs::BfsOptions;
    use crate::check::Internal;
    use crate::inconsistency::tests::counter;
    use fmspec_core::kernel::refine::RefVerdictKind;
    use fmspec_ir::default_conditions;

    #[test]
    fn a_mapping_of_the_wrong_length_is_an_invalid_mapping_and_not_a_rejection() {
        let m = counter();
        let cond = default_conditions(&m, false);
        // 抽象モデルの状態のスロットは1つなので、式のない写像は数が合わない。
        let o = refine(m.checked(), &cond, m.checked(), &Vec::new(), &BfsOptions::default());
        assert_eq!(o.verdict.kind(), RefVerdictKind::InvalidModel);
        assert_eq!(o.status, RefStatus::InternalError(Internal::InvalidMapping));
    }
}
