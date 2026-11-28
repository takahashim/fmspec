//! 詳細化の検査（docs/ir.md の「詳細化」）。結果のJSONは `report::refine_report` が作る。

use crate::options::{bfs_options, options_only, select};
use crate::report;
use crate::Interrupt;
use fmspec_core::kernel::semantics::Conditions;
use fmspec_ir::{Model, Refinement};
use fmspec_search::refine as search_refine;
use serde_json::{Map, Value};

/// 詳細化の文書の概要。
pub fn describe_refinement(r: &Refinement) -> Value {
    report::describe_refinement(r)
}

/// 詳細化の検査条件。具体モデルの対象の操作だけを選ぶ。不変条件、遷移契約、デッドロックは検査しない。
fn ref_conditions(model: &Model, opts: &Map<String, Value>) -> Result<Conditions, String> {
    let mut c = Conditions {
        actions: vec![true; model.names.actions.len()],
        invariants: vec![false; model.names.invariants.len()],
        contracts: vec![false; model.names.contracts.len()],
        deadlock: false,
    };
    select(&mut c.actions, opts.get("actions"), "操作", |n| {
        model.names.action_index(n)
    })?;
    Ok(c)
}

/// 具体モデルが写像のもとで抽象モデルを詳細化するかを検査する。
///
/// オプションは、`actions`（具体モデルの対象の操作の名前の配列。省略時はすべて）、`max_states`、`max_depth`、`max_time_ms`。
/// 抽象モデルの操作は、すべてを照合に使う。検査しない検査条件（`invariants`、`contracts`、`deadlock`）は受け付けない。
pub fn refine(r: &Refinement, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options_only(opts, &["actions", "max_states", "max_depth", "max_time_ms"])?;
    let cond = ref_conditions(&r.concrete, map)?;
    let opts = bfs_options(map, interrupt, None)?;
    let outcome = search_refine(
        r.concrete.checked(),
        &cond,
        r.abstract_model.checked(),
        &r.mapping,
        &opts,
    );
    Ok(report::refine_report(r, &cond, &outcome))
}
