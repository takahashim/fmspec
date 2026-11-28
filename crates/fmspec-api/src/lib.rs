//! fmspec のJSONレベルのAPI（仕様書 §3.2）。
//!
//! モデル、検査のオプション、証拠、結果を、いずれもJSONで受け渡す。
//! CLIとnative extensionは同じ関数を呼ぶので、交換形式とそのテストを共有できる。
//!
//! 結果の形式は docs/ir.md にある。オプションの誤り（未定義の名前、未知のキーなど）は `Err` で返す。

mod coverage;
mod human;
mod inject;
mod options;
mod refine;
mod report;
mod session;

use fmspec_core::kernel::evidence::Evidence;
use fmspec_core::kernel::gate::decide;
use fmspec_core::kernel::gate::VerdictKind;
use fmspec_ir::{read_certificate, read_trace, LoadError};
use fmspec_search::{
    check as search_check, check_sym, judge, sample, shrink as search_shrink, ShrinkOptions, SimOptions,
};
use options::{
    bfs_options, conditions, count, deadline, flag, gate_options, optional_flag, options_only, options_with_conditions,
    size, trace_gate_options,
};
use report::{CheckOutputs, Judged, Provenance, ShrinkSummary};
use serde_json::{json, Value};
use std::time::Instant;

pub use coverage::{coverage, test_paths};
pub use fmspec_ir::{load, load_refinement, Model, Refinement};
pub use human::human;
pub use refine::{describe_refinement, refine};
pub use session::Session;

/// 中断要求の問い合わせ。真を返したら、探索か証明書の検査を打ち切って `inconclusive` を返す。
pub type Interrupt<'a> = Option<&'a dyn Fn() -> bool>;

/// 結果をJSON文字列にする。オプションの誤りは、結果と同じ形（`status` が `usage_error`）で表す。
pub fn to_text(result: Result<Value, String>) -> String {
    match result {
        Ok(body) => body.to_string(),
        Err(message) => report::usage_error(&message).to_string(),
    }
}

/// モデルの概要。IR検証を通ったことの報告に使う。
pub fn describe(model: &Model) -> Value {
    report::describe(model)
}

/// IRを読み込めなかったことの報告。
pub fn load_error(e: &LoadError) -> Value {
    json!({"status": "invalid_model", "message": e.to_string()})
}

/// 幅優先探索でモデルを検査する。
///
/// オプションは、検査条件（`actions`、`invariants`、`contracts`、`deadlock`）、`max_states`、
/// `max_depth`（深さ、つまり初期状態からの遷移数の上限）、`max_time_ms`（探索と証拠の検査の時間の上限）、
/// `max_check_cost`（判定ゲートが証拠の検査にかける評価回数の上限）、
/// `certificate`（真なら、受理された証明書を結果に含める）。
pub fn check(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options_with_conditions(
        opts,
        &[
            "max_states",
            "max_depth",
            "max_time_ms",
            "max_check_cost",
            "certificate",
            "symmetry",
        ],
    )?;
    let cond = conditions(model, map)?;
    let symmetry = optional_flag(map, "symmetry")?;
    let use_symmetry = !model.names.symmetry.is_empty() && symmetry != Some(false);
    let max_check_cost = count(map, "max_check_cost", 0)?;
    // オプションの誤りは、探索を始める前にすべて見つける。
    let want_certificate = flag(map, "certificate")?;
    let opts = bfs_options(map, interrupt, max_check_cost)?;
    let outcome = if use_symmetry {
        if max_check_cost.is_some() || want_certificate {
            return Err("対称性による削減を使う検査では、max_check_cost と certificate を指定できません".to_string());
        }
        check_sym(model.checked(), &cond, &model.names.symmetry, &opts).map_err(|i| {
            format!(
                "宣言した対称性が成り立ちません（{}番目の入れ替え）。ブロックを入れ替えると、モデルの操作、不変条件、遷移契約、終端条件が対応しません",
                i + 1
            )
        })?
    } else {
        search_check(model.checked(), &cond, &opts)
    };
    let outputs = CheckOutputs {
        symmetry: use_symmetry,
        certificate: want_certificate,
    };
    Ok(report::check_report(model, &cond, &outcome, outputs))
}

/// ランダムシミュレーションでモデルを検査する。
///
/// オプションは、検査条件、`seed`（既定は0）、`traces`（既定は100）、`max_steps`（既定は100）、`max_time_ms`。
pub fn simulate(model: &Model, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options_with_conditions(opts, &["seed", "traces", "max_steps", "max_time_ms"])?;
    let cond = conditions(model, map)?;
    let seed = count(map, "seed", 0)?.unwrap_or(0);
    let traces = count(map, "traces", 1)?.unwrap_or(100);
    let max_steps = count(map, "max_steps", 0)?.unwrap_or(100);
    let sim = SimOptions {
        seed,
        traces: size(traces),
        max_steps: size(max_steps),
        interrupt,
        deadline: deadline(map)?,
    };
    let started = Instant::now();
    let sampled = sample(model.checked(), &cond, &sim);
    Ok(report::simulation_report(
        model,
        &cond,
        &sim,
        &sampled,
        started.elapsed(),
    ))
}

/// 別のモデルに対する証拠を読むことを許すオプション（仕様書 §10）。
const ALLOW_OTHER_MODEL: &str = "allow_other_model";

/// 提示された証明書を、オプションの検査条件で検査する。
///
/// オプションは、検査条件、`max_check_cost`、`max_time_ms`、`allow_other_model`（真なら、`model_digest` が違う証明書も、
/// このモデルの名前と型で読んで検査する。省略時は偽で、別のモデルに対する証明書は読めない証拠として拒否する）。
pub fn verify_certificate(
    model: &Model,
    certificate: &str,
    opts: &Value,
    interrupt: Interrupt,
) -> Result<Value, String> {
    let map = options_with_conditions(opts, &["max_check_cost", "max_time_ms", ALLOW_OTHER_MODEL])?;
    let cond = conditions(model, map)?;
    let gate = gate_options(map, interrupt, deadline(map)?)?;
    let loaded = match read_certificate(model, certificate, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => loaded,
        Err(e) => return Ok(report::unreadable_evidence(model, &e)),
    };
    let (verdict, evidence) = judge(model.checked(), &cond, Evidence::Certificate(loaded.evidence), &gate);
    let provenance = Provenance {
        seed: None,
        other_model_digest: loaded.other_model_digest,
    };
    let judged = Judged {
        cond: &cond,
        evidence: &evidence,
        verdict: &verdict,
    };
    Ok(report::evidence_report(model, &judged, &provenance))
}

/// 提示されたトレースを、トレースに記録された検査条件で再生する。`replay_with` をオプションなしで呼ぶのと同じ。
pub fn replay(model: &Model, trace: &str) -> Value {
    // オプションが空なので、誤りにはならない。
    replay_with(model, trace, &json!({})).unwrap_or_else(|message| report::usage_error(&message))
}

/// 提示されたトレースを、トレースに記録された検査条件で再生する。
///
/// オプションは `max_check_cost`（判定ゲートがトレースの検査にかける評価回数の上限。見積もりが超えれば検査せずに
/// `inconclusive` とする）と `allow_other_model`（`verify_certificate` と同じ）。
/// 判定ゲートはトレースを区切らずに検査するので、時間の上限と中断要求は受け付けない。
pub fn replay_with(model: &Model, trace: &str, opts: &Value) -> Result<Value, String> {
    let map = options_only(opts, &["max_check_cost", ALLOW_OTHER_MODEL])?;
    let gate = trace_gate_options(map)?;
    let loaded = match read_trace(model, trace, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => loaded,
        Err(e) => return Ok(report::unreadable_evidence(model, &e)),
    };
    let trace = loaded.evidence;
    let cond = trace.conditions.clone();
    let evidence = Evidence::Trace(trace.start, trace.steps, trace.claim);
    let (verdict, evidence) = judge(model.checked(), &cond, evidence, &gate);
    let provenance = Provenance {
        seed: trace.seed,
        other_model_digest: loaded.other_model_digest,
    };
    let judged = Judged {
        cond: &cond,
        evidence: &evidence,
        verdict: &verdict,
    };
    Ok(report::evidence_report(model, &judged, &provenance))
}

/// 縮小で試す候補の数の、既定の上限。
const DEFAULT_SHRINK_ATTEMPTS: u64 = 10_000;

/// モデル違反のトレースを縮小する（仕様書 §10）。
///
/// 元のトレースを判定ゲートが受理しなければ、その拒否を報告する。
/// ステップの削除と、引数（公開引数と内部選択）を小さくする変更を試す。
/// 縮小結果は判定ゲートが同じ主張で受理したトレースで、元のステップ数を `original_steps` に、
/// 縮小器の報告（試した候補の数と、打ち切ったか）を `shrink` に記録する。
/// オプションは `attempts`（試す候補の数の上限。削除と引数の変更で共有する）、`max_time_ms`（縮小の時間の上限）、
/// `max_check_cost`（判定ゲートが元のトレースの検査にかける評価回数の上限。候補は元のトレースより長くないので、
/// 候補の検査の見積もりも上限を超えない）、`allow_other_model`（`verify_certificate` と同じ）。
/// 時間の上限か中断要求に達したら縮小を打ち切り、それまでに判定ゲートが受理した候補を返す
/// （`shrink.limit` は `max_time_ms` か `interrupted`）。
pub fn shrink(model: &Model, trace: &str, opts: &Value, interrupt: Interrupt) -> Result<Value, String> {
    let map = options_only(opts, &["attempts", "max_time_ms", "max_check_cost", ALLOW_OTHER_MODEL])?;
    let attempts = count(map, "attempts", 1)?.unwrap_or(DEFAULT_SHRINK_ATTEMPTS);
    let deadline = deadline(map)?;
    let gate = trace_gate_options(map)?;
    let loaded = match read_trace(model, trace, flag(map, ALLOW_OTHER_MODEL)?) {
        Ok(loaded) => loaded,
        Err(e) => return Ok(report::unreadable_evidence(model, &e)),
    };
    let trace = loaded.evidence;
    let provenance = Provenance {
        seed: trace.seed,
        other_model_digest: loaded.other_model_digest,
    };
    let cond = &trace.conditions;
    // 元のトレースを判定ゲートに渡す。縮小の起点に使うので、トレースの部分は手元に残す。
    let evidence = Evidence::Trace(trace.start.clone(), trace.steps.clone(), trace.claim.clone());
    let (verdict, evidence) = judge(model.checked(), cond, evidence, &gate);
    if !matches!(verdict.kind(), VerdictKind::Violated | VerdictKind::Error) {
        let judged = Judged {
            cond,
            evidence: &evidence,
            verdict: &verdict,
        };
        return Ok(report::evidence_report(model, &judged, &provenance));
    }
    let result = search_shrink(
        model.checked(),
        cond,
        &trace.start,
        &trace.steps,
        &trace.claim,
        &ShrinkOptions {
            attempts: size(attempts),
            interrupt,
            deadline,
        },
    );
    let summary = ShrinkSummary {
        original_steps: trace.steps.len(),
        attempts: result.attempts,
        stopped: result.stopped,
    };
    let shrunk = Evidence::Trace(trace.start.clone(), result.steps, trace.claim.clone());
    let verdict = decide(model.checked(), cond, &shrunk);
    let judged = Judged {
        cond,
        evidence: &shrunk,
        verdict: &verdict,
    };
    Ok(report::shrink_report(model, &judged, &provenance, &summary))
}
