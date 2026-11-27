//! 結果の人間向けの表示。CLI と、Ruby の `Fmspec::Result#to_s` が使う。

use serde_json::{json, Value};
use std::fmt::Write;

fn plain(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

fn pairs(v: &Value) -> String {
    match v.as_object() {
        Some(map) => map
            .iter()
            .map(|(k, v)| format!("{k}: {}", plain(v)))
            .collect::<Vec<_>>()
            .join(", "),
        None => plain(v),
    }
}

fn error_text(e: &Value) -> String {
    match e["kind"].as_str() {
        Some("overflow") => "符号付き64ビット整数のオーバーフロー".to_string(),
        Some("out_of_range") => {
            let range = match e["type"]["int"].as_object() {
                Some(r) => format!("、型 {}..{} の範囲外", r["min"], r["max"]),
                None => String::new(),
            };
            format!("範囲外更新（値 {}{range}）", e["value"])
        }
        Some("type_mismatch") => "型の不一致".to_string(),
        Some("unbound") => "未束縛の参照".to_string(),
        Some("division_by_zero") => "0による除算".to_string(),
        Some("none") => "空の option の取り出し".to_string(),
        Some("missing_key") => "map にないキーの参照".to_string(),
        Some("index_out_of_range") => "list の範囲外の添字".to_string(),
        Some("full") => "上限に達した list への追加".to_string(),
        Some("empty") => "空の list からの取り出し".to_string(),
        Some("not_in_domain") => "ドメインにない値".to_string(),
        _ => e.to_string(),
    }
}

fn property_text(p: &Value) -> String {
    if let Some(kind) = p["violation"].as_str() {
        return match kind {
            "invariant" => format!("不変条件 {} の違反", plain(&p["name"])),
            "contract" => format!("遷移契約 {} の違反", plain(&p["name"])),
            _ => "非終端のデッドロック".to_string(),
        };
    }
    let error = error_text(&p["error"]);
    match p["site"].as_str() {
        Some("invariant") => format!("不変条件 {} の評価エラー: {error}", plain(&p["name"])),
        Some("contract") => format!("遷移契約 {} の評価エラー: {error}", plain(&p["name"])),
        Some("terminal") => format!("終端条件の評価エラー: {error}"),
        Some(site) => {
            let mut args = pairs(&p["args"]);
            let choices = pairs(&p["choices"]);
            if !choices.is_empty() {
                args = if args.is_empty() {
                    format!("内部選択 {choices}")
                } else {
                    format!("{args}; 内部選択 {choices}")
                };
            }
            let place = match site {
                "guard" => "guard".to_string(),
                "output" => "出力式".to_string(),
                _ => format!("更新式（{}）", plain(&p["target"])),
            };
            format!("操作 {}({args}) の{place}で評価エラー: {error}", plain(&p["action"]))
        }
        None => p.to_string(),
    }
}

/// 詳細化の検査のトレースでは、写した抽象モデルの状態も示す。
fn abstract_text(v: &Value) -> String {
    match v {
        Value::Null => String::new(),
        v => format!("（抽象 {}）", pairs(v)),
    }
}

fn trace_text(out: &mut String, trace: &Value) {
    let _ = writeln!(
        out,
        "  初期状態 {}{}",
        pairs(&trace["initial"]),
        trace.get("initial_abstract").map(abstract_text).unwrap_or_default()
    );
    let Some(steps) = trace["steps"].as_array() else {
        return;
    };
    for (i, st) in steps.iter().enumerate() {
        let mut line = format!("  {}. {}({})", i + 1, plain(&st["action"]), pairs(&st["args"]));
        let choices = pairs(&st["choices"]);
        if !choices.is_empty() {
            let _ = write!(line, " 内部選択 {choices}");
        }
        if let Some(v) = st["output"].get("value") {
            let _ = write!(line, " 出力 {}", plain(v));
        }
        let _ = writeln!(
            out,
            "{line} → {}{}",
            pairs(&st["state"]),
            st.get("abstract").map(abstract_text).unwrap_or_default()
        );
    }
    let _ = writeln!(out, "  （{} ステップ）", steps.len());
}

/// 詳細化の検査の主張。具体モデルの評価エラーは、安全性の検査と同じ形で示す。
fn refinement_property(p: &Value) -> String {
    match p["violation"].as_str() {
        Some("initial" | "step" | "mapping") => plain(&p["message"]),
        _ => property_text(p),
    }
}

/// `inconclusive` の理由（`reason`）の文。キーの名前は括弧に添える。知らない理由はキーの名前のまま示す。
fn reason_text(reason: &Value) -> String {
    match reason.as_str() {
        Some("max_states") => "状態数の上限（max_states）に達しました".to_string(),
        Some("max_depth") => "深さの上限（max_depth）で探索を打ち切りました".to_string(),
        Some("max_time_ms") => "時間の上限（max_time_ms）に達しました".to_string(),
        Some("max_check_cost") => "証拠の検査の見積もりが、評価回数の上限（max_check_cost）を超えました".to_string(),
        Some("interrupted") => "中断の要求で打ち切りました（interrupted）".to_string(),
        Some("abstract_failed") => {
            "写した状態で、抽象モデルの遷移の列挙が評価エラーになりました（abstract_failed）".to_string()
        }
        _ => plain(reason),
    }
}

fn status(body: &Value) -> &str {
    body["status"].as_str().unwrap_or("?")
}

/// 詳細化の検査の結果か。
fn is_refinement(body: &Value) -> bool {
    body.get("refinement").is_some()
}

/// 1行目（見出し）。モデルのない結果（`usage_error`、`invalid_model` など）では `None`。
fn headline(body: &Value) -> Option<String> {
    let refinement = is_refinement(body);
    let model = if refinement {
        format!(
            "{}（{} → {}）",
            plain(&body["refinement"]),
            plain(&body["concrete"]),
            plain(&body["abstract"])
        )
    } else {
        plain(&body["model"])
    };
    let property = || {
        if refinement {
            refinement_property(&body["property"])
        } else {
            property_text(&body["property"])
        }
    };
    let line = match status(body) {
        "refines" => format!("Refines: {model}"),
        "not_refines" => format!("NotRefines: {model} / {}", property()),
        "valid" => format!("Valid: {model}"),
        "verified" => format!("Verified: {model}"),
        "sampled" => format!("Sampled: {model}（網羅性の主張なし）"),
        "violated" => format!("Violated: {model} / {}", property()),
        "error" => format!("Error: {model} / {}", property()),
        "inconclusive" => format!("Inconclusive: {model}"),
        "internal_error" => format!("InternalError: {model}"),
        "rejected" => format!("Rejected: {model}"),
        _ if body.get("model").is_none() && !refinement => return None,
        other => format!("{other}: {model}"),
    };
    Some(line)
}

fn reason_section(body: &Value, out: &mut String) {
    if let Some(reason) = body.get("reason").filter(|_| status(body) == "inconclusive") {
        let _ = writeln!(out, "  打ち切りの理由: {}", reason_text(reason));
    }
}

fn other_model_section(body: &Value, out: &mut String) {
    // 読めなかった証拠（unreadable）は扱っていない。その digest は拒否の理由の文が示す。
    let unreadable = body["rejected"]["reason"] == json!("unreadable");
    if let Some(digest) = body.get("evidence_model_digest").filter(|_| !unreadable) {
        let _ = writeln!(
            out,
            "  別のモデルに対する証拠を、指定によりこのモデルで扱いました（証拠のdigestは {}）",
            plain(digest)
        );
    }
}

fn summary_section(body: &Value, out: &mut String) {
    if status(body) == "valid" && !is_refinement(body) {
        let _ = writeln!(
            out,
            "  状態変数 {}、操作 {}、不変条件 {}、遷移契約 {}",
            body["states"], body["actions"], body["invariants"], body["contracts"]
        );
    }
}

fn source_section(body: &Value, out: &mut String) {
    if let Some(source) = body["property"]["source"].as_object() {
        let _ = writeln!(out, "  定義: {}:{}", plain(&source["file"]), source["line"]);
    }
}

fn trace_section(body: &Value, out: &mut String) {
    if body.get("trace").is_some() {
        trace_text(out, &body["trace"]);
    }
}

/// `key` の項目の `message` と、`fields` のうち `null` でない項目。
fn detail_section(body: &Value, out: &mut String, key: &str, label: &str, fields: &[&str]) {
    let Some(detail) = body.get(key) else {
        return;
    };
    let _ = writeln!(out, "  {label}: {}", plain(&detail["message"]));
    for field in fields {
        if let Some(v) = detail.get(*field).filter(|v| !v.is_null()) {
            let _ = writeln!(out, "    {field}: {}", pairs(v));
        }
    }
}

fn rejected_section(body: &Value, out: &mut String) {
    detail_section(
        body,
        out,
        "rejected",
        "拒否の理由",
        &["state", "action", "invariant", "contract", "step"],
    );
}

fn inconsistency_section(body: &Value, out: &mut String) {
    detail_section(
        body,
        out,
        "inconsistency",
        "不整合",
        &["action", "state", "encoded_state"],
    );
}

fn message_section(body: &Value, out: &mut String) {
    if let Some(message) = body.get("message") {
        let _ = writeln!(out, "  {}", plain(message));
    }
}

fn shrink_section(body: &Value, out: &mut String) {
    if let Some(n) = body.get("original_steps") {
        let _ = writeln!(out, "  縮小前は {n} ステップ");
    }
    if let Some(shrink) = body.get("shrink").filter(|s| s["complete"] != json!(true)) {
        let _ = writeln!(
            out,
            "  縮小は打ち切った（{}、試した候補 {}）。局所最小とは限らない",
            plain(&shrink["limit"]),
            shrink["attempts"]
        );
    }
}

fn certificate_section(body: &Value, out: &mut String) {
    if let Some(n) = body.get("certificate_states") {
        let checked = if matches!(status(body), "verified" | "refines") {
            "（判定ゲートが受理）"
        } else {
            ""
        };
        let _ = writeln!(out, "  証明書の状態数 {n}{checked}");
    }
}

fn simulation_section(body: &Value, out: &mut String) {
    if let Some(sim) = body.get("simulation") {
        let _ = writeln!(
            out,
            "  シミュレーション: seed {}、トレース {}/{}、ステップ数 {}（{}）",
            sim["seed"],
            sim["completed_traces"],
            sim["traces"],
            sim["steps"],
            plain(&sim["prng"])
        );
    }
}

fn search_section(body: &Value, out: &mut String) {
    if let Some(search) = body.get("search") {
        let complete = if search["complete"] == json!(true) {
            "完走"
        } else {
            "未完走"
        };
        let _ = writeln!(
            out,
            "  探索: {complete}、訪問状態数 {}、遷移数 {}（探索器の報告）",
            search["visited_states"], search["transitions"]
        );
    }
}

/// 見出しに続く行。この順に示し、各節は対応する項目がなければ何も書かない。
const SECTIONS: [fn(&Value, &mut String); 12] = [
    reason_section,
    other_model_section,
    summary_section,
    source_section,
    trace_section,
    rejected_section,
    inconsistency_section,
    message_section,
    shrink_section,
    certificate_section,
    simulation_section,
    search_section,
];

pub fn human(body: &Value) -> String {
    let mut out = String::new();
    let Some(headline) = headline(body) else {
        // モデルのない結果は、CLI の標準エラー出力と同じく status と message を示す。
        let _ = writeln!(out, "{}: {}", status(body), plain(&body["message"]));
        return out;
    };
    let _ = writeln!(out, "{headline}");
    for section in SECTIONS {
        section(body, &mut out);
    }
    out
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::error_text;
    use fmspec_core::eval::ErrKind;
    use fmspec_core::source::{FAIL_EMPTY, FAIL_FULL, FAIL_INDEX, FAIL_MISSING_KEY, FAIL_NONE, FAIL_NOT_IN_DOMAIN};
    use fmspec_ir::{error_to_json, load};
    use serde_json::json;

    /// `ErrKind` のすべての種類。種類を足したら、ここと `error_text` に足す（`match` が網羅を強いる）。
    fn every_error() -> Vec<ErrKind> {
        let kinds = vec![
            ErrKind::Overflow,
            ErrKind::TypeMismatch,
            ErrKind::Unbound,
            ErrKind::OutOfRange(5),
            ErrKind::DivByZero,
            ErrKind::Failed(FAIL_NONE),
            ErrKind::Failed(FAIL_MISSING_KEY),
            ErrKind::Failed(FAIL_INDEX),
            ErrKind::Failed(FAIL_FULL),
            ErrKind::Failed(FAIL_EMPTY),
            ErrKind::Failed(FAIL_NOT_IN_DOMAIN),
        ];
        for k in &kinds {
            match k {
                ErrKind::Overflow
                | ErrKind::TypeMismatch
                | ErrKind::Unbound
                | ErrKind::OutOfRange(_)
                | ErrKind::DivByZero
                | ErrKind::Failed(_) => {}
            }
        }
        kinds
    }

    /// `error_to_json` が書くすべての種類に、`error_text` の文がある（JSONの文字列のまま示さない）。
    #[test]
    fn every_error_kind_has_a_text() {
        let ir = json!({
            "ir_version": 1,
            "name": "m",
            "states": [{"name": "x", "type": {"int": {"min": 0, "max": 1}}, "initial": {"int": 0}}],
            "actions": []
        });
        let m = load(&ir.to_string()).unwrap();
        for kind in every_error() {
            let e = error_to_json(&m, &kind, None);
            assert_ne!(error_text(&e), e.to_string(), "{kind:?}");
        }
    }
}
