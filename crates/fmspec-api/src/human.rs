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

pub fn human(body: &Value) -> String {
    let mut out = String::new();
    let status = body["status"].as_str().unwrap_or("?");
    let refinement = body.get("refinement").is_some();
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
    let property = if refinement {
        refinement_property(&body["property"])
    } else {
        property_text(&body["property"])
    };
    let headline = match status {
        "refines" => format!("Refines: {model}"),
        "not_refines" => format!("NotRefines: {model} / {property}"),
        "valid" => format!("Valid: {model}"),
        "verified" => format!("Verified: {model}"),
        "sampled" => format!("Sampled: {model}（網羅性の主張なし）"),
        "violated" => format!("Violated: {model} / {property}"),
        "error" => format!("Error: {model} / {property}"),
        "inconclusive" => format!("Inconclusive: {model}（{}）", plain(&body["reason"])),
        "internal_error" => format!("InternalError: {model}"),
        "rejected" => format!("Rejected: {model}"),
        other => format!("{other}: {model}"),
    };
    let _ = writeln!(out, "{headline}");
    if let Some(digest) = body.get("evidence_model_digest") {
        let _ = writeln!(
            out,
            "  別のモデルに対する証拠を、指定によりこのモデルで扱いました（証拠のdigestは {}）",
            plain(digest)
        );
    }
    if status == "valid" && !refinement {
        let _ = writeln!(
            out,
            "  状態変数 {}、操作 {}、不変条件 {}、遷移契約 {}",
            body["states"], body["actions"], body["invariants"], body["contracts"]
        );
    }
    if let Some(source) = body["property"]["source"].as_object() {
        let _ = writeln!(out, "  定義: {}:{}", plain(&source["file"]), source["line"]);
    }
    if body.get("trace").is_some() {
        trace_text(&mut out, &body["trace"]);
    }
    if let Some(rejected) = body.get("rejected") {
        let _ = writeln!(out, "  拒否の理由: {}", plain(&rejected["message"]));
        for key in ["state", "action", "invariant", "contract", "step"] {
            if let Some(v) = rejected.get(key).filter(|v| !v.is_null()) {
                let _ = writeln!(out, "    {key}: {}", pairs(v));
            }
        }
    }
    if let Some(inconsistency) = body.get("inconsistency") {
        let _ = writeln!(out, "  不整合: {}", plain(&inconsistency["message"]));
        for key in ["action", "state", "encoded_state"] {
            if let Some(v) = inconsistency.get(key).filter(|v| !v.is_null()) {
                let _ = writeln!(out, "    {key}: {}", pairs(v));
            }
        }
    }
    if let Some(message) = body.get("message") {
        let _ = writeln!(out, "  {}", plain(message));
    }
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
    if let Some(n) = body.get("certificate_states") {
        let checked = if status == "verified" || status == "refines" {
            "（判定ゲートが受理）"
        } else {
            ""
        };
        let _ = writeln!(out, "  証明書の状態数 {n}{checked}");
    }
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
    out
}
