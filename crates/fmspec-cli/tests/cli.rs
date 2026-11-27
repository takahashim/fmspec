//! コマンドの終了コードと出力（仕様書 §15）。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod common;

use common::*;
use serde_json::{json, Value};
use std::cell::RefCell;
use std::collections::HashMap;

struct Files(RefCell<HashMap<String, String>>);

impl Files {
    fn new(files: &[(&str, String)]) -> Files {
        Files(RefCell::new(
            files.iter().map(|(k, v)| (k.to_string(), v.clone())).collect(),
        ))
    }

    fn run(&self, args: &[&str]) -> (i32, String, String) {
        let args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        let read = |path: &str| {
            self.0
                .borrow()
                .get(path)
                .cloned()
                .ok_or_else(|| std::io::Error::from(std::io::ErrorKind::NotFound))
        };
        let write = |path: &str, text: &str| {
            self.0.borrow_mut().insert(path.to_string(), text.to_string());
            Ok(())
        };
        let run = fmspec_cli::run(&args, &read, &write);
        (run.code, run.stdout, run.stderr)
    }

    fn json(&self, args: &[&str]) -> (i32, Value) {
        let mut args = args.to_vec();
        args.push("--json");
        let (code, out, err) = self.run(&args);
        let body = serde_json::from_str(&out).unwrap_or_else(|e| panic!("JSONではない出力: {e}\n{out}\n{err}"));
        (code, body)
    }

    /// コマンドが書き出したJSONのファイル。
    fn get(&self, path: &str) -> Value {
        let text = self.0.borrow().get(path).cloned();
        let text = text.unwrap_or_else(|| panic!("{path} が書かれていない"));
        serde_json::from_str(&text).unwrap()
    }

    fn has(&self, path: &str) -> bool {
        self.0.borrow().contains_key(path)
    }

    fn put(&self, path: &str, body: &Value) {
        self.0.borrow_mut().insert(path.to_string(), body.to_string());
    }
}

fn files() -> Files {
    let mut const5 = tickets();
    const5["actions"][0]["updates"][0]["expr"] = json!({"int": 5});
    let mut located = tickets_without_guard();
    located["invariants"][0]["source"] = json!({"file": "spec/models/tickets.rb", "line": 12});
    Files::new(&[
        ("tickets.json", tickets().to_string()),
        ("noguard.json", located.to_string()),
        ("const5.json", const5.to_string()),
        ("broken.json", "{".to_string()),
        ("untyped.json", {
            let mut ir = tickets();
            ir["invariants"][0]["expr"] = json!({"var": 0});
            ir.to_string()
        }),
    ])
}

#[test]
fn validate() {
    let f = files();
    let (code, body) = f.json(&["validate", "tickets.json"]);
    assert_eq!((code, &body["status"]), (0, &json!("valid")));
    for (bad, status) in [
        ("broken.json", "invalid_model"),
        ("untyped.json", "invalid_model"),
        ("missing.json", "input_error"),
    ] {
        let (code, body) = f.json(&["validate", bad]);
        assert_eq!((code, &body["status"]), (2, &json!(status)), "{bad}");
        assert!(body["message"].as_str().unwrap().starts_with(bad), "{body}");
    }
    let (code, out, err) = f.run(&["validate", "untyped.json"]);
    assert_eq!((code, out.as_str()), (2, ""));
    assert!(err.contains("capacity_respected"), "{err}");
}

#[test]
fn check_exit_codes_follow_the_status() {
    let f = files();
    let (code, body) = f.json(&["check", "tickets.json", "--strategy", "bfs", "--max-states", "100000"]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")));
    assert_eq!(body["search"]["visited_states"], json!(4));
    assert_eq!(body["certificate_states"], json!(4));

    let (code, body) = f.json(&["check", "noguard.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")));
    assert_eq!(body["property"]["name"], json!("capacity_respected"));
    assert_eq!(
        body["property"]["source"],
        json!({"file": "spec/models/tickets.rb", "line": 12})
    );
    assert_eq!(body["trace"]["steps"].as_array().unwrap().len(), 2);

    let (code, body) = f.json(&["check", "const5.json"]);
    assert_eq!((code, &body["status"]), (2, &json!("error")));
    assert_eq!(body["property"]["error"]["value"], json!(5));

    let (code, body) = f.json(&["check", "tickets.json", "--max-states", "2"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_states"))
    );
    assert_eq!(body["search"]["complete"], json!(false));

    // チケット例の到達状態は深さ2まで。深さ1では未完了で、証明書を出さない。
    let (code, body) = f.json(&["check", "tickets.json", "--max-depth", "2"]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")));
    let (code, body) = f.json(&["check", "tickets.json", "--max-depth", "1"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_depth"))
    );
    assert!(body.get("certificate_states").is_none());

    let (code, body) = f.json(&["check", "tickets.json", "--max-time-ms", "0"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_time_ms"))
    );
    let (code, body) = f.json(&["simulate", "tickets.json", "--max-time-ms", "0"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_time_ms"))
    );
}

#[test]
fn check_conditions_select_what_is_checked() {
    let f = files();
    // 不変条件を対象から外すと、guard のないモデルは範囲外更新のエラーになる。
    let (code, body) = f.json(&["check", "noguard.json", "--invariants", ""]);
    assert_eq!((code, &body["status"]), (2, &json!("error")));
    assert_eq!(body["conditions"]["invariants"], json!([]));
    // 購入を対象から外すと、初期状態から動けない。
    let (code, body) = f.json(&["check", "noguard.json", "--actions", "cancel"]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")));
    let (code, body) = f.json(&["check", "noguard.json", "--actions", "cancel", "--deadlock"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")));
    assert_eq!(body["property"], json!({"violation": "deadlock", "source": null}));
    let (code, body) = f.json(&["check", "tickets.json", "--actions", "refund"]);
    assert_eq!((code, &body["status"]), (2, &json!("usage_error")));
}

#[test]
fn certificates_can_be_saved_and_verified_separately() {
    let f = files();
    let (code, _) = f.json(&["check", "tickets.json", "--certificate-out", "cert.json"]);
    assert_eq!(code, 0);
    let (code, body) = f.json(&["verify-certificate", "tickets.json", "cert.json"]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")));
    // 探索を行っていないので、探索統計は付けない。
    assert!(body.get("search").is_none());

    // 別の検査条件での検証、状態を欠いた証明書、別のモデルの証明書は拒否する。
    let (code, body) = f.json(&["verify-certificate", "tickets.json", "cert.json", "--deadlock"]);
    assert_eq!((code, &body["rejected"]["reason"]), (1, &json!("condition_mismatch")));
    let mut cert = f.get("cert.json");
    cert["states"].as_array_mut().unwrap().pop();
    f.put("short.json", &cert);
    let (code, body) = f.json(&["verify-certificate", "tickets.json", "short.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("rejected")));
    assert_eq!(body["rejected"]["reason"], json!("missing_successor"));
    assert_eq!(body["rejected"]["state"], json!({"sold": 1}));
    let (code, body) = f.json(&["verify-certificate", "noguard.json", "cert.json"]);
    assert_eq!((code, &body["rejected"]["reason"]), (1, &json!("unreadable")));
}

#[test]
fn certificate_checks_stop_at_their_limits() {
    // 使わない操作 wide の引数の領域が広いので、状態ごとの検査の費用が大きく、証明書の検査は複数の区切りに分かれる。
    // 期限は区切りごとに確かめるので、1つの区切りで終わる証明書では打ち切りを確かめられない。
    let wide = json!({
        "ir_version": 1,
        "name": "wide",
        "states": [{"id": 0, "name": "n", "type": {"int": {"min": 0, "max": 19}}, "initial": {"int": 0}}],
        "actions": [
            {
                "name": "inc",
                "guard": {"lt": [{"var": 0}, {"int": 19}]},
                "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"int": 1}]}}]
            },
            {
                "name": "wide",
                "params": [{"name": "k", "type": {"int": {"min": 0, "max": 65535}}}],
                "choices": [],
                "guard": {"bool": false},
                "updates": []
            }
        ],
        "invariants": []
    });
    let f = files();
    f.put("wide.json", &wide);
    let (code, _) = f.json(&["check", "wide.json", "--certificate-out", "cert.json"]);
    assert_eq!(code, 0);
    let (code, body) = f.json(&["verify-certificate", "wide.json", "cert.json", "--max-time-ms", "0"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_time_ms")),
        "{body}"
    );
    let (code, body) = f.json(&[
        "verify-certificate",
        "wide.json",
        "cert.json",
        "--max-time-ms",
        "600000",
    ]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")), "{body}");
    let (code, body) = f.json(&["verify-certificate", "wide.json", "cert.json", "--max-check-cost", "1"]);
    assert_eq!(
        (code, &body["status"], &body["reason"]),
        (3, &json!("inconclusive"), &json!("max_check_cost")),
        "{body}"
    );
}

#[test]
fn traces_can_be_saved_and_replayed() {
    let f = files();
    let (code, _) = f.json(&["check", "noguard.json", "--trace-out", "trace.json"]);
    assert_eq!(code, 1);
    let (code, body) = f.json(&["replay", "noguard.json", "trace.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")));

    let (_, _) = f.json(&["check", "const5.json", "--trace-out", "error.json"]);
    let (code, body) = f.json(&["replay", "const5.json", "error.json"]);
    assert_eq!((code, &body["status"]), (2, &json!("error")));

    // 途中の状態を書き換えたトレースは拒否する。
    let mut trace = f.get("trace.json");
    trace["steps"][0]["state"]["sold"] = json!(3);
    f.put("forged.json", &trace);
    let (code, body) = f.json(&["replay", "noguard.json", "forged.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("rejected")));
    assert_eq!(
        body["rejected"],
        json!({
            "reason": "step_mismatch", "step": 1,
            "message": "トレースのステップがモデルの遷移と一致しません"
        })
    );
    // 別のモデルのトレース。
    let (code, body) = f.json(&["replay", "tickets.json", "trace.json"]);
    assert_eq!((code, &body["rejected"]["reason"]), (1, &json!("unreadable")));
}

#[test]
fn evidence_for_another_model_is_checked_only_when_allowed() {
    let f = files();
    let (_, found) = f.json(&["check", "noguard.json", "--trace-out", "trace.json"]);
    let (_, model) = f.json(&["validate", "tickets.json"]);
    // guard のあるモデルでは、guard のないモデルの反例の2ステップ目は遷移にないので、判定ゲートが拒否する。
    for command in ["replay", "shrink"] {
        let (code, body) = f.json(&[command, "tickets.json", "trace.json", "--allow-other-model"]);
        assert_eq!((code, &body["status"]), (1, &json!("rejected")), "{body}");
        assert_eq!(body["rejected"]["reason"], "step_mismatch", "{body}");
        assert_eq!(body["model_digest"], model["model_digest"]);
        assert_eq!(body["evidence_model_digest"], found["model_digest"]);
    }
    let (code, text, _) = f.run(&["replay", "tickets.json", "trace.json", "--allow-other-model"]);
    assert_eq!(code, 1);
    assert!(
        text.contains(&format!(
            "別のモデルに対する証拠を、指定によりこのモデルで扱いました（証拠のdigestは {}）",
            found["model_digest"].as_str().unwrap()
        )),
        "{text}"
    );

    let (_, _) = f.json(&["check", "tickets.json", "--certificate-out", "cert.json"]);
    let (code, body) = f.json(&["verify-certificate", "noguard.json", "cert.json", "--allow-other-model"]);
    assert_eq!((code, &body["status"]), (1, &json!("rejected")), "{body}");
    assert_ne!(body["rejected"]["reason"], "unreadable", "{body}");
    assert_eq!(body["evidence_model_digest"], model["model_digest"]);

    for command in ["check", "simulate"] {
        let (code, body) = f.json(&[command, "tickets.json", "--allow-other-model"]);
        assert_eq!((code, &body["status"]), (2, &json!("usage_error")));
        assert_eq!(
            body["message"],
            json!(format!("{command} は --allow-other-model を受け付けません"))
        );
    }
}

#[test]
fn evidence_for_another_model_can_be_carried_over_when_accepted() {
    let f = files();
    // 取り消しの guard だけを変えたモデル。購入だけの反例は、このモデルでも同じ遷移である。
    let mut changed = tickets_without_guard();
    changed["actions"][1]["guard"] = json!({"gt": [{"var": 0}, {"int": 1}]});
    f.put("changed.json", &changed);
    let (_, found) = f.json(&["check", "noguard.json", "--trace-out", "old.json"]);
    let (_, model) = f.json(&["validate", "changed.json"]);
    assert_ne!(found["model_digest"], model["model_digest"]);
    let (code, body) = f.json(&["replay", "changed.json", "old.json"]);
    assert_eq!((code, &body["rejected"]["reason"]), (1, &json!("unreadable")), "{body}");

    for command in ["replay", "shrink"] {
        let (code, body) = f.json(&[command, "changed.json", "old.json", "--allow-other-model"]);
        assert_eq!((code, &body["status"]), (1, &json!("violated")), "{command}: {body}");
        assert_eq!(body["model_digest"], model["model_digest"]);
        assert_eq!(body["evidence_model_digest"], found["model_digest"]);
    }
    // 縮小して書き出したトレースは今のモデルの digest を持つので、指定なしで再生できる。
    let (code, _) = f.json(&[
        "shrink",
        "changed.json",
        "old.json",
        "--allow-other-model",
        "--trace-out",
        "new.json",
    ]);
    assert_eq!(code, 1);
    assert_eq!(f.get("new.json")["model_digest"], model["model_digest"]);
    let (code, body) = f.json(&["replay", "changed.json", "new.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")), "{body}");
    assert!(body.get("evidence_model_digest").is_none(), "{body}");
}

#[test]
fn human_readable_output() {
    let f = files();
    let (code, out, _) = f.run(&["check", "noguard.json"]);
    assert_eq!(code, 1);
    let expected = "\
Violated: tickets / 不変条件 capacity_respected の違反
  定義: spec/models/tickets.rb:12
  初期状態 sold: 0
  1. purchase(quantity: 2) → sold: 2
  2. purchase(quantity: 2) → sold: 4
  （2 ステップ）
  探索: 未完走、訪問状態数 5、遷移数 7（探索器の報告）
";
    assert_eq!(out, expected);
    let (_, out, _) = f.run(&["check", "const5.json"]);
    assert!(out.starts_with("Error: tickets / 操作 purchase(quantity: 1) の更新式（sold）で評価エラー: 範囲外更新（値 5、型 0..4 の範囲外）\n"), "{out}");
}

#[test]
fn usage_errors() {
    let f = files();
    let (code, out, err) = f.run(&[]);
    assert_eq!((code, out.as_str()), (2, ""));
    assert!(err.starts_with("使い方:"), "{err}");
    let (code, out, _) = f.run(&["--help"]);
    assert_eq!(code, 0);
    assert!(out.starts_with("使い方:"), "{out}");
    let (code, out, _) = f.run(&["--version"]);
    assert_eq!((code, out), (0, format!("fmspec {}\n", env!("CARGO_PKG_VERSION"))));
    for args in [
        vec!["frobnicate"],
        vec!["check"],
        vec!["check", "tickets.json", "--max-states", "0"],
        vec!["check", "tickets.json", "--strategy", "dfs"],
        vec!["check", "tickets.json", "--bogus"],
        vec!["verify-certificate", "tickets.json"],
        vec!["simulate", "tickets.json", "--traces", "0"],
        vec!["simulate", "tickets.json", "--max-states", "3"],
        vec!["simulate", "tickets.json", "--max-depth", "3"],
        vec!["verify-certificate", "tickets.json", "c.json", "--max-depth", "3"],
        vec!["check", "tickets.json", "--max-time-ms", "-1"],
        vec!["shrink", "tickets.json"],
        vec!["bisect", "tickets.json"],
    ] {
        let (code, body) = f.json(&args);
        assert_eq!((code, &body["status"]), (2, &json!("usage_error")), "{args:?}");
    }
}

#[test]
fn simulate_samples_traces_reproducibly() {
    let f = files();
    let (code, body) = f.json(&[
        "simulate",
        "tickets.json",
        "--traces",
        "50",
        "--max-steps",
        "20",
        "--seed",
        "42",
    ]);
    assert_eq!((code, &body["status"]), (0, &json!("sampled")));
    assert_eq!(body["simulation"]["completed_traces"], json!(50));
    assert_eq!(body["simulation"]["steps"], json!(1000));
    assert_eq!(body["simulation"]["prng"], json!("splitmix64"));

    // guard のないモデルでは、どこかのトレースで違反か範囲外更新に行き当たる。
    let run = |seed: &str| f.json(&["simulate", "noguard.json", "--seed", seed, "--trace-out", "sim.json"]);
    let (code, first) = run("7");
    assert!(code == 1 || code == 2, "{first}");
    assert_eq!(first["trace"]["seed"], json!(7));
    // 同じ seed なら同じトレース、違う seed なら（このモデルでは）違うトレースになる。
    let (_, again) = run("7");
    assert_eq!(first["trace"], again["trace"]);
    assert!((0..20).any(|seed| run(&seed.to_string()).1["trace"]["steps"] != first["trace"]["steps"]));
    // 見つけたトレースは、判定ゲートで再生できる。
    run("7");
    let (code, replayed) = f.json(&["replay", "noguard.json", "sim.json"]);
    assert_eq!(
        (code, &replayed["status"]),
        (if first["status"] == "violated" { 1 } else { 2 }, &first["status"])
    );

    // 人間向けの表示では、網羅性の主張がないことを示す。
    let (_, out, _) = f.run(&["simulate", "tickets.json", "--traces", "3", "--max-steps", "5"]);
    assert_eq!(
        out,
        "Sampled: tickets（網羅性の主張なし）\n  シミュレーション: seed 0、トレース 3/3、ステップ数 15（splitmix64）\n"
    );
}

#[test]
fn shrink_shortens_a_trace_and_keeps_the_violation() {
    let f = files();
    // シミュレーションで見つけた違反のトレースを、不変条件の違反を保ったまま短くする。
    let seed = (0..200u32)
        .map(|s| s.to_string())
        .find(|seed| {
            let (_, body) = f.json(&[
                "simulate",
                "noguard.json",
                "--seed",
                seed,
                "--invariants",
                "capacity_respected",
            ]);
            body["status"] == "violated" && body["trace"]["steps"].as_array().unwrap().len() > 2
        })
        .expect("2ステップより長い違反のトレースが見つかるはず");
    let (_, found) = f.json(&["simulate", "noguard.json", "--seed", &seed, "--trace-out", "long.json"]);
    let (code, body) = f.json(&["shrink", "noguard.json", "long.json", "--trace-out", "short.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")));
    assert_eq!(body["property"]["name"], json!("capacity_respected"));
    assert_eq!(
        body["original_steps"],
        json!(found["trace"]["steps"].as_array().unwrap().len())
    );
    // このモデルの最短の反例は2ステップで、縮小はそこに達する。
    assert_eq!(body["trace"]["steps"].as_array().unwrap().len(), 2);
    let (code, replayed) = f.json(&["replay", "noguard.json", "short.json"]);
    assert_eq!((code, &replayed["status"]), (1, &json!("violated")));

    // 受理されないトレースは縮小しない。
    let mut forged = f.get("long.json");
    forged["steps"][0]["state"]["sold"] = json!(0);
    f.put("forged.json", &forged);
    let (code, body) = f.json(&["shrink", "noguard.json", "forged.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("rejected")));

    // 試す候補の数と時間の上限。打ち切っても、判定ゲートが受理したトレースを返して書き出す。
    let (code, body) = f.json(&[
        "shrink",
        "noguard.json",
        "long.json",
        "--attempts",
        "1",
        "--trace-out",
        "one.json",
    ]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")), "{body}");
    assert_eq!(
        body["shrink"],
        json!({"attempts": 1, "complete": false, "limit": "attempts"})
    );
    let (code, replayed) = f.json(&["replay", "noguard.json", "one.json"]);
    assert_eq!((code, &replayed["status"]), (1, &json!("violated")));
    let (code, body) = f.json(&["shrink", "noguard.json", "long.json", "--max-time-ms", "0"]);
    assert_eq!((code, &body["shrink"]["limit"]), (1, &json!("max_time_ms")), "{body}");
    assert_eq!(body["trace"]["steps"], f.get("long.json")["steps"]);
    let (code, body) = f.json(&["shrink", "noguard.json", "long.json", "--attempts", "0"]);
    assert_eq!(
        (code, &body["message"]),
        (2, &json!("--attempts は1以上の整数です（\"0\"）"))
    );
    // 見積もりが上限を超えるトレースは検査しない。
    for command in ["replay", "shrink"] {
        let (code, body) = f.json(&[command, "noguard.json", "long.json", "--max-check-cost", "1"]);
        assert_eq!((code, &body["reason"]), (3, &json!("max_check_cost")), "{body}");
    }
    // トレースの検査は区切らないので、replay は時間の上限を受け付けない。
    let (code, body) = f.json(&["replay", "noguard.json", "long.json", "--max-time-ms", "10"]);
    assert_eq!(
        (code, &body["message"]),
        (2, &json!("replay は --max-time-ms を受け付けません"))
    );
    let (code, body) = f.json(&["check", "noguard.json", "--attempts", "10"]);
    assert_eq!(
        (code, &body["message"]),
        (2, &json!("check は --attempts を受け付けません"))
    );
}

#[test]
fn refine_exit_codes_follow_the_status() {
    let mapping = json!([{"state": "sold", "expr": {"var": 0}}]);
    let doc = |concrete: Value| {
        json!({"ir_version": 1, "name": "r", "concrete": concrete, "abstract": tickets(), "mapping": mapping})
            .to_string()
    };
    let f = Files::new(&[
        ("same.json", doc(tickets())),
        ("noguard.json", doc(tickets_without_guard())),
        ("broken.json", "{}".to_string()),
    ]);
    let (code, body) = f.json(&["refine", "same.json"]);
    assert_eq!((code, &body["status"]), (0, &json!("refines")), "{body}");
    let (code, body) = f.json(&["refine", "noguard.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("not_refines")), "{body}");
    assert_eq!(body["property"]["violation"], json!("step"));
    let (code, out, _) = f.run(&["refine", "noguard.json"]);
    assert_eq!(code, 1);
    assert!(out.starts_with("NotRefines: r（tickets → tickets）"), "{out}");
    assert!(out.contains("（抽象 "), "{out}");
    let (code, body) = f.json(&["refine", "same.json", "--max-states", "1"]);
    assert_eq!((code, &body["reason"]), (3, &json!("max_states")));
    let (code, body) = f.json(&["refine", "broken.json"]);
    assert_eq!((code, &body["status"]), (2, &json!("invalid_model")));
    let (code, body) = f.json(&["refine", "same.json", "--deadlock"]);
    assert_eq!((code, &body["status"]), (2, &json!("usage_error")));
}

#[test]
fn shrink_lowers_arguments_and_choices_and_reruns_the_later_steps() {
    // 購入の数量に加えて、遷移に効かない内部選択 gift を持つチケット例。
    let mut ir = tickets_without_guard();
    ir["actions"][0]["choices"] = json!([{"name": "gift", "type": {"bool": {}}}]);
    let f = files();
    f.put("gift.json", &ir);
    // 1、2、1 と買う違反のトレース。gift はどれも真にする。売上3の状態では数量2の購入が範囲外更新になるが、
    // 各ステップはその引数だけで再実行するので、この状態を通るトレースも縮小できる。
    let step = |quantity: i64, sold: i64| {
        json!({"action": "purchase", "args": {"quantity": quantity}, "choices": {"gift": true},
               "output": {"unit": true}, "state": {"sold": sold}})
    };
    let (_, found) = f.json(&["check", "gift.json"]);
    let mut long = found["trace"].clone();
    long["steps"] = json!([step(1, 1), step(2, 3), step(1, 4)]);
    f.put("long.json", &long);
    let (code, replayed) = f.json(&["replay", "gift.json", "long.json"]);
    assert_eq!((code, &replayed["status"]), (1, &json!("violated")), "{replayed}");

    let (code, body) = f.json(&["shrink", "gift.json", "long.json", "--trace-out", "short.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("violated")), "{body}");
    assert_eq!(body["original_steps"], json!(3));
    // どの1ステップも削れず、数量も小さくできない（後続を再実行すると4に届かない）。gift だけが偽になる。
    let short = f.get("short.json");
    let quantities: Vec<&Value> = short["steps"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| &s["args"]["quantity"])
        .collect();
    assert_eq!(quantities, [&json!(1), &json!(2), &json!(1)]);
    for s in short["steps"].as_array().unwrap() {
        assert_eq!(s["choices"]["gift"], json!(false), "{short}");
    }
    let (code, replayed) = f.json(&["replay", "gift.json", "short.json"]);
    assert_eq!((code, &replayed["status"]), (1, &json!("violated")));
}

#[test]
fn commands_reject_options_they_do_not_use() {
    let f = files();
    for (args, flag) in [
        (vec!["validate", "tickets.json", "--deadlock"], "--deadlock"),
        (vec!["check", "tickets.json", "--seed", "1"], "--seed"),
        (
            vec!["simulate", "tickets.json", "--certificate-out", "out.json"],
            "--certificate-out",
        ),
        (
            vec![
                "verify-certificate",
                "tickets.json",
                "c.json",
                "--trace-out",
                "out.json",
            ],
            "--trace-out",
        ),
        (
            vec!["replay", "tickets.json", "t.json", "--actions", "purchase"],
            "--actions",
        ),
        (
            vec!["shrink", "tickets.json", "t.json", "--invariants", "capacity_respected"],
            "--invariants",
        ),
    ] {
        let (code, body) = f.json(&args);
        assert_eq!((code, &body["status"]), (2, &json!("usage_error")), "{args:?}");
        assert_eq!(
            body["message"],
            json!(format!("{} は {flag} を受け付けません", args[0])),
            "{args:?}"
        );
    }
    // 拒否したコマンドは実行しないので、何も書き出さない。
    assert!(!f.has("out.json"));
}

#[test]
fn usage_errors_go_to_stderr_without_json() {
    let f = files();
    for (args, message) in [
        (
            vec!["check", "tickets.json", "--trace-out"],
            "--trace-out には値が必要です",
        ),
        (
            vec!["check", "tickets.json", "--max-states", "-1"],
            "--max-states は1以上の整数です（\"-1\"）",
        ),
        (
            vec!["simulate", "tickets.json", "--seed", "x"],
            "--seed は0以上の整数です（\"x\"）",
        ),
        // 下限はフラグごとに違い、fmspec-api のキー名でなくフラグの名前で報告する。
        (
            vec!["check", "tickets.json", "--max-states", "0"],
            "--max-states は1以上の整数です（\"0\"）",
        ),
        (
            vec!["simulate", "tickets.json", "--traces", "0"],
            "--traces は1以上の整数です（\"0\"）",
        ),
        (
            vec!["shrink", "tickets.json", "t.json", "--attempts", "0"],
            "--attempts は1以上の整数です（\"0\"）",
        ),
        // 数字だけを整数として読む。
        (
            vec!["check", "tickets.json", "--max-states", "+5"],
            "--max-states は1以上の整数です（\"+5\"）",
        ),
        (
            vec!["check", "tickets.json", "--max-depth", " 5"],
            "--max-depth は0以上の整数です（\" 5\"）",
        ),
        (
            vec!["check", "tickets.json", "--max-depth", ""],
            "--max-depth は0以上の整数です（\"\"）",
        ),
        (
            vec!["check", "tickets.json", "--max-depth", "18446744073709551616"],
            "--max-depth が大きすぎます（\"18446744073709551616\"）",
        ),
        (vec!["check", "tickets.json", "--bogus"], "未知のオプション --bogus"),
    ] {
        let (code, out, err) = f.run(&args);
        assert_eq!((code, out.as_str()), (2, ""), "{args:?}");
        assert_eq!(err, format!("usage_error: {message}\n"), "{args:?}");
    }
}

#[test]
fn only_accepted_evidence_is_written() {
    let f = files();
    // 証明書はファイルにだけ書き、標準出力の結果には含めない。
    let (code, body) = f.json(&[
        "check",
        "tickets.json",
        "--certificate-out",
        "cert.json",
        "--trace-out",
        "t0.json",
    ]);
    assert_eq!(code, 0);
    assert!(body.get("certificate").is_none(), "{body}");
    assert!(f.has("cert.json"));
    // 検証できたときは、書き出すトレースがない。
    assert!(!f.has("t0.json"));
    // 違反や探索未完了では、証明書を書き出さない。
    let (code, _) = f.json(&["check", "noguard.json", "--certificate-out", "c1.json"]);
    assert_eq!(code, 1);
    let (code, _) = f.json(&[
        "check",
        "tickets.json",
        "--max-states",
        "2",
        "--certificate-out",
        "c3.json",
    ]);
    assert_eq!(code, 3);
    // 深さや証明書の検査の費用の上限で打ち切ったときも書き出さない。
    let (code, body) = f.json(&[
        "check",
        "tickets.json",
        "--max-depth",
        "1",
        "--certificate-out",
        "c4.json",
    ]);
    assert_eq!((code, &body["reason"]), (3, &json!("max_depth")), "{body}");
    let (code, body) = f.json(&[
        "check",
        "tickets.json",
        "--max-check-cost",
        "1",
        "--certificate-out",
        "c5.json",
    ]);
    assert_eq!((code, &body["reason"]), (3, &json!("max_check_cost")), "{body}");
    for path in ["c1.json", "c3.json", "c4.json", "c5.json"] {
        assert!(!f.has(path), "{path}");
    }
    // 違反なしのシミュレーションは、トレースを書き出さない。
    let (code, _) = f.json(&["simulate", "tickets.json", "--traces", "3", "--trace-out", "t1.json"]);
    assert_eq!(code, 0);
    assert!(!f.has("t1.json"));
    // 判定ゲートが拒否したトレースは、縮小の結果として書き出さない。
    f.json(&["check", "noguard.json", "--trace-out", "trace.json"]);
    let mut forged = f.get("trace.json");
    forged["steps"][0]["state"]["sold"] = json!(3);
    f.put("forged.json", &forged);
    let (code, _) = f.json(&["shrink", "noguard.json", "forged.json", "--trace-out", "t2.json"]);
    assert_eq!(code, 1);
    assert!(!f.has("t2.json"));
}

#[test]
fn a_failed_write_is_an_error() {
    let args: Vec<String> = ["check", "noguard.json", "--json", "--trace-out", "out.json"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let model = tickets_without_guard().to_string();
    let read = |_: &str| Ok(model.clone());
    let write = |_: &str, _: &str| Err(std::io::Error::from(std::io::ErrorKind::PermissionDenied));
    let run = fmspec_cli::run(&args, &read, &write);
    // 違反を見つけても、書き出せなければ終了コード2にする。入力の誤りとは区別する。
    assert_eq!(run.code, 2);
    let body: Value = serde_json::from_str(&run.stdout).unwrap();
    assert_eq!(body["status"], json!("output_error"), "{body}");
    assert!(body["message"].as_str().unwrap().starts_with("out.json: "), "{body}");
}

#[test]
fn an_option_is_not_taken_as_the_value_of_another() {
    let f = files();
    // `--json` を `--trace-out` の値として読むと、結果は人間向けになり、`--json` という名前のファイルに書き出す。
    for args in [
        vec!["check", "noguard.json", "--trace-out", "--json"],
        vec!["check", "--trace-out", "--json"],
    ] {
        let (code, out, err) = f.run(&args);
        let body: Value = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{args:?}: {e}\n{out}{err}"));
        assert_eq!(
            (code, &body["status"], &body["message"]),
            (2, &json!("usage_error"), &json!("--trace-out には値が必要です")),
            "{args:?}"
        );
    }
    assert!(!f.has("--json"));
    let (code, _, err) = f.run(&["check", "tickets.json", "--max-states", "--deadlock"]);
    assert_eq!(
        (code, err.as_str()),
        (2, "usage_error: --max-states には値が必要です\n")
    );
}

#[test]
fn the_command_is_identified_before_its_options_are_read() {
    let f = files();
    // コマンドを先に特定し、そのコマンドが受け付けるかを、値を読む前に確かめる。
    for (args, message) in [
        (
            vec!["validate", "tickets.json", "--seed", "abc"],
            "validate は --seed を受け付けません",
        ),
        (
            vec!["replay", "tickets.json", "t.json", "--trace-out"],
            "replay は --trace-out を受け付けません",
        ),
        (
            vec!["chek", "tickets.json", "--max-states", "x"],
            "未知のコマンド \"chek\"",
        ),
        (
            vec!["check", "tickets.json", "--bogus", "--seed", "1"],
            "未知のオプション --bogus",
        ),
    ] {
        let (code, body) = f.json(&args);
        assert_eq!(
            (code, &body["status"], &body["message"]),
            (2, &json!("usage_error"), &json!(message)),
            "{args:?}"
        );
    }
    // 人間向けの表示では、未知のコマンドの後に使い方を示す。
    let (code, out, err) = f.run(&["chek", "tickets.json"]);
    assert_eq!((code, out.as_str()), (2, ""));
    assert!(
        err.starts_with("usage_error: 未知のコマンド \"chek\"\n使い方:"),
        "{err}"
    );
}

#[test]
fn help_is_accepted_after_the_command() {
    let f = files();
    for args in [
        vec!["check", "-h"],
        vec!["check", "tickets.json", "--help"],
        vec!["replay", "--json", "-h"],
    ] {
        let (code, out, err) = f.run(&args);
        assert_eq!((code, err.as_str()), (0, ""), "{args:?}");
        assert!(out.starts_with("使い方:"), "{args:?}: {out}");
    }
}

#[test]
fn arguments_after_the_separator_are_files() {
    let f = files();
    f.put("--model.json", &tickets());
    f.put("-h", &tickets());
    let (code, out, _) = f.run(&["validate", "--json", "--", "--model.json"]);
    let body: Value = serde_json::from_str(&out).unwrap();
    assert_eq!((code, &body["status"]), (0, &json!("valid")), "{body}");
    let (code, out, _) = f.run(&["validate", "--", "-h"]);
    assert_eq!(code, 0);
    assert!(out.starts_with("Valid: "), "{out}");
    // `--` 以降の `--json` はファイル名なので、出力の形式は変わらない。
    let (code, out, err) = f.run(&["validate", "tickets.json", "--", "--json"]);
    assert_eq!((code, out.as_str()), (2, ""));
    assert_eq!(err, "usage_error: validate にはモデルのファイルを1つ指定します\n");
}

#[test]
fn an_option_given_twice_is_an_error() {
    let f = files();
    // 後の指定だけを黙って使うと、順序で結果が変わり、前の指定が効いたと誤解させる。
    for (args, flag) in [
        (
            vec!["check", "tickets.json", "--max-states", "100000", "--max-states", "1"],
            "--max-states",
        ),
        (
            vec!["check", "noguard.json", "--actions", "purchase", "--actions", "cancel"],
            "--actions",
        ),
        (
            vec![
                "check",
                "noguard.json",
                "--invariants",
                "capacity_respected",
                "--invariants",
                "",
            ],
            "--invariants",
        ),
        (vec!["check", "noguard.json", "--deadlock", "--deadlock"], "--deadlock"),
        (
            vec![
                "check",
                "noguard.json",
                "--trace-out",
                "a.json",
                "--trace-out",
                "b.json",
            ],
            "--trace-out",
        ),
    ] {
        let (code, body) = f.json(&args);
        assert_eq!(
            (code, &body["status"], &body["message"]),
            (
                2,
                &json!("usage_error"),
                &json!(format!("{flag} は1回だけ指定できます"))
            ),
            "{args:?}"
        );
    }
    assert!(!f.has("a.json") && !f.has("b.json"));
    // 出力の形式の指定は、重ねても意味が変わらないので受け付ける。
    let (code, body) = f.json(&["check", "tickets.json", "--json"]);
    assert_eq!((code, &body["status"]), (0, &json!("verified")));
}
