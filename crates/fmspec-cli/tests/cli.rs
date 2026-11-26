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

    fn get(&self, path: &str) -> String {
        self.0
            .borrow()
            .get(path)
            .cloned()
            .unwrap_or_else(|| panic!("{path} が書かれていない"))
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
    for bad in ["broken.json", "untyped.json", "missing.json"] {
        let (code, body) = f.json(&["validate", bad]);
        assert_eq!(code, 2, "{bad}");
        assert!(
            ["invalid_model", "input_error"].contains(&body["status"].as_str().unwrap()),
            "{body}"
        );
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
    let mut cert: Value = serde_json::from_str(&f.get("cert.json")).unwrap();
    cert["states"].as_array_mut().unwrap().pop();
    f.0.borrow_mut().insert("short.json".to_string(), cert.to_string());
    let (code, body) = f.json(&["verify-certificate", "tickets.json", "short.json"]);
    assert_eq!((code, &body["status"]), (1, &json!("rejected")));
    assert_eq!(body["rejected"]["reason"], json!("missing_successor"));
    assert_eq!(body["rejected"]["state"], json!({"sold": 1}));
    let (code, body) = f.json(&["verify-certificate", "noguard.json", "cert.json"]);
    assert_eq!((code, &body["rejected"]["reason"]), (1, &json!("unreadable")));
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
    let mut trace: Value = serde_json::from_str(&f.get("trace.json")).unwrap();
    trace["steps"][0]["state"]["sold"] = json!(3);
    f.0.borrow_mut().insert("forged.json".to_string(), trace.to_string());
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
    assert_eq!(f.run(&[]).0, 2);
    assert_eq!(f.run(&["--help"]).0, 0);
    for args in [
        vec!["frobnicate"],
        vec!["check"],
        vec!["check", "tickets.json", "--max-states", "0"],
        vec!["check", "tickets.json", "--strategy", "dfs"],
        vec!["check", "tickets.json", "--bogus"],
        vec!["verify-certificate", "tickets.json"],
        vec!["simulate", "tickets.json", "--traces", "0"],
        vec!["simulate", "tickets.json", "--max-states", "3"],
        vec!["shrink", "tickets.json"],
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
