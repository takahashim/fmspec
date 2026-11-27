//! 適合性検査のセッションの応答の形。Ruby 側のドライバ（lib/fmspec/testing.rb）は、この形のまま読む。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{load, Model, Session};
use serde_json::{json, Value};
use std::sync::Arc;

/// 支払い回数 `charges`（0..2）。`pay(id)` は内部選択 `ok` が真なら1回増やし、
/// success か forbidden を返す。`double` は2回増やすので、不変条件 `single` を破るか、範囲外更新になる。
fn orders() -> Arc<Model> {
    let charges = json!({"var": 0});
    let ok = json!({"choice": 0});
    let answer = |v: &str| json!({"enum": {"type": "answer", "variant": v}});
    let ir = json!({
        "ir_version": 1,
        "name": "orders",
        "enums": [{"name": "answer", "variants": ["success", "forbidden"]}],
        "states": [
            {"name": "charges", "type": {"int": {"min": 0, "max": 2}}, "initial": {"int": 0}},
            {"name": "open", "type": {"bool": {}}, "initial": {"bool": true}}
        ],
        "actions": [
            {"name": "pay", "params": [{"name": "id", "type": {"int": {"min": 0, "max": 1}}}],
             "choices": [{"name": "ok", "type": {"bool": {}}}],
             "guard": {"lt": [charges, {"int": 2}]},
             "updates": [{"target": 0, "expr": {"ite": [ok, {"add": [charges, {"int": 1}]}, charges]}}],
             "output": {"type": {"enum": "answer"}, "expr": {"ite": [ok, answer("success"), answer("forbidden")]}}},
            {"name": "double", "updates": [{"target": 0, "expr": {"add": [charges, {"int": 2}]}}]}
        ],
        "invariants": [{"name": "single", "expr": {"le": [charges, {"int": 1}]}}]
    });
    Arc::new(load(&ir.to_string()).unwrap())
}

fn started(opts: Value) -> Session {
    let mut session = Session::new(orders(), &opts).unwrap();
    let answer = session.start(&json!({"charges": 0, "open": true})).unwrap();
    assert_eq!(answer["status"], "continue", "{answer}");
    session
}

#[test]
fn a_conformance_failure_shows_the_input_and_every_outcome_the_model_allows() {
    let mut session = started(json!({}));
    // 型の値にできない出力は、どの結果とも一致しない。
    let answer = session
        .observe(&json!({"action": "pay", "args": {"id": 1}, "output": "maybe",
                         "observation": {"charges": 2, "open": true}}))
        .unwrap();
    assert_eq!(
        answer,
        json!({
            "status": "conformance_failure",
            "step": 1,
            "candidates": 1,
            "action": "pay",
            "args": {"id": 1},
            "choices": {},
            "expected": [
                {"state": {"charges": 1, "open": true}, "output": {"value": "success"}},
                {"state": {"charges": 0, "open": true}, "output": {"value": "forbidden"}}
            ],
            "observed": {"state": {"charges": 2, "open": true}, "output": "maybe"},
            "mismatch": ["output", "charges"]
        })
    );

    // 注入した選択は入力の一部として示し、期待する結果もその選択の遷移に絞る。
    let mut session = started(json!({"inject": {"pay": ["ok"]}}));
    let input = session.next_input().unwrap();
    assert_eq!(input["status"], "input", "{input}");
    assert_eq!(
        input.as_object().unwrap().keys().collect::<Vec<_>>(),
        ["action", "args", "choices", "status"]
    );
    assert!(input["choices"]["ok"].is_boolean(), "{input}");
    let answer = session
        .observe(
            &json!({"action": "pay", "args": {"id": 0}, "choices": {"ok": true}, "output": "forbidden",
                         "observation": {"charges": 1, "open": false}}),
        )
        .unwrap();
    assert_eq!(answer["choices"], json!({"ok": true}));
    assert_eq!(
        answer["expected"],
        json!([{"state": {"charges": 1, "open": true}, "output": {"value": "success"}}])
    );
    assert_eq!(answer["mismatch"], json!(["output", "open"]));
}

#[test]
fn errors_in_the_model_are_reported_with_the_state_they_occur_in() {
    let mut session = started(json!({}));
    let answer = session
        .observe(&json!({"action": "double", "args": {}, "observation": {"charges": 2, "open": true}}))
        .unwrap();
    assert_eq!(
        answer,
        json!({
            "status": "model_violation",
            "property": {"violation": "invariant", "name": "single"},
            "state": {"charges": 2, "open": true}
        })
    );

    let mut session = started(json!({}));
    let paid = session
        .observe(&json!({"action": "pay", "args": {"id": 0}, "output": "success",
                         "observation": {"charges": 1, "open": true}}))
        .unwrap();
    assert_eq!(paid["status"], "continue", "{paid}");
    let answer = session
        .observe(&json!({"action": "double", "args": {}, "observation": {"charges": 2, "open": true}}))
        .unwrap();
    assert_eq!(
        answer,
        json!({
            "status": "model_error",
            "property": {
                "action": "double", "args": {}, "choices": {}, "site": "update", "target": "charges",
                "error": {"kind": "out_of_range", "value": 3, "type": {"int": {"min": 0, "max": 2}}}
            },
            "state": {"charges": 1, "open": true}
        })
    );
}

#[test]
fn malformed_requests_are_errors_with_a_message() {
    let opts = |o: Value| Session::new(orders(), &o).err().unwrap();
    assert_eq!(
        opts(json!({"observe": "charges"})),
        "observe は状態変数の名前の配列です（\"charges\"）"
    );
    assert_eq!(opts(json!({"observe": ["sold"]})), "未定義の状態変数 \"sold\"");
    assert_eq!(
        opts(json!({"inject": ["pay"]})),
        "inject は、操作名から内部選択の名前の配列へのオブジェクトです（[\"pay\"]）"
    );
    assert_eq!(opts(json!({"inject": {"refund": []}})), "未定義の操作 \"refund\"");
    assert_eq!(
        opts(json!({"inject": {"pay": ["nope"]}})),
        "操作 \"pay\" に内部選択 \"nope\" はありません"
    );
    assert_eq!(
        opts(json!({"max_candidates": 0})),
        "max_candidates は1以上の整数です（0）"
    );

    let mut fresh = Session::new(orders(), &json!({})).unwrap();
    assert_eq!(
        fresh.next_input().unwrap_err(),
        "初期観測を渡す前に、次の入力は選べません"
    );
    assert_eq!(
        fresh.observe(&json!({})).unwrap_err(),
        "初期観測を渡す前に、応答は渡せません"
    );
    assert_eq!(
        fresh.start(&json!({"charges": 0})).unwrap_err(),
        "observation に状態変数 \"open\" がありません"
    );

    let mut session = started(json!({}));
    let observe = |s: &mut Session, report: Value| s.observe(&report).unwrap_err();
    assert_eq!(observe(&mut session, json!([])), "入力はオブジェクトです");
    assert_eq!(observe(&mut session, json!({"args": {}})), "action は操作の名前です");
    assert_eq!(
        observe(&mut session, json!({"action": "refund"})),
        "未定義の操作 \"refund\""
    );
    assert_eq!(
        observe(&mut session, json!({"action": "pay"})),
        "操作 \"pay\" の引数または注入する選択の個数が合いません"
    );
    assert_eq!(
        observe(&mut session, json!({"action": "pay", "args": {"x": 0}})),
        "引数 \"id\" がありません"
    );
    assert!(
        observe(&mut session, json!({"action": "pay", "args": {"id": "one"}})).starts_with("引数 \"id\": "),
        "引数の値の誤りは、引数の名前を示す"
    );
    assert_eq!(
        observe(&mut session, json!({"action": "pay", "args": {"id": 0}})),
        "observation が必要です"
    );
    // 誤った要求は照合を進めない。
    let answer = session
        .observe(&json!({"action": "pay", "args": {"id": 0}, "output": "success",
                         "observation": {"charges": 1, "open": true}}))
        .unwrap();
    assert_eq!(answer["matched"], 1, "{answer}");
    // 型には合うがドメインの外の引数は、読めるが、どの候補でも有効な入力ではない。
    let mut session = started(json!({"actions": ["pay"]}));
    let answer = session
        .observe(&json!({"action": "pay", "args": {"id": 5}, "output": "success",
                         "observation": {"charges": 1, "open": true}}))
        .unwrap();
    assert_eq!(answer, json!({"status": "invalid_input"}));
    // 無効な入力は候補集合を変えずに退けるだけなので、セッションは続く。
    let answer = session
        .observe(&json!({"action": "pay", "args": {"id": 0}, "output": "success",
                         "observation": {"charges": 1, "open": true}}))
        .unwrap();
    assert_eq!(answer["status"], "continue", "{answer}");
}

/// Setの要素の重複は、値のJSONとして不正である。観測値なら、どの値とも一致しない値として不適合にし、
/// 引数なら、要求の誤りにする。
#[test]
fn duplicate_set_elements_are_unrepresentable_observations_and_malformed_arguments() {
    let bit = json!({"int": {"min": 0, "max": 1}});
    let ir = json!({
        "ir_version": 1,
        "name": "bits",
        "states": [{"name": "s", "type": {"set": bit}, "initial": {"set": {"of": bit, "items": []}}}],
        "actions": [{"name": "replace", "params": [{"name": "x", "type": {"set": bit}}],
                     "updates": [{"target": 0, "expr": {"param": 0}}]}]
    });
    let model = Arc::new(load(&ir.to_string()).unwrap());
    let mut session = Session::new(model.clone(), &json!({})).unwrap();
    let answer = session.start(&json!({"s": [0, 0]})).unwrap();
    assert_eq!(answer["status"], "conformance_failure", "{answer}");

    let mut session = Session::new(model, &json!({})).unwrap();
    assert_eq!(session.start(&json!({"s": []})).unwrap()["status"], "continue");
    assert_eq!(
        session
            .observe(&json!({"action": "replace", "args": {"x": [1, 1]}, "observation": {"s": [1]}}))
            .unwrap_err(),
        "引数 \"x\": 要素 1 が重複しています"
    );
    let answer = session
        .observe(&json!({"action": "replace", "args": {"x": [1]}, "observation": {"s": [1, 1]}}))
        .unwrap();
    assert_eq!(answer["status"], "conformance_failure", "{answer}");
    assert_eq!(answer["mismatch"], json!(["s"]), "{answer}");
}

const FINISHED: &str = "セッションは終わっています";

/// 照合を続けない応答（`continue` 以外）のあとは、セッションへの問い合わせを誤りにする。
fn assert_finished(session: &mut Session) {
    let pay = json!({"action": "pay", "args": {"id": 0}, "output": "success",
                     "observation": {"charges": 1, "open": true}});
    assert_eq!(session.next_input().unwrap_err(), FINISHED);
    assert_eq!(session.check_input(&pay).unwrap_err(), FINISHED);
    assert_eq!(session.observe(&pay).unwrap_err(), FINISHED);
    assert_eq!(
        session.start(&json!({"charges": 0, "open": true})).unwrap_err(),
        "初期観測はすでに渡しました"
    );
}

#[test]
fn a_session_that_has_stopped_answers_nothing_more() {
    // 初期観測の不一致。
    let mut session = Session::new(orders(), &json!({})).unwrap();
    let answer = session.start(&json!({"charges": 1, "open": true})).unwrap();
    assert_eq!(answer["status"], "conformance_failure", "{answer}");
    assert_finished(&mut session);

    // 初期観測で候補が上限を超えた。
    let mut session = Session::new(latch(), &json!({"observe": [], "max_candidates": 1})).unwrap();
    let answer = session.start(&json!({})).unwrap();
    assert_eq!(answer["status"], "inconclusive", "{answer}");
    assert_eq!(answer["reason"], "max_candidates", "{answer}");
    assert_finished(&mut session);

    // 有効な入力がない。
    let mut session = Session::new(latch(), &json!({})).unwrap();
    assert_eq!(session.start(&json!({"n": 1})).unwrap()["status"], "continue");
    assert_eq!(session.next_input().unwrap(), json!({"status": "end", "matched": 0}));
    assert_finished(&mut session);

    // 応答の不適合。
    let mut session = started(json!({}));
    let answer = session
        .observe(&json!({"action": "pay", "args": {"id": 0}, "output": "success",
                         "observation": {"charges": 2, "open": true}}))
        .unwrap();
    assert_eq!(answer["status"], "conformance_failure", "{answer}");
    assert_finished(&mut session);

    // モデルの不変条件の違反。
    let mut session = started(json!({}));
    let answer = session
        .observe(&json!({"action": "double", "args": {}, "observation": {"charges": 2, "open": true}}))
        .unwrap();
    assert_eq!(answer["status"], "model_violation", "{answer}");
    assert_finished(&mut session);

    // 誤った要求は、セッションを終わらせない。
    let mut session = started(json!({}));
    assert!(session.observe(&json!({"action": "refund"})).is_err());
    assert_eq!(session.next_input().unwrap()["status"], "input");
}

/// 状態 `n`（0..1）の初期値は0か1。`set` は `n` が0のときだけ有効で、1にする。
fn latch() -> Arc<Model> {
    let n = json!({"var": 0});
    let ir = json!({
        "ir_version": 1,
        "name": "latch",
        "states": [{"name": "n", "type": {"int": {"min": 0, "max": 1}}, "initial_in": [{"int": 0}, {"int": 1}]}],
        "actions": [{"name": "set", "guard": {"eq": [n, {"int": 0}]}, "updates": [{"target": 0, "expr": {"int": 1}}]}]
    });
    Arc::new(load(&ir.to_string()).unwrap())
}

#[test]
fn inputs_are_checked_only_after_the_initial_observation() {
    let mut session = Session::new(orders(), &json!({})).unwrap();
    assert_eq!(
        session
            .check_input(&json!({"action": "pay", "args": {"id": 0}}))
            .unwrap_err(),
        "初期観測を渡す前に、入力は確かめられません"
    );
    // 開始したあとは、有効かどうかを答え、照合は続く。
    let mut session = started(json!({"actions": ["pay"]}));
    let valid = session
        .check_input(&json!({"action": "pay", "args": {"id": 0}}))
        .unwrap();
    assert_eq!(valid, json!({"status": "valid"}));
    let invalid = session
        .check_input(&json!({"action": "pay", "args": {"id": 5}}))
        .unwrap();
    assert_eq!(invalid, json!({"status": "invalid"}));
    assert_eq!(session.next_input().unwrap()["status"], "input");
}
