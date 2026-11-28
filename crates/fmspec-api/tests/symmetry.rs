//! 対称性による削減の判定ゲート（`decide_symmetric`）。宣言を信用しないこと、代表元の証明書の検査。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_api::{check, load, Model};
use fmspec_core::evidence::{Certificate, Evidence, Reject};
use fmspec_core::gate::{decide_symmetric, VerdictKind};
use fmspec_ir::default_conditions;
use fmspec_search::{bfs, bfs_sym, BfsOptions};
use serde_json::{json, Value};

/// 2つのカウンタ。上限が同じなら対称である。
fn pair(max_a: i64, max_b: i64) -> Model {
    let counter = |name: &str, var: usize, max: i64| {
        json!({
            "name": name,
            "guard": {"lt": [{"var": var}, {"int": max}]},
            "updates": [{"target": var, "expr": {"add": [{"var": var}, {"int": 1}]}}]
        })
    };
    let ir: Value = json!({
        "ir_version": 1,
        "name": "pair",
        "states": [
            {"name": "a", "type": {"int": {"min": 0, "max": 2}}, "initial": {"int": 0}},
            {"name": "b", "type": {"int": {"min": 0, "max": 2}}, "initial": {"int": 0}}
        ],
        "actions": [counter("inc_a", 0, max_a), counter("inc_b", 1, max_b)],
        "invariants": [{"name": "small", "expr": {"le": [{"var": 0}, {"int": 2}]}}],
        "symmetry": [[["a"], ["b"]]]
    });
    load(&ir.to_string()).unwrap()
}

#[test]
fn the_gate_checks_the_symmetry_itself() {
    let m = pair(2, 1);
    let cond = default_conditions(&m, false);
    let full = bfs(m.checked(), &cond, &BfsOptions::default()).evidence.unwrap();
    let v = decide_symmetric(m.checked(), &cond, &m.names.symmetry, &full);
    assert_eq!(v.kind(), VerdictKind::Rejected);
    assert_eq!(v.reject(), Some(Reject::NotSymmetric(0)));
    // 検査は、対称でないことを報告する。
    assert!(check(&m, &json!({}), None)
        .unwrap_err()
        .contains("対称性が成り立ちません"));
}

#[test]
fn representatives_and_supersets_are_accepted_and_missing_representatives_are_rejected() {
    let m = pair(2, 2);
    let cond = default_conditions(&m, false);
    let sw = fmspec_core::sym::symmetry_of(m.checked(), &cond, &m.names.symmetry).unwrap();
    let (reduced, stats) = bfs_sym(m.checked(), &cond, &sw, &BfsOptions::default());
    let reduced = reduced.unwrap();
    assert_eq!(stats.visited_states, 6);
    let v = decide_symmetric(m.checked(), &cond, &m.names.symmetry, &reduced);
    assert_eq!(v.kind(), VerdictKind::Verified);

    // すべての状態を含む証明書も、代表元の証明書として受理する。
    let full = bfs(m.checked(), &cond, &BfsOptions::default()).evidence.unwrap();
    let v = decide_symmetric(m.checked(), &cond, &m.names.symmetry, &full);
    assert_eq!(v.kind(), VerdictKind::Verified);

    // 代表元を1つ欠くと拒否する。
    let Evidence::Certificate(cert) = reduced else {
        panic!("証明書ではない");
    };
    let mut states = cert.states.clone();
    states.retain(|s| s != &vec![1, 1]);
    let forged = Evidence::Certificate(Certificate {
        conditions: cond.clone(),
        states,
    });
    let v = decide_symmetric(m.checked(), &cond, &m.names.symmetry, &forged);
    assert_eq!(v.kind(), VerdictKind::Rejected);
    assert!(
        matches!(v.reject(), Some(Reject::MissingSuccessor(_, _))),
        "{:?}",
        v.reject()
    );
}

#[test]
fn the_check_reports_the_symmetry() {
    let m = pair(2, 2);
    let r = check(&m, &json!({}), None).unwrap();
    assert_eq!(r["status"], "verified");
    assert_eq!(r["search"]["visited_states"], 6);
    assert_eq!(r["symmetry"], json!({"groups": [2], "swaps": 1}));
    let r = check(&m, &json!({"symmetry": false}), None).unwrap();
    assert_eq!(r["search"]["visited_states"], 9);
    assert_eq!(r["symmetry"], Value::Null);
}
