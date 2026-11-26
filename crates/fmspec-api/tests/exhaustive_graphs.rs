//! 3状態の全有向グラフで、公開JSON APIを通してIR変換・探索・証拠の検査を照合する。
#![allow(clippy::unwrap_used, clippy::expect_used)]

use fmspec_api::{check, load, replay, verify_certificate};
use serde_json::{json, Value};

const VERTICES: usize = 3;

fn has_edge(graph: usize, from: usize, to: usize) -> bool {
    graph & (1 << (from * VERTICES + to)) != 0
}

fn actions(graph: usize, expressions: &[Value]) -> Vec<Value> {
    let mut result = Vec::new();
    for (from, source) in expressions.iter().enumerate() {
        for (to, target) in expressions.iter().enumerate() {
            if has_edge(graph, from, to) {
                result.push(json!({
                    "name": format!("edge_{from}_{to}"),
                    "guard": {"eq": [{"var": 0}, source]},
                    "updates": [{"target": 0, "expr": target}]
                }));
            }
        }
    }
    result
}

// expressions はIRの式、values は証明書・トレースに現れる公開JSON値。
// 両方を明示し、エンジンの符号化関数を期待値の計算に使わない。
struct Encoding {
    ty: Value,
    expressions: [Value; VERTICES],
    values: [Value; VERTICES],
}

#[test]
fn option_graphs() {
    let bit = json!({"int": {"min": 0, "max": 1}});
    check_all_graphs(Encoding {
        ty: json!({"option": bit}),
        expressions: [
            json!({"none": bit}),
            json!({"some": [{"int": 0}]}),
            json!({"some": [{"int": 1}]}),
        ],
        values: [Value::Null, json!({"some": 0}), json!({"some": 1})],
    });
}

#[test]
fn enum_graphs() {
    // 頂点順とenumの宣言順を変え、内部の添字に依存した比較を検出する。
    let labels = ["middle", "last", "first"];
    check_all_graphs(Encoding {
        ty: json!({"enum": "position"}),
        expressions: labels.map(|label| json!({"enum": {"type": "position", "variant": label}})),
        values: labels.map(|label| json!(label)),
    });
}

#[test]
fn record_graphs() {
    // どちらか一方のフィールドを無視すると、別々の2頂点が同一になる。
    let vertices = [(1, 0), (0, 0), (0, 1)];
    let bit = json!({"int": {"min": 0, "max": 1}});
    check_all_graphs(Encoding {
        ty: json!({"record": [{"name": "x", "type": bit}, {"name": "y", "type": bit}]}),
        expressions: vertices.map(|(x, y)| {
            json!({"record": [
                {"name": "x", "expr": {"int": x}}, {"name": "y", "expr": {"int": y}}
            ]})
        }),
        values: vertices.map(|(x, y)| json!({"x": x, "y": y})),
    });
}

fn check_all_graphs(encoding: Encoding) {
    let Encoding {
        ty,
        expressions,
        values,
    } = encoding;
    for graph in 0..(1 << (VERTICES * VERTICES)) {
        let ir = json!({
            "ir_version": 1, "name": "graph",
            "enums": [{"name": "position", "variants": ["first", "middle", "last"]}],
            "states": [{"name": "vertex", "type": ty, "initial": expressions[0]}],
            "actions": actions(graph, &expressions),
            "invariants": [{"name": "avoid_target", "expr": {"ne": [{"var": 0}, expressions[2]]}}]
        });
        let model = load(&ir.to_string()).unwrap();
        let options = json!({"invariants": []});
        let result = check(&model, &json!({"invariants": [], "certificate": true}), None).unwrap();
        assert_eq!(result["status"], "verified", "graph={graph}: {result}");
        let mut cert = result["certificate"].clone();

        // 3頂点なら、到達できる頂点には長さ2以下の単純路がある。エンジンのBFSは使わない。
        let reachable = |v| {
            v == 0
                || has_edge(graph, 0, v)
                || (0..VERTICES).any(|middle| has_edge(graph, 0, middle) && has_edge(graph, middle, v))
        };
        let rows: Vec<_> = (0..VERTICES)
            .filter(|&v| reachable(v))
            .map(|v| json!([values[v]]))
            .collect();
        let actual = cert["states"].as_array().unwrap();
        assert_eq!(actual.len(), rows.len(), "graph={graph}");
        assert!(rows.iter().all(|row| actual.contains(row)), "graph={graph}: {actual:?}");

        // 帰納的な上位集合を含め、8通りの候補集合の受理・拒否を直接計算する。
        for mask in 0usize..(1 << VERTICES) {
            let contains = |v: usize| mask & (1 << v) != 0;
            let closed = (0..VERTICES)
                .filter(|&v| contains(v))
                .all(|v| (0..VERTICES).all(|w| !has_edge(graph, v, w) || contains(w)));
            cert["states"] = json!((0..VERTICES)
                .filter(|&v| contains(v))
                .map(|v| json!([values[v]]))
                .collect::<Vec<_>>());
            let verdict = verify_certificate(&model, &cert.to_string(), &options).unwrap();
            let expected = if contains(0) && closed { "verified" } else { "rejected" };
            assert_eq!(verdict["status"], expected, "graph={graph}, mask={mask}: {verdict}");
        }

        let checked = check(&model, &json!({}), None).unwrap();
        if reachable(2) {
            assert_eq!(checked["status"], "violated", "graph={graph}: {checked}");
            let trace = &checked["trace"];
            let steps = trace["steps"].as_array().unwrap();
            let expected_len = if has_edge(graph, 0, 2) { 1 } else { 2 };
            assert_eq!(steps.len(), expected_len, "graph={graph}");
            assert_eq!(trace["initial"]["vertex"], values[0], "graph={graph}");
            let mut from = 0;
            for step in steps {
                let to = values
                    .iter()
                    .position(|value| *value == step["state"]["vertex"])
                    .expect("既知の頂点");
                assert!(has_edge(graph, from, to), "graph={graph}: {from} → {to}");
                assert_eq!(step["action"], format!("edge_{from}_{to}"), "graph={graph}");
                from = to;
            }
            assert_eq!(from, 2, "graph={graph}");
            assert_eq!(
                replay(&model, &trace.to_string())["status"],
                "violated",
                "graph={graph}"
            );
            // 操作列はそのままで末尾の公開値だけを別頂点に差し替える。
            let mut altered = trace.clone();
            altered["steps"][steps.len() - 1]["state"]["vertex"] = values[0].clone();
            assert_eq!(
                replay(&model, &altered.to_string())["status"],
                "rejected",
                "graph={graph}"
            );
        } else {
            assert_eq!(checked["status"], "verified", "graph={graph}: {checked}");
        }
    }
}
