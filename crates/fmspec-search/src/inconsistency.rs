//! 探索器の内部の不整合（仕様書 §8.3 の `InternalError`）。
//!
//! 不整合は、探索器が前提とする性質が破れたことを表し、fmspec の不具合を示す。
//! 判定ゲートが検査する証拠ではないので、中核の `Evidence` や `Limit` には含めない。
//! 探索器は不整合を見つけたら探索をやめ、証拠の代わりに不整合を返す。
//! 検査の経路（`check`、`sample`）は、それを中断や資源上限と区別して `Status::InternalError` にする。

use fmspec_core::gate::CheckedModel;
use fmspec_core::step::Enumerated;

/// 探索器の内部の不整合。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Inconsistency {
    /// 状態 `state` での操作 `action` の遷移を列挙できなかった。
    /// `CheckedModel::successors` は、操作の添字が範囲外か、状態が状態型に従わないときに列挙しない。
    /// 探索器は定義済みの操作を、初期状態と列挙した遷移先の状態でだけ列挙するので、ここには来ないはずである。
    Successors { action: usize, state: Vec<i64> },
    /// 対称性による削減で、代表元の経路から具体的なトレースを作れなかった。
    /// 宣言した入れ替えは判定ゲートが対称性と確かめているので、ここには来ないはずである。
    SymmetryTrace,
}

/// 状態 `s` での操作 `a` の有効な遷移を列挙する。列挙できなければ、不整合として返す。
pub(crate) fn successors(model: &CheckedModel, a: usize, s: &Vec<i64>) -> Result<Enumerated, Inconsistency> {
    model.successors(a, s).ok_or_else(|| Inconsistency::Successors {
        action: a,
        state: s.clone(),
    })
}

#[cfg(test)]
pub(crate) mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

    use super::{successors, Inconsistency};
    use fmspec_core::step::Enumerated;
    use fmspec_ir::{load, Model};
    use serde_json::json;

    /// 1つの状態変数 `x`（`0..=3`、初期値0）と、`x` を1増やす操作 `inc` を持つモデル。
    pub(crate) fn counter() -> Model {
        let ir = json!({
            "ir_version": 1,
            "name": "counter",
            "states": [{"name": "x", "type": {"int": {"min": 0, "max": 3}}, "initial": {"int": 0}}],
            "actions": [{
                "name": "inc",
                "guard": {"lt": [{"var": 0}, {"int": 3}]},
                "updates": [{"target": 0, "expr": {"add": [{"var": 0}, {"int": 1}]}}]
            }],
            "invariants": [{"name": "small", "expr": {"le": [{"var": 0}, {"int": 3}]}}]
        });
        load(&ir.to_string()).unwrap()
    }

    #[test]
    fn a_state_of_the_wrong_length_is_an_inconsistency() {
        let m = counter();
        assert_eq!(
            successors(m.checked(), 0, &vec![0, 0]).err(),
            Some(Inconsistency::Successors {
                action: 0,
                state: vec![0, 0]
            })
        );
    }

    #[test]
    fn a_state_outside_its_type_is_an_inconsistency() {
        let m = counter();
        assert!(matches!(
            successors(m.checked(), 0, &vec![4]).err(),
            Some(Inconsistency::Successors { action: 0, .. })
        ));
    }

    #[test]
    fn an_undefined_action_is_an_inconsistency() {
        let m = counter();
        assert_eq!(
            successors(m.checked(), 1, &vec![0]).err(),
            Some(Inconsistency::Successors {
                action: 1,
                state: vec![0]
            })
        );
    }

    #[test]
    fn a_defined_action_in_a_well_typed_state_is_enumerated() {
        let m = counter();
        let Ok(Enumerated::Ok(ts)) = successors(m.checked(), 0, &vec![0]) else {
            panic!("列挙できるはずです");
        };
        assert_eq!(ts.len(), 1);
        assert_eq!(ts[0].state, vec![1]);
    }
}
