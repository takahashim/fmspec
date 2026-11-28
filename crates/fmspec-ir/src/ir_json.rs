//! 中核の変換検証（`fmspec_core::ir_check`）に渡す、JSONの木と名前の表。
//!
//! `serde_json::Value` を中核の [`Json`] に機械的に写す。ここは信頼基盤に含まれるので、
//! 名前の解決や意味の判断を含めない。

use fmspec_core::ir_json::{IrNames, Json, Member};
use serde_json::Value;

fn chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

/// JSONの値を中核の木にする。符号付き64ビット整数に収まらない数は `Other` にする。
pub(crate) fn to_json(v: &Value) -> Json {
    match v {
        Value::Null => Json::Null,
        Value::Bool(b) => Json::Bool(*b),
        Value::Number(n) => match n.as_i64() {
            Some(i) => Json::Int(i),
            None => Json::Other,
        },
        Value::String(s) => Json::Str(chars(s)),
        Value::Array(xs) => Json::Arr(xs.iter().map(to_json).collect()),
        Value::Object(m) => Json::Obj(
            m.iter()
                .map(|(k, v)| Member {
                    key: chars(k),
                    value: to_json(v),
                })
                .collect(),
        ),
    }
}

fn names(xs: &[String]) -> Vec<Vec<char>> {
    xs.iter().map(|s| chars(s)).collect()
}

/// 名前の表の中身。
pub(crate) struct NameParts<'a> {
    pub enums: &'a [crate::model::EnumNames],
    pub consts: Vec<String>,
    pub states: &'a [String],
    pub actions: &'a [crate::model::ActionNames],
    pub invariants: &'a [String],
    pub contracts: &'a [String],
    pub fields: Vec<String>,
}

pub(crate) fn ir_names(p: &NameParts) -> IrNames {
    IrNames {
        enums: p.enums.iter().map(|e| chars(&e.name)).collect(),
        variants: p.enums.iter().map(|e| names(&e.variants)).collect(),
        consts: names(&p.consts),
        states: names(p.states),
        actions: p.actions.iter().map(|a| chars(&a.name)).collect(),
        params: p.actions.iter().map(|a| names(&a.params)).collect(),
        choices: p.actions.iter().map(|a| names(&a.choices)).collect(),
        invariants: names(p.invariants),
        contracts: names(p.contracts),
        fields: names(&p.fields),
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
mod tests {
    use super::to_json;
    use crate::model::build;
    use fmspec_core::ir_check::check_ir;
    use fmspec_core::model::{BinOp, Value as CV};
    use fmspec_core::source::TExpr;
    use serde_json::{json, Value};

    /// 状態変数を2つ持ち、局所変数、引数、内部選択、列挙型、Recordを使うモデル。
    fn model() -> Value {
        json!({
            "ir_version": 1,
            "name": "t",
            "enums": [{"name": "color", "variants": ["red", "blue"]}],
            "constants": [{"name": "limit", "type": {"int": {"min": 0, "max": 9}}, "value": {"int": 3}}],
            "states": [
                {"name": "a", "type": {"int": {"min": 0, "max": 9}}, "initial": {"int": 0}},
                {"name": "b", "type": {"int": {"min": 0, "max": 9}}, "initial_in": [{"int": 0}, {"int": 1}]},
                {"name": "c", "type": {"enum": "color"}, "initial": {"enum": {"type": "color", "variant": "red"}}},
                {"name": "r", "type": {"record": [{"name": "x", "type": {"bool": {}}}]},
                 "initial": {"record": [{"name": "x", "expr": {"bool": false}}]}}
            ],
            "actions": [{
                "name": "step",
                "params": [{"name": "p", "type": {"int": {"min": 0, "max": 2}}, "in": {"set": {"of": {"int": {"min": 0, "max": 2}}, "items": [{"int": 1}]}}}],
                "choices": [{"name": "q", "type": {"bool": {}}}],
                "guard": {"let": {"name": "s", "value": {"add": [{"var": 0}, {"param": 0}]},
                                  "body": {"le": [{"local": "s"}, {"const": "limit"}]}}},
                "updates": [
                    {"target": 0, "expr": {"add": [{"var": 0}, {"param": 0}]}},
                    {"target": 1, "expr": {"ite": [{"choice": 0}, {"var": 1}, {"var": 0}]}}
                ]
            }],
            "invariants": [{"name": "inv", "expr": {"forall": {"name": "i", "type": {"int": {"min": 0, "max": 1}},
                "body": {"ge": [{"var": 0}, {"sub": [{"local": "i"}, {"int": 1}]}]}}}}],
            "terminal": {"eq": [{"var": 2}, {"enum": {"type": "color", "variant": "blue"}}]}
        })
    }

    fn accepts(v: &Value, tamper: impl FnOnce(&mut crate::model::Built)) -> bool {
        let mut b = build(v, &[]).expect("組み立てられる");
        tamper(&mut b);
        check_ir(&to_json(v), &b.ir_names, &b.sm)
    }

    #[test]
    fn accepts_the_resolved_model() {
        assert!(accepts(&model(), |_| {}));
        for path in [
            "../../examples/models/tickets.json",
            "../../examples/models/basket.json",
        ] {
            let text = std::fs::read_to_string(path).unwrap();
            let v: Value = serde_json::from_str(&text).unwrap();
            assert!(accepts(&v, |_| {}), "{path}");
        }
    }

    #[test]
    fn rejects_a_wrong_state_variable() {
        assert!(!accepts(&model(), |b| b.sm.actions[0].updates[1].var = 0));
        assert!(!accepts(&model(), |b| {
            if let TExpr::Bin(_, x, _) = &mut b.sm.actions[0].updates[0].expr {
                **x = TExpr::Var(1);
            }
        }));
    }

    #[test]
    fn rejects_a_wrong_operator_or_literal() {
        assert!(!accepts(&model(), |b| {
            if let TExpr::Bin(op, _, _) = &mut b.sm.actions[0].updates[0].expr {
                *op = BinOp::Sub;
            }
        }));
        assert!(!accepts(&model(), |b| b.sm.inits[1][1] = TExpr::Lit(CV::Int(2))));
        assert!(!accepts(&model(), |b| b.sm.inits[2][0] = TExpr::Lit(CV::Enum(0, 1))));
    }

    #[test]
    fn rejects_a_wrong_argument_or_local() {
        // 内部選択を公開引数として読む。
        assert!(!accepts(&model(), |b| {
            if let TExpr::Ite(c, _, _) = &mut b.sm.actions[0].updates[1].expr {
                **c = TExpr::Arg(0);
            }
        }));
        // 局所変数の番号を取り違える。
        assert!(!accepts(&model(), |b| {
            if let TExpr::Quant(_, _, body) = &mut b.sm.invariants[0] {
                if let TExpr::Bin(_, _, y) = &mut **body {
                    if let TExpr::Bin(_, l, _) = &mut **y {
                        **l = TExpr::Local(1);
                    }
                }
            }
        }));
        // 動的ドメインの検査を落とす。
        assert!(!accepts(&model(), |b| {
            if let TExpr::Fold(_, es) = &mut b.sm.actions[0].guard {
                es.remove(0);
            }
        }));
    }

    #[test]
    fn rejects_wrong_names() {
        assert!(!accepts(&model(), |b| b.ir_names.states.swap(0, 1)));
        assert!(!accepts(&model(), |b| b.ir_names.variants[0].swap(0, 1)));
        assert!(!accepts(&model(), |b| b.ir_names.fields[0] = "y".chars().collect()));
        assert!(!accepts(&model(), |b| b.ir_names.params[0].clear()));
    }

    #[test]
    fn rejects_missing_or_extra_definitions() {
        assert!(!accepts(&model(), |b| b.sm.terminal = None));
        assert!(!accepts(&model(), |b| {
            b.sm.invariants.pop();
            b.ir_names.invariants.pop();
        }));
        assert!(!accepts(&model(), |b| b.sm.constraint = Some(TExpr::Lit(CV::Bool(true)))));
    }
}
