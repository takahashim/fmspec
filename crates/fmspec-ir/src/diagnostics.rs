//! 中核の下ろしと中核のIR検証が返す誤りを、IRの定義の名前と位置で説明する。

use crate::model::{invalid, LoadError, Names};
use crate::resolve::Constant;
use fmspec_core::eval::ErrKind;
use fmspec_core::model_lower::MAX_INITIAL_CANDIDATES;
use fmspec_core::smodel::{Fault, LowerError};
use fmspec_core::typing::InvalidModel;

/// 中核の下ろしの失敗を、読み込みの誤りにする。
/// 型の誤りと未定義の参照は名前解決で報告するので、残るのは値の評価の失敗と、型の不正である。
pub(crate) fn lower_error(
    e: LowerError,
    names: &Names,
    constants: &[Constant],
    choice_paths: &[Vec<String>],
) -> LoadError {
    let internal = |path: &str| LoadError::Schema {
        path: path.to_string(),
        message: "内部エラー: 中核の下ろしが式を受理しません".to_string(),
    };
    let too_deep = |path: &str| LoadError::Schema {
        path: path.to_string(),
        message: "式が大きすぎます（局所変数の束縛が深すぎます）".to_string(),
    };
    let eval = |path: &str, k: ErrKind| LoadError::Schema {
        path: path.to_string(),
        message: format!("値を評価できません（{k:?}）"),
    };
    let reason = |r: InvalidModel| invalid(r, describe(&r, names));
    match e {
        LowerError::State(i) => reason(InvalidModel::StateType(i)),
        LowerError::Const(i, f) => {
            let path = format!("$.constants[{i}].value");
            match f {
                Fault::Lower => internal(&path),
                Fault::Depth => too_deep(&path),
                Fault::Eval(ErrKind::OutOfRange(x)) => LoadError::Schema {
                    message: format!("定数 {:?} の値 {x} が型の範囲の外です", constants[i].name),
                    path,
                },
                Fault::Eval(k) => eval(&path, k),
            }
        }
        LowerError::Init(i, j, f) => {
            let path = &choice_paths[i][j];
            match f {
                Fault::Lower => internal(path),
                Fault::Depth => too_deep(path),
                Fault::Eval(ErrKind::OutOfRange(x)) => invalid(
                    InvalidModel::Initial(j),
                    format!(
                        "{path}: 状態変数 {:?} の初期値 {x} が型の範囲外です",
                        names.states.get(i).map(String::as_str).unwrap_or("?")
                    ),
                ),
                Fault::Eval(k) => eval(path, k),
            }
        }
        LowerError::InitCount => LoadError::Schema {
            path: "$.states".to_string(),
            message: format!("初期値の候補の組み合わせが {MAX_INITIAL_CANDIDATES} 個を超えます"),
        },
        LowerError::Constraint(Fault::Lower) => internal("$.initial_constraint"),
        LowerError::Constraint(Fault::Depth) => too_deep("$.initial_constraint"),
        LowerError::Constraint(Fault::Eval(k)) => LoadError::Schema {
            path: "$.initial_constraint".to_string(),
            message: format!("初期条件を評価できません（{k:?}）"),
        },
        LowerError::NoInit => LoadError::Schema {
            path: "$.initial_constraint".to_string(),
            message: "初期条件を満たす初期状態がありません".to_string(),
        },
        LowerError::Args(a, d) => reason(InvalidModel::Domain(a, d)),
        LowerError::Guard(a) => reason(InvalidModel::Guard(a)),
        LowerError::Update(a, u) => reason(InvalidModel::Update(a, u)),
        LowerError::Output(a) => reason(InvalidModel::Output(a)),
        LowerError::Invariant(i) => reason(InvalidModel::Invariant(i)),
        LowerError::Contract(k) => reason(InvalidModel::Contract(k)),
        LowerError::Terminal => reason(InvalidModel::Terminal),
        LowerError::Type => LoadError::Schema {
            path: "$".to_string(),
            message: "内部エラー: fmspec-ir と中核の型検査が食い違います".to_string(),
        },
        LowerError::Depth => too_deep("$"),
        LowerError::Mapping(_) => internal("$"),
    }
}

/// 中核のIR検証が返した理由の添字（スロットと中核の更新）を、IRの定義の添字に戻す。
pub(crate) fn user_reason(reason: InvalidModel, names: &Names) -> InvalidModel {
    let update = |a: usize, k: usize| {
        names
            .actions
            .get(a)
            .and_then(|act| act.updates.get(k))
            .map(|o| o.update)
            .unwrap_or(k)
    };
    match reason {
        InvalidModel::StateType(i) => InvalidModel::StateType(names.state_of_slot(i).map(|(v, _)| v).unwrap_or(i)),
        InvalidModel::Domain(a, d) => InvalidModel::Domain(
            a,
            names
                .actions
                .get(a)
                .and_then(|act| act.arg_of_slot(d))
                .map(|(x, _)| x)
                .unwrap_or(d),
        ),
        InvalidModel::Update(a, k) => InvalidModel::Update(a, update(a, k)),
        InvalidModel::DuplicateUpdate(a, k) => InvalidModel::DuplicateUpdate(a, update(a, k)),
        other => other,
    }
}

pub(crate) fn describe(reason: &InvalidModel, names: &Names) -> String {
    let action = |a: &usize| names.actions[*a].name.as_str();
    match reason {
        InvalidModel::EmptyEnum(i) => format!("列挙型 {:?} にラベルがありません", names.enums[*i].name),
        InvalidModel::StateType(i) => {
            format!(
                "状態変数 {:?} の型が不正です（空の整数範囲、または未定義の列挙型）",
                names.states.get(*i).map(String::as_str).unwrap_or("?")
            )
        }
        InvalidModel::NoInitial => "初期状態がありません".to_string(),
        InvalidModel::Initial(_) => "初期値が状態変数の型の範囲外です".to_string(),
        InvalidModel::Params(a) => format!("操作 {:?} の引数の個数が不正です", action(a)),
        InvalidModel::Domain(a, d) => {
            let act = &names.actions[*a];
            let name = act.arg_names().nth(*d).map(String::as_str).unwrap_or("?");
            format!(
                "操作 {:?} の引数 {name:?} のドメインが不正です（空の整数範囲、または未定義の列挙型）",
                act.name
            )
        }
        InvalidModel::Guard(a) => {
            format!(
                "操作 {:?} の guard が Bool 式でないか、未定義の参照を含みます",
                action(a)
            )
        }
        InvalidModel::Update(a, u) => format!(
            "操作 {:?} の {} 番目の更新が不正です（対象が未定義、または式の型が対象と合わない）",
            action(a),
            u + 1
        ),
        InvalidModel::DuplicateUpdate(a, u) => {
            format!(
                "操作 {:?} の {} 番目の更新は、同じ状態変数への重複代入です",
                action(a),
                u + 1
            )
        }
        InvalidModel::Output(a) => format!("操作 {:?} の出力の型または式が不正です", action(a)),
        InvalidModel::Invariant(i) => {
            format!(
                "不変条件 {:?} が Bool 式でないか、未定義の参照を含みます",
                names.invariants[*i]
            )
        }
        InvalidModel::Contract(c) => {
            format!(
                "遷移契約 {:?} が Bool 式でないか、未定義の参照を含みます",
                names.contracts[*c]
            )
        }
        InvalidModel::Terminal => "終端条件が Bool 式でないか、未定義の参照を含みます".to_string(),
    }
}
