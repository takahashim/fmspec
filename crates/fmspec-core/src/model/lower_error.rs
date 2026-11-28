//! モデルの下ろしが返す誤り（`LowerError`）と、その分類（利用者の誤りか、型の誤りか）。

use crate::kernel::eval::ErrKind;
use vstd::prelude::*;

verus! {

/// 下ろしの失敗の理由。
pub enum Fault {
    /// 式を下ろせない（型が合わない、または参照が未定義）。
    Lower,
    /// 式の評価に失敗した。範囲外の値は `OutOfRange` である。
    Eval(ErrKind),
    /// 局所変数の束縛の深さが上限に達した（式が大きすぎる）。
    Depth,
}

/// 下ろしの失敗の場所。
pub enum LowerError {
    /// 状態変数の型が整形式でないか、符号化が大きすぎる。
    State(usize),
    /// 定数。
    Const(usize, Fault),
    /// 状態変数 `.0` の `.1` 番目の初期値の候補。
    Init(usize, usize, Fault),
    /// 初期値の候補の列の数が状態変数の数と違うか、候補の組み合わせが多すぎる。
    InitCount,
    /// 初期条件。
    Constraint(Fault),
    /// 初期条件を満たす初期状態がない。
    NoInit,
    /// 操作 `.0` の `.1` 番目の引数の型。
    Args(usize, usize),
    /// 操作のguard。
    Guard(usize),
    /// 操作 `.0` の `.1` 番目の代入。
    Update(usize, usize),
    /// 操作の出力。
    Output(usize),
    /// 不変条件。
    Invariant(usize),
    /// 遷移契約。
    Contract(usize),
    /// 終端条件。
    Terminal,
    /// モデルの式が型を持たないか、大きさの条件を満たさない（[`crate::model::model_total::model_typed`] が偽）。
    Type,
    /// 局所変数の束縛の深さが上限に達した（式が大きすぎる）。
    Depth,
    /// 詳細化の検査の写像の式（添字）が、置く場所の型を持たない。
    Mapping(usize),
}

/// 型の誤り。`fmspec-ir` の型検査を通ったモデルでは起きない。
pub open spec fn type_err(e: LowerError) -> bool {
    e is Type || e is State || e is Args
}

/// 利用者の誤り（値の評価の失敗、初期状態の数、式の大きさ）。これ以外は内部の誤りである。
pub open spec fn user_err(e: LowerError) -> bool {
    match e {
        LowerError::Const(_, f) => !(f is Lower),
        LowerError::Init(_, _, f) => !(f is Lower),
        LowerError::Constraint(f) => !(f is Lower),
        LowerError::InitCount => true,
        LowerError::NoInit => true,
        LowerError::Depth => true,
        _ => false,
    }
}

} // verus!
