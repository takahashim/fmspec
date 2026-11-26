//! 証拠の型。探索器が生成し、判定ゲートが検査する（仕様書 §3.1、§7.1）。

use crate::eval::*;
use crate::semantics::*;
use crate::step::*;
use vstd::prelude::*;

verus! {

/// 安全性証明書。状態集合と、それを作成したときの検査条件を持つ。
/// 状態は符号化列の辞書順に整列しておく（仕様書 §7.3）。
pub struct Certificate {
    pub conditions: Conditions,
    pub states: Vec<Vec<i64>>,
}

/// トレースの1ステップ。操作、引数（公開引数と内部選択）、出力、遷移後の状態。
pub struct TraceStep {
    pub action: usize,
    pub args: Vec<i64>,
    pub output: Option<i64>,
    pub state: Vec<i64>,
}

/// トレースの末尾で起きる事象の主張。
pub enum Claim {
    /// 末尾の状態で不変条件が偽。
    Invariant(usize),
    /// 最後の遷移で遷移契約が偽。
    Contract(usize),
    /// 末尾の状態は終端でなく、有効な遷移がない。
    Deadlock,
    /// 末尾の状態で不変条件の評価が失敗する。
    InvariantError(usize, ErrKind),
    /// 最後の遷移で遷移契約の評価が失敗する。
    ContractError(usize, ErrKind),
    /// 末尾の状態に有効な遷移がなく、終端条件の評価が失敗する。
    TerminalError(ErrKind),
    /// 末尾の状態で、操作と引数を適用すると、指定の箇所の評価または更新が失敗する。
    StepError(usize, Vec<i64>, Site, ErrKind),
}

/// 証拠を得られなかった理由。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limit {
    /// 状態数の上限。
    MaxStates,
    /// 中断要求。
    Interrupted,
}

pub enum Evidence {
    Certificate(Certificate),
    Trace(Vec<TraceStep>, Claim),
    Unavailable(Limit),
}

/// 証拠を拒否した理由。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    /// 証明書の検査条件が、要求された検査条件と一致しない。
    ConditionMismatch,
    /// 証明書が初期状態を含まない。
    MissingInitial,
    /// 証明書の状態（添字）が状態型に従わない。
    IllTypedState(usize),
    /// 証明書の状態で、不変条件が真に評価されない。
    InvariantNotHeld(usize, usize),
    /// 証明書の状態で、操作の評価が失敗する。
    StepFailed(usize, usize),
    /// 証明書の状態からの操作の遷移先が、証明書に含まれない。
    MissingSuccessor(usize, usize),
    /// 証明書の状態からの遷移で、遷移契約が真に評価されない。
    ContractNotHeld(usize, usize),
    /// 証明書の状態が非終端のデッドロックである。
    Deadlock(usize),
    /// トレースのステップ（添字）の操作が未定義か対象外、または引数がドメインに従わない。
    BadStep(usize),
    /// トレースのステップ（添字）が、モデルの遷移と一致しない。
    StepMismatch(usize),
    /// トレースは有効だが、末尾で主張どおりの事象が起きない。
    ClaimNotReproduced,
}

} // verus!
