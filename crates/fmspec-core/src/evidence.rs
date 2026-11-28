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

/// 証拠を得られなかった理由。判定ゲートは理由を記録するだけで、判定は理由によらず `Inconclusive` である。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limit {
    /// 状態数の上限。
    MaxStates,
    /// 中断要求。
    Interrupted,
    /// 証拠の検査の資源上限。
    CheckBudget,
    /// 探索の深さ（初期状態からの遷移数）の上限。
    MaxDepth,
    /// 時間の上限。
    MaxTime,
    /// 詳細化の検査で、写した状態からの抽象モデルの遷移列挙が評価エラーになった。
    AbstractFailed,
}

pub enum Evidence {
    Certificate(Certificate),
    /// 開始状態、ステップ、末尾の事象の主張。
    Trace(Vec<i64>, Vec<TraceStep>, Claim),
    Unavailable(Limit),
}

/// 詳細化の証明書を拒否した理由。具体モデルの安全性の理由（`Reject` のほかの値）には入らない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefReject {
    /// 証明書の状態（添字）か、その遷移先で、写像のスロット（添字）の評価が失敗する。
    MappingFailed(usize, usize),
    /// 証明書の状態（添字）からの操作（添字）の遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写らない。
    StepNotMapped(usize, usize),
    /// 初期状態（添字）で、写像のスロット（添字）の評価が失敗する。
    InitialMappingFailed(usize, usize),
    /// 初期状態（添字）が、抽象モデルの初期状態に写らない。
    InitialNotMapped(usize),
}

/// 証拠を拒否した理由。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    /// 証明書の検査条件が、要求された検査条件と一致しない。対象の操作、不変条件、遷移契約と、デッドロック検査の
    /// 有無を比べる。列の長さは問わず、列より後ろとモデルにない添字は対象外として比べる。
    ConditionMismatch,
    /// 証明書が初期状態（添字）を含まない。
    MissingInitial(usize),
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
    /// トレースの開始状態が初期状態でない。
    BadStart,
    /// トレースのステップ（添字）の操作が未定義か対象外、または引数がドメインに従わない。
    BadStep(usize),
    /// トレースのステップ（添字）が、モデルの遷移と一致しない。
    StepMismatch(usize),
    /// トレースは有効だが、末尾で主張どおりの事象が起きない。
    ClaimNotReproduced,
    /// 詳細化の証明書に特有の理由。
    Refine(RefReject),
    /// 宣言した入れ替え（添字）が、モデルと検査条件の対称性ではない。
    NotSymmetric(usize),
}

/// 詳細化が破れる事象の主張。トレースの末尾について述べる。
pub enum RefClaim {
    /// 開始状態（トレースの長さは0）を写した状態が、抽象モデルの初期状態でない。
    Init,
    /// 最後の遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写らない。
    Step,
    /// 末尾の状態で、写像のスロット（添字）の評価または符号化が失敗する。
    Map(usize, ErrKind),
    /// 具体モデルそのものについての主張（操作の評価の失敗など）。
    Model(Claim),
}

/// 詳細化の証拠。
pub enum RefEvidence {
    /// 具体モデルの証明書。
    Certificate(Certificate),
    /// 開始状態、ステップ、末尾の事象の主張。
    Trace(Vec<i64>, Vec<TraceStep>, RefClaim),
    Unavailable(Limit),
}

} // verus!
