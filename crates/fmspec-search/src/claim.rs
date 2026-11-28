//! 状態と遷移の性質を検査し、違反の主張を作る。幅優先探索とシミュレーションで共有する。

use fmspec_core::checked::CheckedModel;
use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::Claim;
use fmspec_core::semantics::Conditions;

/// 検査条件の選択 `mask` で、`i` 番目が対象か。範囲外は対象外とする。
pub(crate) fn selected(mask: &[bool], i: usize) -> bool {
    mask.get(i).copied().unwrap_or(false)
}

/// 性質の検査結果を主張にする。評価エラーなら `failed`、偽なら `violated` である。
fn property_claim(
    index: usize,
    value: Result<bool, ErrKind>,
    violated: fn(usize) -> Claim,
    failed: fn(usize, ErrKind) -> Claim,
) -> Claim {
    match value {
        Err(e) => failed(index, e),
        Ok(_) => violated(index),
    }
}

/// 状態 `s` が満たさない不変条件の主張。すべて満たせば `None`。
pub(crate) fn invariant_claim(model: &CheckedModel, cond: &Conditions, s: &Vec<i64>) -> Option<Claim> {
    let (i, v) = model.invariants(cond, s)?;
    Some(property_claim(i, v, Claim::Invariant, Claim::InvariantError))
}

/// 遷移が満たさない遷移契約の主張。すべて満たせば `None`。
pub(crate) fn contract_claim(
    model: &CheckedModel,
    cond: &Conditions,
    action: usize,
    pre: &Vec<i64>,
    args: &Vec<i64>,
    post: &Vec<i64>,
    output: &Option<i64>,
) -> Option<Claim> {
    let (k, v) = model.contracts(cond, action, pre, args, post, output)?;
    Some(property_claim(k, v, Claim::Contract, Claim::ContractError))
}

/// 有効な遷移のない状態 `s` が終端でなければ、デッドロックの主張。終端なら `None`。
pub(crate) fn deadlock_claim(model: &CheckedModel, s: &Vec<i64>) -> Option<Claim> {
    match model.terminal(s) {
        Ok(true) => None,
        Ok(false) => Some(Claim::Deadlock),
        Err(e) => Some(Claim::TerminalError(e)),
    }
}
