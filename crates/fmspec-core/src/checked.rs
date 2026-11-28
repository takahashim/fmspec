//! IR検証を通ったモデル（`CheckedModel`）。フィールドは非公開で、`validate` を通らずには作れない。

use crate::eval::ErrKind;
use crate::model::RawModel;
#[cfg(verus_keep_ghost)]
use crate::semantics::terminal_spec;
use crate::semantics::{check_contracts, check_invariants, eval_terminal, Conditions};
#[cfg(verus_keep_ghost)]
use crate::semantics::{con_on, con_spec, cons_hold, inv_on, inv_spec, invs_hold, not_true};
use crate::state_enc::vals_ok_exec;
#[cfg(verus_keep_ghost)]
use crate::state_enc::{args_ok, state_ok};
use crate::step::{enumerate, step, Enumerated, StepR};
#[cfg(verus_keep_ghost)]
use crate::step::{enumerated_ok, step_spec};
#[cfg(verus_keep_ghost)]
use crate::typing::wf;
use crate::typing::{validate_raw, InvalidModel};
use vstd::prelude::*;

verus! {

/// IR検証を通過したモデル。`validate` だけが構築する。
pub struct CheckedModel {
    raw: RawModel,
}

impl CheckedModel {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        wf(self.raw)
    }

    pub closed spec fn view(self) -> RawModel {
        self.raw
    }

    /// 検証済みのモデルの中身。整形式である。
    pub fn raw(&self) -> (r: &RawModel)
        ensures
            *r == self@,
            wf(*r),
    {
        proof {
            use_type_invariant(self);
        }
        &self.raw
    }

    /// 初期状態の符号化列。1つ以上ある。
    pub fn initials(&self) -> (r: &Vec<Vec<i64>>)
        ensures
            *r == self@.inits,
            r@.len() >= 1,
    {
        proof {
            use_type_invariant(self);
        }
        &self.raw.inits
    }

    /// 符号化列が状態型に従うか。
    pub fn state_ok(&self, s: &Vec<i64>) -> (r: bool)
        ensures
            r == state_ok(self@, s@),
    {
        vals_ok_exec(&self.raw.enums, &self.raw.state_types, s)
    }

    /// 状態 `s` での操作 `a` の有効な遷移を、引数の辞書順に、漏れなく列挙する。
    /// 操作が未定義か、状態が状態型に従わなければ `None`。それ以外は `Some`。
    pub fn successors(&self, a: usize, s: &Vec<i64>) -> (r: Option<Enumerated>)
        ensures
            r is Some <==> a < self@.actions@.len() && state_ok(self@, s@),
            r matches Some(e) ==> enumerated_ok(self@, a as int, s@, e),
    {
        if a < self.raw.actions.len() && self.state_ok(s) {
            Some(enumerate(&self.raw, a, s))
        } else {
            None
        }
    }

    /// 状態 `s` で操作 `a` を引数 `args`（公開引数と内部選択）で適用した結果を計算する。
    /// 他の引数の評価に関係しないので、列挙が評価エラーになる状態でも、この引数の遷移を計算できる。
    /// 操作が未定義か、状態が状態型に、引数が操作のドメインに従わなければ `None`。それ以外は `Some`。
    pub fn apply(&self, a: usize, args: &Vec<i64>, s: &Vec<i64>) -> (r: Option<StepR>)
        ensures
            r is Some <==> a < self@.actions@.len() && state_ok(self@, s@) && args_ok(self@, a as int, args@),
            r matches Some(x) ==> x@ == step_spec(self@, a as int, args@, s@),
    {
        if a < self.raw.actions.len() && self.state_ok(s) && vals_ok_exec(
            &self.raw.enums,
            &self.raw.actions[a].domains,
            args,
        ) {
            Some(step(&self.raw, a, args, s))
        } else {
            None
        }
    }

    /// 対象の不変条件を定義順に評価し、真でない最初のものと、その評価結果を返す。
    /// `None` なら対象の不変条件はすべて真で、`Some((i, v))` なら `i` は対象の不変条件で、`v` はその評価結果
    /// （真でない）である。
    pub fn invariants(&self, c: &Conditions, s: &Vec<i64>) -> (r: Option<(usize, Result<bool, ErrKind>)>)
        ensures
            match r {
                None => invs_hold(self@, *c, s@),
                Some((i, v)) => inv_on(self@, *c, i as int) && inv_spec(self@, i as int, s@) == v && not_true(v),
            },
    {
        check_invariants(&self.raw, c, s)
    }

    /// 操作 `a` の遷移に適用する対象の契約を定義順に評価し、真でない最初のものと、その評価結果を返す。
    /// `None` なら適用する対象の契約はすべて真で、`Some((k, v))` なら `k` は操作 `a` の対象の契約で、`v` は
    /// その評価結果（真でない）である。
    pub fn contracts(
        &self,
        c: &Conditions,
        a: usize,
        pre: &Vec<i64>,
        args: &Vec<i64>,
        post: &Vec<i64>,
        o: &Option<i64>,
    ) -> (r: Option<(usize, Result<bool, ErrKind>)>)
        ensures
            match r {
                None => cons_hold(self@, *c, a as int, pre@, args@, post@, *o),
                Some((k, v)) => con_on(self@, *c, k as int) && self@.contracts@[k as int].action == a && con_spec(
                    self@,
                    k as int,
                    pre@,
                    args@,
                    post@,
                    *o,
                ) == v && not_true(v),
            },
    {
        check_contracts(&self.raw, c, a, pre, args, post, o)
    }

    /// 終端条件を評価する。
    pub fn terminal(&self, s: &Vec<i64>) -> (r: Result<bool, ErrKind>)
        ensures
            r == terminal_spec(self@, s@),
    {
        eval_terminal(&self.raw, s)
    }
}

/// IRを検証する。受理するのは、モデルが整形式であるとき、かつそのときに限る。
pub fn validate(raw: RawModel) -> (r: Result<CheckedModel, InvalidModel>)
    ensures
        match r {
            Ok(cm) => cm@ == raw && wf(raw),
            Err(_) => !wf(raw),
        },
{
    match validate_raw(&raw) {
        Ok(()) => Ok(CheckedModel { raw }),
        Err(e) => Err(e),
    }
}

} // verus!
