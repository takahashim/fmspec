//! `impls.rs` の手書きの標準トレイト実装。
//!
//! `impls.rs` は証明の対象外である（docs/verification.md）。判定の経路からは呼ばれないが、
//! 他のcrateのテストは `assert_eq!` でこれらの `PartialEq` を使って結果を比べるので、
//! 等しさが値を区別しないと、それらのテストが何も確かめなくなる。

use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, TraceStep};
use fmspec_core::model::{BinOp, Expr, Type, Value};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::Site;

/// どの2つも等しくない値の列について、`PartialEq` と `Clone` を確かめる。
fn distinct<T: PartialEq + Clone + std::fmt::Debug>(xs: &[T]) {
    for (i, x) in xs.iter().enumerate() {
        assert_eq!(x.clone(), *x, "{x:?}");
        for (j, y) in xs.iter().enumerate() {
            assert_eq!(x == y, i == j, "{x:?} と {y:?}");
        }
    }
}

fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}

#[test]
fn expr_equality_distinguishes_every_variant_and_field() {
    let one = || Expr::Const(Value::Int(1));
    let two = || Expr::Const(Value::Int(2));
    let t = || Expr::Const(Value::Bool(true));
    distinct(&[
        one(),
        two(),
        t(),
        Expr::Const(Value::Enum(0, 1)),
        Expr::Const(Value::Enum(1, 1)),
        Expr::Var(0),
        Expr::Var(1),
        Expr::Arg(0),
        Expr::Next(0),
        Expr::Local(0),
        Expr::Out,
        Expr::Bin(BinOp::Add, b(one()), b(two())),
        Expr::Bin(BinOp::Sub, b(one()), b(two())),
        Expr::Bin(BinOp::Add, b(two()), b(two())),
        Expr::Bin(BinOp::Add, b(one()), b(one())),
        Expr::Not(b(t())),
        Expr::Code(b(t())),
        Expr::And(b(t()), b(one())),
        Expr::And(b(one()), b(t())),
        Expr::Or(b(t()), b(one())),
        Expr::Implies(b(t()), b(one())),
        Expr::Let(b(t()), b(one())),
        Expr::Ite(b(t()), b(one()), b(two())),
        Expr::Ite(b(t()), b(two()), b(two())),
        Expr::Ite(b(t()), b(one()), b(one())),
        Expr::Ite(b(one()), b(one()), b(two())),
        Expr::Forall(Type::Bool, 0, 1, b(t())),
        Expr::Forall(Type::Int(0, 1), 0, 1, b(t())),
        Expr::Forall(Type::Bool, 1, 1, b(t())),
        Expr::Forall(Type::Bool, 0, 0, b(t())),
        Expr::Forall(Type::Bool, 0, 1, b(one())),
        Expr::Exists(Type::Bool, 0, 1, b(t())),
        Expr::Fail(Type::Bool, 0),
        Expr::Fail(Type::Bool, 1),
        Expr::Fail(Type::Enum(0), 0),
    ]);
}

#[test]
fn evidence_equality_distinguishes_every_field() {
    let step = |action, args: Vec<i64>, output, state: Vec<i64>| TraceStep {
        action,
        args,
        output,
        state,
    };
    distinct(&[
        step(0, vec![1], Some(1), vec![1]),
        step(1, vec![1], Some(1), vec![1]),
        step(0, vec![2], Some(1), vec![1]),
        step(0, vec![1], Some(2), vec![1]),
        step(0, vec![1], None, vec![1]),
        step(0, vec![1], Some(1), vec![2]),
    ]);
    let err = |a, args, site, kind| Claim::StepError(a, args, site, kind);
    distinct(&[
        Claim::Invariant(0),
        Claim::Invariant(1),
        Claim::Contract(0),
        Claim::Deadlock,
        Claim::InvariantError(0, ErrKind::Overflow),
        Claim::InvariantError(1, ErrKind::Overflow),
        Claim::InvariantError(0, ErrKind::DivByZero),
        Claim::ContractError(0, ErrKind::Overflow),
        Claim::TerminalError(ErrKind::Overflow),
        Claim::TerminalError(ErrKind::Failed(0)),
        err(0, vec![1], Site::Update(0), ErrKind::OutOfRange(4)),
        err(1, vec![1], Site::Update(0), ErrKind::OutOfRange(4)),
        err(0, vec![2], Site::Update(0), ErrKind::OutOfRange(4)),
        err(0, vec![1], Site::Update(1), ErrKind::OutOfRange(4)),
        err(0, vec![1], Site::Guard, ErrKind::OutOfRange(4)),
        err(0, vec![1], Site::Update(0), ErrKind::OutOfRange(5)),
    ]);
    let cond = |actions: Vec<bool>, invariants: Vec<bool>, contracts: Vec<bool>, deadlock| Conditions {
        actions,
        invariants,
        contracts,
        deadlock,
    };
    distinct(&[
        cond(vec![true], vec![true], vec![true], true),
        cond(vec![false], vec![true], vec![true], true),
        cond(vec![true], vec![], vec![true], true),
        cond(vec![true], vec![true], vec![true, true], true),
        cond(vec![true], vec![true], vec![true], false),
    ]);
}

#[test]
fn evidence_clone_keeps_every_field() {
    let conditions = Conditions {
        actions: vec![true, false],
        invariants: vec![false],
        contracts: vec![true],
        deadlock: true,
    };
    let cert = Certificate {
        conditions: conditions.clone(),
        states: vec![vec![0, 1], vec![2, 3]],
    };
    match Evidence::Certificate(cert).clone() {
        Evidence::Certificate(c) => {
            assert_eq!(c.conditions, conditions);
            assert_eq!(c.states, vec![vec![0, 1], vec![2, 3]]);
        }
        other => panic!("{other:?}"),
    }
    let step = TraceStep {
        action: 1,
        args: vec![2],
        output: Some(3),
        state: vec![4],
    };
    let claim = Claim::StepError(0, vec![5], Site::Output, ErrKind::Unbound);
    match Evidence::Trace(vec![6], vec![step.clone()], claim.clone()).clone() {
        Evidence::Trace(start, steps, c) => assert_eq!((start, steps, c), (vec![6], vec![step], claim)),
        other => panic!("{other:?}"),
    }
    match Evidence::Unavailable(Limit::CheckBudget).clone() {
        Evidence::Unavailable(l) => assert_eq!(l, Limit::CheckBudget),
        other => panic!("{other:?}"),
    }
}
