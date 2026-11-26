//! Evaluator の演算ごとの意味論、型エラー、境界値（仕様書 §14 の表）。

use fmspec_core::eval::{eval, eval_prop, Ctx, ErrKind};
use fmspec_core::model::{BinOp, Expr, Type, Value};

fn int(x: i64) -> Expr {
    Expr::Const(Value::Int(x))
}

fn boolean(b: bool) -> Expr {
    Expr::Const(Value::Bool(b))
}

fn bin(op: BinOp, a: Expr, b: Expr) -> Expr {
    Expr::Bin(op, Box::new(a), Box::new(b))
}

/// 状態 `[7, 1, 2]`（Int、Bool、Enum(0)）、引数 `[3]`、遷移後の状態 `[8, 0, 0]`、出力 `Int(9)` の環境で評価する。
fn run(e: &Expr) -> Result<Value, ErrKind> {
    let st_tys = vec![Type::Int(0, 10), Type::Bool, Type::Enum(0)];
    let arg_tys = vec![Type::Int(0, 5)];
    let (pre, args, post) = (vec![7, 1, 2], vec![3], vec![8, 0, 0]);
    let ctx = Ctx {
        st_tys: &st_tys,
        arg_tys: &arg_tys,
        pre: &pre,
        args: &args,
        post: &post,
        out: Some(Value::Int(9)),
    };
    eval(e, &ctx)
}

/// 評価するとオーバーフローで失敗する式。
fn overflow() -> Expr {
    bin(BinOp::Add, int(i64::MAX), int(1))
}

#[test]
fn references_decode_by_type() {
    assert_eq!(run(&Expr::Var(0)), Ok(Value::Int(7)));
    assert_eq!(run(&Expr::Var(1)), Ok(Value::Bool(true)));
    assert_eq!(run(&Expr::Var(2)), Ok(Value::Enum(0, 2)));
    assert_eq!(run(&Expr::Arg(0)), Ok(Value::Int(3)));
    assert_eq!(run(&Expr::Next(0)), Ok(Value::Int(8)));
    assert_eq!(run(&Expr::Next(1)), Ok(Value::Bool(false)));
    assert_eq!(run(&Expr::Out), Ok(Value::Int(9)));
}

#[test]
fn unbound_references_fail() {
    assert_eq!(run(&Expr::Var(3)), Err(ErrKind::Unbound));
    assert_eq!(run(&Expr::Arg(1)), Err(ErrKind::Unbound));
    assert_eq!(run(&Expr::Next(usize::MAX)), Err(ErrKind::Unbound));
    let (tys, vals): (Vec<Type>, Vec<i64>) = (vec![], vec![]);
    let ctx = Ctx {
        st_tys: &tys,
        arg_tys: &tys,
        pre: &vals,
        args: &vals,
        post: &vals,
        out: None,
    };
    assert_eq!(eval(&Expr::Out, &ctx), Err(ErrKind::Unbound));
}

#[test]
fn arithmetic_detects_overflow_at_the_i64_boundary() {
    let (max, min) = (i64::MAX, i64::MIN);
    assert_eq!(run(&bin(BinOp::Add, int(max - 1), int(1))), Ok(Value::Int(max)));
    assert_eq!(run(&bin(BinOp::Add, int(max), int(1))), Err(ErrKind::Overflow));
    assert_eq!(run(&bin(BinOp::Add, int(min), int(-1))), Err(ErrKind::Overflow));
    assert_eq!(run(&bin(BinOp::Sub, int(min + 1), int(1))), Ok(Value::Int(min)));
    assert_eq!(run(&bin(BinOp::Sub, int(min), int(1))), Err(ErrKind::Overflow));
    assert_eq!(run(&bin(BinOp::Sub, int(0), int(min))), Err(ErrKind::Overflow));
    assert_eq!(run(&bin(BinOp::Mul, int(min), int(1))), Ok(Value::Int(min)));
    assert_eq!(run(&bin(BinOp::Mul, int(min), int(-1))), Err(ErrKind::Overflow));
    assert_eq!(
        run(&bin(BinOp::Mul, int(1 << 32), int(1 << 31))),
        Err(ErrKind::Overflow)
    );
    assert_eq!(
        run(&bin(BinOp::Mul, int(1 << 31), int(1 << 31))),
        Ok(Value::Int(1 << 62))
    );
    assert_eq!(run(&bin(BinOp::Mul, int(-3), int(4))), Ok(Value::Int(-12)));
}

#[test]
fn comparisons() {
    for (op, lt, eq, gt) in [
        (BinOp::Lt, true, false, false),
        (BinOp::Le, true, true, false),
        (BinOp::Gt, false, false, true),
        (BinOp::Ge, false, true, true),
        (BinOp::Eq, false, true, false),
        (BinOp::Ne, true, false, true),
    ] {
        assert_eq!(run(&bin(op, int(-1), int(2))), Ok(Value::Bool(lt)), "{op:?}");
        assert_eq!(run(&bin(op, int(2), int(2))), Ok(Value::Bool(eq)), "{op:?}");
        assert_eq!(run(&bin(op, int(3), int(2))), Ok(Value::Bool(gt)), "{op:?}");
    }
}

#[test]
fn equality_requires_the_same_kind() {
    let e = |k| Expr::Const(Value::Enum(0, k));
    assert_eq!(
        run(&bin(BinOp::Eq, boolean(true), boolean(true))),
        Ok(Value::Bool(true))
    );
    assert_eq!(
        run(&bin(BinOp::Ne, boolean(true), boolean(false))),
        Ok(Value::Bool(true))
    );
    assert_eq!(run(&bin(BinOp::Eq, e(2), Expr::Var(2))), Ok(Value::Bool(true)));
    assert_eq!(run(&bin(BinOp::Eq, e(1), Expr::Var(2))), Ok(Value::Bool(false)));
    assert_eq!(run(&bin(BinOp::Eq, int(1), boolean(true))), Err(ErrKind::TypeMismatch));
    assert_eq!(
        run(&bin(BinOp::Ne, e(1), Expr::Const(Value::Enum(1, 1)))),
        Err(ErrKind::TypeMismatch)
    );
    assert_eq!(run(&bin(BinOp::Eq, e(1), int(1))), Err(ErrKind::TypeMismatch));
}

#[test]
fn operators_reject_operands_of_the_wrong_type() {
    assert_eq!(run(&bin(BinOp::Add, boolean(true), int(1))), Err(ErrKind::TypeMismatch));
    assert_eq!(run(&bin(BinOp::Lt, int(1), boolean(true))), Err(ErrKind::TypeMismatch));
    assert_eq!(run(&Expr::Not(Box::new(int(1)))), Err(ErrKind::TypeMismatch));
    assert_eq!(
        run(&Expr::And(Box::new(int(1)), Box::new(boolean(true)))),
        Err(ErrKind::TypeMismatch)
    );
    assert_eq!(
        run(&Expr::And(Box::new(boolean(true)), Box::new(int(1)))),
        Err(ErrKind::TypeMismatch)
    );
    assert_eq!(
        run(&Expr::Ite(Box::new(int(1)), Box::new(int(1)), Box::new(int(2)))),
        Err(ErrKind::TypeMismatch)
    );
    let (tys, vals): (Vec<Type>, Vec<i64>) = (vec![], vec![]);
    let ctx = Ctx {
        st_tys: &tys,
        arg_tys: &tys,
        pre: &vals,
        args: &vals,
        post: &vals,
        out: None,
    };
    assert_eq!(eval_prop(&int(1), &ctx), Err(ErrKind::TypeMismatch));
}

#[test]
fn binary_operators_evaluate_the_left_operand_first() {
    // 左がオーバーフロー、右が未束縛。左の失敗が伝播する。
    assert_eq!(run(&bin(BinOp::Add, overflow(), Expr::Var(9))), Err(ErrKind::Overflow));
    assert_eq!(run(&bin(BinOp::Add, Expr::Var(9), overflow())), Err(ErrKind::Unbound));
    // 型エラーより先に、両辺の評価の失敗が伝播する。
    assert_eq!(run(&bin(BinOp::Add, boolean(true), overflow())), Err(ErrKind::Overflow));
}

#[test]
fn logical_operators_short_circuit() {
    let and = |a, b| Expr::And(Box::new(a), Box::new(b));
    let or = |a, b| Expr::Or(Box::new(a), Box::new(b));
    let implies = |a, b| Expr::Implies(Box::new(a), Box::new(b));
    let bad = || bin(BinOp::Gt, overflow(), int(0));
    assert_eq!(run(&and(boolean(false), bad())), Ok(Value::Bool(false)));
    assert_eq!(run(&and(boolean(true), bad())), Err(ErrKind::Overflow));
    assert_eq!(run(&and(bad(), boolean(false))), Err(ErrKind::Overflow));
    assert_eq!(run(&or(boolean(true), bad())), Ok(Value::Bool(true)));
    assert_eq!(run(&or(boolean(false), bad())), Err(ErrKind::Overflow));
    assert_eq!(run(&implies(boolean(false), bad())), Ok(Value::Bool(true)));
    assert_eq!(run(&implies(boolean(true), bad())), Err(ErrKind::Overflow));
    assert_eq!(run(&implies(boolean(true), boolean(false))), Ok(Value::Bool(false)));
    assert_eq!(run(&Expr::Not(Box::new(boolean(false)))), Ok(Value::Bool(true)));
}

#[test]
fn ite_evaluates_only_the_chosen_branch() {
    let ite = |c, a, b| Expr::Ite(Box::new(c), Box::new(a), Box::new(b));
    assert_eq!(run(&ite(boolean(true), int(1), overflow())), Ok(Value::Int(1)));
    assert_eq!(run(&ite(boolean(false), overflow(), int(2))), Ok(Value::Int(2)));
    assert_eq!(run(&ite(boolean(true), overflow(), int(2))), Err(ErrKind::Overflow));
}
