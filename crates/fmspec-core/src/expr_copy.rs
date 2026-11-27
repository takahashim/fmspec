//! 中核の式の複製。検証済みの下ろしで、同じ式を複数のスロットで使うときに使う。

use crate::model::Expr;
use vstd::prelude::*;

verus! {

pub fn copy_expr(e: &Expr) -> (out: Expr)
    ensures out == *e,
    decreases e,
{
    match e {
        Expr::Const(v) => Expr::Const(*v),
        Expr::Var(i) => Expr::Var(*i),
        Expr::Arg(i) => Expr::Arg(*i),
        Expr::Next(i) => Expr::Next(*i),
        Expr::Out => Expr::Out,
        Expr::Bin(op, a, b) => Expr::Bin(*op, Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Not(a) => Expr::Not(Box::new(copy_expr(a))),
        Expr::And(a, b) => Expr::And(Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Or(a, b) => Expr::Or(Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Implies(a, b) => Expr::Implies(Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Ite(c, a, b) => Expr::Ite(Box::new(copy_expr(c)), Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Local(i) => Expr::Local(*i),
        Expr::Let(a, b) => Expr::Let(Box::new(copy_expr(a)), Box::new(copy_expr(b))),
        Expr::Forall(ty, lo, hi, a) => Expr::Forall(*ty, *lo, *hi, Box::new(copy_expr(a))),
        Expr::Exists(ty, lo, hi, a) => Expr::Exists(*ty, *lo, *hi, Box::new(copy_expr(a))),
        Expr::Code(a) => Expr::Code(Box::new(copy_expr(a))),
        Expr::Fail(ty, k) => Expr::Fail(*ty, *k),
    }
}

} // verus!
