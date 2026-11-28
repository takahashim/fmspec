//! Setの要素とMapのキーに付ける番号（rank）の計算。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{as_bool, eval_l, int_result, Env, ErrKind};
use crate::kernel::expr_copy::copy_expr;
use crate::kernel::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::kernel::typing::{ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::pure_below;
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::has_ty;
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{mixed_rank_eval, ranks_pure};
use vstd::prelude::*;

verus! {

/// 下端が `min` の整数の区間での番号。
pub fn offset_rank(value: Expr, min: i64) -> (out: Expr)
    ensures
        out == if min == 0 {
            value
        } else {
            Expr::Bin(BinOp::Sub, Box::new(value), Box::new(Expr::Const(Value::Int(min))))
        },
        forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) ==
                match eval_l(value, env, locals) {
                    Ok(Value::Int(n)) => int_result(n as int - min as int),
                    Err(error) => Err(error),
                    Ok(v) => if min == 0 { Ok(v) } else { Err(ErrKind::TypeMismatch) },
                },
{
    if min == 0 {
        proof {
            reveal_with_fuel(eval_l, 2);
        }
        value
    } else {
        let out = Expr::Bin(BinOp::Sub, Box::new(value), Box::new(Expr::Const(Value::Int(min))));
        proof {
            reveal_with_fuel(eval_l, 3);
        }
        out
    }
}

/// TupleとRecordの番号に、要素の番号を1桁加える（混合基数）。
pub fn extend_rank(prefix: Expr, radix: i64, component: Expr) -> (out: Expr)
    ensures
        out == Expr::Bin(
            BinOp::Add,
            Box::new(Expr::Bin(BinOp::Mul, Box::new(prefix), Box::new(Expr::Const(Value::Int(radix))))),
            Box::new(component),
        ),
        forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) ==
                match eval_l(prefix, env, locals) {
                    Err(error) => Err(error),
                    Ok(Value::Int(high)) => match int_result((high as int) * (radix as int)) {
                        Err(error) => Err(error),
                        Ok(Value::Int(base)) => match eval_l(component, env, locals) {
                            Err(error) => Err(error),
                            Ok(Value::Int(low)) => int_result(base as int + low as int),
                            _ => Err(ErrKind::TypeMismatch),
                        },
                        _ => Err(ErrKind::TypeMismatch),
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
{
    let base = Expr::Bin(BinOp::Mul, Box::new(prefix), Box::new(Expr::Const(Value::Int(radix))));
    let out = Expr::Bin(BinOp::Add, Box::new(base), Box::new(component));
    proof {
        reveal_with_fuel(eval_l, 4);
    }
    out
}

/// 桁の番号の式が、どれも Int の型を持つ。
pub open spec fn ranks_int(parts: Seq<(Expr, i64)>, tv: TyEnv, lt: Seq<ETy>) -> bool {
    forall|k: int| 0 <= k < parts.len() ==> #[trigger] has_ty(parts[k].0, tv, lt, ETy::Int)
}

/// TupleとRecordの番号の式を作る。要素を左から順に、混合基数の桁として加える。
pub fn mixed_rank_expr(parts: &Vec<(Expr, i64)>) -> (out: Expr)
    ensures forall|env: Env, locals: Seq<Value>|
        #[trigger] eval_l(out, env, locals) == mixed_rank_eval(parts@, parts@.len() as nat, env, locals),
        forall|n: nat| #[trigger] ranks_pure(parts@, n) ==> pure_below(out, n),
        forall|tv: TyEnv, lt: Seq<ETy>| #[trigger] ranks_int(parts@, tv, lt) ==> has_ty(out, tv, lt, ETy::Int),
{
    if parts.len() == 0 {
        return Expr::Const(Value::Int(0));
    }
    let mut out = copy_expr(&parts[0].0);
    let mut used = 1;
    proof {
        assert forall|n: nat| #[trigger] ranks_pure(parts@, n) implies pure_below(out, n) by {
            assert(pure_below(parts@[0].0, n));
        }
        assert forall|tv: TyEnv, lt: Seq<ETy>| #[trigger] ranks_int(parts@, tv, lt) implies has_ty(out, tv, lt, ETy::Int) by {
            assert(has_ty(parts@[0].0, tv, lt, ETy::Int));
        }
    }
    while used < parts.len()
        invariant
            1 <= used <= parts@.len(),
            forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_l(out, env, locals) == mixed_rank_eval(parts@, used as nat, env, locals),
            forall|n: nat| #[trigger] ranks_pure(parts@, n) ==> pure_below(out, n),
            forall|tv: TyEnv, lt: Seq<ETy>| #[trigger] ranks_int(parts@, tv, lt) ==> has_ty(out, tv, lt, ETy::Int),
        decreases parts@.len() - used,
    {
        let _previous = used;
        let _prefix = copy_expr(&out);
        out = extend_rank(out, parts[used].1, copy_expr(&parts[used].0));
        used = used + 1;
        proof {
            assert forall|n: nat| #[trigger] ranks_pure(parts@, n) implies pure_below(out, n) by {
                assert(pure_below(_prefix, n));
                assert(pure_below(parts@[_previous as int].0, n));
                assert(pure_below(Expr::Const(Value::Int(parts@[_previous as int].1)), n));
                assert(pure_below(
                    Expr::Bin(
                        BinOp::Mul,
                        Box::new(_prefix),
                        Box::new(Expr::Const(Value::Int(parts@[_previous as int].1))),
                    ),
                    n,
                ));
            }
            assert forall|tv: TyEnv, lt: Seq<ETy>| #[trigger] ranks_int(parts@, tv, lt) implies has_ty(out, tv, lt, ETy::Int) by {
                assert(has_ty(_prefix, tv, lt, ETy::Int));
                assert(has_ty(parts@[_previous as int].0, tv, lt, ETy::Int));
                assert(has_ty(Expr::Const(Value::Int(parts@[_previous as int].1)), tv, lt, ETy::Int));
                assert(has_ty(
                    Expr::Bin(
                        BinOp::Mul,
                        Box::new(_prefix),
                        Box::new(Expr::Const(Value::Int(parts@[_previous as int].1))),
                    ),
                    tv,
                    lt,
                    ETy::Int,
                ));
            }
            assert forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_l(out, env, locals) == mixed_rank_eval(parts@, used as nat, env, locals) by {
                reveal(mixed_rank_eval);
                assert(eval_l(out, env, locals) == match eval_l(_prefix, env, locals) {
                    Err(error) => Err(error),
                    Ok(Value::Int(high)) => match int_result((high as int) * (parts@[_previous as int].1 as int)) {
                        Err(error) => Err(error),
                        Ok(Value::Int(base)) => match eval_l(parts@[_previous as int].0, env, locals) {
                            Err(error) => Err(error),
                            Ok(Value::Int(low)) => int_result((base as int) + (low as int)),
                            _ => Err(ErrKind::TypeMismatch),
                        },
                        _ => Err(ErrKind::TypeMismatch),
                    },
                    _ => Err(ErrKind::TypeMismatch),
                });
            }
        }
    }
    out
}

/// Optionの番号。空を0とし、中身の番号は値があるときだけ評価する。
pub fn option_rank(present: Expr, payload: Expr) -> (out: Expr)
    ensures
        out == Expr::Ite(
            Box::new(present),
            Box::new(Expr::Bin(BinOp::Add, Box::new(Expr::Const(Value::Int(1))), Box::new(payload))),
            Box::new(Expr::Const(Value::Int(0))),
        ),
        forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) == match as_bool(eval_l(present, env, locals)) {
                Err(error) => Err(error),
                Ok(false) => Ok(Value::Int(0)),
                Ok(true) => match eval_l(payload, env, locals) {
                    Err(error) => Err(error),
                    Ok(Value::Int(rank)) => int_result(1 + rank as int),
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
{
    let some = Expr::Bin(BinOp::Add, Box::new(Expr::Const(Value::Int(1))), Box::new(payload));
    let out = Expr::Ite(Box::new(present), Box::new(some), Box::new(Expr::Const(Value::Int(0))));
    proof {
        reveal_with_fuel(eval_l, 4);
    }
    out
}

} // verus!
