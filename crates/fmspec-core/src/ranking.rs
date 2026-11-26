//! Building the arithmetic used by finite key rankings.

#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, int_result, Env, ErrKind};
use crate::model::{BinOp, Expr, Value};
use vstd::prelude::*;

verus! {

/// Rank within a closed integer interval whose lower endpoint is `min`.
pub fn offset_rank(value: Expr, min: i64) -> (out: Expr)
    ensures
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

/// Append one component of a tuple or record rank in mixed radix.
pub fn extend_rank(prefix: Expr, radix: i64, component: Expr) -> (out: Expr)
    ensures
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

/// Reserve rank zero for None. The payload is evaluated only for Some.
pub fn option_rank(present: Expr, payload: Expr) -> (out: Expr)
    ensures
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
