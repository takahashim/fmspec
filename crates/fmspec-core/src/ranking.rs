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

/// Combining two in-range ranks preserves both digits.
pub proof fn rank_digits_are_unique(radix: int, a: int, b: int, c: int, d: int)
    requires
        0 <= b < radix,
        0 <= d < radix,
    ensures
        a * radix + b == c * radix + d <==> a == c && b == d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a * radix + b, radix, a, b);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c * radix + d, radix, c, d);
}

/// Append a rank digit while encoding a key value.
pub fn append_rank_digit(prefix: u64, radix: u64, digit: u64) -> (out: Option<u64>)
    ensures
        out is Some <==> digit < radix && (prefix as int) * (radix as int) + digit <= u64::MAX,
        out matches Some(rank) ==> rank as int == (prefix as int) * (radix as int) + digit,
{
    if digit >= radix {
        return None;
    }
    prefix.checked_mul(radix)?.checked_add(digit)
}

pub open spec fn product_rank(radices: Seq<int>, digits: Seq<int>, n: nat) -> int
    recommends n <= radices.len(), n <= digits.len(),
    decreases n,
{
    if n == 0 {
        0
    } else {
        product_rank(radices, digits, (n - 1) as nat) * radices[n - 1] + digits[n - 1]
    }
}

/// The ranks of two products are equal exactly when every component rank is equal.
pub proof fn product_rank_is_injective(radices: Seq<int>, a: Seq<int>, b: Seq<int>, n: nat)
    requires
        n <= radices.len(),
        n <= a.len(),
        n <= b.len(),
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] a[i] < radices[i],
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] b[i] < radices[i],
    ensures
        product_rank(radices, a, n) == product_rank(radices, b, n)
            <==> a.take(n as int) == b.take(n as int),
    decreases n,
{
    if n > 0 {
        let prefix = (n - 1) as nat;
        product_rank_is_injective(radices, a, b, prefix);
        rank_digits_are_unique(
            radices[n - 1],
            product_rank(radices, a, prefix), a[n - 1],
            product_rank(radices, b, prefix), b[n - 1],
        );
        assert(a.take(n as int) =~= a.take(prefix as int).push(a[n - 1]));
        assert(b.take(n as int) =~= b.take(prefix as int).push(b[n - 1]));
        if a.take(n as int) == b.take(n as int) {
            assert(a.take(n as int)[prefix as int] == a[n - 1]);
            assert(b.take(n as int)[prefix as int] == b[n - 1]);
            assert(a[n - 1] == b[n - 1]);
            assert forall|i: int| 0 <= i < prefix implies #[trigger] a.take(prefix as int)[i] == b.take(prefix as int)[i] by {
                assert(a.take(n as int)[i] == a[i]);
                assert(b.take(n as int)[i] == b[i]);
            }
            assert(a.take(prefix as int) =~= b.take(prefix as int));
        }
        reveal_with_fuel(product_rank, 2);
    } else {
        assert(a.take(0) =~= b.take(0));
    }
}

} // verus!
