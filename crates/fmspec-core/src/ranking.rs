//! Building the arithmetic used by finite key rankings.

#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, int_result, Env, ErrKind};
use crate::expr_copy::copy_expr;
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

pub open spec fn mixed_rank_eval(
    parts: Seq<(Expr, i64)>, count: nat, env: Env, locals: Seq<Value>,
) -> Result<Value, ErrKind>
    recommends count <= parts.len(),
    decreases count,
{
    if count == 0 {
        Ok(Value::Int(0))
    } else if count == 1 {
        eval_l(parts[0].0, env, locals)
    } else {
        match mixed_rank_eval(parts, (count - 1) as nat, env, locals) {
            Err(error) => Err(error),
            Ok(Value::Int(high)) => match int_result((high as int) * (parts[count - 1].1 as int)) {
                Err(error) => Err(error),
                Ok(Value::Int(base)) => match eval_l(parts[count - 1].0, env, locals) {
                    Err(error) => Err(error),
                    Ok(Value::Int(low)) => int_result((base as int) + (low as int)),
                    _ => Err(ErrKind::TypeMismatch),
                },
                _ => Err(ErrKind::TypeMismatch),
            },
            _ => Err(ErrKind::TypeMismatch),
        }
    }
}

/// Build the left-to-right mixed-radix expression used for tuple and record ranks.
pub fn mixed_rank_expr(parts: &Vec<(Expr, i64)>) -> (out: Expr)
    ensures forall|env: Env, locals: Seq<Value>|
        #[trigger] eval_l(out, env, locals) == mixed_rank_eval(parts@, parts@.len() as nat, env, locals),
{
    if parts.len() == 0 {
        return Expr::Const(Value::Int(0));
    }
    let mut out = copy_expr(&parts[0].0);
    let mut used = 1;
    while used < parts.len()
        invariant
            1 <= used <= parts@.len(),
            forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_l(out, env, locals) == mixed_rank_eval(parts@, used as nat, env, locals),
        decreases parts@.len() - used,
    {
        let _previous = used;
        let _prefix = copy_expr(&out);
        out = extend_rank(out, parts[used].1, copy_expr(&parts[used].0));
        used = used + 1;
        proof {
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

pub open spec fn rank_digit_step(prefix: Option<u64>, radix: u64, digit: u64) -> Option<u64> {
    match prefix {
        Some(value) => {
            let rank = (value as int) * (radix as int) + (digit as int);
            if digit < radix && rank <= u64::MAX as int { Some(rank as u64) } else { None }
        },
        None => None,
    }
}

pub open spec fn rank_digits_value(parts: Seq<(u64, u64)>, count: nat) -> Option<u64>
    recommends count <= parts.len(),
    decreases count,
{
    if count == 0 {
        Some(0)
    } else {
        rank_digit_step(
            rank_digits_value(parts, (count - 1) as nat),
            parts[count - 1].1,
            parts[count - 1].0,
        )
    }
}

/// Fold component ranks in order, checking each digit against its radix.
pub fn rank_digits_exec(parts: &Vec<(u64, u64)>) -> (out: Option<u64>)
    ensures out == rank_digits_value(parts@, parts@.len() as nat),
{
    let mut out = Some(0u64);
    let mut used = 0;
    while used < parts.len()
        invariant
            used <= parts@.len(),
            out == rank_digits_value(parts@, used as nat),
        decreases parts@.len() - used,
    {
        let _prefix = out;
        out = match out {
            Some(value) => append_rank_digit(value, parts[used].1, parts[used].0),
            None => None,
        };
        used = used + 1;
        proof {
            reveal(rank_digits_value);
            assert(out == rank_digit_step(_prefix, parts@[used as int - 1].1, parts@[used as int - 1].0));
        }
    }
    out
}

/// Rank a scalar code within a closed signed integer interval.
pub fn rank_interval_code(value: i64, min: i64, max: i64) -> (out: Option<u64>)
    ensures
        out is Some <==> min <= value <= max,
        out matches Some(rank) ==> rank as int == value as int - min as int,
{
    if value < min || value > max {
        return None;
    }
    let offset = (value as i128) - (min as i128);
    Some(offset as u64)
}

/// Rank an option tag, evaluating the payload rank only for the present case.
pub open spec fn rank_payload_can_increment(payload_rank: Option<u64>) -> bool {
    match payload_rank {
        Some(rank) => rank < u64::MAX,
        None => false,
    }
}

pub fn rank_option_code(tag: i64, payload_rank: Option<u64>) -> (out: Option<u64>)
    ensures
        out is Some <==> tag == 0 || (tag == 1 && rank_payload_can_increment(payload_rank)),
        tag == 0 ==> out == Some(0),
        tag == 1 ==> match payload_rank {
            Some(rank) if rank < u64::MAX => out matches Some(result) && result as int == rank as int + 1,
            _ => out is None,
        },
{
    match tag {
        0 => Some(0),
        1 => payload_rank?.checked_add(1),
        _ => None,
    }
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
