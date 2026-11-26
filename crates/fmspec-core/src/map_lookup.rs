//! Map lookup lowering over the slots of an already evaluated map and key.

#[cfg(verus_keep_ghost)]
use crate::bindings::{eval_bindings, eval_bound_body};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, Env, ErrKind};
use crate::expr_copy::copy_expr;
use crate::model::*;
use vstd::prelude::*;

verus! {

pub const MISSING_KEY: i64 = 2;

pub open spec fn selected(column: Seq<Expr>, rank: int, env: Env, locals: Seq<Value>) -> Result<Value, ErrKind> {
    eval_l(column[rank], env, locals)
}

pub open spec fn key_rank(locals: Seq<Value>, index: usize) -> int {
    match locals[index as int] {
        Value::Int(n) => n as int,
        _ => -1,
    }
}

/// Index a column in the flat layout [present, payload..., present, payload..., ...].
pub fn map_slot_indices(rows: usize, payload_width: usize, column: usize, len: usize)
    -> (out: Option<Vec<usize>>)
    ensures
        out is Some <==> column <= payload_width && (rows == 0 || payload_width < usize::MAX)
            && (rows as int) * (1 + payload_width) == len,
        out matches Some(indices) ==> indices@.len() == rows
            && forall|r: int| 0 <= r < rows ==> {
                &&& #[trigger] indices@[r] == r * (1 + payload_width) + column
                &&& indices@[r] < len
            },
{
    if column > payload_width {
        return None;
    }
    // A zero-row map has no offsets, even when its payload width is very large.
    if rows == 0 {
        return if len == 0 { Some(Vec::new()) } else { None };
    }
    let stride = payload_width.checked_add(1)?;
    let size = rows.checked_mul(stride)?;
    if size != len {
        return None;
    }
    let mut indices: Vec<usize> = Vec::new();
    let mut row = 0;
    let mut base: usize = 0;
    while row < rows
        invariant
            row <= rows,
            stride == 1 + payload_width,
            column < stride,
            base == row * stride,
            len == rows * stride,
            indices@.len() == row,
            forall|r: int| 0 <= r < row ==> {
                &&& #[trigger] indices@[r] == r * stride + column
                &&& indices@[r] < len
            },
        decreases rows - row,
    {
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(row as int + 1, rows as int, stride as int);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(stride as int, row as int, 1);
            vstd::arithmetic::mul::lemma_mul_is_commutative(stride as int, row as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(stride as int, row as int + 1);
            assert(base + stride <= len);
        }
        let offset = base + column;
        indices.push(offset);
        base = base + stride;
        row = row + 1;
    }
    Some(indices)
}

/// Build a balanced decision tree, consuming the leaves from right to left.
fn select(column: &mut Vec<Expr>, lo: usize, hi: usize, rank_local: usize) -> (out: Expr)
    requires
        lo < hi == old(column)@.len(),
        hi <= i64::MAX,
    ensures
        final(column)@ == old(column)@.take(lo as int),
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && lo as int <= key_rank(locals, rank_local) < hi as int
            ==> #[trigger] eval_l(out, env, locals)
                == selected(old(column)@, key_rank(locals, rank_local), env, locals),
    decreases hi - lo,
{
    if hi - lo == 1 {
        let out = column.pop().unwrap();
        proof {
            assert(hi == old(column)@.len());
            assert(column@ =~= old(column)@.take(lo as int));
        }
        out
    } else {
        let mid = lo + (hi - lo) / 2;
        let right = select(column, mid, hi, rank_local);
        let left = select(column, lo, mid, rank_local);
        let cond = Expr::Bin(
            BinOp::Lt,
            Box::new(Expr::Local(rank_local)),
            Box::new(Expr::Const(Value::Int(mid as i64))),
        );
        let out = Expr::Ite(Box::new(cond), Box::new(left), Box::new(right));
        proof {
            assert(column@ =~= old(column)@.take(lo as int));
            assert forall|env: Env, locals: Seq<Value>|
                rank_local < locals.len() && locals[rank_local as int] is Int
                    && lo as int <= key_rank(locals, rank_local) < hi as int
                implies #[trigger] eval_l(out, env, locals)
                    == selected(old(column)@, key_rank(locals, rank_local), env, locals) by {
                let rank = key_rank(locals, rank_local);
                if rank < mid {
                    assert(eval_l(left, env, locals) == selected(old(column)@, rank, env, locals));
                } else {
                    assert(eval_l(right, env, locals) == selected(old(column)@, rank, env, locals));
                }
                reveal_with_fuel(eval_l, 4);
            }
        }
        out
    }
}

/// Select a slot from a column indexed by the bound key's rank.
pub fn select_map_slot(column: Vec<Expr>, rank_local: usize, fallback: Expr) -> (out: Expr)
    ensures
        column@.len() == 0 ==> out == fallback,
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && 0 <= key_rank(locals, rank_local) < column@.len() <= i64::MAX
            ==> #[trigger] eval_l(out, env, locals)
                == selected(column@, key_rank(locals, rank_local), env, locals),
{
    let mut column = column;
    let len = column.len();
    if len == 0 || len as u128 > i64::MAX as u128 {
        fallback
    } else {
        select(&mut column, 0, len, rank_local)
    }
}

/// Build the binding that raises MissingKey before any payload slot is used.
pub fn require_map_key(present: Expr, rank_local: usize) -> (out: Expr)
    ensures
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int ==>
                #[trigger] eval_l(out, env, locals) ==
                    if key_rank(locals, rank_local) < 0 {
                        Err(ErrKind::Failed(MISSING_KEY))
                    } else {
                        match as_bool(eval_l(present, env, locals)) {
                            Ok(true) => Ok(Value::Bool(true)),
                            Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                            Err(k) => Err(k),
                        }
                    },
{
    let nonnegative = Expr::Bin(
        BinOp::Ge,
        Box::new(Expr::Local(rank_local)),
        Box::new(Expr::Const(Value::Int(0))),
    );
    let hit = Expr::And(Box::new(nonnegative), Box::new(present));
    let out = Expr::Ite(
        Box::new(hit),
        Box::new(Expr::Const(Value::Bool(true))),
        Box::new(Expr::Fail(Type::Bool, MISSING_KEY)),
    );
    proof {
        reveal_with_fuel(eval_l, 5);
    }
    out
}

pub open spec fn flat_slot(flat: Seq<Expr>, width: usize, column: usize, rank: int, env: Env, locals: Seq<Value>)
    -> Result<Value, ErrKind>
{
    eval_l(flat[rank * (1 + width as int) + column as int], env, locals)
}

/// Project and select directly from the actual row-major lowered operand.
pub fn select_flat_map_slot(
    flat: &Vec<Expr>, rows: usize, width: usize, column: usize, rank_local: usize, fallback: Expr,
) -> (out: Option<Expr>)
    ensures
        out is Some <==> column <= width && (rows == 0 || width < usize::MAX)
            && (rows as int) * (1 + width) == flat@.len(),
        out matches Some(expr) ==> (rows == 0 ==> expr == fallback)
            && forall|env: Env, locals: Seq<Value>|
                rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(expr, env, locals)
                    == flat_slot(flat@, width, column, key_rank(locals, rank_local), env, locals),
{
    let indices = map_slot_indices(rows, width, column, flat.len())?;
    let mut expressions: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < indices.len()
        invariant
            i <= indices@.len() == rows,
            expressions@.len() == i,
            forall|j: int| 0 <= j < rows ==> #[trigger] indices@[j] == j * (1 + width) + column
                && indices@[j] < flat@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] expressions@[j] == flat@[indices@[j] as int],
        decreases indices@.len() - i,
    {
        expressions.push(copy_expr(&flat[indices[i]]));
        i = i + 1;
    }
    let ghost projected = expressions@;
    let expr = select_map_slot(expressions, rank_local, fallback);
    proof {
        assert forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
            implies #[trigger] eval_l(expr, env, locals)
                == flat_slot(flat@, width, column, key_rank(locals, rank_local), env, locals) by {
            let rank = key_rank(locals, rank_local);
            assert(projected[rank] == flat@[indices@[rank] as int]);
            assert(eval_l(expr, env, locals) == selected(projected, rank, env, locals));
        }
    }
    Some(expr)
}

pub open spec fn guarded_map_slot(
    check: Expr, payload: Expr, env: Env, locals: Seq<Value>,
) -> Result<Value, ErrKind> {
    eval_bound_body(seq![check], 1, payload, env, locals)
}

/// Compose the presence check and the selected payload as Block does with its let binding.
pub proof fn guarded_lookup_matches_flat_row(
    check: Expr, payload: Expr, flat: Seq<Expr>, rows: usize, width: usize,
    column: usize, rank_local: usize, env: Env, locals: Seq<Value>,
)
    requires
        0 < column <= width,
        rank_local < locals.len(),
        locals[rank_local as int] is Int,
        0 <= key_rank(locals, rank_local) < rows,
        eval_l(check, env, locals) == match as_bool(flat_slot(
            flat, width, 0, key_rank(locals, rank_local), env, locals,
        )) {
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
            Err(error) => Err(error),
        },
        eval_l(payload, env, locals.push(Value::Bool(true))) == flat_slot(
            flat, width, column, key_rank(locals, rank_local), env, locals.push(Value::Bool(true)),
        ),
    ensures
        guarded_map_slot(check, payload, env, locals) == match as_bool(flat_slot(
            flat, width, 0, key_rank(locals, rank_local), env, locals,
        )) {
            Ok(true) => flat_slot(
                flat, width, column, key_rank(locals, rank_local), env, locals.push(Value::Bool(true)),
            ),
            Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
            Err(error) => Err(error),
        },
{
    reveal_with_fuel(eval_bindings, 2);
}

/// Compile the presence check from the same flat operand used for payload selection.
pub fn select_flat_map_check(flat: &Vec<Expr>, rows: usize, width: usize, rank_local: usize)
    -> (out: Option<Expr>)
    ensures
        out is Some <==> (rows == 0 || width < usize::MAX) && (rows as int) * (1 + width) == flat@.len(),
        out matches Some(check) ==> forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && (key_rank(locals, rank_local) < 0 || key_rank(locals, rank_local) < rows <= i64::MAX)
            ==> #[trigger] eval_l(check, env, locals) ==
                if key_rank(locals, rank_local) < 0 {
                    Err(ErrKind::Failed(MISSING_KEY))
                } else {
                    match as_bool(flat_slot(flat@, width, 0, key_rank(locals, rank_local), env, locals)) {
                        Ok(true) => Ok(Value::Bool(true)),
                        Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                        Err(error) => Err(error),
                    }
                },
{
    let presence = select_flat_map_slot(flat, rows, width, 0, rank_local, Expr::Const(Value::Bool(false)))?;
    let ghost p = presence;
    let check = require_map_key(presence, rank_local);
    proof {
        assert forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && (key_rank(locals, rank_local) < 0 || key_rank(locals, rank_local) < rows <= i64::MAX)
            implies #[trigger] eval_l(check, env, locals) ==
                if key_rank(locals, rank_local) < 0 {
                    Err(ErrKind::Failed(MISSING_KEY))
                } else {
                    match as_bool(flat_slot(flat@, width, 0, key_rank(locals, rank_local), env, locals)) {
                        Ok(true) => Ok(Value::Bool(true)),
                        Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                        Err(error) => Err(error),
                    }
                } by {
            if key_rank(locals, rank_local) >= 0 {
                assert(eval_l(p, env, locals) == flat_slot(flat@, width, 0, key_rank(locals, rank_local), env, locals));
            }
        }
    }
    Some(check)
}

} // verus!
