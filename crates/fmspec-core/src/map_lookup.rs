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

pub open spec fn put_presence_node(old: Expr, rank_local: usize, row: i64) -> Expr {
    Expr::Or(
        Box::new(old),
        Box::new(Expr::Bin(
            BinOp::Eq,
            Box::new(Expr::Local(rank_local)),
            Box::new(Expr::Const(Value::Int(row))),
        )),
    )
}

pub open spec fn put_payload_node(old: Expr, new: Expr, rank_local: usize, row: i64) -> Expr {
    Expr::Ite(
        Box::new(Expr::Bin(
            BinOp::Eq,
            Box::new(Expr::Local(rank_local)),
            Box::new(Expr::Const(Value::Int(row))),
        )),
        Box::new(new),
        Box::new(old),
    )
}

pub open spec fn put_map_row_slot(
    flat: Seq<Expr>, payload: Seq<Expr>, width: usize, rank_local: usize, row: int, column: int,
) -> Expr {
    let stride = 1 + width as int;
    let base = row * stride;
    if column == 0 {
        put_presence_node(flat[base], rank_local, row as i64)
    } else {
        put_payload_node(flat[base + column], payload[column - 1], rank_local, row as i64)
    }
}

pub open spec fn put_map_row_sequence(
    flat: Seq<Expr>, payload: Seq<Expr>, width: usize, rank_local: usize, row: int,
) -> Seq<Expr> {
    Seq::new(width as nat + 1, |column: int|
        put_map_row_slot(flat, payload, width, rank_local, row, column))
}

/// Construct the updated expression row at one known map rank.
pub fn put_map_row(
    flat: &Vec<Expr>, payload: &Vec<Expr>, width: usize, rank_local: usize, row: usize,
) -> (out: Option<Vec<Expr>>)
    requires
        payload@.len() == width,
        width < usize::MAX,
        row as int <= i64::MAX as int,
        (row as int + 1) * (1 + width as int) <= flat@.len(),
        (row as int) * (1 + width as int) <= usize::MAX as int,
    ensures
        out is Some,
        out matches Some(result) ==> result@.len() == 1 + width
            && forall|column: int| 0 <= column <= width
                ==> #[trigger] result@[column] == put_map_row_slot(
                    flat@, payload@, width, rank_local, row as int, column,
                )
            && result@ =~= put_map_row_sequence(flat@, payload@, width, rank_local, row as int),
{
    let stride = width + 1;
    proof {
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride as int, row as int, 1);
        assert((row as int) * (stride as int) <= flat@.len());
        assert((row as int) * (stride as int) <= usize::MAX as int);
    }
    let base = row * stride;
    proof {
        assert(base as int == (row as int) * (stride as int));
        assert(base < flat.len());
        assert(base as int + stride as int <= flat@.len());
    }
    let mut result = Vec::new();
    let present = put_presence_expr(copy_expr(&flat[base]), Expr::Local(rank_local), row as i64);
    result.push(present);
    let mut column = 0;
    while column < width
        invariant
            column <= width,
            result@.len() == column + 1,
            base == row * stride,
            stride == width + 1,
            base + stride <= flat.len(),
            payload@.len() == width,
            row as int <= i64::MAX as int,
            (row as int + 1) * stride as int <= flat@.len(),
            forall|c: int| 0 <= c <= column
                ==> #[trigger] result@[c] == put_map_row_slot(
                    flat@, payload@, width, rank_local, row as int, c,
                ),
        decreases width - column,
    {
        proof {
            assert(base + column + 1 < base + stride);
        }
        let offset = base + column + 1;
        result.push(put_payload_expr(
            copy_expr(&flat[offset]), copy_expr(&payload[column]), Expr::Local(rank_local), row as i64,
        ));
        column = column + 1;
        proof {
            assert(offset as int == (row as int) * stride as int + column as int);
            assert(result@[column as int] == put_map_row_slot(
                flat@, payload@, width, rank_local, row as int, column as int,
            ));
        }
    }
    Some(result)
}

pub open spec fn flatten_map_rows(rows: Seq<Vec<Expr>>, count: nat) -> Seq<Expr>
    recommends count <= rows.len(),
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        flatten_map_rows(rows, (count - 1) as nat) + rows[count - 1]@
    }
}

pub open spec fn put_map_rows_sequence(
    flat: Seq<Expr>, payload: Seq<Expr>, width: usize, rank_local: usize, count: nat,
) -> Seq<Expr>
    recommends count * (1 + width as nat) <= flat.len(), count <= i64::MAX as nat,
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        put_map_rows_sequence(flat, payload, width, rank_local, (count - 1) as nat)
            + put_map_row_sequence(flat, payload, width, rank_local, count as int - 1)
    }
}

pub proof fn lemma_flattened_put_rows(
    flat: Seq<Expr>, payload: Seq<Expr>, width: usize, rank_local: usize,
    rows: Seq<Vec<Expr>>, count: nat,
)
    requires
        count <= rows.len(),
        count * (1 + width as nat) <= flat.len(),
        count <= i64::MAX as nat,
        forall|row: int| 0 <= row < count
            ==> #[trigger] rows[row]@ =~= put_map_row_sequence(
                flat, payload, width, rank_local, row,
            ),
    ensures
        flatten_map_rows(rows, count) == put_map_rows_sequence(flat, payload, width, rank_local, count),
    decreases count,
{
    if count > 0 {
        assert((count - 1) * (1 + width as nat) <= count * (1 + width as nat)) by (nonlinear_arith);
        lemma_flattened_put_rows(flat, payload, width, rank_local, rows, (count - 1) as nat);
        reveal(flatten_map_rows);
        reveal(put_map_rows_sequence);
        assert(rows[(count - 1) as int]@ =~= put_map_row_sequence(
            flat, payload, width, rank_local, count as int - 1,
        ));
    }
}

/// Update every row in rank order and flatten the resulting map.
pub fn put_map_rows_exec(
    flat: &Vec<Expr>, rows: usize, width: usize, rank_local: usize, payload: &Vec<Expr>,
) -> (out: Option<Vec<Expr>>)
    ensures
        out matches Some(updated) ==> updated@ =~= put_map_rows_sequence(
            flat@, payload@, width, rank_local, rows as nat,
        ),
{
    if payload.len() != width || rows > i64::MAX as usize {
        return None;
    }
    proof { assert(payload@.len() == width); }
    if rows == 0 {
        return if flat.len() == 0 { Some(Vec::new()) } else { None };
    }
    if width == usize::MAX {
        return None;
    }
    let stride = width.checked_add(1)?;
    let size = rows.checked_mul(stride)?;
    if size != flat.len() {
        return None;
    }
    let mut row_updates: Vec<Vec<Expr>> = Vec::new();
    let mut row = 0;
    while row < rows
        invariant
            row <= rows,
            size == rows * stride,
            flat.len() == size,
            flat@.len() == size,
            stride == width + 1,
            row_updates@.len() == row,
            rows <= i64::MAX as usize,
            payload@.len() == width,
            width < usize::MAX,
            forall|r: int| 0 <= r < row
                ==> #[trigger] row_updates@[r]@ =~= put_map_row_sequence(
                    flat@, payload@, width, rank_local, r,
                ),
        decreases rows - row,
    {
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(row as int + 1, rows as int, stride as int);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride as int, row as int, 1);
            assert((row as int + 1) * stride as int <= size as int);
            assert((row as int) * stride as int <= size as int);
            assert(size as int <= usize::MAX as int);
            assert(0 < stride) by (nonlinear_arith)
                requires stride == width + 1;
            assert((row as int) * stride as int <= (row as int + 1) * stride as int) by (nonlinear_arith);
            assert((row as int) * stride as int <= usize::MAX as int);
        }
        let row_slots = put_map_row(flat, payload, width, rank_local, row)?;
        let ghost expected = put_map_row_sequence(flat@, payload@, width, rank_local, row as int);
        proof { assert(row_slots@ =~= expected); }
        row_updates.push(row_slots);
        row = row + 1;
        proof {
            assert forall|r: int| 0 <= r < row
                implies #[trigger] row_updates@[r]@ =~= put_map_row_sequence(
                    flat@, payload@, width, rank_local, r,
                ) by {
                if r < row - 1 {
                    assert(row_updates@[r]@ =~= put_map_row_sequence(flat@, payload@, width, rank_local, r));
                } else {
                    assert(r == row - 1);
                    assert(row_updates@[r]@ =~= expected);
                }
            }
        }
    }
    let updated = flatten_map_rows_exec(&row_updates);
    proof {
        lemma_flattened_put_rows(flat@, payload@, width, rank_local, row_updates@, rows as nat);
        assert(updated@ =~= put_map_rows_sequence(flat@, payload@, width, rank_local, rows as nat));
    }
    Some(updated)
}

/// Concatenate map rows and verify that their order and contents are preserved.
pub fn flatten_map_rows_exec(rows: &Vec<Vec<Expr>>) -> (out: Vec<Expr>)
    ensures
        out@ =~= flatten_map_rows(rows@, rows@.len() as nat),
{
    let mut flat = Vec::new();
    let mut row = 0;
    while row < rows.len()
        invariant
            row <= rows@.len(),
            flat@ =~= flatten_map_rows(rows@, row as nat),
        decreases rows@.len() - row,
    {
        let mut column = 0;
        while column < rows[row].len()
            invariant
                column <= rows@[row as int]@.len(),
                row < rows@.len(),
                flat@ =~= flatten_map_rows(rows@, row as nat) + rows@[row as int]@.take(column as int),
            decreases rows@[row as int]@.len() - column,
        {
            flat.push(copy_expr(&rows[row][column]));
            column = column + 1;
        }
        proof {
            assert(rows@[row as int]@.take(rows@[row as int]@.len() as int) =~= rows@[row as int]@);
            reveal(flatten_map_rows);
            assert(flatten_map_rows(rows@, (row + 1) as nat)
                =~= flatten_map_rows(rows@, row as nat) + rows@[row as int]@);
        }
        row = row + 1;
    }
    flat
}

/// Set a map row's presence bit when the evaluated rank equals this row.
pub fn put_presence_expr(old: Expr, rank: Expr, row: i64) -> (out: Expr)
    ensures
        out == Expr::Or(
            Box::new(old),
            Box::new(Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row))))),
        ),
        forall|env: Env, locals: Seq<Value>|
        #[trigger] eval_l(out, env, locals) == match as_bool(eval_l(old, env, locals)) {
            Err(error) => Err(error),
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => match eval_l(
                Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row)))),
                env, locals,
            ) {
                Ok(Value::Bool(hit)) => Ok(Value::Bool(hit)),
                Ok(_) => Err(ErrKind::TypeMismatch),
                Err(error) => Err(error),
            },
        },
{
    let hit = Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row))));
    let out = Expr::Or(Box::new(old), Box::new(hit));
    proof { reveal_with_fuel(eval_l, 4); }
    out
}

/// Replace a map row's payload exactly when the evaluated rank equals this row.
pub fn put_payload_expr(old: Expr, new: Expr, rank: Expr, row: i64) -> (out: Expr)
    ensures
        out == Expr::Ite(
            Box::new(Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row))))),
            Box::new(new), Box::new(old),
        ),
        forall|env: Env, locals: Seq<Value>|
        #[trigger] eval_l(out, env, locals) == match as_bool(eval_l(
            Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row)))), env, locals,
        )) {
            Err(error) => Err(error),
            Ok(true) => eval_l(new, env, locals),
            Ok(false) => eval_l(old, env, locals),
        },
{
    let hit = Expr::Bin(BinOp::Eq, Box::new(rank), Box::new(Expr::Const(Value::Int(row))));
    let out = Expr::Ite(Box::new(hit), Box::new(new), Box::new(old));
    proof { reveal_with_fuel(eval_l, 4); }
    out
}

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

pub open spec fn flat_slot_int(flat: Seq<Expr>, width: usize, column: int, rank: int, env: Env, locals: Seq<Value>)
    -> Result<Value, ErrKind>
{
    eval_l(flat[rank * (1 + width as int) + column], env, locals)
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
    column: int, rank_local: usize, env: Env, locals: Seq<Value>,
)
    requires
        0 < column <= width as int,
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
        eval_l(payload, env, locals.push(Value::Bool(true))) == flat_slot_int(
            flat, width, column, key_rank(locals, rank_local), env, locals.push(Value::Bool(true)),
        ),
    ensures
        guarded_map_slot(check, payload, env, locals) == match as_bool(flat_slot(
            flat, width, 0, key_rank(locals, rank_local), env, locals,
        )) {
            Ok(true) => flat_slot_int(
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

/// Build the complete checked lookup operands used by `Map#get` from one flat map.
/// The payload vector is in slot order and is selected only for in-range ranks;
/// the check expression reports a missing key before the caller evaluates it.
pub fn select_flat_map_lookup(
    flat: &Vec<Expr>, rows: usize, width: usize, rank_local: usize, defaults: &Vec<Expr>,
) -> (out: Option<(Expr, Vec<Expr>)>)
    ensures
        out is Some <==> defaults@.len() == width
            && (rows == 0 || width < usize::MAX)
            && (rows as int) * (1 + width) == flat@.len(),
        out matches Some(result) ==> result.1@.len() == width
            && forall|env: Env, locals: Seq<Value>|
                rank_local < locals.len() && locals[rank_local as int] is Int
                    && (key_rank(locals, rank_local) < 0 || key_rank(locals, rank_local) < rows <= i64::MAX)
                ==> #[trigger] eval_l(result.0, env, locals) ==
                    if key_rank(locals, rank_local) < 0 {
                        Err(ErrKind::Failed(MISSING_KEY))
                    } else {
                        match as_bool(flat_slot(flat@, width, 0, key_rank(locals, rank_local), env, locals)) {
                            Ok(true) => Ok(Value::Bool(true)),
                            Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                            Err(error) => Err(error),
                        }
                    }
            && forall|i: int, env: Env, locals: Seq<Value>|
                0 <= i < width && rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(result.1@[i], env, locals)
                    == flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env, locals)
            && forall|i: int, env: Env, locals: Seq<Value>|
                0 <= i < width && rank_local < locals.len() && locals[rank_local as int] is Int
                    && (key_rank(locals, rank_local) < 0 || key_rank(locals, rank_local) < rows <= i64::MAX)
                ==> #[trigger] guarded_map_slot(result.0, result.1@[i], env, locals) ==
                    if key_rank(locals, rank_local) < 0 {
                        Err(ErrKind::Failed(MISSING_KEY))
                    } else {
                        match as_bool(flat_slot_int(flat@, width, 0, key_rank(locals, rank_local), env, locals)) {
                            Ok(true) => flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env,
                                locals.push(Value::Bool(true))),
                            Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                            Err(error) => Err(error),
                        }
                    },
{
    if defaults.len() != width {
        return None;
    }
    let check = select_flat_map_check(flat, rows, width, rank_local)?;
    let mut payload = Vec::new();
    let mut column = 0;
    while column < width
        invariant
            column <= width,
            defaults@.len() == width,
            payload@.len() == column,
            (rows as int) * (1 + width) == flat@.len(),
            forall|i: int, env: Env, locals: Seq<Value>|
                0 <= i < column && rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(payload@[i], env, locals)
                    == flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env, locals),
        decreases width - column,
    {
        let selected = select_flat_map_slot(flat, rows, width, column + 1, rank_local, copy_expr(&defaults[column]))?;
        payload.push(selected);
        column = column + 1;
    }
    proof {
        assert forall|i: int, env: Env, locals: Seq<Value>|
            0 <= i < width && rank_local < locals.len() && locals[rank_local as int] is Int
                && (key_rank(locals, rank_local) < 0 || key_rank(locals, rank_local) < rows <= i64::MAX)
            implies #[trigger] guarded_map_slot(check, payload@[i], env, locals) ==
                if key_rank(locals, rank_local) < 0 {
                    Err(ErrKind::Failed(MISSING_KEY))
                } else {
                    match as_bool(flat_slot_int(flat@, width, 0, key_rank(locals, rank_local), env, locals)) {
                        Ok(true) => flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env,
                            locals.push(Value::Bool(true))),
                        Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                        Err(error) => Err(error),
                    }
                } by {
            if 0 <= key_rank(locals, rank_local) < rows {
                guarded_lookup_matches_flat_row(
                    check, payload@[i], flat@, rows, width, i + 1, rank_local, env, locals,
                );
            } else {
                reveal_with_fuel(eval_bindings, 2);
            }
        }
    }
    Some((check, payload))
}


} // verus!
