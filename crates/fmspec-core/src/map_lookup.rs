//! Mapの参照の下ろし。Mapとキーは評価済みで、Mapはスロットの式の列、キーは番号を束縛した局所変数で受け取る。

#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, pure_below};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::lower_types::{all_ty, col_ty, has_ty, typed};
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::{eval_bindings, eval_bound_body};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

pub const MISSING_KEY: i64 = 2;

pub open spec fn selected(column: Seq<Expr>, rank: int, env: Env, locals: Seq<Value>) -> Result<Value, ErrKind> {
    eval_l(column[rank], env, locals)
}

/// 番号の局所変数は Int の型を持つ。
pub open spec fn rank_ty(lt: Seq<ETy>, rank_local: usize) -> bool {
    rank_local < lt.len() && lt[rank_local as int] == ETy::Int
}

pub open spec fn key_rank(locals: Seq<Value>, index: usize) -> int {
    match locals[index as int] {
        Value::Int(n) => n as int,
        _ => -1,
    }
}

/// スロットの列 [有無, 値..., 有無, 値..., ...] での、列 `column` の位置。
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
    // 行のないMapは、値の幅が大きくても位置を持たない。
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

/// 平衡した二分木の `ite` を作る。葉は右から順に取り出す。
#[verifier::spinoff_prover]
fn select_by_rank(column: &mut Vec<Expr>, lo: usize, hi: usize, rank_local: usize) -> (out: Expr)
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
        forall|n: nat| #[trigger] all_pure(old(column)@, n) && rank_local < n ==> pure_below(out, n),
        forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            rank_ty(lt, rank_local) && #[trigger] all_ty(old(column)@, y, tv, lt) ==> has_ty(out, tv, lt, y),
    decreases hi - lo,
{
    if hi - lo == 1 {
        let out = column.pop().unwrap();
        proof {
            assert(hi == old(column)@.len());
            assert(column@ =~= old(column)@.take(lo as int));
            assert(out == old(column)@[lo as int]);
            assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
                rank_ty(lt, rank_local) && #[trigger] all_ty(old(column)@, y, tv, lt) implies has_ty(out, tv, lt, y) by {
                assert(has_ty(old(column)@[lo as int], tv, lt, y));
            }
        }
        out
    } else {
        let mid = lo + (hi - lo) / 2;
        let right = select_by_rank(column, mid, hi, rank_local);
        let left = select_by_rank(column, lo, mid, rank_local);
        let cond = Expr::Bin(
            BinOp::Lt,
            Box::new(Expr::Local(rank_local)),
            Box::new(Expr::Const(Value::Int(mid as i64))),
        );
        let out = Expr::Ite(Box::new(cond), Box::new(left), Box::new(right));
        proof {
            assert(column@ =~= old(column)@.take(lo as int));
            assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
                rank_ty(lt, rank_local) && #[trigger] all_ty(old(column)@, y, tv, lt) implies has_ty(out, tv, lt, y) by {
                let c = old(column)@.take(mid as int);
                assert forall|j: int| 0 <= j < c.len() implies #[trigger] has_ty(c[j], tv, lt, y) by {
                    assert(c[j] == old(column)@[j]);
                    assert(has_ty(old(column)@[j], tv, lt, y));
                }
                assert(all_ty(c, y, tv, lt));
                assert(has_ty(left, tv, lt, y) && has_ty(right, tv, lt, y));
                assert(has_ty(Expr::Const(Value::Int(mid as i64)), tv, lt, ETy::Int));
                assert(has_ty(Expr::Local(rank_local), tv, lt, ETy::Int));
                assert(has_ty(cond, tv, lt, ETy::Bool));
            }
            assert forall|n: nat| #[trigger] all_pure(old(column)@, n) && rank_local < n implies pure_below(out, n) by {
                let c = old(column)@.take(mid as int);
                assert forall|j: int| 0 <= j < c.len() implies pure_below(#[trigger] c[j], n) by {
                    assert(c[j] == old(column)@[j]);
                }
                assert(all_pure(c, n));
                assert(pure_below(Expr::Const(Value::Int(mid as i64)), n));
                assert(pure_below(Expr::Local(rank_local), n));
                assert(pure_below(cond, n));
            }
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

/// 束縛したキーの番号で、列からスロットを選ぶ。
pub fn select_map_slot(column: Vec<Expr>, rank_local: usize, fallback: Expr) -> (out: Expr)
    ensures
        column@.len() == 0 ==> out == fallback,
        forall|n: nat|
            #[trigger] all_pure(column@, n) && rank_local < n && pure_below(fallback, n) ==> pure_below(out, n),
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && 0 <= key_rank(locals, rank_local) < column@.len() <= i64::MAX
            ==> #[trigger] eval_l(out, env, locals)
                == selected(column@, key_rank(locals, rank_local), env, locals),
        forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            rank_ty(lt, rank_local) && #[trigger] all_ty(column@, y, tv, lt) && has_ty(fallback, tv, lt, y) ==> has_ty(
                out,
                tv,
                lt,
                y,
            ),
{
    let mut column = column;
    let len = column.len();
    if len == 0 || len as u128 > i64::MAX as u128 {
        fallback
    } else {
        select_by_rank(&mut column, 0, len, rank_local)
    }
}

/// キーがなければ MissingKey で失敗する束縛を作る。値のスロットを使う前に評価する。
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
        forall|tv: TyEnv, lt: Seq<ETy>|
            rank_ty(lt, rank_local) && #[trigger] has_ty(present, tv, lt, ETy::Bool) ==> has_ty(out, tv, lt, ETy::Bool),
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
        assert forall|tv: TyEnv, lt: Seq<ETy>|
            rank_ty(lt, rank_local) && #[trigger] has_ty(present, tv, lt, ETy::Bool) implies has_ty(out, tv, lt, ETy::Bool) by {
            assert(has_ty(Expr::Local(rank_local), tv, lt, ETy::Int));
            assert(has_ty(Expr::Const(Value::Int(0)), tv, lt, ETy::Int));
            assert(has_ty(nonnegative, tv, lt, ETy::Bool));
            assert(has_ty(hit, tv, lt, ETy::Bool));
            assert(has_ty(Expr::Const(Value::Bool(true)), tv, lt, ETy::Bool));
            assert(has_ty(Expr::Fail(Type::Bool, MISSING_KEY), tv, lt, ETy::Bool));
        }
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

/// 下ろしたMapのスロットの列（行の順）から、列 `column` を取り出して選ぶ。
pub fn select_flat_map_slot(
    flat: &Vec<Expr>, rows: usize, width: usize, column: usize, rank_local: usize, fallback: Expr,
) -> (out: Option<Expr>)
    ensures
        out is Some <==> column <= width && (rows == 0 || width < usize::MAX)
            && (rows as int) * (1 + width) == flat@.len(),
        out matches Some(expr) ==> (rows == 0 ==> expr == fallback)
            && (forall|n: nat|
                #[trigger] all_pure(flat@, n) && rank_local < n && pure_below(fallback, n) ==> pure_below(expr, n))
            && forall|env: Env, locals: Seq<Value>|
                rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(expr, env, locals)
                    == flat_slot(flat@, width, column, key_rank(locals, rank_local), env, locals),
        out matches Some(expr) ==> forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            rank_ty(lt, rank_local) && #[trigger] col_ty(flat@, rows, width, column as int, y, tv, lt) && has_ty(
                fallback,
                tv,
                lt,
                y,
            ) ==> has_ty(expr, tv, lt, y),
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
    let ghost fb = fallback;
    let expr = select_map_slot(expressions, rank_local, fallback);
    proof {
        assert forall|n: nat|
            #[trigger] all_pure(flat@, n) && rank_local < n && pure_below(fb, n) implies pure_below(expr, n) by {
            assert forall|j: int| 0 <= j < projected.len() implies pure_below(#[trigger] projected[j], n) by {
                assert(projected[j] == flat@[indices@[j] as int]);
            }
            assert(all_pure(projected, n));
        }
        assert forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int
                && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
            implies #[trigger] eval_l(expr, env, locals)
                == flat_slot(flat@, width, column, key_rank(locals, rank_local), env, locals) by {
            let rank = key_rank(locals, rank_local);
            assert(projected[rank] == flat@[indices@[rank] as int]);
            assert(eval_l(expr, env, locals) == selected(projected, rank, env, locals));
        }
        assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            rank_ty(lt, rank_local) && #[trigger] col_ty(flat@, rows, width, column as int, y, tv, lt) && has_ty(
                fb,
                tv,
                lt,
                y,
            ) implies has_ty(expr, tv, lt, y) by {
            assert forall|j: int| 0 <= j < projected.len() implies #[trigger] has_ty(projected[j], tv, lt, y) by {
                assert(projected[j] == flat@[indices@[j] as int]);
                assert(has_ty(flat@[j * (1 + width as int) + column as int], tv, lt, y));
            }
            assert(all_ty(projected, y, tv, lt));
        }
    }
    Some(expr)
}

pub open spec fn guarded_map_slot(
    check: Expr, payload: Expr, env: Env, locals: Seq<Value>,
) -> Result<Value, ErrKind> {
    eval_bound_body(seq![check], 1, payload, env, locals)
}

/// 有無の検査を `let` で束縛してから選んだ値を評価する（`Block` の束縛と同じ形）と、行の値が得られる。
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

/// 有無の検査を、値を選ぶのと同じスロットの列から作る。
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
        out matches Some(check) ==> forall|tv: TyEnv, lt: Seq<ETy>|
            rank_ty(lt, rank_local) && #[trigger] col_ty(flat@, rows, width, 0, ETy::Bool, tv, lt) ==> has_ty(
                check,
                tv,
                lt,
                ETy::Bool,
            ),
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
        assert forall|tv: TyEnv, lt: Seq<ETy>|
            rank_ty(lt, rank_local) && #[trigger] col_ty(flat@, rows, width, 0, ETy::Bool, tv, lt) implies has_ty(
            check,
            tv,
            lt,
            ETy::Bool,
        ) by {
            assert(has_ty(Expr::Const(Value::Bool(false)), tv, lt, ETy::Bool));
            assert(has_ty(p, tv, lt, ETy::Bool));
        }
    }
    Some(check)
}

/// `Map#get` の下ろしに使う、検査と値のスロットの式を作る。
/// 値のスロットは順に並び、番号が範囲内のときに限って行を選ぶ。
/// 呼び出し側が検査を先に束縛するので、キーがなければ値を評価する前に失敗する。
pub fn select_flat_map_lookup(
    flat: &Vec<Expr>, rows: usize, width: usize, rank_local: usize, defaults: &Vec<Expr>,
) -> (out: Option<(Expr, Vec<Expr>)>)
    ensures
        out is Some <==> defaults@.len() == width
            && (rows == 0 || width < usize::MAX)
            && (rows as int) * (1 + width) == flat@.len(),
        out matches Some(result) ==> result.1@.len() == width
            && (forall|n: nat|
                #[trigger] all_pure(flat@, n) && rank_local < n && all_pure(defaults@, n) ==> all_pure(result.1@, n))
            && (forall|env: Env, locals: Seq<Value>|
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
                    })
            && (forall|i: int, env: Env, locals: Seq<Value>|
                0 <= i < width && rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(result.1@[i], env, locals)
                    == flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env, locals))
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
        out matches Some(result) ==> forall|tv: TyEnv, lt: Seq<ETy>, ys: Seq<ETy>|
            ys.len() > 0 && ys[0] == ETy::Bool && rank_ty(lt, rank_local) && ys.len() == 1 + width && (forall|c: int|
                0 <= c <= width ==> #[trigger] col_ty(flat@, rows, width, c, ys[c], tv, lt)) && #[trigger] typed(
                defaults@,
                ys.subrange(1, 1 + width),
                tv,
                lt,
            ) ==> has_ty(result.0, tv, lt, ETy::Bool) && typed(result.1@, ys.subrange(1, 1 + width), tv, lt),
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
            forall|n: nat| #[trigger] all_pure(flat@, n) && rank_local < n && all_pure(defaults@, n) ==> all_pure(payload@, n),
            forall|tv: TyEnv, lt: Seq<ETy>, ys: Seq<ETy>|
                rank_ty(lt, rank_local) && ys.len() == 1 + width && (forall|c: int|
                0 <= c <= width ==> #[trigger] col_ty(flat@, rows, width, c, ys[c], tv, lt)) && #[trigger] typed(
                defaults@,
                ys.subrange(1, 1 + width),
                tv,
                lt,
            ) ==> forall|i: int| 0 <= i < column ==> #[trigger] has_ty(payload@[i], tv, lt, ys[i + 1]),
            forall|i: int, env: Env, locals: Seq<Value>|
                0 <= i < column && rank_local < locals.len() && locals[rank_local as int] is Int
                    && 0 <= key_rank(locals, rank_local) < rows <= i64::MAX
                ==> #[trigger] eval_l(payload@[i], env, locals)
                    == flat_slot_int(flat@, width, i + 1, key_rank(locals, rank_local), env, locals),
        decreases width - column,
    {
        let selected = select_flat_map_slot(flat, rows, width, column + 1, rank_local, copy_expr(&defaults[column]))?;
        let ghost prev = payload@;
        payload.push(selected);
        proof {
            assert forall|tv: TyEnv, lt: Seq<ETy>, ys: Seq<ETy>|
                rank_ty(lt, rank_local) && ys.len() == 1 + width && (forall|c: int|
                0 <= c <= width ==> #[trigger] col_ty(flat@, rows, width, c, ys[c], tv, lt)) && #[trigger] typed(
                defaults@,
                ys.subrange(1, 1 + width),
                tv,
                lt,
            ) implies forall|i: int| 0 <= i < column + 1 ==> #[trigger] has_ty(payload@[i], tv, lt, ys[i + 1]) by {
                assert(col_ty(flat@, rows, width, column + 1, ys[column + 1], tv, lt));
                assert(has_ty(defaults@[column as int], tv, lt, ys.subrange(1, 1 + width)[column as int]));
                assert(has_ty(selected, tv, lt, ys[column + 1]));
                assert forall|i: int| 0 <= i < column + 1 implies #[trigger] has_ty(payload@[i], tv, lt, ys[i + 1]) by {
                    if i < column {
                        assert(payload@[i] == prev[i]);
                    }
                }
            }
            assert forall|n: nat| #[trigger] all_pure(flat@, n) && rank_local < n && all_pure(defaults@, n) implies all_pure(payload@, n) by {
                assert(pure_below(defaults@[column as int], n));
                assert(all_pure(prev, n));
                assert forall|j: int| 0 <= j < payload@.len() implies pure_below(#[trigger] payload@[j], n) by {
                    if j < prev.len() {
                        assert(payload@[j] == prev[j]);
                    }
                }
            }
        }
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
    proof {
        assert forall|tv: TyEnv, lt: Seq<ETy>, ys: Seq<ETy>|
            ys.len() > 0 && ys[0] == ETy::Bool && rank_ty(lt, rank_local) && ys.len() == 1 + width && (forall|c: int|
                0 <= c <= width ==> #[trigger] col_ty(flat@, rows, width, c, ys[c], tv, lt)) && #[trigger] typed(
                defaults@,
                ys.subrange(1, 1 + width),
                tv,
                lt,
            ) implies has_ty(check, tv, lt, ETy::Bool) && typed(payload@, ys.subrange(1, 1 + width), tv, lt) by {
            assert(col_ty(flat@, rows, width, 0, ys[0], tv, lt));
            assert forall|i: int| 0 <= i < payload@.len() implies #[trigger] has_ty(payload@[i], tv, lt, ys.subrange(1, 1 + width)[i]) by {
                assert(has_ty(payload@[i], tv, lt, ys[i + 1]));
            }
        }
    }
    Some((check, payload))
}


} // verus!
