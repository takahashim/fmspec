//! Map lookup lowering over the slots of an already evaluated map and key.

#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, Env, ErrKind};
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

} // verus!
