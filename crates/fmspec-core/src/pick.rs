//! 番号で選ぶ部品。番号の位置の値を、平衡した二分木の条件式で選ぶ（`pick_slot`）。その仕様（`picks`、`at_rank`、`vals_at`）と補題も置く。

#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, lemma_pure_mono, pure_below};
use crate::expr_build::{bin, cb, ci, ite};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::lower_types::{all_ty, has_ty};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
use crate::model::{BinOp, Expr};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_weaken, prefix};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

/// 式 `r` が、局所変数 `l` のもとで整数 `i` になる。
pub open spec fn at_rank(r: Expr, env: Env, l: Seq<Value>, i: i64) -> bool {
    pure_below(r, l.len()) && eval_l(r, env, l) == Ok::<Value, ErrKind>(Value::Int(i))
}

/// 整数の定数との二項演算は、`r` と同じく純粋である。
pub proof fn lemma_bin_const_pure(op: BinOp, r: Expr, k: i64, n: nat)
    requires
        pure_below(r, n),
    ensures
        pure_below(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), n),
{
    assert(pure_below(Expr::Const(Value::Int(k)), n));
}

/// 整数の定数との二項演算の値。
pub proof fn lemma_bin_const(op: BinOp, r: Expr, k: i64, env: Env, l: Seq<Value>, i: i64)
    requires
        at_rank(r, env, l, i),
    ensures
        pure_below(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), l.len()),
        eval_l(Expr::Bin(op, Box::new(r), Box::new(Expr::Const(Value::Int(k)))), env, l) == binop_spec(
            op,
            Value::Int(i),
            Value::Int(k),
        ),
{
    lemma_bin_const_pure(op, r, k, l.len());
    assert(eval_l(Expr::Const(Value::Int(k)), env, l) == Ok::<Value, ErrKind>(Value::Int(k)));
}

/// 式の列 `fs` の各式は、局所変数 `l` のもとで純粋で、値は `vals` になる。
pub open spec fn vals_at(fs: Seq<Expr>, vals: Seq<Value>, env: Env, l: Seq<Value>) -> bool {
    &&& fs.len() == vals.len()
    &&& forall|j: int|
        0 <= j < fs.len() ==> pure_below(#[trigger] fs[j], l.len()) && eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(
            vals[j],
        )
}

/// `x` は、番号 `r` が `lo..hi` にあれば、その位置の式 `fs[r]` と同じ値になる。
pub open spec fn picks_in(x: Expr, fs: Seq<Expr>, r: Expr, lo: int, hi: int) -> bool {
    &&& forall|m: nat| pure_below(r, m) && all_pure(fs, m) ==> #[trigger] pure_below(x, m)
    &&& forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
        lo < hi && has_ty(r, tv, lt, ETy::Int) && #[trigger] all_ty(fs, y, tv, lt) ==> has_ty(x, tv, lt, y)
    &&& forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
        #[trigger] at_rank(r, env, l, i) && #[trigger] vals_at(fs, vals, env, l) && lo <= i < hi ==> eval_l(x, env, l)
            == Ok::<Value, ErrKind>(vals[i as int])
}

pub open spec fn picks(x: Expr, fs: Seq<Expr>, r: Expr) -> bool {
    picks_in(x, fs, r, 0, fs.len() as int)
}

/// 局所変数を後ろに加えても、式の値は変わらない。
pub proof fn lemma_vals_weaken(fs: Seq<Expr>, vals: Seq<Value>, env: Env, l: Seq<Value>, l2: Seq<Value>)
    requires
        vals_at(fs, vals, env, l),
        prefix(l, l2),
    ensures
        vals_at(fs, vals, env, l2),
{
    assert forall|j: int| 0 <= j < fs.len() implies pure_below(#[trigger] fs[j], l2.len()) && eval_l(fs[j], env, l2)
        == Ok::<Value, ErrKind>(vals[j]) by {
        lemma_weaken(fs[j], env, l, l2);
        lemma_pure_mono(fs[j], l.len(), l2.len());
    }
}

/// 番号 `r` が範囲内で、その位置のスロットが真であるという式は純粋である。
pub proof fn lemma_hit_pure(r: Expr, fs: Seq<Expr>, hit: Expr, n: nat)
    requires
        picks(hit, fs, r),
        pure_below(r, n),
        all_pure(fs, n),
    ensures
        pure_below(
            crate::expr_build::and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit),
            n,
        ),
{
    assert(pure_below(hit, n));
    lemma_bin_const_pure(BinOp::Ge, r, 0, n);
}

/// 番号 `r` の位置の式を選ぶ式。
pub(crate) fn pick_slot(fs: &Vec<Expr>, r: &Expr) -> (x: Expr)
    requires
        fs@.len() <= 0x7fff_ffff,
    ensures
        picks(x, fs@, *r),
        fs@.len() == 0 ==> x == crate::expr_build::bool_lit(false),
{
    if fs.len() == 0 {
        return cb(false);
    }
    pick_range(fs, 0, fs.len(), r)
}

/// 番号 `r` の `lo..hi` の位置の式を、二分木の `ite` で選ぶ。
pub(crate) fn pick_range(fs: &Vec<Expr>, lo: usize, hi: usize, r: &Expr) -> (x: Expr)
    requires
        lo < hi <= fs@.len() <= 0x7fff_ffff,
    ensures
        picks_in(x, fs@, *r, lo as int, hi as int),
    decreases hi - lo,
{
    if hi - lo == 1 {
        let x = copy_expr(&fs[lo]);
        proof {
            assert forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
                #[trigger] at_rank(*r, env, l, i) && #[trigger] vals_at(fs@, vals, env, l) && lo <= i < hi implies eval_l(
                x,
                env,
                l,
            ) == Ok::<Value, ErrKind>(vals[i as int]) by {
                assert(i == lo);
            }
            assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
                lo < hi && has_ty(*r, tv, lt, ETy::Int) && #[trigger] all_ty(fs@, y, tv, lt) implies has_ty(x, tv, lt, y) by {
                assert(has_ty(fs@[lo as int], tv, lt, y));
            }
        }
        return x;
    }
    let mid = lo + (hi - lo) / 2;
    let a = pick_range(fs, lo, mid, r);
    let b = pick_range(fs, mid, hi, r);
    let c = bin(BinOp::Lt, copy_expr(r), ci(mid as i64));
    let x = ite(c, a, b);
    proof {
        assert forall|m: nat| pure_below(*r, m) && all_pure(fs@, m) implies #[trigger] pure_below(x, m) by {
            lemma_bin_const_pure(BinOp::Lt, *r, mid as i64, m);
            assert(pure_below(a, m) && pure_below(b, m));
        }
        assert forall|tv: TyEnv, lt: Seq<ETy>, y: ETy|
            lo < hi && has_ty(*r, tv, lt, ETy::Int) && #[trigger] all_ty(fs@, y, tv, lt) implies has_ty(x, tv, lt, y) by {
            assert(has_ty(Expr::Const(Value::Int(mid as i64)), tv, lt, ETy::Int));
            assert(has_ty(c, tv, lt, ETy::Bool));
            assert(has_ty(a, tv, lt, y) && has_ty(b, tv, lt, y));
        }
        assert forall|env: Env, l: Seq<Value>, i: i64, vals: Seq<Value>|
            #[trigger] at_rank(*r, env, l, i) && #[trigger] vals_at(fs@, vals, env, l) && lo <= i < hi implies eval_l(
            x,
            env,
            l,
        ) == Ok::<Value, ErrKind>(vals[i as int]) by {
            lemma_bin_const(BinOp::Lt, *r, mid as i64, env, l, i);
            assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(i < mid)));
        }
    }
    x
}

} // verus!
