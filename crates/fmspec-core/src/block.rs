//! 束縛の列（`Block`）の操作。式を束縛して局所変数で指す（`bind`）、束縛するかそのまま使うかを選ぶ（`keep`、`atom`）、束縛の深さを確かめる（`need`、`check`）。型は `lower_ctx` にある。

use crate::bindings::wrap_bindings;
#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, Env};
#[cfg(verus_keep_ghost)]
use crate::expr_build::pure_below;
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, ite_s, lemma_all_pure_mono, lemma_pure_mono};
use crate::expr_build::{cb, is_bool_lit, ite};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{added, extends};
use crate::lower_ctx::{binds, Block, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::typed;
#[cfg(verus_keep_ghost)]
use crate::lower_types::{binds_typed, blt, has_ty, lemma_added_typed, lemma_has_ty_blk, lenv, lts};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
use crate::model::{Expr, Type};
#[cfg(verus_keep_ghost)]
use crate::preserve::{atoms_ok, eval_bound_body, lemma_atoms_empty, lemma_atoms_step};
#[cfg(verus_keep_ghost)]
use crate::slots::atomic_s;
use crate::slots::{atomic, copy_exprs, may_fail};
#[cfg(verus_keep_ghost)]
use crate::total::deep;
use crate::typing::ETy;
#[cfg(verus_keep_ghost)]
use crate::typing::TyEnv;
use vstd::prelude::*;

verus! {

pub proof fn lemma_extends_refl(a: Block)
    requires
        a.wf(),
    ensures
        extends(a, a),
{
}

pub fn new_block(base: usize, outer: Ghost<Seq<ETy>>) -> (r: Result<Block, Fail>)
    ensures
        r matches Ok(b) ==> b.wf() && b.base == base && b.binds@.len() == 0 && b.outer == outer,
        r is Err ==> r == Err::<Block, Fail>(Fail::Depth) && base == usize::MAX,
{
    if base < usize::MAX {
        Ok(Block { base, binds: Vec::new(), outer })
    } else {
        Err(Fail::Depth)
    }
}

pub(crate) fn depth(blk: &Block) -> (r: usize)
    requires
        blk.wf(),
    ensures
        r == blk.depth_s(),
{
    blk.base + blk.binds.len()
}

/// 値がなければ `Fail::Type` で失敗する。
pub fn need<T>(x: Option<T>) -> (r: Result<T, Fail>)
    ensures
        match x {
            Some(v) => r == Ok::<T, Fail>(v),
            None => r == Err::<T, Fail>(Fail::Type),
        },
{
    match x {
        Some(v) => Ok(v),
        None => Err(Fail::Type),
    }
}

/// 式を束縛し、それを指す局所変数を返す。
pub(crate) fn bind(blk: &mut Block, e: Expr) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r matches Ok(x) ==> x == Expr::Local(old(blk).depth_s() as usize) && final(blk).binds@ == old(
            blk,
        ).binds@.push(e),
        r is Err ==> *final(blk) == *old(blk) && r == Err::<Expr, Fail>(Fail::Depth),
{
    let i = depth(blk);
    if i + 1 == usize::MAX {
        proof {
            lemma_extends_refl(*blk);
        }
        return Err(Fail::Depth);
    }
    blk.binds.push(e);
    Ok(Expr::Local(i))
}

/// 失敗しうる式と束縛子を含む式は束縛し、それ以外はそのまま返す。
pub(crate) fn keep(blk: &mut Block, e: Expr) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Err ==> *final(blk) == *old(blk),
        r matches Ok(x) ==> added(*old(blk), *final(blk), e, x),
        r is Err ==> r == Err::<Expr, Fail>(Fail::Depth),
{
    if may_fail(&e) || binds(&e) {
        bind(blk, e)
    } else {
        proof {
            lemma_extends_refl(*blk);
        }
        Ok(e)
    }
}

/// 何度も参照する式を束縛する。
pub(crate) fn atom(blk: &mut Block, e: Expr) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Err ==> *final(blk) == *old(blk),
        r matches Ok(x) ==> added(*old(blk), *final(blk), e, x) && (atomic_s(e) ==> x == e),
        r is Err ==> r == Err::<Expr, Fail>(Fail::Depth),
{
    if atomic(&e) {
        proof {
            lemma_extends_refl(*blk);
        }
        Ok(e)
    } else {
        bind(blk, e)
    }
}

/// `cond` が偽なら、番号 `code` で失敗する。
pub(crate) fn check(blk: &mut Block, cond: Expr, code: i64) -> (r: Result<(), Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Err ==> *final(blk) == *old(blk),
        r is Err ==> r == Err::<(), Fail>(Fail::Depth),
        r is Ok ==> (cond == bool_lit(true) && final(blk).binds@ == old(blk).binds@) || final(blk).binds@ == old(
            blk,
        ).binds@.push(ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code))),
{
    if is_bool_lit(&cond, true) {
        proof {
            lemma_extends_refl(*blk);
        }
        Ok(())
    } else {
        let _ = bind(blk, ite(cond, cb(true), Expr::Fail(Type::Bool, code)))?;
        Ok(())
    }
}

/// 束縛を順に評価してから `e` を評価する式。
pub fn wrap(binds: &Vec<Expr>, e: Expr) -> (r: Expr)
    ensures
        forall|env: Env, ls: Seq<Value>|
            #[trigger] eval_l(r, env, ls) == eval_bound_body(binds@, binds@.len(), e, env, ls),
        forall|t: TyEnv, outer: Seq<ETy>|
            #[trigger] binds_typed(outer, binds@, t) ==> crate::typing::type_l(r, t, outer) == crate::typing::type_l(
                e,
                t,
                lts(outer, binds@, t),
            ),
{
    wrap_bindings(copy_exprs(binds), e)
}

/// `xs` の各スロットを、何度も参照できるように束縛する。
pub(crate) fn atoms(xs: Vec<Expr>, blk: &mut Block, Ghost(cx): Ghost<LowerCtx>, Ghost(ys): Ghost<Seq<ETy>>) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
    ensures
        all_pure(xs@, old(blk).depth_s()) && old(blk).outer@.len() == old(blk).base && binds_typed(
            old(blk).outer@,
            old(blk).binds@,
            lenv(cx),
        ) && typed(xs@, ys, lenv(cx), blt(*old(blk), cx)) ==> binds_typed(final(blk).outer@, final(blk).binds@, lenv(cx))
            && (r matches Ok(out) ==> typed(out@, ys, lenv(cx), blt(*final(blk), cx))),
        extends(*old(blk), *final(blk)),
        r matches Ok(out) ==> atoms_ok(xs@, out@, *old(blk), *final(blk)),
        deep(r),
        r matches Ok(out) ==> out@.len() == xs@.len() && (all_pure(xs@, old(blk).depth_s()) ==> all_pure(
            out@,
            final(blk).depth_s(),
        )),
{
    let ghost b0 = *blk;
    let ghost p0 = all_pure(xs@, b0.depth_s());
    let ghost q0 = p0 && b0.outer@.len() == b0.base && binds_typed(b0.outer@, b0.binds@, lenv(cx)) && typed(
        xs@,
        ys,
        lenv(cx),
        blt(b0, cx),
    );
    let mut out: Vec<Expr> = Vec::new();
    proof {
        lemma_extends_refl(*blk);
        lemma_atoms_empty(*blk);
        assert(xs@.take(0) =~= Seq::<Expr>::empty());
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            extends(b0, *blk),
            atoms_ok(xs@.take(i as int), out@, b0, *blk),
            b0 == *old(blk),
            out@.len() == i,
            p0 == all_pure(xs@, b0.depth_s()),
            p0 ==> all_pure(out@, blk.depth_s()),
            q0 == (p0 && b0.outer@.len() == b0.base && binds_typed(b0.outer@, b0.binds@, lenv(cx)) && typed(
                xs@,
                ys,
                lenv(cx),
                blt(b0, cx),
            )),
            q0 ==> binds_typed(blk.outer@, blk.binds@, lenv(cx)) && forall|j: int|
                0 <= j < i ==> #[trigger] has_ty(out@[j], lenv(cx), blt(*blk, cx), ys[j]),
        decreases xs.len() - i,
    {
        let ghost b1 = *blk;
        let ghost o1 = out@;
        let x = copy_expr(&xs[i]);
        let y = atom(blk, x)?;
        out.push(y);
        proof {
            if p0 {
                assert(pure_below(xs@[i as int], b0.depth_s()));
                lemma_all_pure_mono(o1, b1.depth_s(), blk.depth_s());
                if y == x {
                    lemma_pure_mono(x, b0.depth_s(), blk.depth_s());
                }
                assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                    if j < o1.len() {
                        assert(out@[j] == o1[j]);
                    }
                }
            }
        }
        proof {
            if q0 {
                assert(has_ty(xs@[i as int], lenv(cx), blt(b0, cx), ys[i as int]));
                lemma_has_ty_blk(x, ys[i as int], cx, b0, b1);
                lemma_added_typed(b1, *blk, x, y, cx, ys[i as int]);
                assert forall|j: int| 0 <= j < i + 1 implies #[trigger] has_ty(out@[j], lenv(cx), blt(*blk, cx), ys[j]) by {
                    if j < i {
                        assert(out@[j] == o1[j]);
                        assert(has_ty(o1[j], lenv(cx), blt(b1, cx), ys[j]));
                        assert(pure_below(o1[j], b1.depth_s()));
                        lemma_has_ty_blk(o1[j], ys[j], cx, b1, *blk);
                    }
                }
            }
            lemma_atoms_step(xs@.take(i as int), x, o1, y, b0, b1, *blk);
            assert(xs@.take(i as int).push(x) =~= xs@.take(i + 1));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs.len() as int) =~= xs@);
        if q0 {
            assert(out@.len() == ys.len());
        }
    }
    Ok(out)
}

} // verus!
