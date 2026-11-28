//! IRの型付き構文木を、中核の式に下ろす。
//!
//! 複合型の値は、[`crate::encoding`] の配置に従ってスロットの列で表す。式は、スロットごとの中核の式に下ろす。
//!
//! 部分式の評価の順序と打ち切りは、値の上の意味論（[`crate::source::eval_src`]）と一致させる。
//! そのために、下ろした式は「束縛の列」（[`Block`]）と「スロットの式」の組で表す。
//! 束縛は、評価の順に `let` で局所変数に束縛する式で、失敗しうる計算はすべてここに置く。
//! スロットの式は失敗せず、束縛子（`let`、量化）も含まないので、どの深さで評価しても同じ値になる。
//! 短絡する演算（`all`、`any`、`implies`、`ite`）と量化の本体は、評価する位置の深さで
//! 独立に下ろし、外側の束縛の列には混ぜない。
//!
//! 局所変数は外側から数えた添字で指すので、下ろした式は評価する深さに依存する。
//! 束縛子を含む式は、作った深さでただちに束縛する。
//!
//! 下ろしは、型の合わない式や、長さの合わないスロットの列に対して `Fail::Type` を返し、
//! 束縛の深さが上限に達すると `Fail::Depth` を返す。
//!
//! 下ろしが意味を保存することの補題は、[`crate::preserve`] と、式の種類ごとの `preserve_*.rs` にある。

#[cfg(verus_keep_ghost)]
use crate::canon::{lemma_in_member, lemma_models_has, lemma_shaped_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, keys, keys_or_zero, lemma_stys, lemma_xtys, lemma_xwidth_of, member};
#[cfg(verus_keep_ghost)]
use crate::encoding::{sty, stys, to_xty, wf_stype, width, xty, xtys, STy, SVal, XTy};
use crate::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, int_lit, kind_expr, pure_below, tree_s, Join};
use crate::expr_build::{ci, eq};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::ir_type_of;
#[cfg(verus_keep_ghost)]
use crate::keys::rank;
#[cfg(verus_keep_ghost)]
use crate::limits::*;
use crate::lower_core::low_core;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::extends;
use crate::lower_ctx::{Block, Bound, Fail, Layout, LowerCtx};
use crate::lower_list::{low_list_contains, low_list_get, low_list_lit, low_list_update};
use crate::lower_map::{low_get, low_map_access, low_map_lit};
use crate::lower_quant::low_quant;
use crate::lower_set::{low_member, low_set_lit, low_setop};
use crate::lower_struct::low_struct;
#[cfg(verus_keep_ghost)]
use crate::lower_types::*;
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Type};
use crate::model::{Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_elem::{elem_lowers, elem_rank_lowers, lemma_elem_rank, lemma_element};
#[cfg(verus_keep_ghost)]
use crate::preserve_list::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_set::*;
#[cfg(verus_keep_ghost)]
use crate::slot_store::store_ok;
use crate::slot_store::{rank_expr, rank_or_neg, store};
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, SEnv};
use crate::source::{TExpr, FAIL_NOT_IN_DOMAIN};
use crate::stype_exec::{keys_exec, stype_eq, stype_width, to_xtype, usizes_eq, xtype_eq};
#[cfg(verus_keep_ghost)]
use crate::total::*;
use crate::typing::ETy;
use vstd::prelude::*;

verus! {

/// 値を型 `st` の場所に置けるか。整数の範囲は問わない（値ごとに検査する）。
pub fn fits(t: &XType, st: &SType) -> (r: bool)
    ensures
        r == fits_s(xty(*t), sty(*st)),
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Bool, SType::Bool) => true,
        (XType::Int, SType::Int(_, _)) => true,
        (XType::Enum(a), SType::Enum(b)) => *a == *b,
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            fits_all(t, xs, ts)
        },
        (XType::Record(a, xs), SType::Record(b, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            usizes_eq(a, b) && fits_all(t, xs, ts)
        },
        (XType::Option(x), SType::Option(u)) => fits(x, u),
        (XType::Set(a), SType::Set(b)) => stype_eq(a, b),
        (XType::Map(ka, va), SType::Map(kb, vb)) => stype_eq(ka, kb) && stype_eq(va, vb),
        (XType::List(a, n), SType::List(b, m)) => *n == *m && stype_eq(a, b),
        _ => false,
    }
}

fn fits_all(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r == fits_all_s(xtys(xs@), stys(ts@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_fits_all(xtys(xs@), stys(ts@));
    }
    if xs.len() != ts.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ts.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> fits_s(#[trigger] xty(xs@[j]), sty(ts@[j])),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !fits(&xs[i], &ts[i]) {
            proof {
                lemma_xtys(xs@);
                lemma_stys(ts@);
                lemma_fits_all(xtys(xs@), stys(ts@));
                assert(!fits_s(xtys(xs@)[i as int], stys(ts@)[i as int]));
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_fits_all(xtys(xs@), stys(ts@));
        assert forall|j: int| 0 <= j < xs@.len() implies #[trigger] fits_s(xtys(xs@)[j], stys(ts@)[j]) by {
            assert(fits_s(xty(xs@[j]), sty(ts@[j])));
        }
    }
    true
}

/// 状態変数や引数のスロット。`kind` は 0 が遷移前の状態変数、1 が遷移後の状態変数、2 が引数。
pub(crate) fn layout_slots(l: &Layout, kind: u8, enums: &Vec<i64>) -> (r: Option<(XType, Vec<Expr>)>)
    ensures
        lim_s(sty(l.ty), enums@) && l.offset + width(sty(l.ty), enums@) <= usize::MAX ==> r is Some,
        r matches Some((_, out)) ==> forall|n: nat| #[trigger] all_pure(out@, n),
        r matches Some((t, out)) ==> xty(t) == to_xty(sty(l.ty)) && out@.len() == width(sty(l.ty), enums@) && forall|j: int|
            0 <= j < out@.len() ==> #[trigger] out@[j] == kind_expr(kind, (l.offset + j) as usize),
{
    let w = stype_width(&l.ty, enums)?;
    let end = l.offset.checked_add(w)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = l.offset;
    while i < end
        invariant
            l.offset <= i <= end,
            end == l.offset + w,
            out@.len() == i - l.offset,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == kind_expr(kind, (l.offset + j) as usize),
        decreases end - i,
    {
        out.push(
            if kind == 0 {
                Expr::Var(i)
            } else if kind == 1 {
                Expr::Next(i)
            } else {
                Expr::Arg(i)
            },
        );
        i += 1;
    }
    proof {
        assert forall|n: nat| #[trigger] all_pure(out@, n) by {
            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], n) by {
                assert(out@[j] == kind_expr(kind, (l.offset + j) as usize));
            }
        }
    }
    Some((to_xtype(&l.ty), out))
}

pub(crate) fn lit_type(v: &Value) -> (r: XType)
    ensures
        xty(r) == match *v {
            Value::Bool(_) => XTy::Bool,
            Value::Int(_) => XTy::Int,
            Value::Enum(id, _) => XTy::Enum(id),
        },
{
    match v {
        Value::Bool(_) => XType::Bool,
        Value::Int(_) => XType::Int,
        Value::Enum(id, _) => XType::Enum(*id),
    }
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

pub(crate) fn append(out: &mut Vec<Expr>, xs: &Vec<Expr>)
    ensures
        final(out)@ == old(out)@ + xs@,
{
    let ghost o = out@;
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            out@ == o + xs@.take(i as int),
        decreases xs.len() - i,
    {
        out.push(copy_expr(&xs[i]));
        proof {
            assert(o + xs@.take(i + 1) =~= (o + xs@.take(i as int)).push(xs@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs@.len() as int) =~= xs@);
    }
}

pub(crate) fn copy_usizes(xs: &Vec<usize>) -> (r: Vec<usize>)
    ensures
        r@ == xs@,
{
    let mut out: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            out@ == xs@.take(i as int),
        decreases xs.len() - i,
    {
        out.push(xs[i]);
        proof {
            assert(xs@.take(i + 1) =~= xs@.take(i as int).push(xs@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs@.len() as int) =~= xs@);
    }
    out
}

/// 式を `blk` の中に下ろす。部分式の束縛は評価の順に `blk` に追加し、失敗しないスロットの式を返す。
pub(crate) fn low(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 3nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_)
        | TExpr::Bin(_, _, _) | TExpr::Eq(_, _, _) | TExpr::Not(_) | TExpr::Fold(_, _) | TExpr::Implies(_, _)
        | TExpr::Ite(_, _, _) | TExpr::Let(_, _) => low_core(e, cx, sc, blk),
        TExpr::Quant(_, _, _) => low_quant(e, cx, sc, blk),
        TExpr::Tuple(_) | TExpr::Record(_, _) | TExpr::Nth(_, _) | TExpr::Field(_, _, _)
        | TExpr::None(_) | TExpr::Some(_) | TExpr::IsSome(_) | TExpr::IsNone(_) | TExpr::Unwrap(_) => low_struct(
            e,
            cx,
            sc,
            blk,
        ),
        TExpr::SetLit(_, _) => low_set_lit(e, cx, sc, blk),
        TExpr::MapLit(_, _, _) => low_map_lit(e, cx, sc, blk),
        TExpr::ListLit(_, _, _) => low_list_lit(e, cx, sc, blk),
        TExpr::SetContains(_, _, _) | TExpr::ListContains(_, _) | TExpr::Insert(_, _, _) | TExpr::Remove(_, _, _)
        | TExpr::SetBin(_, _, _) | TExpr::Size(_) | TExpr::IsEmpty(_) => low_coll(e, cx, sc, blk),
        _ => low_access(e, cx, sc, blk),
    }
}

/// 型 `want` のスカラーの式として下ろす。
pub(crate) fn sub_scalar(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, want: &XType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(*want), seq![x]),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(xty(*want))
            && scalar_x(xty(*want)) ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(x) ==> has_ty(x, lenv(*cx), blt(*final(blk), *cx), xetys(xty(*want), cx.enums@)[0])),
    decreases e, 4nat,
{
    let (t, slots) = low(e, cx, sc, blk)?;
    if !xtype_eq(&t, want) || slots.len() != 1 {
        return Err(Fail::Type);
    }
    let x = copy_expr(&slots[0]);
    proof {
        assert(slots@ =~= seq![x]);
        assert(xty(t) == xty(*want));
    }
    Ok(x)
}

/// スカラー型の式として、深さ `depth` で単独に評価できるように下ろす。
fn scalar_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize, outer: Ghost<Seq<ETy>>) -> (r: Result<(XType, Expr), Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, x)) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, xty(t), x),
        tpre(*e, *cx, old(sc)@, depth as nat) && scalar_x(ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@))->0) ==> deep(r) && (
        r matches Ok((t, _)) ==> Some(xty(t)) == ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@))),
        tpre(*e, *cx, old(sc)@, depth as nat) && tok_in(*cx, old(sc)@, outer@, depth as nat) ==> (r matches Ok((t, x))
            ==> has_ty(x, lenv(*cx), outer@, xetys(xty(t), cx.enums@)[0])),
    decreases e, 6nat,
{
    let mut blk = new_block(depth, outer)?;
    let ghost b0 = blk;
    proof {
        assert(blt(b0, *cx) == outer@);
    }
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    if !is_scalar(&t) || slots.len() != 1 {
        return Err(Fail::Type);
    }
    let x = wrap(&blk.binds, copy_expr(&slots[0]));
    proof {
        if tpre(*e, *cx, old(sc)@, depth as nat) && tok_in(*cx, old(sc)@, outer@, depth as nat) {
            assert(tok(*cx, old(sc)@, b0));
            assert(binds_typed(outer@, blk.binds@, lenv(*cx)));
            assert(has_ty(slots@[0], lenv(*cx), blt(blk, *cx), xetys(xty(t), cx.enums@)[0]));
        }
        assert(fresh(b0, blk) =~= blk.binds@);
        assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
            #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == depth as nat && frag(*e) implies scalar_result(
            eval_src(*e, se, sls),
            eval_l(x, env, ls),
            xty(t),
            se.enums,
        ) by {
            match eval_src(*e, se, sls) {
                Ok(v) => {
                    let l = run(blk.binds@, env, ls)->Ok_0;
                    assert(denotes(slots@, env, l, v, xty(t), se.enums));
                    assert(slot_vals(slots@, env, l) =~= seq![eval_l(slots@[0], env, l)->Ok_0]);
                },
                Err(_) => {},
            }
        }
    }
    Ok((t, x))
}

/// 述語として、深さ `depth` で単独に評価できるように下ろす。
pub(crate) fn bool_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize, outer: Ghost<Seq<ETy>>) -> (r: Result<Expr, Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, XTy::Bool, x),
        tpre(*e, *cx, old(sc)@, depth as nat) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(XTy::Bool) ==> deep(r),
        tpre(*e, *cx, old(sc)@, depth as nat) && tok_in(*cx, old(sc)@, outer@, depth as nat) ==> (r matches Ok(x) ==> has_ty(
            x,
            lenv(*cx),
            outer@,
            ETy::Bool,
        )),
    decreases e, 7nat,
{
    let (t, x) = scalar_in(e, cx, sc, depth, outer)?;
    match t {
        XType::Bool => Ok(x),
        _ => Err(Fail::Type),
    }
}

/// 要素を集合の型に合わせて評価し、属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。正規形のスロットを返す。
pub(crate) fn element(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(xs) ==> frag(*e) ==> elem_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), xs@),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) ==> deep(r) && (r matches Ok(xs) ==> xs@.len() == width(sty(*st), cx.enums@) && all_pure(
            xs@,
            final(blk).depth_s(),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(final(blk).outer@, final(blk).binds@, lenv(*cx)) && (r matches Ok(xs) ==> typed(
            xs@,
            etys(slot_tys(sty(*st), cx.enums@)),
            lenv(*cx),
            blt(*final(blk), *cx),
        )),
    decreases e, 4nat,
{
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    );
    let ghost tq = pre && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let (t, slots) = low(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    proof {
        lemma_to_fits(sty(*st));
        if pre {
            lemma_xwidth_of(sty(*st), cx.enums@);
        }
    }
    if !fits(&t, st) {
        return Err(Fail::Type);
    }
    let (cond, stored) = need(store(&t, &slots, st, &cx.enums))?;
    let ghost cg = cond;
    let ghost sg = stored@;
    proof {
        if tq {
            assert(typed(slots@, xetys(xty(t), cx.enums@), tv, blt(b1, *cx)));
            assert(has_ty(cg, tv, blt(b1, *cx), ETy::Bool) && typed(sg, xetys(xty(t), cx.enums@), tv, blt(b1, *cx)));
        }
    }
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    let ghost b2 = *blk;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(all_pure(stored@, b1.depth_s()));
            lemma_all_pure_mono(stored@, b1.depth_s(), b2.depth_s());
        }
        if tq {
            lemma_check_typed(b1, b2, cg, FAIL_NOT_IN_DOMAIN, *cx);
            lemma_fits_etys(xty(t), sty(*st), cx.enums@);
            lemma_typed_blk(sg, xetys(xty(t), cx.enums@), *cx, b1, b2);
        }
    }
    let xs = atoms(stored, blk, Ghost(*cx), Ghost(etys(slot_tys(sty(*st), cx.enums@))))?;
    proof {
        lemma_extends_trans(b0, b1, b2);
        if frag(*e) {
            lemma_element(*e, *cx, sc@, b0, b1, b2, *blk, xty(t), slots@, sty(*st), cg, sg, xs@);
        }
    }
    Ok(xs)
}

/// 要素の番号。属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
pub(crate) fn element_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> elem_rank_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), x),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && keys(sty(*st), cx.enums@) is Some ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(final(blk).outer@, final(blk).binds@, lenv(*cx)) && (r matches Ok(x) ==> has_ty(
            x,
            lenv(*cx),
            blt(*final(blk), *cx),
            ETy::Int,
        )),
    decreases e, 4nat,
{
    if keys_exec(st, &cx.enums).is_none() {
        proof {
            lemma_extends_refl(*blk);
        }
        return Err(Fail::Type);
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && keys(sty(*st), cx.enums@) is Some;
    let ghost tq = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let (t, slots) = low(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    proof {
        lemma_to_fits(sty(*st));
        if pre {
            lemma_xwidth_of(sty(*st), cx.enums@);
        }
    }
    if !fits(&t, st) {
        return Err(Fail::Type);
    }
    let (cond, _out) = need(store(&t, &slots, st, &cx.enums))?;
    let ghost cg = cond;
    proof {
        if tq {
            assert(typed(slots@, xetys(xty(t), cx.enums@), tv, blt(b1, *cx)));
            assert(has_ty(cg, tv, blt(b1, *cx), ETy::Bool));
        }
    }
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    let ghost b2 = *blk;
    let r = need(rank_expr(&t, &slots, st, &cx.enums))?;
    let ghost rg = r;
    let ghost bq = *blk;
    proof {
        if tq {
            lemma_check_typed(b1, b2, cg, FAIL_NOT_IN_DOMAIN, *cx);
            assert(has_ty(rg, tv, blt(b1, *cx), ETy::Int));
            assert(all_pure(slots@, b1.depth_s()));
            assert(pure_below(rg, b1.depth_s()));
            lemma_has_ty_blk(rg, ETy::Int, *cx, b1, b2);
        }
    }
    let x = atom(blk, r)?;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(pure_below(r, b1.depth_s()));
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
        }
        if tq {
            lemma_added_typed(bq, *blk, rg, x, *cx, ETy::Int);
        }
    }
    proof {
        lemma_extends_trans(b0, b1, b2);
        if frag(*e) {
            lemma_elem_rank(*e, *cx, sc@, b0, b1, b2, *blk, xty(t), slots@, sty(*st), cg, _out@, rg, x);
        }
    }
    Ok(x)
}

/// 要素の番号。属さなければ -1。
pub(crate) fn lookup_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> rank_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), x),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && keys(sty(*st), cx.enums@) is Some ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk)) ==> binds_typed(final(blk).outer@, final(blk).binds@, lenv(*cx)) && (r matches Ok(x) ==> has_ty(
            x,
            lenv(*cx),
            blt(*final(blk), *cx),
            ETy::Int,
        )),
    decreases e, 4nat,
{
    if keys_exec(st, &cx.enums).is_none() {
        proof {
            lemma_extends_refl(*blk);
        }
        return Err(Fail::Type);
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && keys(sty(*st), cx.enums@) is Some;
    let ghost tq = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && ir_type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && wf_stype(sty(*st), cx.enums@) && small(sty(*st)) && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    let (t, slots) = low(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    proof {
        lemma_to_fits(sty(*st));
        if pre {
            lemma_xwidth_of(sty(*st), cx.enums@);
        }
    }
    if !fits(&t, st) {
        return Err(Fail::Type);
    }
    let r = need(rank_or_neg(&t, &slots, st, &cx.enums))?;
    let ghost rr = r;
    let ghost bq = *blk;
    proof {
        if tq {
            assert(typed(slots@, xetys(xty(t), cx.enums@), tv, blt(b1, *cx)));
            assert(has_ty(rr, tv, blt(b1, *cx), ETy::Int));
        }
    }
    let x = atom(blk, r)?;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(pure_below(r, b1.depth_s()));
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
        }
        if tq {
            lemma_added_typed(bq, *blk, rr, x, *cx, ETy::Int);
        }
    }
    proof {
        let enums = cx.enums@;
        assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
            #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == b0.depth_s() && frag(*e) implies rank_result(
            eval_src(*e, se, sls),
            run(fresh(b0, *blk), env, ls),
            x,
            env,
            sty(*st),
            se.enums,
        ) by {
            lemma_run_fresh(b0, b1, *blk, env, ls);
            lemma_run_len(fresh(b0, b1), env, ls);
            match eval_src(*e, se, sls) {
                Ok(v) => {
                    let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                    assert(denotes(slots@, env, l1, v, xty(t), enums));
                    lemma_clean_pure(slots@, env, l1);
                    assert(eval_l(rr, env, l1) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums) {
                        rank(v, sty(*st), enums) as i64
                    } else {
                        -1i64
                    })));
                    lemma_added(b1, *blk, rr, x, env, l1, Value::Int(if member(v, sty(*st), enums) {
                        rank(v, sty(*st), enums) as i64
                    } else {
                        -1i64
                    }));
                },
                Err(_) => {},
            }
        }
    }
    Ok(x)
}

/// Setの要素の判定と更新、Setの演算、Listの要素の判定、大きさ。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_coll(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is SetContains || e is ListContains || e is Insert || e is Remove || e is SetBin || e is Size || e is IsEmpty,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    match e {
        TExpr::SetContains(_, _, _) => low_member(e, cx, sc, blk),
        TExpr::ListContains(_, _) => low_list_contains(e, cx, sc, blk),
        TExpr::Insert(_, _, _) | TExpr::Remove(_, _, _) | TExpr::SetBin(_, _, _) => low_setop(e, cx, sc, blk),
        _ => low_size(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_size(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Size || e is IsEmpty,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Size(a) | TExpr::IsEmpty(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                    assert(here_ok(**a, c, bt));
                }
            }
            let ghost ys = xetys(xty(t), cx.enums@);
            proof {
                if tp {
                    assert(typed(s@, ys, tv, blt(b1, *cx)));
                    assert(binds_typed(b1.outer@, b1.binds@, tv));
                }
            }
            let is_size = match e {
                TExpr::Size(_) => true,
                _ => false,
            };
            let flags: Vec<Expr> = match &t {
                XType::Set(_u) => {
                    proof {
                        if frag(*e) {
                            lemma_flags_set(**a, *cx, sc@, b0, b1, sty(**_u), s@);
                        }
                        if tp {
                            lemma_typed_bools(s@, keys_or_zero(sty(**_u), cx.enums@), tv, blt(b1, *cx));
                        }
                    }
                    copy_exprs(&s)
                },
                XType::Map(k, v) => {
                    let n = need(keys_exec(k, enums))?;
                    proof {
                        if pre {
                            assert(n <= crate::encoding::MAX_KEYS);
                            assert(lim_s(sty(**v), enums@));
                        }
                    }
                    if n > 0x7fff_ffff {
                        return Err(Fail::Type);
                    }
                    let w = need(stype_width(v, enums))?;
                    proof {
                        assert(usize::MAX >= 0xffff_ffff);
                    }
                    let stride = need(w.checked_add(1))?;
                    let mut fs: Vec<Expr> = Vec::new();
                    let mut j: usize = 0;
                    while j < n as usize
                        invariant
                            n <= 0x7fff_ffff,
                            j <= n,
                            fs@.len() == j,
                            forall|q: int| 0 <= q < j ==> #[trigger] fs@[q] == s@[q * stride],
                            extends(*old(blk), *blk),
                            *blk == b1,
                            pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                            pre ==> s@.len() == n * stride && all_pure(s@, b1.depth_s()) && stride == w + 1,
                            pre ==> all_pure(fs@, b1.depth_s()),
                        decreases n - j,
                    {
                        proof {
                            assert((j + 1) * stride <= n * stride) by (nonlinear_arith)
                                requires
                                    j < n,
                            ;
                            assert(j * stride + stride == (j + 1) * stride) by (nonlinear_arith);
                            assert(usize::MAX >= 0xffff_ffff);
                        }
                        let pos = need(j.checked_mul(stride))?;
                        if pos >= s.len() {
                            return Err(Fail::Type);
                        }
                        let ghost f0 = fs@;
                        fs.push(copy_expr(&s[pos]));
                        proof {
                            if pre {
                                assert forall|q: int| 0 <= q < fs@.len() implies pure_below(#[trigger] fs@[q], b1.depth_s()) by {
                                    if q < f0.len() {
                                        assert(fs@[q] == f0[q]);
                                    }
                                }
                            }
                        }
                        j += 1;
                    }
                    proof {
                        if frag(*e) {
                            lemma_flags_map(**a, *cx, sc@, b0, b1, sty(**k), sty(**v), stride as int, s@, fs@, n as nat);
                        }
                        if tp {
                            let mt = STy::Map(Box::new(sty(**k)), Box::new(sty(**v)));
                            lemma_xetys_of(mt, cx.enums@);
                            assert(xty(t) == to_xty(mt));
                            crate::lower_types::lemma_slot_tys_len(sty(**v), cx.enums@);
                            lemma_xwidth_of(sty(**v), cx.enums@);
                            let row = seq![Type::Bool] + slot_tys(sty(**v), cx.enums@);
                            assert(row[0] == Type::Bool);
                            assert(slot_tys(mt, cx.enums@) == crate::lower_types::ty_repeat(row, keys_or_zero(sty(**k), cx.enums@)));
                            lemma_map_flags_typed(s@, fs@, row, keys_or_zero(sty(**k), cx.enums@), stride as int, tv, blt(b1, *cx));
                        }
                    }
                    fs
                },
                XType::List(_u, max) => {
                    if s.len() == 0 || *max > 0x7fff_ffffusize {
                        return Err(Fail::Type);
                    }
                    let len = copy_expr(&s[0]);
                    proof {
                        if pre {
                            assert(pure_below(s@[0], b1.depth_s()));
                            assert(len == s@[0]);
                            assert(pure_below(len, b1.depth_s()));
                            assert(pure_below(Expr::Const(Value::Int(0)), b1.depth_s()));
                            assert(pure_below(Expr::Bin(BinOp::Eq, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), b1.depth_s()));
                        }
                    }
                    proof {
                        if tp {
                            let lt0 = STy::List(Box::new(sty(**_u)), *max);
                            lemma_xetys_of(lt0, cx.enums@);
                            assert(xty(t) == to_xty(lt0));
                            assert(etys(slot_tys(lt0, cx.enums@))[0] == ETy::Int);
                            assert(has_ty(s@[0], tv, blt(b1, *cx), ys[0]));
                            assert(has_ty(len, tv, blt(b1, *cx), ETy::Int));
                            assert(has_ty(Expr::Const(Value::Int(0)), tv, blt(b1, *cx), ETy::Int));
                        }
                    }
                    let mut out: Vec<Expr> = Vec::new();
                    if is_size {
                        out.push(len);
                    } else {
                        out.push(eq(len, ci(0)));
                    }
                    proof {
                        if frag(*e) {
                            lemma_list_size(*e, **a, *cx, sc@, b0, b1, sty(**_u), *max, s@, out@);
                        }
                    }
                    return Ok((if is_size { XType::Int } else { XType::Bool }, out));
                },
                _ => return Err(Fail::Type),
            };
            proof {
                if pre {
                    assert(flags@.len() <= crate::encoding::MAX_KEYS);
                    assert(all_pure(flags@, b1.depth_s()));
                }
                if tp {
                    assert(all_ty(flags@, ETy::Bool, tv, blt(b1, *cx)));
                }
            }
            if flags.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let mut out: Vec<Expr> = Vec::new();
            if is_size {
                let mut codes: Vec<Expr> = Vec::new();
                let mut i = 0;
                while i < flags.len()
                    invariant
                        i <= flags@.len(),
                        codes@.len() == i,
                        forall|q: int| 0 <= q < i ==> #[trigger] codes@[q] == Expr::Code(Box::new(flags@[q])),
                        pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                        pre ==> all_pure(flags@, b1.depth_s()),
                        *blk == b1,
                        tp == (pre && tok(*cx, old(sc)@, *old(blk))),
                        tv == lenv(*cx),
                        tp ==> all_ty(flags@, ETy::Bool, tv, blt(b1, *cx)),
                    decreases flags.len() - i,
                {
                    codes.push(Expr::Code(Box::new(copy_expr(&flags[i]))));
                    i += 1;
                }
                proof {
                    if pre {
                        assert forall|q: int| 0 <= q < codes@.len() implies pure_below(#[trigger] codes@[q], b1.depth_s()) by {
                            assert(codes@[q] == Expr::Code(Box::new(flags@[q])));
                            assert(pure_below(flags@[q], b1.depth_s()));
                        }
                        lemma_tree_pure(codes@, int_lit(0), Join::Add, b1.depth_s());
                    }
                    if tp {
                        assert forall|q: int| 0 <= q < codes@.len() implies #[trigger] has_ty(codes@[q], tv, blt(b1, *cx), ETy::Int) by {
                            assert(codes@[q] == Expr::Code(Box::new(flags@[q])));
                            assert(has_ty(flags@[q], tv, blt(b1, *cx), ETy::Bool));
                        }
                        lemma_tree_typed(codes@, int_lit(0), Join::Add, tv, blt(b1, *cx), ETy::Int);
                    }
                }
                let ghost sm = tree_s(codes@, int_lit(0), Join::Add);
                let x = keep(blk, sum(&codes))?;
                proof {
                    if pre {
                        lemma_pure_mono(sm, b1.depth_s(), blk.depth_s());
                    }
                    if tp {
                        assert(b1.outer@.len() == b1.base);
                        lemma_added_typed(b1, *blk, sm, x, *cx, ETy::Int);
                    }
                }
                proof {
                    if frag(*e) {
                        lemma_size(*e, **a, *cx, sc@, b0, b1, *blk, flags@, codes@, x);
                    }
                }
                out.push(x);
                Ok((XType::Int, out))
            } else {
                out.push(not(any_of(&flags)));
                proof {
                    if pre {
                        lemma_tree_pure(flags@, bool_lit(false), Join::Or, b1.depth_s());
                    }
                    if tp {
                        lemma_tree_typed(flags@, bool_lit(false), Join::Or, tv, blt(b1, *cx), ETy::Bool);
                    }
                }
                proof {
                    if frag(*e) {
                        lemma_is_empty(*e, **a, *cx, sc@, b0, b1, flags@);
                    }
                }
                Ok((XType::Bool, out))
            }
        },
        _ => Err(Fail::Type),
    }
}

/// Mapの参照と更新、Listの参照と更新。
fn low_access(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is HasKey || e is Get || e is Put || e is Delete || e is Keys || e is At || e is First || e is Last || e is Push || e is Pop || e is Shift,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && tok(*cx, old(sc)@, *old(blk)) ==> ty_post(*cx, *final(blk), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 2nat,
{
    match e {
        TExpr::Get(_, _, _) => low_get(e, cx, sc, blk),
        TExpr::HasKey(_, _, _) | TExpr::Put(_, _, _, _, _) | TExpr::Delete(_, _, _) | TExpr::Keys(_) => low_map_access(
            e,
            cx,
            sc,
            blk,
        ),
        TExpr::At(_, _) | TExpr::First(_) | TExpr::Last(_) => low_list_get(e, cx, sc, blk),
        _ => low_list_update(e, cx, sc, blk),
    }
}

/// 述語（guard、不変条件、遷移契約、終端条件）として下ろす。
///
/// 環境が対応するとき、下ろした式の値は、値の上の意味論の値と一致する（失敗するなら同じ失敗）。
pub fn lower_prop(e: &TExpr, cx: &LowerCtx) -> (r: Result<Expr, Fail>)
    ensures
        cx_wf(*cx) && ir_type_of(*e, sctx(*cx), Seq::empty()) == Some(XTy::Bool) && lim_ok(*e, sctx(*cx), Seq::empty())
            ==> deep(r),
        cx_wf(*cx) && ir_type_of(*e, sctx(*cx), Seq::empty()) == Some(XTy::Bool) && lim_ok(*e, sctx(*cx), Seq::empty())
            && cx_tok(*cx) ==> (r matches Ok(c) ==> has_ty(c, lenv(*cx), Seq::empty(), ETy::Bool)),
        r matches Ok(c) ==> forall|env: Env, se: SEnv|
            #[trigger] env_rel(*cx, env, se) ==> prop_result(
                eval_src(*e, se, Seq::empty()),
                eval_l(c, env, Seq::empty()),
            ),
{
    let mut sc: Vec<Bound> = Vec::new();
    proof {
        assert(bound_tys(sc@) =~= Seq::<XTy>::empty());
    }
    proof {
        assert(sc_typed(sc@, *cx, Seq::empty()));
    }
    let r = bool_in(e, cx, &mut sc, 0, Ghost(Seq::empty()));
    proof {
        lemma_frag_total(*e);
        if r is Ok {
            let c = r->Ok_0;
            if frag(*e) {
                assert forall|env: Env, se: SEnv| #[trigger] env_rel(*cx, env, se) implies prop_result(
                    eval_src(*e, se, Seq::empty()),
                    eval_l(c, env, Seq::empty()),
                ) by {
                    assert(ctx_ok(*cx, Seq::empty(), env, se, Seq::empty(), Seq::empty()));
                    assert(sc@ =~= Seq::<Bound>::empty());
                }
            }
        }
    }
    r
}

/// 値を型 `st` の場所に置くスロット（正規形）。整数の範囲は検査しない（中核の範囲外更新で検出する）。
///
/// 環境が対応し、局所変数の数が `depth` のとき、値が型に属するなら、各スロットの値はその正規形の符号化になる。
/// 失敗するなら、各スロットは同じ失敗になる。
pub fn lower_stored(e: &TExpr, cx: &LowerCtx, st: &SType, depth: usize) -> (r: Result<Vec<Expr>, Fail>)
    ensures
        cx_wf(*cx) && ir_type_of(*e, sctx(*cx), Seq::empty()) == Some(to_xty(sty(*st))) && lim_ok(
            *e,
            sctx(*cx),
            Seq::empty(),
        ) && ok_s(sty(*st), cx.enums@) ==> deep(r) && (r matches Ok(out) ==> out@.len() == width(sty(*st), cx.enums@)),
        cx_wf(*cx) && ir_type_of(*e, sctx(*cx), Seq::empty()) == Some(to_xty(sty(*st))) && lim_ok(
            *e,
            sctx(*cx),
            Seq::empty(),
        ) && ok_s(sty(*st), cx.enums@) && depth == 0 && cx_tok(*cx) ==> (r matches Ok(out) ==> typed(
            out@,
            etys(slot_tys(sty(*st), cx.enums@)),
            lenv(*cx),
            Seq::empty(),
        )),
        r matches Ok(out) ==> forall|env: Env, se: SEnv, ls: Seq<Value>|
            #[trigger] top_ok(*cx, env, se, ls, depth as nat) ==> stored_result(
                eval_src(*e, se, Seq::empty()),
                out@,
                env,
                ls,
                sty(*st),
                se.enums,
            ),
{
    let mut sc: Vec<Bound> = Vec::new();
    proof {
        assert(bound_tys(sc@) =~= Seq::<XTy>::empty());
        lemma_to_fits(sty(*st));
        lemma_xwidth_of(sty(*st), cx.enums@);
    }
    let mut blk = new_block(depth, Ghost(Seq::empty()))?;
    let ghost b0 = blk;
    let ghost tp = cx_wf(*cx) && ir_type_of(*e, sctx(*cx), Seq::empty()) == Some(to_xty(sty(*st))) && lim_ok(
        *e,
        sctx(*cx),
        Seq::empty(),
    ) && ok_s(sty(*st), cx.enums@) && depth == 0 && cx_tok(*cx);
    let ghost tv = lenv(*cx);
    proof {
        if tp {
            assert(sc_typed(sc@, *cx, blt(b0, *cx)));
            assert(binds_typed(b0.outer@, b0.binds@, tv));
            assert(tok(*cx, sc@, b0));
        }
    }
    let (t, slots) = low(e, cx, &mut sc, &mut blk)?;
    if !fits(&t, st) {
        return Err(Fail::Type);
    }
    let (_c, stored) = need(store(&t, &slots, st, &cx.enums))?;
    proof {
        if tp {
            lemma_lim_small(sty(*st), cx.enums@);
            assert(typed(slots@, xetys(xty(t), cx.enums@), tv, blt(blk, *cx)));
            assert(typed(stored@, xetys(xty(t), cx.enums@), tv, blt(blk, *cx)));
            lemma_fits_etys(xty(t), sty(*st), cx.enums@);
            assert(binds_typed(blk.outer@, blk.binds@, tv));
            assert(blk.outer@ == Seq::<ETy>::empty());
        }
    }
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < stored.len()
        invariant
            i <= stored@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, stored@[j]),
            tv == lenv(*cx),
            tp ==> typed(stored@, etys(slot_tys(sty(*st), cx.enums@)), tv, blt(blk, *cx)),
            tp ==> binds_typed(Seq::empty(), blk.binds@, tv) && blk.outer@ == Seq::<ETy>::empty(),
            tp ==> forall|j: int| 0 <= j < i ==> #[trigger] has_ty(out@[j], tv, Seq::empty(), etys(slot_tys(sty(*st), cx.enums@))[j]),
        decreases stored.len() - i,
    {
        let x = wrap(&blk.binds, copy_expr(&stored[i]));
        out.push(x);
        proof {
            assert(wraps(out@[i as int], blk.binds@, stored@[i as int]));
            if tp {
                assert(has_ty(stored@[i as int], tv, blt(blk, *cx), etys(slot_tys(sty(*st), cx.enums@))[i as int]));
                assert(has_ty(out@[i as int], tv, Seq::empty(), etys(slot_tys(sty(*st), cx.enums@))[i as int]));
            }
        }
        i += 1;
    }
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        lemma_frag_total(*e);
        if frag(*e) {
            assert forall|env: Env, se: SEnv, ls: Seq<Value>| #[trigger] top_ok(*cx, env, se, ls, depth as nat) implies stored_result(
                eval_src(*e, se, Seq::empty()),
                out@,
                env,
                ls,
                sty(*st),
                se.enums,
            ) by {
                assert(sc@ =~= Seq::<Bound>::empty());
                assert(ctx_ok(*cx, sc@, env, se, ls, Seq::empty()));
                match eval_src(*e, se, Seq::empty()) {
                    Ok(v) => {
                        let l = run(blk.binds@, env, ls)->Ok_0;
                        assert(denotes(slots@, env, l, v, xty(t), se.enums));
                        assert(store_ok(_c, stored@, env, l, v, sty(*st), se.enums));
                        lemma_models_has(slot_vals(slots@, env, l), v, xty(t), se.enums);
                        lemma_fits_to(xty(t), sty(*st));
                        lemma_shaped_len(v, sty(*st), se.enums);
                        if in_slots(enc(v, sty(*st), se.enums), slot_tys(sty(*st), se.enums), se.enums) {
                            lemma_in_member(v, sty(*st), se.enums);
                        }
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Ok::<
                            Value,
                            ErrKind,
                        >(enc(v, sty(*st), se.enums)[j]) by {
                            assert(wraps(out@[j], blk.binds@, stored@[j]));
                            assert(eval_l(stored@[j], env, l) == Ok::<Value, ErrKind>(slot_vals(stored@, env, l)[j]));
                        }
                    },
                    Err(_) => {
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Err::<
                            Value,
                            ErrKind,
                        >(eval_src(*e, se, Seq::empty())->Err_0) by {
                            assert(wraps(out@[j], blk.binds@, stored@[j]));
                        }
                    },
                }
            }
        }
    }
    Ok(out)
}

} // verus!
