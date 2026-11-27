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
//! 下ろしは、型の合わない式や、長さの合わないスロットの列に対して `None` を返す。
//!
//! 下ろしが意味を保存することの補題は、[`crate::preserve`] と、式の種類ごとの `preserve_*.rs` にある。

#[cfg(verus_keep_ghost)]
use crate::canon::{in_slots, lemma_fits_to, lemma_in_member, lemma_models_has, lemma_shaped_len, slot_tys};
use crate::encoding::{copy_stype, copy_xtype, keys_exec, stype_eq, to_xtype, usizes_eq, xtype_eq, SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_repeat, keys, keys_or_zero, lemma_default_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_models_enc, lemma_stys, lemma_xtys, lemma_xwidth_of, member, sty, stys, to_xty};
#[cfg(verus_keep_ghost)]
use crate::encoding::{wf_xtype, width, xty, xtys, xwidth, xwidth_sum, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, lookup, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::{lemma_all_typed_bool, lemma_all_typed_iff, lemma_types_of_iff, type_of, types_of};
#[cfg(verus_keep_ghost)]
use crate::keys::rank;
#[cfg(verus_keep_ghost)]
use crate::limits::*;
#[cfg(verus_keep_ghost)]
use crate::lists::{flat, rows_view};
use crate::map_lookup::select_flat_map_lookup;
use crate::model::{BinOp, Expr, Type, Value};
use crate::preserve::pure_exec;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_list::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_map::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_ops::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_quant::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_set::*;
#[cfg(verus_keep_ghost)]
use crate::preserve_tuple::*;
use crate::quant::{pick_slot, unrank};
#[cfg(verus_keep_ghost)]
use crate::quant::{picks, unrank_ok};
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, Item, SEnv};
use crate::source::{Over, SetOp, TExpr, FAIL_EMPTY, FAIL_FULL, FAIL_INDEX, FAIL_NONE, FAIL_NOT_IN_DOMAIN};
#[cfg(verus_keep_ghost)]
use crate::total::*;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// 状態変数や引数の、スロットの列での位置。
pub struct Layout {
    pub ty: SType,
    pub offset: usize,
}

/// 名前付きの定数。値はスロットごとの中核の値。
pub struct Constant {
    pub ty: SType,
    pub slots: Vec<Value>,
}

/// 下ろしの文脈。
pub struct LowerCtx {
    /// 各列挙型のラベルの数。
    pub enums: Vec<i64>,
    /// 状態変数。`None` なら状態を参照できない（初期値と定数）。
    pub states: Option<Vec<Layout>>,
    /// 公開引数に続けて内部選択。
    pub args: Vec<Layout>,
    /// 遷移後の状態と出力を参照できる（遷移契約）。
    pub next: bool,
    pub out: Option<SType>,
    pub consts: Vec<Constant>,
}

/// 局所変数（`let` と量化の束縛）。
pub struct Bound {
    pub ty: XType,
    pub slots: Vec<Expr>,
}

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
fn layout_slots(l: &Layout, kind: u8, enums: &Vec<i64>) -> (r: Option<(XType, Vec<Expr>)>)
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

fn lit_type(v: &Value) -> (r: XType)
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
fn atoms(xs: Vec<Expr>, blk: &mut Block) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
    ensures
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
            lemma_atoms_step(xs@.take(i as int), x, o1, y, b0, b1, *blk);
            assert(xs@.take(i as int).push(x) =~= xs@.take(i + 1));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs.len() as int) =~= xs@);
    }
    Ok(out)
}

fn append(out: &mut Vec<Expr>, xs: &Vec<Expr>)
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

fn copy_usizes(xs: &Vec<usize>) -> (r: Vec<usize>)
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
fn low(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
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
fn sub_scalar(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, want: &XType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(*want), seq![x]),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(xty(*want))
            && scalar_x(xty(*want)) ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
    decreases e, 4nat,
{
    let (t, slots) = low(e, cx, sc, blk)?;
    if !xtype_eq(&t, want) || slots.len() != 1 {
        return Err(Fail::Type);
    }
    let x = copy_expr(&slots[0]);
    proof {
        assert(slots@ =~= seq![x]);
    }
    Ok(x)
}

/// 深さ `depth` で単独に評価できるように下ろす。スロットごとに、束縛を含む式を返す。
fn closed_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Result<(XType, Vec<Expr>), Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, xs)) ==> frag(*e) ==> closed_slots(*e, *cx, old(sc)@, depth as nat, xty(t), xs@),
        tpre(*e, *cx, old(sc)@, depth as nat) ==> deep(r) && (r matches Ok((t, xs)) ==> Some(xty(t)) == type_of(
            *e,
            sctx(*cx),
            bound_tys(old(sc)@),
        ) && xs@.len() == xwidth(xty(t), cx.enums@)),
    decreases e, 5nat,
{
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < slots.len()
        invariant
            i <= slots@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, slots@[j]),
        decreases slots.len() - i,
    {
        let x = wrap(&blk.binds, copy_expr(&slots[i]));
        out.push(x);
        proof {
            assert(wraps(out@[i as int], blk.binds@, slots@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        if frag(*e) {
            assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == depth as nat implies slots_result(
                eval_src(*e, se, sls),
                out@,
                env,
                ls,
                xty(t),
                se.enums,
            ) by {
                match eval_src(*e, se, sls) {
                    Ok(v) => {
                        let l = run(blk.binds@, env, ls)->Ok_0;
                        assert(denotes(slots@, env, l, v, xty(t), se.enums));
                        lemma_models_len(slot_vals(slots@, env, l), v, xty(t), se.enums);
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Ok::<
                            Value,
                            ErrKind,
                        >(slot_vals(slots@, env, l)[j]) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                        assert(slot_vals(out@, env, ls) =~= slot_vals(slots@, env, l));
                    },
                    Err(_) => {
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Err::<
                            Value,
                            ErrKind,
                        >(eval_src(*e, se, sls)->Err_0) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                    },
                }
            }
        }
    }
    Ok((t, out))
}

/// スカラー型の式として、深さ `depth` で単独に評価できるように下ろす。
fn scalar_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Result<(XType, Expr), Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, x)) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, xty(t), x),
        tpre(*e, *cx, old(sc)@, depth as nat) && scalar_x(type_of(*e, sctx(*cx), bound_tys(old(sc)@))->0) ==> deep(r) && (
        r matches Ok((t, _)) ==> Some(xty(t)) == type_of(*e, sctx(*cx), bound_tys(old(sc)@))),
    decreases e, 6nat,
{
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    if !is_scalar(&t) || slots.len() != 1 {
        return Err(Fail::Type);
    }
    let x = wrap(&blk.binds, copy_expr(&slots[0]));
    proof {
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
fn bool_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Result<Expr, Fail>)
    ensures
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, XTy::Bool, x),
        tpre(*e, *cx, old(sc)@, depth as nat) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(XTy::Bool) ==> deep(r),
    decreases e, 7nat,
{
    let (t, x) = scalar_in(e, cx, sc, depth)?;
    match t {
        XType::Bool => Ok(x),
        _ => Err(Fail::Type),
    }
}

/// 要素を集合の型に合わせて評価し、属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。正規形のスロットを返す。
fn element(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(xs) ==> frag(*e) ==> elem_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), xs@),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) ==> deep(r) && (r matches Ok(xs) ==> xs@.len() == width(sty(*st), cx.enums@) && all_pure(
            xs@,
            final(blk).depth_s(),
        )),
    decreases e, 4nat,
{
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    );
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
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    let ghost b2 = *blk;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(all_pure(stored@, b1.depth_s()));
            lemma_all_pure_mono(stored@, b1.depth_s(), b2.depth_s());
        }
    }
    let xs = atoms(stored, blk)?;
    proof {
        lemma_extends_trans(b0, b1, b2);
        if frag(*e) {
            lemma_element(*e, *cx, sc@, b0, b1, b2, *blk, xty(t), slots@, sty(*st), cg, sg, xs@);
        }
    }
    Ok(xs)
}

/// 要素の番号。属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
fn element_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> elem_rank_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), x),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && keys(sty(*st), cx.enums@) is Some ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
    decreases e, 4nat,
{
    if keys_exec(st, &cx.enums).is_none() {
        proof {
            lemma_extends_refl(*blk);
        }
        return Err(Fail::Type);
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && keys(sty(*st), cx.enums@) is Some;
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
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    let ghost b2 = *blk;
    let r = need(rank_expr(&t, &slots, st, &cx.enums))?;
    let ghost rg = r;
    let ghost bq = *blk;
    let x = atom(blk, r)?;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(pure_below(r, b1.depth_s()));
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
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
fn lookup_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Result<Expr, Fail>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(x) ==> frag(*e) ==> rank_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), x),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
            to_xty(sty(*st)),
        ) && keys(sty(*st), cx.enums@) is Some ==> deep(r) && (r matches Ok(x) ==> pure_below(x, final(blk).depth_s())),
    decreases e, 4nat,
{
    if keys_exec(st, &cx.enums).is_none() {
        proof {
            lemma_extends_refl(*blk);
        }
        return Err(Fail::Type);
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s()) && type_of(*e, sctx(*cx), bound_tys(old(sc)@)) == Some(
        to_xty(sty(*st)),
    ) && keys(sty(*st), cx.enums@) is Some;
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
    let x = atom(blk, r)?;
    proof {
        if pre {
            assert(all_pure(slots@, b1.depth_s()));
            assert(pure_below(r, b1.depth_s()));
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
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

/// Mapのスロット `ms` のキー `key` に値 `value` を置く。キーと値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn put(
    _parent: &TExpr,
    ms: &Vec<Expr>,
    k: &SType,
    v: &SType,
    key: &TExpr,
    value: &TExpr,
    cx: &LowerCtx,
    sc: &mut Vec<Bound>,
    blk: &mut Block,
) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
        decreases_to!(*_parent => *key),
        decreases_to!(*_parent => *value),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(out) ==> frag(*key) && frag(*value) ==> put_lowers(
            *key,
            *value,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            sty(*k),
            sty(*v),
            ms@,
            out@,
        ),
        put_pre(*key, *value, *cx, old(sc)@, old(blk).depth_s(), sty(*k), sty(*v), ms@) ==> deep(r) && (r matches Ok(
            out,
        ) ==> shaped(out@, XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), final(blk).depth_s(), cx.enums@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_extends_refl(*blk);
    }
    let ghost b0 = *blk;
    let ghost pre = put_pre(*key, *value, *cx, old(sc)@, old(blk).depth_s(), sty(*k), sty(*v), ms@);
    proof {
        reveal(put_pre);
    }
    let ghost mt = STy::Map(Box::new(sty(*k)), Box::new(sty(*v)));
    let rows = need(map_rows(k, v, ms, &cx.enums))?;
    proof {
        if pre {
            assert(keys(sty(*k), cx.enums@) is Some);
            assert(rows@.len() <= crate::encoding::MAX_KEYS);
        }
    }
    if rows.len() > 0x7fff_ffffusize {
        return Err(Fail::Type);
    }
    let r = element_rank(key, cx, sc, blk, k)?;
    let ghost b1 = *blk;
    proof {
        if pre {
            lemma_sc_wf_mono(sc@, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
    }
    let xs = element(value, cx, sc, blk, v)?;
    let mut alt: Vec<Expr> = Vec::new();
    alt.push(cb(true));
    append(&mut alt, &xs);
    proof {
        if pre {
            let w1 = (1 + width(sty(*v), cx.enums@)) as nat;
            lemma_all_pure_mono(ms@, b0.depth_s(), blk.depth_s());
            lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(*k), cx.enums@), blk.depth_s());
            assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == alt@.len() by {
                assert(rows_view(rows@)[q] == rows@[q]@);
            }
            assert(all_pure(alt@, blk.depth_s())) by {
                assert forall|j: int| 0 <= j < alt@.len() implies pure_below(#[trigger] alt@[j], blk.depth_s()) by {
                    if j > 0 {
                        assert(alt@[j] == xs@[j - 1]);
                    }
                }
            }
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
        }
    }
    let out = need(ite_rows(&rows, &r, &alt))?;
    let res = join_rows(&out);
    proof {
        if pre {
            let w1 = (1 + width(sty(*v), cx.enums@)) as nat;
            lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), r, alt@, blk.depth_s());
            lemma_flat_shape(rows_view(out@), w1, blk.depth_s());
            assert(res@.len() == keys_or_zero(sty(*k), cx.enums@) * w1);
        }
    }
    proof {
        lemma_extends_trans(b0, b1, *blk);
        if frag(*key) && frag(*value) {
            lemma_put(*key, *value, *cx, sc@, b0, b1, *blk, sty(*k), sty(*v), ms@, rows_view(rows@), r, xs@, alt@, rows_view(out@), res@);
        }
    }
    Ok(res)
}

/// リテラルと参照。束縛を加えない。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_leaf(e: &TExpr, cx: &LowerCtx, sc: &Vec<Bound>, _blk: &Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        _blk.wf(),
        e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const,
    ensures
        tpre(*e, *cx, sc@, _blk.depth_s()) ==> low_post(*e, *cx, sc@, _blk.depth_s(), r),
        r matches Ok((t, slots)) ==> lowers(*e, *cx, sc@, *_blk, *_blk, xty(t), slots@),
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, sc@, _blk.depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(sc@);
    match e {
        TExpr::Lit(v) => {
            match v {
                Value::Enum(id, k) => {
                    if !(*id < enums.len() && 0 <= *k && *k < enums[*id]) {
                        return Err(Fail::Type);
                    }
                },
                _ => {},
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Const(*v));
            let t = lit_type(v);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(slot_vals(out@, env, ls) =~= seq![*v]);
                }
            }
            Ok((t, out))
        },
        TExpr::Var(i) | TExpr::Next(i) => {
            let states = match &cx.states {
                Some(s) => s,
                None => return Err(Fail::Type),
            };
            let is_next = match e {
                TExpr::Next(_) => true,
                _ => false,
            };
            if is_next && !cx.next {
                return Err(Fail::Type);
            }
            if *i >= states.len() {
                return Err(Fail::Type);
            }
            let kind: u8 = if is_next {
                1
            } else {
                0
            };
            proof {
                if pre {
                    assert(layout_wf(states@[*i as int], enums@));
                }
                lemma_xwidth_of(sty(states@[*i as int].ty), enums@);
            }
            let (t, out) = need(layout_slots(&states[*i], kind, enums))?;
            proof {
                assert(all_pure(out@, _blk.depth_s()));
            }
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = states@[*i as int];
                    let xs = if is_next {
                        env.post
                    } else {
                        env.pre
                    };
                    let vs = if is_next {
                        se.post
                    } else {
                        se.pre
                    };
                    assert(layouts_ok(states@, vs, env.st_tys, xs, enums@));
                    let v = vs[*i as int];
                    assert(layout_ok(l, v, env.st_tys, xs, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(kind, (l.offset + j) as usize));
                        assert(lookup(env.st_tys, xs, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Ok((t, out))
        },
        TExpr::Arg(i) => {
            if *i >= cx.args.len() {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(layout_wf(cx.args@[*i as int], enums@));
                }
                lemma_xwidth_of(sty(cx.args@[*i as int].ty), enums@);
            }
            let (t, out) = need(layout_slots(&cx.args[*i], 2, enums))?;
            proof {
                assert(all_pure(out@, _blk.depth_s()));
            }
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = cx.args@[*i as int];
                    let v = se.args[*i as int];
                    assert(layout_ok(l, v, env.arg_tys, env.args, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(2, (l.offset + j) as usize));
                        assert(lookup(env.arg_tys, env.args, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Ok((t, out))
        },
        TExpr::Out => {
            let st = match &cx.out {
                Some(t) => t,
                None => return Err(Fail::Type),
            };
            if !cx.next {
                return Err(Fail::Type);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Out);
            let t = to_xtype(st);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.out->Some_0;
                    lemma_enc_len(v, sty(*st), enums@);
                    lemma_models_enc(v, sty(*st), enums@);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Ok((t, out))
        },
        TExpr::Local(i) => {
            if *i >= sc.len() {
                return Err(Fail::Type);
            }
            let t = copy_xtype(&sc[*i].ty);
            proof {
                if pre {
                    assert(ok_x(xty(sc@[*i as int].ty), enums@));
                    assert(bt[*i as int] == xty(sc@[*i as int].ty));
                }
            }
            let out = copy_exprs(&sc[*i].slots);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(denotes(sc@[*i as int].slots@, env, ls, sls[*i as int], xty(sc@[*i as int].ty), se.enums));
                }
            }
            Ok((t, out))
        },
        TExpr::Const(i) => {
            if *i >= cx.consts.len() {
                return Err(Fail::Type);
            }
            let c = &cx.consts[*i];
            let mut out: Vec<Expr> = Vec::new();
            let mut j = 0;
            while j < c.slots.len()
                invariant
                    j <= c.slots@.len(),
                    out@ == lits(c.slots@.take(j as int)),
                decreases c.slots.len() - j,
            {
                out.push(Expr::Const(c.slots[j]));
                proof {
                    assert(out@ =~= lits(c.slots@.take(j + 1)));
                }
                j += 1;
            }
            let t = to_xtype(&c.ty);
            proof {
                lemma_lits(c.slots@, arbitrary(), Seq::empty());
                assert(c.slots@.take(c.slots@.len() as int) =~= c.slots@);
                assert(all_pure(out@, _blk.depth_s()));
                lemma_xwidth_of(sty(c.ty), enums@);
                if pre {
                    assert(ok_s(sty(cx.consts@[*i as int].ty), enums@));
                }
            }
            proof {
                assert(c.slots@.take(c.slots@.len() as int) =~= c.slots@);
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.consts[*i as int];
                    assert(member(v, sty(c.ty), enums@) && c.slots@ == enc(v, sty(c.ty), enums@));
                    lemma_lits(c.slots@, env, ls);
                    lemma_models_enc(v, sty(c.ty), enums@);
                }
            }
            Ok((t, out))
        },
        _ => Err(Fail::Type),
    }
}

/// リテラル、参照、スカラーの演算、短絡する演算、`let`。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_core(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const || e is Bin || e is Eq || e is Not || e is Fold || e is Implies || e is Ite || e is Let,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 2nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost sc0 = sc@;
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_) => {
            proof {
                lemma_extends_refl(*blk);
            }
            low_leaf(e, cx, sc, blk)
        },
        TExpr::Bin(op, a, b) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Int)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let y = sub_scalar(b, cx, sc, blk, &XType::Int)?;
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_pure_mono(x, b1.depth_s(), b2.depth_s());
                }
            }
            let ghost z = Expr::Bin(*op, Box::new(x), Box::new(y));
            let mut out: Vec<Expr> = Vec::new();
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    out.push(bind(blk, bin(*op, x, y))?);
                    proof {
                        if frag(*e) {
                            lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Int, out@);
                        }
                    }
                    Ok((XType::Int, out))
                },
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    out.push(bin(*op, x, y));
                    proof {
                        if pre {
                            assert(pure_below(out@[0], blk.depth_s()));
                        }
                    }
                    proof {
                        lemma_extends_refl(*blk);
                        if frag(*e) {
                            lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Bool, out@);
                        }
                    }
                    Ok((XType::Bool, out))
                },
                _ => Err(Fail::Type),
            }
        },
        TExpr::Eq(positive, a, b) => {
            let ghost b0 = *blk;
            let (tx, x) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (ty, y) = low(b, cx, sc, blk)?;
            proof {
                if pre {
                    lemma_all_pure_mono(x@, b1.depth_s(), blk.depth_s());
                }
            }
            if !xtype_eq(&ty, &tx) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, sctx(*cx), bound_tys(sc0)));
                    assert(here_ok(**a, sctx(*cx), bound_tys(sc0)));
                    assert(ok_x(xty(tx), cx.enums@));
                }
            }
            let c = need(eq_slots(&tx, &x, &y, enums))?;
            let ghost cg = c;
            let mut out: Vec<Expr> = Vec::new();
            out.push(
                if *positive {
                    c
                } else {
                    not(c)
                },
            );
            proof {
                if frag(*e) {
                    lemma_eq(*e, *cx, sc@, b0, b1, *blk, xty(tx), x@, y@, cg, out@);
                }
            }
            proof {
                if pre {
                    assert(all_pure(x@, blk.depth_s()) && all_pure(y@, blk.depth_s()));
                    assert(pure_below(cg, blk.depth_s()));
                    assert(pure_below(out@[0], blk.depth_s()));
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Not(a) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(not(x));
            proof {
                if pre {
                    assert(pure_below(out@[0], blk.depth_s()));
                }
            }
            proof {
                if frag(*e) {
                    lemma_not(*e, *cx, sc@, b0, *blk, x);
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Fold(_, _) => low_fold(e, cx, sc, blk),
        TExpr::Implies(a, b) => {
            let ghost b0 = *blk;
            let p = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let q = bool_in(b, cx, sc, depth(blk))?;
            let mut out: Vec<Expr> = Vec::new();
            let ghost z = Expr::Implies(Box::new(p), Box::new(q));
            out.push(bind(blk, Expr::Implies(Box::new(p), Box::new(q)))?);
            proof {
                if frag(*e) {
                    lemma_implies(*e, *cx, sc@, b0, b1, *blk, p, q);
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Ite(_, _, _) => low_ite(e, cx, sc, blk),
        TExpr::Let(a, b) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let ghost s0 = slots@;
            let slots = atoms(slots, blk)?;
            let ghost b2 = *blk;
            let ghost before = sc@;
            let ghost bound = Bound { ty: t, slots };
            sc.push(Bound { ty: t, slots });
            let ghost sc1 = sc@;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b2.depth_s(), cx.enums@);
                    assert(sc1 == sc0.push(bound));
                    assert(bound_tys(sc1) =~= bound_tys(sc0).push(xty(t)));
                    assert(sc_wf(sc1, b2.depth_s(), cx.enums@)) by {
                        assert forall|i: int| 0 <= i < sc1.len() implies ok_x(xty(#[trigger] sc1[i].ty), cx.enums@) && shaped(
                            sc1[i].slots@,
                            xty(sc1[i].ty),
                            b2.depth_s(),
                            cx.enums@,
                        ) by {
                            if i < sc0.len() {
                                assert(sc1[i] == sc0[i]);
                            } else {
                                assert(sc1[i] == bound);
                                assert(lim_ok(**a, sctx(*cx), bound_tys(sc0)));
                                assert(here_ok(**a, sctx(*cx), bound_tys(sc0)));
                            }
                        }
                    }
                }
            }
            let r = low(b, cx, sc, blk);
            if r.is_err() {
                return r;
            }
            sc.pop();
            proof {
                assert(sc@ =~= before);
                assert(sc1 == before.push(bound));
                if frag(*e) {
                    let (tb, out) = r->Ok_0;
                    lemma_let(*e, *cx, before, b0, b1, b2, *blk, s0, bound, xty(tb), out@);
                }
            }
            r
        },
        _ => Err(Fail::Type),
    }
}

/// `all` と `any`。先頭の項はスロットにし、残りの項は単独に評価する式にして、短絡する木にたたむ。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_fold(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Fold,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let (all, es) = match e {
        TExpr::Fold(all, es) => (*all, es),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    proof {
        assert(decreases_to!(*e => *es));
    }
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    proof {
        lemma_all_typed_bool(es@, c, bt);
        lemma_all_typed_iff(es@, XTy::Bool, c, bt);
        if pre {
            assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                lemma_lim_ok_seq_at(es@, c, bt, j);
            }
        }
    }
    let mut out: Vec<Expr> = Vec::new();
    if es.len() == 0 {
        proof {
            lemma_extends_refl(*blk);
        }
        out.push(cb(all));
        proof {
            if frag(*e) {
                lemma_fold_empty(*e, *cx, sc@, *blk, out@);
            }
        }
        return Ok((XType::Bool, out));
    }
    proof {
        vstd::std_specs::vec::axiom_vec_index_decreases(*es, 0);
        if pre {
            assert(type_of(es@[0], c, bt) == Some(XTy::Bool));
            assert(lim_ok(es@[0], c, bt));
        }
    }
    let x = sub_scalar(&es[0], cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let d = depth(blk);
    let mut terms: Vec<Expr> = Vec::new();
    terms.push(x);
    let ghost sc0 = sc@;
    proof {
        if pre {
            lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
    }
    let mut i = 1;
    while i < es.len()
        invariant
            decreases_to!(*e => *es),
            *e == TExpr::Fold(all, *es),
            1 <= i <= es@.len(),
            sc@ == sc0,
            *blk == b1,
            b0 == *old(blk),
            extends(b0, b1),
            d == b1.depth_s(),
            frag(es@[0]) ==> lowers(es@[0], *cx, sc0, b0, b1, XTy::Bool, seq![x]),
            terms@.len() == i,
            terms@[0] == x,
            pre == tpre(*e, *cx, sc0, b0.depth_s()),
            sc0 == old(sc)@,
            c == sctx(*cx),
            bt == bound_tys(sc0),
            pre ==> sc_wf(sc0, d as nat, cx.enums@) && cx_wf(*cx),
            pre ==> forall|j: int| 0 <= j < es@.len() ==> type_of(#[trigger] es@[j], c, bt) == Some(XTy::Bool) && lim_ok(
                es@[j],
                c,
                bt,
            ),
            frag(*e) ==> forall|j: int|
                1 <= j < i ==> #[trigger] closed_lowers(es@[j], *cx, sc0, d as nat, XTy::Bool, terms@[j]),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            if pre {
                assert(type_of(es@[i as int], c, bt) == Some(XTy::Bool));
                assert(lim_ok(es@[i as int], c, bt));
                assert(sc_wf(sc@, d as nat, cx.enums@));
                assert(tpre(es@[i as int], *cx, sc@, d as nat));
            }
        }
        let q = bool_in(&es[i], cx, sc, d)?;
        let ghost t0 = terms@;
        terms.push(q);
        proof {
            if frag(*e) {
                lemma_frag_seq(es@, i as int);
                assert forall|j: int| 1 <= j < i + 1 implies #[trigger] closed_lowers(
                    es@[j],
                    *cx,
                    sc0,
                    d as nat,
                    XTy::Bool,
                    terms@[j],
                ) by {
                    if j < i {
                        assert(terms@[j] == t0[j]);
                    }
                }
            }
        }
        i += 1;
    }
    let joined = tree(&terms, cb(all), if all { Join::RawAnd } else { Join::RawOr });
    out.push(bind(blk, joined)?);
    proof {
        if frag(*e) {
            lemma_frag_seq(es@, 0);
            lemma_fold(*e, *cx, sc0, b0, b1, *blk, terms@);
        }
    }
    Ok((XType::Bool, out))
}

/// 条件式のスロット。枝のスロットが局所変数 `n` 個のもとで純粋でなければ `None`。
fn ite_slots(c: &Expr, xs: &Vec<Expr>, ys: &Vec<Expr>, n: usize) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(out) ==> xs@.len() == ys@.len() && out@.len() == xs@.len() && (forall|i: int|
            0 <= i < out@.len() ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i])) && (forall|i: int|
            0 <= i < xs@.len() ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat)),
        xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat) ==> r is Some,
{
    let ghost pre = xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat);
    if xs.len() != ys.len() {
        return None;
    }
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < xs.len()
        invariant
            xs@.len() == ys@.len(),
            j <= xs@.len(),
            out@.len() == j,
            forall|i: int| 0 <= i < j ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i]),
            forall|i: int| 0 <= i < j ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat),
            pre == (xs@.len() == ys@.len() && all_pure(xs@, n as nat) && all_pure(ys@, n as nat)),
        decreases xs.len() - j,
    {
        proof {
            if pre {
                assert(pure_below(xs@[j as int], n as nat));
                assert(pure_below(ys@[j as int], n as nat));
            }
        }
        if !pure_exec(&xs[j], n) || !pure_exec(&ys[j], n) {
            return None;
        }
        let ghost px = pure_below(xs@[j as int], n as nat) && pure_below(ys@[j as int], n as nat);
        out.push(ite(copy_expr(c), copy_expr(&xs[j]), copy_expr(&ys[j])));
        proof {
            assert(px);
            assert forall|i: int| 0 <= i < j + 1 implies pure_below(#[trigger] xs@[i], n as nat) && pure_below(
                ys@[i],
                n as nat,
            ) by {}
        }
        j += 1;
    }
    Some(out)
}

/// 束縛を持つ `ite` の枝を、最後のスロットを束縛する深さで一度だけ単独に評価する式に下ろす。
/// スロット `j` ごとに、足りない深さを空の `let` で埋めて、`j` 番目のスロットを選ぶ式を束縛する。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_ite_slots(
    _parent: &TExpr,
    a: &TExpr,
    b: &TExpr,
    c: &Expr,
    tx: &XType,
    w: usize,
    cx: &LowerCtx,
    sc: &mut Vec<Bound>,
    blk: &mut Block,
) -> (r: Result<(Vec<Expr>, Ghost<Seq<Seq<Expr>>>, Ghost<Seq<Seq<Expr>>>), Fail>)
    requires
        old(blk).wf(),
        w > 0,
        decreases_to!(*_parent => *a),
        decreases_to!(*_parent => *b),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((out, fa, fb)) ==> {
            let d = old(blk).depth_s();
            &&& final(blk).binds@ == old(blk).binds@ + ite_binds(*c, fa@, fb@, w as nat)
            &&& fa@.len() == w
            &&& fb@.len() == w
            &&& out@ == Seq::new(w as nat, |i: int| Expr::Local((d + i) as usize))
            &&& frag(*a) ==> forall|i: int|
                0 <= i < w ==> #[trigger] closed_slots(*a, *cx, old(sc)@, (d + i) as nat, xty(*tx), fa@[i])
            &&& frag(*b) ==> forall|i: int|
                0 <= i < w ==> #[trigger] closed_slots(*b, *cx, old(sc)@, (d + i) as nat, xty(*tx), fb@[i])
            &&& forall|i: int| 0 <= i < w ==> i < (#[trigger] fa@[i]).len() && i < fb@[i].len()
        },
        tpre(*a, *cx, old(sc)@, old(blk).depth_s()) && tpre(*b, *cx, old(sc)@, old(blk).depth_s()) && type_of(
            *a,
            sctx(*cx),
            bound_tys(old(sc)@),
        ) == Some(xty(*tx)) && type_of(*b, sctx(*cx), bound_tys(old(sc)@)) == Some(xty(*tx)) && w == xwidth(
            xty(*tx),
            cx.enums@,
        ) ==> deep(r),
    decreases _parent, 0nat,
{
    let ghost b2 = *blk;
    let ghost sc0 = sc@;
    let d = depth(blk);
    let ghost pre = tpre(*a, *cx, sc0, d as nat) && tpre(*b, *cx, sc0, d as nat) && type_of(*a, sctx(*cx), bound_tys(sc0))
        == Some(xty(*tx)) && type_of(*b, sctx(*cx), bound_tys(sc0)) == Some(xty(*tx)) && w == xwidth(xty(*tx), cx.enums@);
    proof {
        lemma_extends_refl(*blk);
    }
    if w - 1 >= usize::MAX - d {
        return Err(Fail::Depth);
    }
    let top = d + (w - 1);
    proof {
        if pre {
            lemma_sc_wf_mono(sc0, d as nat, top as nat, cx.enums@);
        }
    }
    // 各枝を、最後のスロットを束縛する深さ `top` で一度だけ下ろす。
    // スロット `j` は深さ `d + j` で束縛するので、足りない `w - 1 - j` 個の深さを空の `let` で埋めてから評価する。
    let (ta, xa) = closed_in(a, cx, sc, top)?;
    let (tb, yb) = closed_in(b, cx, sc, top)?;
    if !xtype_eq(&ta, tx) || !xtype_eq(&tb, tx) || xa.len() != w || yb.len() != w {
        return Err(Fail::Type);
    }
    let ghost mut fa: Seq<Seq<Expr>> = Seq::empty();
    let ghost mut fb: Seq<Seq<Expr>> = Seq::empty();
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < w
        invariant
            sc@ == sc0,
            j <= w,
            w == xa@.len(),
            w == yb@.len(),
            top == d + w - 1,
            b2.wf(),
            d == b2.depth_s(),
            b2 == *old(blk),
            extends(b2, *blk),
            blk.base == b2.base,
            blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, j as nat),
            fa.len() == j,
            fb.len() == j,
            out@ == Seq::new(j as nat, |i: int| Expr::Local((d + i) as usize)),
            frag(*a) ==> closed_slots(*a, *cx, sc0, top as nat, xty(*tx), xa@),
            frag(*b) ==> closed_slots(*b, *cx, sc0, top as nat, xty(*tx), yb@),
            frag(*a) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*a, *cx, sc0, (d + i) as nat, xty(*tx), fa[i]),
            frag(*b) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*b, *cx, sc0, (d + i) as nat, xty(*tx), fb[i]),
            forall|i: int| 0 <= i < fa.len() ==> i < (#[trigger] fa[i]).len(),
            forall|i: int| 0 <= i < fb.len() ==> i < (#[trigger] fb[i]).len(),
            sc0 == old(sc)@,
        decreases w - j,
    {
        let k = w - 1 - j;
        let ghost bj = *blk;
        let o = bind(blk, ite(copy_expr(c), pad_lets(k, copy_expr(&xa[j])), pad_lets(k, copy_expr(&yb[j]))))?;
        out.push(o);
        proof {
            lemma_extends_trans(b2, bj, *blk);
            let fa0 = fa;
            let fb0 = fb;
            let pa = pad_lets_seq(xa@, k as nat);
            let pb = pad_lets_seq(yb@, k as nat);
            assert(pa[j as int] == pad_lets_s(k as nat, xa@[j as int]));
            assert(pb[j as int] == pad_lets_s(k as nat, yb@[j as int]));
            fa = fa.push(pa);
            fb = fb.push(pb);
            lemma_ite_binds_push(*c, fa0, fb0, pa, pb, j as nat);
            assert(blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, (j + 1) as nat));
            assert(out@ =~= Seq::new((j + 1) as nat, |i: int| Expr::Local((d + i) as usize)));
            assert(fa[j as int] == pa && fb[j as int] == pb);
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fa[i]).len() by {
                if i < j {
                    assert(fa[i] == fa0[i]);
                } else {
                    assert(fa[i] == pa);
                }
            }
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fb[i]).len() by {
                if i < j {
                    assert(fb[i] == fb0[i]);
                } else {
                    assert(fb[i] == pb);
                }
            }
            if frag(*a) {
                lemma_pads_closed(*a, *cx, sc0, top as nat, (d + j) as nat, k as nat, xty(*tx), xa@);
                assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                    *a,
                    *cx,
                    sc0,
                    (d + i) as nat,
                    xty(*tx),
                    fa[i],
                ) by {
                    if i < j {
                        assert(fa[i] == fa0[i]);
                    }
                }
            }
            if frag(*b) {
                lemma_pads_closed(*b, *cx, sc0, top as nat, (d + j) as nat, k as nat, xty(*tx), yb@);
                assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                    *b,
                    *cx,
                    sc0,
                    (d + i) as nat,
                    xty(*tx),
                    fb[i],
                ) by {
                    if i < j {
                        assert(fb[i] == fb0[i]);
                    }
                }
            }
        }
        j += 1;
    }
    proof {
        assert forall|i: int| 0 <= i < w implies i < (#[trigger] fa[i]).len() && i < fb[i].len() by {}
    }
    Ok((out, Ghost(fa), Ghost(fb)))
}

/// 条件式。条件を束縛する。枝が束縛を持たなければ、スロットごとに `ite` で選ぶ。
/// 束縛を持つなら、各枝を単独に評価する式に一度だけ下ろし、スロットごとに、その位置の深さで評価できるように
/// 空の `let` で深さを合わせて束縛する（[`low_ite_slots`]）。
/// 中核の `ite` は2つの枝が同じ型でなければならないので、枝の束縛を条件で守って並べることはしない。
#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
fn low_ite(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Ite,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let (p, a, b) = match e {
        TExpr::Ite(p, a, b) => (p, a, b),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost scs = sc@;
    proof {
        if pre {
            lemma_ite_tpre(*e, *cx, scs, b0.depth_s(), b0.depth_s());
        }
    }
    let c0 = sub_scalar(p, cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let c = atom(blk, c0)?;
    let ghost b2 = *blk;
    proof {
        if pre {
            lemma_sc_wf_mono(scs, b0.depth_s(), b2.depth_s(), cx.enums@);
            lemma_pure_mono(c0, b1.depth_s(), b2.depth_s());
        }
    }
    let d = depth(blk);
    proof {
        lemma_extends_trans(b0, b1, b2);
        if pre {
            lemma_ite_tpre(*e, *cx, scs, b0.depth_s(), d as nat);
        }
    }
    let mut ba = new_block(d)?;
    let ghost ba0 = ba;
    let (tx, xs) = low(a, cx, sc, &mut ba)?;
    let mut bb = new_block(d)?;
    let ghost bb0 = bb;
    let (ty, ys) = low(b, cx, sc, &mut bb)?;
    if !xtype_eq(&ty, &tx) {
        return Err(Fail::Type);
    }
    proof {
        if pre {
            assert(here_ok(**a, sctx(*cx), bound_tys(scs)));
            assert(shaped(xs@, xty(tx), ba.depth_s(), cx.enums@));
            assert(shaped(ys@, xty(ty), bb.depth_s(), cx.enums@));
            lemma_xwidth_pos(xty(tx), cx.enums@);
        }
    }
    if ba.binds.len() == 0 && bb.binds.len() == 0 {
        proof {
            assert(ba.depth_s() == d && bb.depth_s() == d);
        }
        let out = need(ite_slots(&c, &xs, &ys, d))?;
        proof {
            if pre {
                assert(pure_below(c, d as nat));
                lemma_ite_out_pure(c, xs@, ys@, out@, d as nat);
            }
        }
        proof {
            lemma_extends_refl(*blk);
            if frag(*e) {
                lemma_ite_simple(*e, *cx, sc@, b0, b1, b2, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, out@);
            }
        }
        return Ok((tx, out));
    }
    if xs.len() == 0 || xs.len() != ys.len() {
        return Err(Fail::Type);
    }
    let w = xs.len();
    let ghost sc0 = sc@;
    proof {
        lemma_extends_trans(b0, b1, b2);
        assert(decreases_to!(*e => **a));
        assert(decreases_to!(*e => **b));
        if pre {
            assert(tpre(**a, *cx, scs, d as nat) && tpre(**b, *cx, scs, d as nat));
            assert(type_of(**a, sctx(*cx), bound_tys(scs)) == Some(xty(tx)));
            assert(w == xwidth(xty(tx), cx.enums@));
        }
    }
    let (out, Ghost(fa), Ghost(fb)) = low_ite_slots(e, a, b, &c, &tx, w, cx, sc, blk)?;
    proof {
        lemma_extends_trans(b0, b2, *blk);
    }
    proof {
        if frag(*e) {
            lemma_ite_bound(*e, *cx, sc0, b0, b1, b2, *blk, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, fa, fb, out@);
        }
        if pre {
            assert(all_pure(out@, blk.depth_s())) by {
                assert forall|i: int| 0 <= i < out@.len() implies pure_below(#[trigger] out@[i], blk.depth_s()) by {
                    assert(out@[i] == Expr::Local((d + i) as usize));
                }
            }
        }
    }
    Ok((tx, out))
}

fn pad_lets(k: usize, x: Expr) -> (r: Expr)
    ensures
        r == pad_lets_s(k as nat, x),
    decreases k,
{
    if k == 0 {
        x
    } else {
        Expr::Let(Box::new(Expr::Const(Value::Bool(true))), Box::new(pad_lets(k - 1, x)))
    }
}

/// 量化、Tuple、Record、Option。
fn low_struct(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Tuple || e is Record || e is Nth || e is Field || e is None || e is Some || e is IsSome || e is IsNone || e is Unwrap,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    match e {
        TExpr::Tuple(_) | TExpr::Record(_, _) => low_tuple(e, cx, sc, blk),
        TExpr::Nth(_, _) | TExpr::Field(_, _, _) => low_proj(e, cx, sc, blk),
        _ => low_opt(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_tuple(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Tuple || e is Record,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::Tuple(es) | TExpr::Record(_, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            if es.len() == 0 {
                return Err(Fail::Type);
            }
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            proof {
                lemma_types_of_iff(es@, c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
                lemma_xtys(Seq::<XType>::empty());
            }
            proof {
                lemma_extends_refl(*blk);
                lemma_seq_base(*cx, sc0, b0);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
            }
            let mut ts: Vec<XType> = Vec::new();
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= es@.len(),
                    ts@.len() == i,
                    (e is Tuple || e is Record) && (e is Tuple ==> e->Tuple_0 == *es) && (e is Record ==> e->Record_1 == *es),
                    frag(*e) ==> lowers_seq(es@.take(i as int), *cx, sc0, b0, *blk, xtys(ts@), out@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> type_of(#[trigger] es@[j], c, bt) is Some && lim_ok(
                        es@[j],
                        c,
                        bt,
                    ),
                    pre ==> types_of(es@.take(i as int), c, bt) == Some(xtys(ts@)),
                    pre ==> out@.len() == xwidth_sum(xtys(ts@), cx.enums@) && all_pure(out@, blk.depth_s()),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost o1 = out@;
                let ghost t1 = ts@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(type_of(es@[i as int], c, bt) is Some && lim_ok(es@[i as int], c, bt));
                    }
                }
                let (t, s) = low(&es[i], cx, sc, blk)?;
                let ghost tg = t;
                ts.push(t);
                append(&mut out, &s);
                proof {
                    assert(ts@.drop_last() == t1);
                    assert(xtys(ts@) == xtys(t1).push(xty(t)));
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    assert(es@.take(i + 1).last() == es@[i as int]);
                    if pre {
                        lemma_all_pure_mono(o1, b1.depth_s(), blk.depth_s());
                        assert(xtys(ts@).drop_last() == xtys(t1));
                        assert(all_pure(out@, blk.depth_s())) by {
                            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                                if j < o1.len() {
                                    assert(out@[j] == o1[j]);
                                } else {
                                    assert(out@[j] == s@[j - o1.len()]);
                                }
                            }
                        }
                    }
                }
                proof {
                    lemma_extends_trans(*old(blk), b1, *blk);
                    lemma_xtys(t1);
                    lemma_xtys(ts@);
                    assert(xtys(ts@) =~= xtys(t1).push(xty(tg)));
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    if frag(*e) {
                        lemma_frag_seq(es@, i as int);
                        lemma_seq_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, xtys(t1), o1, xty(tg), s@);
                    }
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
            }
            match e {
                TExpr::Record(names, _) => {
                    let nm = copy_usizes(names);
                    proof {
                        if frag(*e) {
                            lemma_tuple_done(*e, es@, *cx, sc0, b0, *blk, xtys(ts@), out@);
                        }
                    }
                    Ok((XType::Record(nm, ts), out))
                },
                _ => {
                    proof {
                        if frag(*e) {
                            lemma_tuple_done(*e, es@, *cx, sc0, b0, *blk, xtys(ts@), out@);
                        }
                    }
                    Ok((XType::Tuple(ts), out))
                },
            }
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_proj(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Nth || e is Field,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::Nth(a, i) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Tuple(ts) => {
                    proof {
                        lemma_xtys(ts@);
                        if pre {
                            assert(lim_ok(**a, c, bt));
                            assert(here_ok(**a, c, bt));
                        }
                    }
                    let parts = need(split(&ts, &slots, enums))?;
                    if *i < ts.len() && *i < parts.len() {
                        let x = copy_exprs(&parts[*i]);
                        let u = copy_xtype(&ts[*i]);
                        proof {
                            if pre {
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                let o = xoff(xtys(ts@), *i as int, enums@);
                                assert(all_pure(x@, blk.depth_s())) by {
                                    assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                                        assert(x@[j] == slots@[o + j]);
                                    }
                                }
                            }
                        }
                        proof {
                            if frag(*e) {
                                lemma_xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                lemma_part(*e, **a, *i, *cx, sc@, b0, *blk, xtys(ts@), slots@, x@);
                            }
                        }
                        Ok((u, x))
                    } else {
                        Err(Fail::Type)
                    }
                },
                _ => Err(Fail::Type),
            }
        },
        TExpr::Field(a, name, i) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Record(names, ts) => {
                    proof {
                        lemma_xtys(ts@);
                        if pre {
                            assert(lim_ok(**a, c, bt));
                            assert(here_ok(**a, c, bt));
                        }
                    }
                    let parts = need(split(&ts, &slots, enums))?;
                    if *i < ts.len() && *i < parts.len() && *i < names.len() && names[*i] == *name {
                        let x = copy_exprs(&parts[*i]);
                        let u = copy_xtype(&ts[*i]);
                        proof {
                            if pre {
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                let o = xoff(xtys(ts@), *i as int, enums@);
                                assert(all_pure(x@, blk.depth_s())) by {
                                    assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                                        assert(x@[j] == slots@[o + j]);
                                    }
                                }
                            }
                        }
                        proof {
                            if frag(*e) {
                                lemma_xtys(ts@);
                                assert(split_ok(parts@[*i as int]@, slots@, xtys(ts@), *i as int, enums@));
                                lemma_part(*e, **a, *i, *cx, sc@, b0, *blk, xtys(ts@), slots@, x@);
                            }
                        }
                        Ok((u, x))
                    } else {
                        Err(Fail::Type)
                    }
                },
                _ => Err(Fail::Type),
            }
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_opt(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is None || e is Some || e is IsSome || e is IsNone || e is Unwrap,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::None(t) => {
            proof {
                lemma_extends_refl(*blk);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(false));
            let ds = defaults(t, enums);
            append(&mut out, &ds);
            let u = to_xtype(t);
            proof {
                lemma_default_len(sty(*t), enums@);
                lemma_xwidth_of(sty(*t), enums@);
                lemma_lits(enc(default_val(sty(*t), enums@), sty(*t), enums@), arbitrary(), Seq::empty());
                if pre {
                    assert(all_pure(out@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(out@[j] == ds@[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                lemma_none(*e, sty(*t), *cx, sc@, *blk, out@);
            }
            Ok((XType::Option(Box::new(u)), out))
        },
        TExpr::Some(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(true));
            append(&mut out, &s);
            proof {
                if pre {
                    assert(all_pure(out@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(out@[j] == s@[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                if frag(*e) {
                    lemma_some(*e, **a, *cx, sc@, b0, *blk, xty(t), s@, out@);
                }
            }
            Ok((XType::Option(Box::new(t)), out))
        },
        TExpr::IsSome(a) | TExpr::IsNone(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let ghost xt = xty(t);
            match t {
                XType::Option(_) => {},
                _ => return Err(Fail::Type),
            }
            if s.len() == 0 {
                return Err(Fail::Type);
            }
            let tag = copy_expr(&s[0]);
            let mut out: Vec<Expr> = Vec::new();
            match e {
                TExpr::IsSome(_) => out.push(tag),
                _ => out.push(not(tag)),
            }
            proof {
                if pre {
                    assert(pure_below(s@[0], blk.depth_s()));
                    assert(pure_below(out@[0], blk.depth_s()));
                }
            }
            proof {
                if frag(*e) {
                    lemma_is_some(*e, **a, *cx, sc@, b0, *blk, xt, s@, out@);
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Unwrap(a) => {
            let ghost b0 = *blk;
            let (t, s) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let inner = match t {
                XType::Option(x) => *x,
                _ => return Err(Fail::Type),
            };
            if s.len() == 0 {
                return Err(Fail::Type);
            }
            check(blk, copy_expr(&s[0]), FAIL_NONE)?;
            let x = sub_exprs(&s, 1, s.len());
            proof {
                if pre {
                    lemma_all_pure_mono(s@, b1.depth_s(), blk.depth_s());
                    assert(all_pure(x@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < x@.len() implies pure_below(#[trigger] x@[j], blk.depth_s()) by {
                            assert(x@[j] == s@[j + 1]);
                        }
                    }
                }
            }
            proof {
                lemma_extends_trans(b0, b1, *blk);
                if frag(*e) {
                    lemma_unwrap(*e, **a, *cx, sc@, b0, b1, *blk, xty(inner), s@, x@);
                }
            }
            Ok((inner, x))
        },
        _ => Err(Fail::Type),
    }
}

/// `forall` と `exists`。型の全体、Set の要素、Map のキー、List の要素をたどる。
///
/// 位置を1つの整数の局所変数でたどる。型の全体、Set、Mapでは位置は値の正規順での番号で、
/// 束縛する値のスロットは番号から作る（[`unrank`]）。Listでは位置は添字で、スロットは
/// その位置の要素のスロットを選ぶ。位置が対象に含まれるかは、ガードで表す。
/// 量化でたどる値の型、位置が対象に含まれるかのガード、位置の数、束縛する値のスロットを求める。
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
fn quant_over(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<
    (SType, Expr, usize, Vec<Expr>),
    Fail,
>)
    requires
        old(blk).wf(),
        e is Quant,
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((st, g, n, us)) ==> n <= 0x7fff_ffff && (frag(*e) ==> over_ok(
            e->Quant_1,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            g,
            n as nat,
            us@,
            to_xty(sty(st)),
        )),
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> deep(r) && (r matches Ok((st, g, n, us)) ==> Some(
            to_xty(sty(st)),
        ) == quant_bound(e->Quant_1, sctx(*cx), bound_tys(old(sc)@)) && ok_s(sty(st), cx.enums@) && us@.len() == width(
            sty(st),
            cx.enums@,
        ) && all_pure(us@, final(blk).depth_s() + 1) && pure_below(g, final(blk).depth_s() + 1)),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let enums = &cx.enums;
    let over = match e {
        TExpr::Quant(_, over, _) => over,
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    proof {
        lemma_extends_refl(*blk);
        if pre {
            assert(lim_ok(*e, c, bt));
            assert(quant_bound(*over, c, bt) is Some);
        }
    }
    match over {
        Over::Type(t) => {
            let n = need(keys_exec(t, enums))?;
            proof {
                if pre {
                    assert(n <= crate::encoding::MAX_KEYS);
                }
            }
            if n > 0x7fff_ffff {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                lemma_extends_refl(*blk);
                lemma_over_type(*over, *cx, sc@, *blk, n as nat, us@);
            }
            Ok((copy_stype(t), cb(true), n as usize, us))
        },
        Over::Set(t, s) => {
            proof {
                if pre {
                    assert(lim_ok(**s, c, bt));
                }
            }
            let (ty, cs) = low(s, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**s, c, bt));
                    assert(n_ok_set(xty(ty), sty(*t), cx.enums@));
                }
            }
            let u = match ty {
                XType::Set(u) => u,
                _ => return Err(Fail::Type),
            };
            let n = need(keys_exec(t, enums))?;
            if !stype_eq(&u, t) || n > 0x7fff_ffff || cs.len() != n as usize {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let g = pick_slot(&cs, &Expr::Local(d));
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    lemma_all_pure_mono(cs@, d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                if frag(*e) {
                    lemma_over_set(*over, *t, **s, *cx, sc@, b0, *blk, cs@, g, n as nat, us@);
                }
            }
            Ok((copy_stype(t), g, n as usize, us))
        },
        Over::Map(t, m) => {
            proof {
                if pre {
                    assert(lim_ok(**m, c, bt));
                }
            }
            let (ty, cs) = low(m, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**m, c, bt));
                }
            }
            let (kt, vt) = match ty {
                XType::Map(k, v) => (k, v),
                _ => return Err(Fail::Type),
            };
            let n = need(keys_exec(t, enums))?;
            if !stype_eq(&kt, t) || n > 0x7fff_ffff {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_s(sty(*vt), enums@));
                    assert(n <= crate::encoding::MAX_KEYS);
                }
            }
            let w = need(stype_width(&vt, enums))?;
            proof {
                assert(usize::MAX >= 0xffff_ffff);
            }
            let stride = need(w.checked_add(1))?;
            let ghost b1 = *blk;
            let mut fs: Vec<Expr> = Vec::new();
            let mut j: usize = 0;
            while j < n as usize
                invariant
                    n <= 0x7fff_ffff,
                    j <= n,
                    fs@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] fs@[q] == cs@[q * stride],
                    extends(*old(blk), *blk),
                    *blk == b1,
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> cs@.len() == n * stride && all_pure(cs@, b1.depth_s()) && stride == w + 1,
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
                let at = need(j.checked_mul(stride))?;
                if at >= cs.len() {
                    return Err(Fail::Type);
                }
                let ghost f0 = fs@;
                fs.push(copy_expr(&cs[at]));
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
            let d = depth(blk);
            need(d.checked_add(1))?;
            let g = pick_slot(&fs, &Expr::Local(d));
            let us = need(unrank(t, &Expr::Local(d), enums))?;
            proof {
                if pre {
                    lemma_all_pure_mono(fs@, d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(unrank_ok(sty(*t), Expr::Local(d), us@, enums@));
                    assert(all_pure(us@, (d + 1) as nat));
                }
            }
            proof {
                if frag(*e) {
                    lemma_over_map(*over, *t, **m, *cx, sc@, b0, *blk, sty(*vt), stride as int, cs@, fs@, g, n as nat, us@);
                }
            }
            Ok((copy_stype(t), g, n as usize, us))
        },
        Over::List(li) => {
            proof {
                if pre {
                    assert(lim_ok(**li, c, bt));
                }
            }
            let (ty, cs) = low(li, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**li, c, bt));
                }
            }
            let (u, max) = match ty {
                XType::List(u, max) => (u, max),
                _ => return Err(Fail::Type),
            };
            proof {
                if pre {
                    assert(lim_s(sty(*u), enums@));
                }
            }
            let w = need(stype_width(&u, enums))?;
            if max > 0x7fff_ffff || cs.len() == 0 {
                return Err(Fail::Type);
            }
            let d = depth(blk);
            need(d.checked_add(1))?;
            let ghost b1 = *blk;
            let mut us: Vec<Expr> = Vec::new();
            let mut j: usize = 0;
            while j < w
                invariant
                    max <= 0x7fff_ffff,
                    j <= w,
                    us@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] picks(us@[q], list_col(cs@, w as int, max as nat, q), Expr::Local(d)),
                    extends(*old(blk), *blk),
                    *blk == b1,
                    d == b1.depth_s(),
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> cs@.len() == 1 + max * w && all_pure(cs@, d as nat) && cs@.len() <= 0x7fff_ffff,
                    pre ==> all_pure(us@, (d + 1) as nat),
                decreases w - j,
            {
                let mut col: Vec<Expr> = Vec::new();
                let mut k: usize = 0;
                while k < max
                    invariant
                        max <= 0x7fff_ffff,
                        k <= max,
                        j < w,
                        col@ =~= Seq::new(k as nat, |q: int| cs@[1 + q * w + j]),
                        extends(*old(blk), *blk),
                        *blk == b1,
                        d == b1.depth_s(),
                        pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                        pre ==> cs@.len() == 1 + max * w && all_pure(cs@, d as nat) && cs@.len() <= 0x7fff_ffff,
                        pre ==> all_pure(col@, d as nat),
                    decreases max - k,
                {
                    proof {
                        assert(k * w + w <= max * w) by (nonlinear_arith)
                            requires
                                k < max,
                        ;
                        assert(usize::MAX >= 0xffff_ffff);
                    }
                    let at = need(need(need(k.checked_mul(w))?.checked_add(1))?.checked_add(j))?;
                    if at >= cs.len() {
                        return Err(Fail::Type);
                    }
                    let ghost c0 = col@;
                    col.push(copy_expr(&cs[at]));
                    proof {
                        assert(col@ =~= Seq::new((k + 1) as nat, |q: int| cs@[1 + q * w + j]));
                        if pre {
                            assert forall|q: int| 0 <= q < col@.len() implies pure_below(#[trigger] col@[q], d as nat) by {
                                if q < c0.len() {
                                    assert(col@[q] == c0[q]);
                                }
                            }
                        }
                    }
                    k += 1;
                }
                proof {
                    assert(col@ =~= list_col(cs@, w as int, max as nat, j as int));
                }
                let ghost u0 = us@;
                let pk = pick_slot(&col, &Expr::Local(d));
                proof {
                    if pre {
                        lemma_all_pure_mono(col@, d as nat, (d + 1) as nat);
                        assert(pure_below(Expr::Local(d), (d + 1) as nat));
                        assert(pure_below(pk, (d + 1) as nat));
                    }
                }
                us.push(pk);
                proof {
                    if pre {
                        assert forall|q: int| 0 <= q < us@.len() implies pure_below(#[trigger] us@[q], (d + 1) as nat) by {
                            if q < u0.len() {
                                assert(us@[q] == u0[q]);
                            }
                        }
                    }
                }
                j += 1;
            }
            let g = bin(BinOp::Lt, Expr::Local(d), copy_expr(&cs[0]));
            proof {
                if pre {
                    assert(pure_below(cs@[0], d as nat));
                    lemma_pure_mono(cs@[0], d as nat, (d + 1) as nat);
                    assert(pure_below(Expr::Local(d), (d + 1) as nat));
                    assert(pure_below(g, (d + 1) as nat));
                }
            }
            proof {
                if frag(*e) {
                    lemma_over_list(*over, **li, *cx, sc@, b0, *blk, sty(*u), max as nat, w as int, cs@, us@, g);
                }
            }
            Ok((copy_stype(&u), g, max, us))
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_quant(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Quant,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let (all, _over, body) = match e {
        TExpr::Quant(all, over, body) => (*all, over, body),
        _ => return Err(Fail::Type),
    };
    let ghost b0 = *blk;
    let ghost before = sc@;
    // たどる値の型、位置が対象に含まれるかのガード、位置の数、束縛する値のスロット。
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let (st, g, n, us) = quant_over(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    let d = depth(blk);
    let top = need(d.checked_add(1))?;
    let bd = Bound { ty: to_xtype(&st), slots: us };
    let ghost bg = bd;
    sc.push(bd);
    proof {
        if pre {
            let sc1 = sc@;
            assert(sc1 == before.push(bg));
            lemma_ok_to_x(sty(st), cx.enums@);
            lemma_xwidth_of(sty(st), cx.enums@);
            lemma_sc_wf_mono(before, b0.depth_s(), top as nat, cx.enums@);
            assert(bound_tys(sc1) =~= bt.push(to_xty(sty(st))));
            assert(sc_wf(sc1, top as nat, cx.enums@)) by {
                assert forall|i: int| 0 <= i < sc1.len() implies ok_x(xty(#[trigger] sc1[i].ty), cx.enums@) && shaped(
                    sc1[i].slots@,
                    xty(sc1[i].ty),
                    top as nat,
                    cx.enums@,
                ) by {
                    if i < before.len() {
                        assert(sc1[i] == before[i]);
                    } else {
                        assert(sc1[i] == bg);
                    }
                }
            }
            assert(lim_ok(*e, c, bt));
            assert(type_of(**body, c, bt.push(to_xty(sty(st)))) == Some(XTy::Bool));
            assert(lim_ok(**body, c, bt.push(to_xty(sty(st)))));
        }
    }
    let b = bool_in(body, cx, sc, top)?;
    sc.pop();
    proof {
        assert(sc@ =~= before);
    }
    let qb = combine(all, g, b);
    let hi = n as i64 - 1;
    let top_code = if n == 0 {
        0i64
    } else {
        hi
    };
    let q = quant(all, Type::Int(0, top_code), 0, hi, qb);
    let z = bind(blk, q)?;
    let mut out: Vec<Expr> = Vec::new();
    out.push(z);
    proof {
        if pre {
            assert(pure_below(out@[0], blk.depth_s()));
        }
    }
    proof {
        if frag(*e) {
            lemma_quant(*e, all, *_over, **body, *cx, before, b0, b1, *blk, n as nat, g, bg, b, qb, q);
        }
    }
    Ok((XType::Bool, out))
}

/// 量化の本体と、値が対象に含まれる条件を組み合わせる。
fn combine(all: bool, guard: Expr, e: Expr) -> (r: Expr)
    ensures
        combine_ok(all, guard, e, r),
{
    if is_bool_lit(&guard, true) {
        proof {
            assert forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(e, env, l)) == match as_bool(eval_l(guard, env, l)) {
                Err(k) => Err(k),
                Ok(true) => as_bool(eval_l(e, env, l)),
                Ok(false) => Ok::<bool, ErrKind>(all),
            } by {
                assert(eval_l(guard, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
        }
        e
    } else if all {
        Expr::Implies(Box::new(guard), Box::new(e))
    } else {
        Expr::And(Box::new(guard), Box::new(e))
    }
}

fn quant(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> (r: Expr)
    ensures
        r == quant_s(all, ty, lo, hi, e),
{
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

/// Setのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_set_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is SetLit,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::SetLit(t, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            if keys_exec(t, enums).is_none() {
                return Err(Fail::Type);
            }
            let n = keys_or_zero_exec(t, enums);
            if n > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let mut bits: Vec<Expr> = Vec::new();
            let mut k = 0;
            while k < n
                invariant
                    k <= n,
                    bits@ =~= Seq::new(k as nat, |_j: int| bool_lit(false)),
                decreases n - k,
            {
                bits.push(cb(false));
                k += 1;
            }
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            proof {
                lemma_all_typed_iff(es@, to_xty(sty(*t)), c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
            }
            proof {
                lemma_setlit_base(*cx, sc0, b0, sty(*t), bits@);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
            }
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= es@.len(),
                    bits@.len() == n,
                    n <= 0x7fff_ffff,
                    e is SetLit && e->SetLit_1 == *es && e->SetLit_0 == *t,
                    frag(*e) ==> setlit_ok(es@.take(i as int), *cx, sc0, b0, *blk, sty(*t), bits@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> keys(sty(*t), enums@) is Some && n == keys_or_zero(sty(*t), enums@),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> type_of(#[trigger] es@[j], c, bt) == Some(to_xty(sty(*t)))
                        && lim_ok(es@[j], c, bt),
                    pre ==> all_pure(bits@, blk.depth_s()),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost bv = bits@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(type_of(es@[i as int], c, bt) == Some(to_xty(sty(*t))) && lim_ok(es@[i as int], c, bt));
                    }
                }
                let r = element_rank(&es[i], cx, sc, blk, t)?;
                let ghost bv2 = bits@;
                bits = mark(&bits, &r, true);
                proof {
                    if pre {
                        lemma_all_pure_mono(bv2, b1.depth_s(), blk.depth_s());
                        lemma_mark_pure(true, bv2, r, bits@, blk.depth_s());
                    }
                }
                proof {
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    if frag(*e) {
                        lemma_frag_seq(es@, i as int);
                        lemma_setlit_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, sty(*t), bv, r, bits@);
                    }
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
            }
            Ok((XType::Set(Box::new(copy_stype(t))), bits))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

/// Mapのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
fn low_map_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is MapLit,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::MapLit(k, v, items) => {
            proof {
                assert(decreases_to!(*e => *items));
                lemma_extends_refl(*blk);
            }
            if keys_exec(k, enums).is_none() {
                return Err(Fail::Type);
            }
            let map = SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v)));
            let mut slots = defaults(&map, enums);
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            let ghost kt = sty(*k);
            let ghost vt = sty(*v);
            proof {
                lemma_default_len(sty(map), enums@);
                lemma_lits(enc(default_val(sty(map), enums@), sty(map), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_items_ok_intro(items@, c, bt, kt, vt);
                    assert(here_ok(*e, c, bt));
                    assert(type_of(*e, c, bt) == Some(XTy::Map(Box::new(kt), Box::new(vt))));
                    lemma_ok_map(kt, vt, enums@);
                    assert(ok_s_o(STy::Map(Box::new(kt), Box::new(vt)), enums@)) by {
                        reveal(ok_s_o);
                    }
                }
            }
            proof {
                lemma_maplit_base(*cx, sc0, b0, kt, vt, slots@);
                assert(items@.take(0) =~= Seq::<Item>::empty());
            }
            let mut i = 0;
            while i < items.len()
                invariant
                    decreases_to!(*e => *items),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= items@.len(),
                    kt == sty(*k),
                    vt == sty(*v),
                    e is MapLit && e->MapLit_2 == *items,
                    frag(*e) ==> maplit_ok(items@.take(i as int), *cx, sc0, b0, *blk, kt, vt, slots@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> items_ok(items@, c, bt, kt, vt),
                    pre ==> ok_s_o(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
                    pre ==> slots@.len() == width(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@) && all_pure(
                        slots@,
                        blk.depth_s(),
                    ),
                decreases items.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*items, i as int);
                }
                let item = &items[i];
                proof {
                    assert(decreases_to!(*e => item.key));
                    assert(decreases_to!(*e => item.value));
                }
                let ghost b1 = *blk;
                let ghost s1 = slots@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        lemma_items_ok_at(items@, c, bt, kt, vt, i as int);
                        assert(tpre(item.key, *cx, sc@, blk.depth_s()));
                        assert(tpre(item.value, *cx, sc@, blk.depth_s()));
                        assert(type_of(item.key, sctx(*cx), bound_tys(sc@)) == Some(to_xty(kt)));
                        assert(type_of(item.value, sctx(*cx), bound_tys(sc@)) == Some(to_xty(vt)));
                        assert(slots@.len() == width(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@));
                        assert(all_pure(slots@, blk.depth_s()));
                        lemma_put_pre(item.key, item.value, *cx, sc@, blk.depth_s(), kt, vt, slots@);
                    }
                }
                slots = put(e, &slots, k, v, &item.key, &item.value, cx, sc, blk)?;
                proof {
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(items@.take(i + 1).drop_last() =~= items@.take(i as int));
                    if pre {
                        lemma_xwidth_of(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@);
                    }
                    if frag(*e) {
                        lemma_frag_items(items@, i as int);
                        lemma_maplit_step(items@.take(i + 1), *cx, sc0, b0, b1, *blk, kt, vt, s1, slots@);
                    }
                }
                i += 1;
            }
            proof {
                assert(items@.take(items@.len() as int) =~= items@);
            }
            Ok((to_xtype(&map), slots))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

/// Listのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_list_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is ListLit,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    match e {
        TExpr::ListLit(t, max, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            if es.len() > *max || es.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(ci(es.len() as i64));
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            let ghost st = sty(*t);
            let ghost n = es.len() as i64;
            proof {
                lemma_all_typed_iff(es@, to_xty(sty(*t)), c, bt);
                if pre {
                    assert forall|j: int| 0 <= j < es@.len() implies lim_ok(#[trigger] es@[j], c, bt) by {
                        lemma_lim_ok_seq_at(es@, c, bt, j);
                    }
                }
            }
            proof {
                lemma_listlit_base(*cx, sc0, b0, st, n, out@);
                assert(es@.take(0) =~= Seq::<TExpr>::empty());
            }
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= es@.len(),
                    st == sty(*t),
                    n == es.len() as i64,
                    e is ListLit && e->ListLit_2 == *es && e->ListLit_0 == *t,
                    frag(*e) ==> listlit_ok(es@.take(i as int), *cx, sc0, b0, *blk, st, n, out@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> forall|j: int| 0 <= j < es@.len() ==> type_of(#[trigger] es@[j], c, bt) == Some(to_xty(sty(*t)))
                        && lim_ok(es@[j], c, bt),
                    pre ==> out@.len() == 1 + i * width(st, cx.enums@) && all_pure(out@, blk.depth_s()),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let ghost b1 = *blk;
                let ghost o1 = out@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        assert(type_of(es@[i as int], c, bt) == Some(to_xty(sty(*t))) && lim_ok(es@[i as int], c, bt));
                    }
                }
                let x = element(&es[i], cx, sc, blk, t)?;
                append(&mut out, &x);
                proof {
                    if pre {
                        lemma_all_pure_mono(o1, b1.depth_s(), blk.depth_s());
                        assert(1 + i * width(st, cx.enums@) + width(st, cx.enums@) == 1 + (i + 1) * width(st, cx.enums@)) by (nonlinear_arith);
                        assert(all_pure(out@, blk.depth_s())) by {
                            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                                if j < o1.len() {
                                    assert(out@[j] == o1[j]);
                                } else {
                                    assert(out@[j] == x@[j - o1.len()]);
                                }
                            }
                        }
                    }
                }
                proof {
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
                    if frag(*e) {
                        lemma_frag_seq(es@, i as int);
                        lemma_listlit_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, st, n, o1, x@, out@);
                    }
                }
                i += 1;
            }
            proof {
                assert(es@.take(es@.len() as int) =~= es@);
            }
            let defs = defaults(t, enums);
            proof {
                lemma_default_len(st, enums@);
                lemma_xwidth_of(st, enums@);
            }
            let ghost o2 = out@;
            let ghost dv = enc(default_val(st, enums@), st, enums@);
            let ghost b2 = *blk;
            proof {
                assert(o2 =~= o2 + lits(enc_repeat(dv, 0)));
            }
            let mut p = es.len();
            while p < *max
                invariant
                    es.len() <= p <= *max,
                    defs@ == lits(dv),
                    out@ == o2 + lits(enc_repeat(dv, (p - es.len()) as nat)),
                    pre ==> out@.len() == 1 + p * width(st, cx.enums@) && all_pure(out@, blk.depth_s()),
                    dv.len() == width(st, cx.enums@),
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                decreases *max - p,
            {
                let ghost o3 = out@;
                append(&mut out, &defs);
                proof {
                    lemma_lits(dv, arbitrary(), Seq::empty());
                    if pre {
                        assert(1 + p * width(st, cx.enums@) + width(st, cx.enums@) == 1 + (p + 1) * width(st, cx.enums@)) by (nonlinear_arith);
                        assert(all_pure(out@, blk.depth_s())) by {
                            assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], blk.depth_s()) by {
                                if j < o3.len() {
                                    assert(out@[j] == o3[j]);
                                } else {
                                    assert(out@[j] == defs@[j - o3.len()]);
                                }
                            }
                        }
                    }
                }
                proof {
                    let k = (p - es.len()) as nat;
                    assert(enc_repeat(dv, (k + 1) as nat) == enc_repeat(dv, k) + dv);
                    assert(lits(enc_repeat(dv, k) + dv) =~= lits(enc_repeat(dv, k)) + lits(dv));
                    assert(out@ =~= o2 + lits(enc_repeat(dv, (k + 1) as nat)));
                }
                p += 1;
            }
            proof {
                if frag(*e) {
                    lemma_listlit_done(*e, *cx, sc0, b0, b2, st, *max, o2, dv, out@);
                }
            }
            Ok((XType::List(Box::new(copy_stype(t)), *max), out))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
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
#[verifier::rlimit(120)]
fn low_member(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is SetContains,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::SetContains(t, a, x) => {
            let ghost b0 = *blk;
            let (tc, cs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let elem = match tc {
                XType::Set(u) => *u,
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&elem, t) || cs.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    assert(wf_xtype(XTy::Set(Box::new(sty(elem))), cx.enums@));
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let r = lookup_rank(x, cx, sc, blk, &elem)?;
            let ghost rg = r;
            let hit = pick_slot(&cs, &r);
            let ghost hg = hit;
            let mut out: Vec<Expr> = Vec::new();
            out.push(and(bin(BinOp::Ge, r, ci(0)), hit));
            proof {
                if pre {
                    lemma_all_pure_mono(cs@, b1.depth_s(), blk.depth_s());
                    crate::quant::lemma_hit_pure(rg, cs@, hg, blk.depth_s());
                    assert(out@[0] == crate::slots::and_s(
                        Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                        hg,
                    ));
                }
            }
            proof {
                if frag(*e) {
                    lemma_set_contains(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, cs@, rg, hg, out@);
                }
            }
            Ok((XType::Bool, out))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_list_contains(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is ListContains,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::ListContains(a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tc, cs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                }
            }
            let (elem, max) = match tc {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let et = to_xtype(&elem);
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    lemma_ok_list(sty(elem), max, enums@);
                    lemma_ok_to_x(sty(elem), enums@);
                    lemma_xwidth_of(sty(elem), enums@);
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (tx, xv) = low(x, cx, sc, blk)?;
            if !xtype_eq(&tx, &et) {
                return Err(Fail::Type);
            }
            let (len, rows) = need(list_parts(&elem, max, &cs, enums))?;
            let ghost lg = len;
            let ghost t = xty(et);
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_all_pure_mono(cs@, b1.depth_s(), b2.depth_s());
                    lemma_list_rows_shape(cs@, len, rows_view(rows@), width(sty(elem), enums@), max as nat, b2.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == width(sty(elem), enums@)
                        && all_pure(rows@[q]@, b2.depth_s()) by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                    assert(xwidth(t, enums@) == width(sty(elem), enums@));
                    assert(lim_x(t, enums@));
                    assert(all_pure(xv@, b2.depth_s()));
                }
            }
            let mut hits: Vec<Expr> = Vec::new();
            let ghost mut cg: Seq<Expr> = Seq::empty();
            let mut p = 0;
            while p < rows.len()
                invariant
                    extends(*old(blk), *blk),
                    rows@.len() == max,
                    max <= 0x7fff_ffff,
                    lg == len,
                    t == xty(et),
                    p <= rows@.len(),
                    hits@.len() == p,
                    cg.len() == p,
                    forall|q: int| 0 <= q < p ==> #[trigger] hit_at(hits@[q], rows@[q]@, xv@, lg, cg[q], q, t, enums@),
                    *blk == b2,
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    pre ==> pure_below(len, b2.depth_s()) && all_pure(xv@, b2.depth_s()) && xv@.len() == xwidth(t, enums@)
                        && lim_x(t, enums@),
                    pre ==> forall|q: int| 0 <= q < rows@.len() ==> (#[trigger] rows@[q])@.len() == width(sty(elem), enums@)
                        && all_pure(rows@[q]@, b2.depth_s()),
                    pre ==> xwidth(t, enums@) == width(sty(elem), enums@),
                    pre ==> all_pure(hits@, b2.depth_s()),
                decreases rows.len() - p,
            {
                proof {
                    if pre {
                        assert(rows_view(rows@)[p as int] == rows@[p as int]@);
                    }
                }
                let same = need(eq_slots(&et, &rows[p], &xv, enums))?;
                let ghost h1 = hits@;
                let ghost c1 = cg;
                proof {
                    cg = cg.push(same);
                }
                let ghost hh = hits@;
                hits.push(and(bin(BinOp::Gt, copy_expr(&len), ci(p as i64)), same));
                proof {
                    if pre {
                        let gt = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(p as i64))));
                        assert(pure_below(len, b2.depth_s()));
                        assert(pure_below(Expr::Const(Value::Int(p as i64)), b2.depth_s()));
                        assert(pure_below(gt, b2.depth_s()));
                        assert(all_pure(rows@[p as int]@, b2.depth_s()));
                        assert(all_pure(xv@, b2.depth_s()));
                        assert(pure_below(same, b2.depth_s()));
                        lemma_join_pure(Join::And, gt, same, b2.depth_s());
                        assert forall|q: int| 0 <= q < hits@.len() implies pure_below(#[trigger] hits@[q], b2.depth_s()) by {
                            if q < hh.len() {
                                assert(hits@[q] == hh[q]);
                            }
                        }
                    }
                }
                proof {
                    assert(hit_at(hits@[p as int], rows@[p as int]@, xv@, lg, cg[p as int], p as int, t, enums@));
                    assert forall|q: int| 0 <= q < p implies #[trigger] hit_at(hits@[q], rows@[q]@, xv@, lg, cg[q], q, t, enums@) by {
                        assert(hits@[q] == h1[q]);
                        assert(cg[q] == c1[q]);
                    }
                }
                p += 1;
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(any_of(&hits));
            proof {
                if pre {
                    lemma_tree_pure(hits@, bool_lit(false), Join::Or, b2.depth_s());
                }
            }
            proof {
                let rv = rows_view(rows@);
                assert forall|q: int| 0 <= q < rv.len() implies #[trigger] hit_at(hits@[q], rv[q], xv@, lg, cg[q], q, t, enums@) by {
                    assert(rv[q] == rows@[q]@);
                }
                if frag(*e) {
                    lemma_list_contains(*e, *cx, sc@, b0, b1, *blk, sty(elem), max, cs@, t, xv@, lg, rv, hits@, cg, out@);
                }
            }
            Ok((XType::Bool, out))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn low_setop(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Insert || e is Remove || e is SetBin,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::Insert(t, a, x) | TExpr::Remove(t, a, x) => {
            let ghost b0 = *blk;
            let (ts, bits) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let elem = match &ts {
                XType::Set(u) => copy_stype(u),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&elem, t) || bits.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
                    assert(here_ok(**a, c, bt));
                    assert(wf_xtype(XTy::Set(Box::new(sty(elem))), cx.enums@));
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let slots = match e {
                TExpr::Insert(_, _, _) => {
                    let r = element_rank(x, cx, sc, blk, &elem)?;
                    let out = mark(&bits, &r, true);
                    proof {
                        if pre {
                            lemma_all_pure_mono(bits@, b1.depth_s(), blk.depth_s());
                            lemma_mark_pure(true, bits@, r, out@, blk.depth_s());
                        }
                    }
                    proof {
                        if frag(*e) {
                            lemma_insert(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, bits@, r, out@);
                        }
                    }
                    out
                },
                _ => {
                    let r = lookup_rank(x, cx, sc, blk, &elem)?;
                    let out = mark(&bits, &r, false);
                    proof {
                        if pre {
                            lemma_all_pure_mono(bits@, b1.depth_s(), blk.depth_s());
                            lemma_mark_pure(false, bits@, r, out@, blk.depth_s());
                        }
                    }
                    proof {
                        if frag(*e) {
                            lemma_remove(*e, *t, **a, **x, *cx, sc@, b0, b1, *blk, bits@, r, out@);
                        }
                    }
                    out
                },
            };
            Ok((ts, slots))
        },
        TExpr::SetBin(op, a, b) => {
            let ghost b0 = *blk;
            let (ta, xs) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (tb, ys) = low(b, cx, sc, blk)?;
            let ghost b2 = *blk;
            proof {
                if pre {
                    lemma_all_pure_mono(xs@, b1.depth_s(), b2.depth_s());
                }
            }
            match &ta {
                XType::Set(_) => {},
                _ => return Err(Fail::Type),
            }
            if !xtype_eq(&tb, &ta) {
                return Err(Fail::Type);
            }
            let n = if xs.len() < ys.len() {
                xs.len()
            } else {
                ys.len()
            };
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= xs.len(),
                    n <= ys.len(),
                    i <= n,
                    out@.len() == i,
                    forall|q: int| 0 <= q < i ==> #[trigger] out@[q] == setop_s(*op, xs@[q], ys@[q]),
                    pre == tpre(*e, *cx, old(sc)@, old(blk).depth_s()),
                    *blk == b2,
                    pre ==> all_pure(xs@, b2.depth_s()) && all_pure(ys@, b2.depth_s()) && xs@.len() == ys@.len(),
                    pre ==> all_pure(out@, b2.depth_s()),
                decreases n - i,
            {
                let x = copy_expr(&xs[i]);
                let y = copy_expr(&ys[i]);
                out.push(
                    match op {
                        SetOp::Union => or(x, y),
                        SetOp::Intersection => and(x, y),
                        SetOp::Difference => and(x, not(y)),
                        SetOp::Subset => implies(x, y),
                    },
                );
                proof {
                    if pre {
                        lemma_setop_pure(*op, xs@[i as int], ys@[i as int], b2.depth_s());
                        assert forall|q: int| 0 <= q < out@.len() implies pure_below(#[trigger] out@[q], b2.depth_s()) by {
                            assert(out@[q] == setop_s(*op, xs@[q], ys@[q]));
                            lemma_setop_pure(*op, xs@[q], ys@[q], b2.depth_s());
                        }
                    }
                }
                i += 1;
            }
            proof {
                if frag(*e) {
                    lemma_setbin(*e, *op, **a, **b, *cx, sc@, b0, b1, b2, xty(ta), xs@, ys@, out@);
                }
            }
            match op {
                SetOp::Subset => {
                    let mut r: Vec<Expr> = Vec::new();
                    r.push(all_of(&out));
                    proof {
                        if pre {
                            lemma_tree_pure(out@, bool_lit(true), Join::And, b2.depth_s());
                        }
                    }
                    Ok((XType::Bool, r))
                },
                _ => {
                    proof {
                        lemma_extends_trans(b0, b1, b2);
                    }
                    Ok((ta, out))
                },
            }
        },
        _ => Err(Fail::Type),
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
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
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
                }
                let ghost sm = tree_s(codes@, int_lit(0), Join::Add);
                let x = keep(blk, sum(&codes))?;
                proof {
                    if pre {
                        lemma_pure_mono(sm, b1.depth_s(), blk.depth_s());
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

/// Setのスロット `bits` の、番号 `r` の位置を `on` にする。
fn mark(bits: &Vec<Expr>, r: &Expr, on: bool) -> (out: Vec<Expr>)
    requires
        bits@.len() <= 0x7fff_ffff,
    ensures
        out@.len() == bits@.len(),
        forall|k: int| 0 <= k < bits@.len() ==> #[trigger] out@[k] == mark_s(on, bits@[k], *r, k as i64),
{
    let mut out: Vec<Expr> = Vec::new();
    let mut k = 0;
    while k < bits.len()
        invariant
            bits@.len() <= 0x7fff_ffff,
            k <= bits@.len(),
            out@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] out@[q] == mark_s(on, bits@[q], *r, q as i64),
        decreases bits.len() - k,
    {
        let bit = copy_expr(&bits[k]);
        out.push(
            if on {
                or(bit, eq(copy_expr(r), ci(k as i64)))
            } else {
                and(bit, bin(BinOp::Ne, copy_expr(r), ci(k as i64)))
            },
        );
        k += 1;
    }
    out
}

/// `Map#get`。キーの番号を束縛し、キーがなければ失敗する検査を束縛してから、行の値を選ぶ。
fn low_get(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Get,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let (t, a, x) = match e {
        TExpr::Get(t, a, x) => (t, a, x),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    proof {
        if pre {
            assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
        }
    }
    let (tm, ms) = low(a, cx, sc, blk)?;
    let ghost b1 = *blk;
    proof {
        if pre {
            assert(here_ok(**a, c, bt));
            lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
    }
    let ghost tmx = xty(tm);
    let (k, v) = match tm {
        XType::Map(k, v) => (*k, *v),
        _ => return Err(Fail::Type),
    };
    if !stype_eq(&k, t) {
        return Err(Fail::Type);
    }
    proof {
        if pre {
            lemma_ok_map(sty(k), sty(v), enums@);
        }
    }
    let r = lookup_rank(x, cx, sc, blk, &k)?;
    let ghost b2 = *blk;
    let ghost rr = r;
    let rank_local = match r {
        Expr::Local(index) => index,
        _ => {
            let index = depth(blk);
            bind(blk, r)?;
            index
        },
    };
    let ghost b3 = *blk;
    let rows = keys_or_zero_exec(&k, enums);
    let width = need(stype_width(&v, enums))?;
    let fallback = defaults(&v, enums);
    proof {
        lemma_default_len(sty(v), enums@);
        lemma_lits(enc(default_val(sty(v), enums@), sty(v), enums@), arbitrary(), Seq::empty());
        lemma_xwidth_of(sty(v), enums@);
        assert(usize::MAX >= 0xffff_ffff);
        if pre {
            assert(rank_local < b3.depth_s());
            lemma_all_pure_mono(ms@, b1.depth_s(), b3.depth_s());
        }
    }
    let (chk, slots) = need(select_flat_map_lookup(&ms, rows, width, rank_local, &fallback))?;
    let ghost c = chk;
    bind(blk, chk)?;
    proof {
        if pre {
            assert(all_pure(slots@, b3.depth_s()));
            lemma_all_pure_mono(slots@, b3.depth_s(), blk.depth_s());
        }
    }
    let ty = to_xtype(&v);
    proof {
        assert(added(b2, b3, rr, Expr::Local(rank_local)));
        lemma_fresh_push(b3, *blk, c);
        if frag(*e) {
            lemma_get(
                *e, *cx, sc@, b0, b1, b2, b3, *blk, **a, **x, ms@, sty(k), sty(v), rr, rank_local, c, slots@,
                fallback@, rows, width,
            );
        }
    }
    Ok((ty, slots))
}

/// Mapの参照と更新、Listの参照と更新。
fn low_access(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is HasKey || e is Get || e is Put || e is Delete || e is Keys || e is At || e is First || e is Last || e is Push || e is Pop || e is Shift,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
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

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn low_map_access(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is HasKey || e is Put || e is Delete || e is Keys,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::HasKey(t, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, t) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt));
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), b1.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() > 0 by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let present = need(heads(&rows))?;
            proof {
                if pre {
                    lemma_heads_pure(present@, rows_view(rows@), b1.depth_s());
                    assert(present@.len() <= crate::encoding::MAX_KEYS);
                }
            }
            if present.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let ghost rg = r;
            let hit = pick_slot(&present, &r);
            let ghost hg = hit;
            let known = bin(BinOp::Ge, r, ci(0));
            let mut out: Vec<Expr> = Vec::new();
            out.push(and(known, hit));
            proof {
                if pre {
                    lemma_all_pure_mono(present@, b1.depth_s(), blk.depth_s());
                    crate::quant::lemma_hit_pure(rg, present@, hg, blk.depth_s());
                    assert(out@[0] == crate::slots::and_s(
                        Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                        hg,
                    ));
                }
            }
            proof {
                if frag(*e) {
                    lemma_has_key(*e, *cx, sc@, b0, b1, *blk, sty(v), ms@, rows_view(rows@), present@, rg, hg, out@);
                }
            }
            Ok((XType::Bool, out))
        },
        TExpr::Put(kt, vt, a, x, y) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, kt) || !stype_eq(&v, vt) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt) && lim_ok(**y, c, bt));
                    assert(tpre(**x, *cx, sc@, blk.depth_s()));
                    assert(tpre(**y, *cx, sc@, blk.depth_s()));
                    lemma_put_pre(**x, **y, *cx, sc@, blk.depth_s(), sty(k), sty(v), ms@);
                }
            }
            let slots = put(e, &ms, &k, &v, x, y, cx, sc, blk)?;
            proof {
                if frag(*e) {
                    lemma_put_expr(*e, *cx, sc@, b0, b1, *blk, sty(k), sty(v), ms@, slots@);
                }
            }
            Ok((tm, slots))
        },
        TExpr::Delete(t, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, t) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt));
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    assert(rows@.len() <= crate::encoding::MAX_KEYS);
                }
            }
            if rows.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let mut alt: Vec<Expr> = Vec::new();
            alt.push(cb(false));
            let dv = defaults(&v, enums);
            append(&mut alt, &dv);
            proof {
                lemma_default_len(sty(v), enums@);
                lemma_lits(enc(default_val(sty(v), enums@), sty(v), enums@), arbitrary(), Seq::empty());
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_all_pure_mono(ms@, b1.depth_s(), blk.depth_s());
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == alt@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                    assert(all_pure(alt@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < alt@.len() implies pure_below(#[trigger] alt@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(alt@[j] == dv@[j - 1]);
                            }
                        }
                    }
                }
            }
            let out = need(ite_rows(&rows, &r, &alt))?;
            let res = join_rows(&out);
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), r, alt@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), w1, blk.depth_s());
                }
            }
            proof {
                if frag(*e) {
                    lemma_delete(*e, *cx, sc@, b0, b1, *blk, sty(v), ms@, rows_view(rows@), r, alt@, rows_view(out@), res@);
                }
            }
            Ok((tm, res))
        },
        TExpr::Keys(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
            }
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return Err(Fail::Type),
            };
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() > 0 by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let present = need(heads(&rows))?;
            proof {
                if pre {
                    lemma_heads_pure(present@, rows_view(rows@), blk.depth_s());
                }
            }
            proof {
                if frag(*e) {
                    lemma_keys(*e, *cx, sc@, b0, *blk, sty(k), sty(v), ms@, rows_view(rows@), present@);
                }
            }
            Ok((XType::Set(Box::new(k)), present))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn low_list_get(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is At || e is First || e is Last,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::At(a, ix) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                    assert(lim_ok(**ix, c, bt));
                }
            }
            let i0 = sub_scalar(ix, cx, sc, blk, &XType::Int)?;
            let ghost b2 = *blk;
            let ghost ig = i0;
            let i = atom(blk, i0)?;
            let ghost b3 = *blk;
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            proof {
                if pre {
                    lemma_pure_mono(i0, b2.depth_s(), b3.depth_s());
                    lemma_all_pure_mono(ls@, b1.depth_s(), b3.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, b3.depth_s());
                }
            }
            let cond = and(bin(BinOp::Ge, copy_expr(&i), ci(0)), bin(BinOp::Lt, copy_expr(&i), len));
            let ghost cg = cond;
            check(blk, cond, FAIL_INDEX)?;
            let dv = defaults(&t, enums);
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == rows@[0]@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                }
            }
            let slots = need(select(&rows, &i, &dv))?;
            proof {
                if pre {
                    if rows@.len() > 0 {
                        lemma_select_shape(rows_view(rows@), i, slots@, width(sty(t), enums@), b3.depth_s());
                    }
                    lemma_all_pure_mono(slots@, b3.depth_s(), blk.depth_s());
                }
            }
            proof {
                if frag(*e) {
                    lemma_at(*e, *cx, sc@, b0, b1, b2, b3, *blk, sty(t), max, ls@, ig, i, lg, rows_view(rows@), cg, slots@);
                }
            }
            Ok((to_xtype(&t), slots))
        },
        TExpr::First(a) | TExpr::Last(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                }
            }
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            let ghost b2 = *blk;
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), b2.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, b2.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == rows@[0]@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                    if rows@.len() > 0 {
                        assert(rows_view(rows@)[0] == rows@[0]@);
                    }
                }
            }
            match e {
                TExpr::First(_) => {
                    let slots = if rows.len() > 0 {
                        copy_exprs(&rows[0])
                    } else {
                        defaults(&t, enums)
                    };
                    proof {
                        if frag(*e) {
                            lemma_first(*e, *cx, sc@, b0, b1, b2, sty(t), max, ls@, lg, rows_view(rows@), slots@);
                        }
                    }
                    return Ok((to_xtype(&t), slots));
                },
                _ => {},
            }
            let i = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            let dv = defaults(&t, enums);
            let slots = need(select(&rows, &i, &dv))?;
            proof {
                if pre {
                    lemma_all_pure_mono(ls@, b2.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, blk.depth_s());
                    if rows@.len() > 0 {
                        lemma_select_shape(rows_view(rows@), i, slots@, width(sty(t), enums@), blk.depth_s());
                    }
                }
            }
            proof {
                if frag(*e) {
                    lemma_last(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rows_view(rows@), i, slots@);
                }
            }
            Ok((to_xtype(&t), slots))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn low_list_update(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Push || e is Pop || e is Shift,
    ensures
        tpre(*e, *cx, old(sc)@, old(blk).depth_s()) ==> low_post(*e, *cx, old(sc)@, final(blk).depth_s(), r),
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    match e {
        TExpr::Push(t, n, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (u, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return Err(Fail::Type),
            };
            if max != *n || !stype_eq(&u, t) || max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(u), max, enums@);
                    lemma_xwidth_of(sty(u), enums@);
                    assert(lim_ok(**x, c, bt));
                }
            }
            let xs = element(x, cx, sc, blk, &u)?;
            let ghost b2 = *blk;
            let (len, rows) = need(list_parts(&u, max, &ls, enums))?;
            let ghost lg = len;
            check(blk, bin(BinOp::Lt, copy_expr(&len), ci(max as i64)), FAIL_FULL)?;
            let ghost b3 = *blk;
            let new_len = bind(blk, bin(BinOp::Add, copy_expr(&len), ci(1)))?;
            let ghost ng = new_len;
            proof {
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), blk.depth_s());
                    lemma_all_pure_mono(xs@, b2.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(u), enums@), max as nat, blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == xs@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let out = need(ite_rows(&rows, &len, &xs))?;
            let ghost og = rows_view(out@);
            let r = list_join(new_len, &out);
            proof {
                if pre {
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), len, xs@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), width(sty(u), enums@), blk.depth_s());
                    assert(all_pure(r@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(r@[j] == flat(rows_view(out@))[j - 1]);
                            }
                        }
                    }
                }
            }
            proof {
                let rv = rows_view(rows@);
                if frag(*e) {
                    lemma_push(*e, *cx, sc@, b0, b1, b2, b3, *blk, sty(u), max, ls@, xs@, lg, rv, ng, og, r@);
                }
            }
            Ok((tl, r))
        },
        TExpr::Pop(a) | TExpr::Shift(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tl, ls) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), b1.depth_s(), cx.enums@);
                }
            }
            let (t, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return Err(Fail::Type),
            };
            if max > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_list(sty(t), max, enums@);
                    lemma_xwidth_of(sty(t), enums@);
                }
            }
            let (len, rows) = need(list_parts(&t, max, &ls, enums))?;
            let ghost lg = len;
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            let ghost b2 = *blk;
            let new_len = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            let ghost ng = new_len;
            let defs = defaults(&t, enums);
            proof {
                lemma_default_len(sty(t), enums@);
                lemma_lits(enc(default_val(sty(t), enums@), sty(t), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_all_pure_mono(ls@, b1.depth_s(), blk.depth_s());
                    lemma_list_rows_shape(ls@, len, rows_view(rows@), width(sty(t), enums@), max as nat, blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == defs@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            match e {
                TExpr::Pop(_) => {
                    let out = need(ite_rows(&rows, &new_len, &defs))?;
                    let ghost og = rows_view(out@);
                    let r = list_join(new_len, &out);
            proof {
                if pre {
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), new_len, defs@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), width(sty(t), enums@), blk.depth_s());
                    assert(all_pure(r@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(r@[j] == flat(rows_view(out@))[j - 1]);
                            }
                        }
                    }
                }
            }
                    proof {
                        let rv = rows_view(rows@);
                        if frag(*e) {
                            lemma_pop(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rv, ng, defs@, og, r@);
                        }
                    }
                    Ok((tl, r))
                },
                _ => {
                    let mut out: Vec<Vec<Expr>> = Vec::new();
                    let mut p = 1;
                    while p < rows.len()
                        invariant
                            1 <= p,
                            p <= rows@.len() || rows@.len() == 0,
                            rows@.len() > 0 ==> out@.len() == p - 1,
                            rows@.len() == 0 ==> out@.len() == 0,
                            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q]@ == rows@[q + 1]@,
                        decreases rows.len() - p,
                    {
                        let ghost o1 = out@;
                        out.push(copy_exprs(&rows[p]));
                        proof {
                            assert forall|q: int| 0 <= q < out@.len() implies #[trigger] out@[q]@ == rows@[q + 1]@ by {
                                if q < o1.len() {
                                    assert(out@[q] == o1[q]);
                                }
                            }
                        }
                        p += 1;
                    }
                    let ghost o1 = out@;
                    if rows.len() > 0 {
                        out.push(defs);
                    }
                    let ghost og = rows_view(out@);
                    let r = list_join(new_len, &out);
                    proof {
                        if pre {
                            let rv = rows_view(rows@);
                            let w = width(sty(t), enums@);
                            assert forall|q: int| 0 <= q < og.len() implies (#[trigger] og[q]).len() == w && all_pure(
                                og[q],
                                blk.depth_s(),
                            ) by {
                                assert(og[q] == out@[q]@);
                                if q < o1.len() {
                                    assert(out@[q] == o1[q]);
                                    assert(o1[q]@ == rows@[q + 1]@);
                                    assert(rv[q + 1] == rows@[q + 1]@);
                                } else {
                                    assert(out@[q]@ == defs@);
                                }
                            }
                            lemma_flat_shape(og, w, blk.depth_s());
                            assert(og.len() == max) by {
                                assert(rv.len() == max);
                            }
                            assert(all_pure(r@, blk.depth_s())) by {
                                assert forall|j: int| 0 <= j < r@.len() implies pure_below(#[trigger] r@[j], blk.depth_s()) by {
                                    if j > 0 {
                                        assert(r@[j] == flat(og)[j - 1]);
                                    }
                                }
                            }
                        }
                    }
                    proof {
                        let rv = rows_view(rows@);
                        if rv.len() > 0 {
                            assert(og.len() == rv.len());
                            assert forall|q: int| 0 <= q < rv.len() - 1 implies #[trigger] og[q] == rv[q + 1] by {
                                assert(og[q] == out@[q]@);
                                assert(out@[q] == o1[q]);
                                assert(rv[q + 1] == rows@[q + 1]@);
                            }
                            assert(og[rv.len() - 1] == out@[rv.len() - 1]@);
                        }
                        if frag(*e) {
                            lemma_shift(*e, *cx, sc@, b0, b1, b2, *blk, sty(t), max, ls@, lg, rv, ng, defaults_s(sty(t), enums@), og, r@);
                        }
                    }
                    Ok((tl, r))
                },
            }
        },
        _ => Err(Fail::Type),
    }
}

/// 述語（guard、不変条件、遷移契約、終端条件）として下ろす。
///
/// 環境が対応するとき、下ろした式の値は、値の上の意味論の値と一致する（失敗するなら同じ失敗）。
pub fn lower_prop(e: &TExpr, cx: &LowerCtx) -> (r: Result<Expr, Fail>)
    ensures
        cx_wf(*cx) && type_of(*e, sctx(*cx), Seq::empty()) == Some(XTy::Bool) && lim_ok(*e, sctx(*cx), Seq::empty())
            ==> deep(r),
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
    let r = bool_in(e, cx, &mut sc, 0);
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
        cx_wf(*cx) && type_of(*e, sctx(*cx), Seq::empty()) == Some(to_xty(sty(*st))) && lim_ok(
            *e,
            sctx(*cx),
            Seq::empty(),
        ) && ok_s(sty(*st), cx.enums@) ==> deep(r) && (r matches Ok(out) ==> out@.len() == width(sty(*st), cx.enums@)),
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
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, &mut sc, &mut blk)?;
    if !fits(&t, st) {
        return Err(Fail::Type);
    }
    let (_c, stored) = need(store(&t, &slots, st, &cx.enums))?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < stored.len()
        invariant
            i <= stored@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, stored@[j]),
        decreases stored.len() - i,
    {
        let x = wrap(&blk.binds, copy_expr(&stored[i]));
        out.push(x);
        proof {
            assert(wraps(out@[i as int], blk.binds@, stored@[i as int]));
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
