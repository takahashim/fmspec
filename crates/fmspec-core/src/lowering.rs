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

#[cfg(verus_keep_ghost)]
use crate::bindings::eval_bound_body;
#[cfg(verus_keep_ghost)]
use crate::canon::{in_slots, lemma_fits_to, lemma_in_member, lemma_models_has, lemma_shaped_len, slot_tys};
use crate::encoding::{copy_stype, copy_xtype, keys_exec, stype_eq, to_xtype, usizes_eq, xtype_eq, SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_rows, keys, keys_or_zero, member, sty, stys, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc_items, enc_repeat, lemma_default_len, lemma_enc_items_len, lemma_repeat_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_len, lemma_models_enc, lemma_stys, lemma_xtys, models};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_xwidth_of, list_items_member, models_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, xty, xtys, xwidth, XTy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{wf_xtype, xwidth_sum};
#[cfg(verus_keep_ghost)]
use crate::equality::eq_ok;
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, binop_spec, eval_l, lookup, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::infer::{lemma_all_typed_bool, lemma_all_typed_iff, lemma_items_typed_iff};
#[cfg(verus_keep_ghost)]
use crate::infer::{lemma_types_of_iff, type_of, types_of};
#[cfg(verus_keep_ghost)]
use crate::keys::{domain, lemma_domain_len, lemma_domain_rank, lemma_rank_in_domain, rank};
#[cfg(verus_keep_ghost)]
use crate::limits::*;
#[cfg(verus_keep_ghost)]
use crate::lists::{flat, ite_rows_ok, lemma_ite_rows, lemma_list_join, pad, select_ok};
#[cfg(verus_keep_ghost)]
use crate::lists::{lemma_list_parts, lemma_rows_weaken, lemma_select, pad_vals, parts_ok, rows_at, rows_view};
use crate::map_lookup::select_flat_map_lookup;
#[cfg(verus_keep_ghost)]
use crate::map_lookup::{flat_slot, flat_slot_int, key_rank, MISSING_KEY};
#[cfg(verus_keep_ghost)]
use crate::maps::{lemma_map_join, lemma_map_parts, lemma_none_rows, lemma_rows_update, mparts_ok, row_vals};
use crate::model::{BinOp, Expr, Type, Value};
use crate::preserve::pure_exec;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::quant::lemma_bin_const;
#[cfg(verus_keep_ghost)]
use crate::quant::unrank_ok;
#[cfg(verus_keep_ghost)]
use crate::quant::{at_rank, lemma_items_index, lemma_items_member, lemma_qscan, picks, q_step_ok};
#[cfg(verus_keep_ghost)]
use crate::quant::{lemma_select_all, lemma_select_prefix, lemma_vals_weaken, qprefix, vals_at};
use crate::quant::{pick_slot, unrank};
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::eval_src;
#[cfg(verus_keep_ghost)]
use crate::source::{count_some, count_true, eval_elements, eval_fold, eval_quant, eval_seq, eval_set_items};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_map_items, put_row, Item};
#[cfg(verus_keep_ghost)]
use crate::source::{select_bits, src_bool, SEnv};
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

/// 要素の下ろしの正しさ。値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
pub open spec fn elem_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, xs: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(e, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => if member(v, st, se.enums) {
                run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                    cx,
                    sc,
                    env,
                    se,
                    l,
                    sls,
                ) && clean(xs, env, l) && slot_vals(xs, env, l) == enc(v, st, se.enums)
            } else {
                run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
            },
        }
}

#[verifier::spinoff_prover]
proof fn lemma_element(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    t: XTy,
    slots: Seq<Expr>,
    st: STy,
    cond: Expr,
    out: Seq<Expr>,
    xs: Seq<Expr>,
)
    requires
        lowers(e, cx, sc, b0, b1, t, slots),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        fits_s(t, st),
        store_spec(t, slots, st, cx.enums@, cond, out),
        (cond == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN)),
        ),
        atoms_ok(out, xs, b2, b3),
    ensures
        elem_lowers(e, cx, sc, b0, b3, st, xs),
{
    let c = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN));
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(e, se, sls) {
        Err(k) => run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => if member(v, st, se.enums) {
            run(fresh(b0, b3), env, ls) matches Ok(l) && l.len() == b3.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && clean(xs, env, l) && slot_vals(xs, env, l) == enc(v, st, se.enums)
        } else {
            run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
        },
    } by {
        let enums = se.enums;
        lemma_one(e, cx, sc, b0, b1, t, slots, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(v) = eval_src(e, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(store_ok(cond, out, env, l1, v, st, enums));
            let m = member(v, st, enums);
            assert(eval_l(bool_lit(true), env, l1) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN), env, l1) == Err::<Value, ErrKind>(
                ErrKind::Failed(FAIL_NOT_IN_DOMAIN),
            ));
            let l2 = if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l1) == Ok::<Seq<Value>, ErrKind>(l1));
                assert(m);
                l1
            } else {
                lemma_run_one(b1, b2, c, env, l1);
                l1.push(Value::Bool(true))
            };
            if m {
                assert(run(fresh(b1, b2), env, l1) == Ok::<Seq<Value>, ErrKind>(l2));
                assert(prefix(l1, l2));
                lemma_run_len(fresh(b0, b1), env, ls);
                lemma_run_fresh_ok(b0, b2, env, ls);
                lemma_clean_weaken(out, env, l1, l2);
                assert(atoms_run(out, xs, b2, b3, env, l2));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_prefix_trans(ls, l2, l3);
                lemma_ctx_weaken(cx, sc, env, se, ls, l3, sls);
            }
        }
    }
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

/// 要素の番号の下ろしの正しさ。値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
pub open spec fn elem_rank_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, x: Expr) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(e, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => if member(v, st, se.enums) {
                run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                    cx,
                    sc,
                    env,
                    se,
                    l,
                    sls,
                ) && pure_below(x, l.len()) && eval_l(x, env, l) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, st, se.enums) as i64),
                )
            } else {
                run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
            },
        }
}

proof fn lemma_elem_rank(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    t: XTy,
    slots: Seq<Expr>,
    st: STy,
    cond: Expr,
    out: Seq<Expr>,
    r: Expr,
    x: Expr,
)
    requires
        lowers(e, cx, sc, b0, b1, t, slots),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        fits_s(t, st),
        keys(st, cx.enums@) is Some,
        store_spec(t, slots, st, cx.enums@, cond, out),
        (cond == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN)),
        ),
        rank_spec(t, slots, st, cx.enums@, r),
        added(b2, b3, r, x),
    ensures
        elem_rank_lowers(e, cx, sc, b0, b3, st, x),
{
    let c = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN));
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(e, se, sls) {
        Err(k) => run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => if member(v, st, se.enums) {
            run(fresh(b0, b3), env, ls) matches Ok(l) && l.len() == b3.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && pure_below(x, l.len()) && eval_l(x, env, l) == Ok::<Value, ErrKind>(
                Value::Int(rank(v, st, se.enums) as i64),
            )
        } else {
            run(fresh(b0, b3), env, ls) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(FAIL_NOT_IN_DOMAIN))
        },
    } by {
        let enums = se.enums;
        lemma_one(e, cx, sc, b0, b1, t, slots, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(v) = eval_src(e, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(store_ok(cond, out, env, l1, v, st, enums));
            let m = member(v, st, enums);
            assert(eval_l(bool_lit(true), env, l1) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NOT_IN_DOMAIN), env, l1) == Err::<Value, ErrKind>(
                ErrKind::Failed(FAIL_NOT_IN_DOMAIN),
            ));
            let l2 = if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l1) == Ok::<Seq<Value>, ErrKind>(l1));
                assert(m);
                l1
            } else {
                lemma_run_one(b1, b2, c, env, l1);
                l1.push(Value::Bool(true))
            };
            if m {
                assert(run(fresh(b1, b2), env, l1) == Ok::<Seq<Value>, ErrKind>(l2));
                assert(prefix(l1, l2));
                lemma_denotes_weaken(slots, env, l1, l2, v, t, enums);
                lemma_clean_pure(slots, env, l2);
                assert(pure_below(r, l2.len()));
                lemma_run_len(fresh(b0, b1), env, ls);
                lemma_run_fresh_ok(b0, b2, env, ls);
                lemma_added(b2, b3, r, x, env, l2, Value::Int(rank(v, st, enums) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_prefix_trans(ls, l2, l3);
                lemma_ctx_weaken(cx, sc, env, se, ls, l3, sls);
            }
        }
    }
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

/// Mapのスロット `ms` にキー `key` と値 `value` を置いた結果が `out` である。
pub open spec fn put_lowers(
    key: TExpr,
    value: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    out: Seq<Expr>,
) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>, rows: Seq<Option<SVal>>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() && #[trigger] denotes(
            ms,
            env,
            ls,
            SVal::Map(rows),
            XTy::Map(Box::new(kt), Box::new(vt)),
            se.enums,
        ) ==> match put_row(SVal::Map(rows), kt, vt, eval_src(key, se, sls), eval_src(value, se, sls), se.enums) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(rows2) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && denotes(out, env, l, SVal::Map(rows2), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
        }
}

/// キーの番号の行だけを、有無が真で値が `xs` の行に置き換える。
#[verifier::spinoff_prover]
proof fn lemma_put(
    key: TExpr,
    value: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    r: Expr,
    xs: Seq<Expr>,
    alt: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    res: Seq<Expr>,
)
    requires
        elem_rank_lowers(key, cx, sc, b0, b1, kt, r),
        elem_lowers(value, cx, sc, b1, b2, vt, xs),
        extends(b0, b1),
        extends(b1, b2),
        mparts_ok(ms, mrows, (1 + width(vt, cx.enums@)) as nat, keys_or_zero(kt, cx.enums@)),
        mrows.len() <= 0x7fff_ffff,
        alt == seq![bool_lit(true)] + xs,
        ite_rows_ok(out, mrows, r, alt),
        res == flat(out),
    ensures
        put_lowers(key, value, cx, sc, b0, b2, kt, vt, ms, res),
{
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>, rows: Seq<Option<SVal>>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() && #[trigger] denotes(
            ms,
            env,
            ls,
            SVal::Map(rows),
            mt,
            se.enums,
        ) implies match put_row(SVal::Map(rows), kt, vt, eval_src(key, se, sls), eval_src(value, se, sls), se.enums) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows2) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(res, env, l, SVal::Map(rows2), mt, se.enums),
    } by {
        let enums = se.enums;
        lemma_map_parts(ms, mrows, env, ls, rows, kt, vt, enums);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(kv) = eval_src(key, se, sls) {
            if member(kv, kt, enums) {
                let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                assert(ctx_ok(cx, sc, env, se, l1, sls));
                if let Ok(vv) = eval_src(value, se, sls) {
                    if member(vv, vt, enums) {
                        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                        lemma_prefix_trans(ls, l1, l2);
                        lemma_rows_weaken(mrows, row_vals(rows, vt, enums), env, ls, l2);
                        lemma_weaken(r, env, l1, l2);
                        lemma_pure_mono(r, l1.len(), l2.len());
                        let rk = rank(kv, kt, enums);
                        lemma_rank_in_domain(kv, kt, enums);
                        assert(at_rank(r, env, l2, rk as i64));
                        let av = row_slots(Some(vv), vt, enums);
                        lemma_lits(seq![Value::Bool(true)], env, l2);
                        assert(lits(seq![Value::Bool(true)]) =~= seq![bool_lit(true)]);
                        lemma_clean_concat(seq![bool_lit(true)], xs, env, l2);
                        lemma_ite_rows(out, mrows, r, alt, row_vals(rows, vt, enums), av, env, l2, rk as i64);
                        lemma_rows_update(rows, vt, enums, rk as int, Some(vv));
                        let rows2 = rows.update(rk as int, Some(vv));
                        assert(row_vals(rows2, vt, enums) =~= Seq::new(
                            mrows.len(),
                            |p: int| if p == rk as i64 { av } else { row_vals(rows, vt, enums)[p] },
                        ));
                        lemma_map_join(out, env, l2, rows2, kt, vt, enums);
                    }
                }
            }
        }
    }
}

/// Mapの更新の下ろし。
#[verifier::spinoff_prover]
proof fn lemma_put_expr(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    slots: Seq<Expr>,
)
    requires
        e matches TExpr::Put(skt, svt, a, x, y) && sty(skt) == kt && sty(svt) == vt && lowers(
            *a,
            cx,
            sc,
            b0,
            b1,
            XTy::Map(Box::new(kt), Box::new(vt)),
            ms,
        ) && put_lowers(*x, *y, cx, sc, b1, b2, kt, vt, ms, slots),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Map(Box::new(kt), Box::new(vt)), slots),
{
    let a = e->Put_2;
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        slots,
        env,
        mt,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), se.enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            assert(denotes(ms, env, l1, SVal::Map(rows), mt, se.enums));
            assert(ctx_ok(cx, sc, env, se, l1, sls));
        }
    }
}

/// Mapのリテラルの要素を順に置くと、`slots` は置いた結果のMapを表す。
pub open spec fn maplit_ok(
    items: Seq<Item>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    slots: Seq<Expr>,
) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_map_items(
            kt,
            vt,
            items,
            se,
            sls,
        ) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(rows) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && denotes(slots, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
        }
}

proof fn lemma_maplit_base(cx: LowerCtx, sc: Seq<Bound>, b0: Block, kt: STy, vt: STy, slots: Seq<Expr>)
    requires
        keys(kt, cx.enums@) is Some,
        slots == lits(
            enc(default_val(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@), STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
        ),
    ensures
        maplit_ok(Seq::empty(), cx, sc, b0, b0, kt, vt, slots),
{
    let mst = STy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_map_items(
        kt,
        vt,
        Seq::<Item>::empty(),
        se,
        sls,
    ) {
        Err(k) => run(fresh(b0, b0), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows) => run(fresh(b0, b0), env, ls) matches Ok(l) && l.len() == b0.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(slots, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
    } by {
        let enums = se.enums;
        let rows = eval_map_items(kt, vt, Seq::<Item>::empty(), se, sls)->Ok_0;
        lemma_fresh_refl(b0);
        assert(fresh(b0, b0) =~= Seq::<Expr>::empty());
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        assert(prefix(ls, ls));
        lemma_none_rows(keys_or_zero(kt, enums), vt, enums);
        assert(rows =~= Seq::new(keys_or_zero(kt, enums), |_i: int| None::<SVal>));
        assert(default_val(mst, enums)->Map_0 =~= rows);
        lemma_lits(enc(default_val(mst, enums), mst, enums), env, ls);
    }
}

proof fn lemma_maplit_step(
    items: Seq<Item>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    kt: STy,
    vt: STy,
    s1: Seq<Expr>,
    s2: Seq<Expr>,
)
    requires
        items.len() > 0,
        maplit_ok(items.drop_last(), cx, sc, b0, b1, kt, vt, s1),
        put_lowers(items.last().key, items.last().value, cx, sc, b1, b2, kt, vt, s1, s2),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        maplit_ok(items, cx, sc, b0, b2, kt, vt, s2),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_map_items(
        kt,
        vt,
        items,
        se,
        sls,
    ) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(rows) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && denotes(s2, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(rows) = eval_map_items(kt, vt, items.drop_last(), se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            assert(denotes(s1, env, l1, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums));
            if let Ok(rows2) = eval_map_items(kt, vt, items, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
            }
        }
    }
}

/// Mapのキーの集合は、各行の有無のスロットである。
#[verifier::spinoff_prover]
proof fn lemma_keys(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    kt: STy,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    h: Seq<Expr>,
)
    requires
        e matches TExpr::Keys(a) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(kt), Box::new(vt)), ms),
        extends(b0, b1),
        mparts_ok(ms, mrows, (1 + width(vt, cx.enums@)) as nat, keys_or_zero(kt, cx.enums@)),
        heads_ok(h, mrows),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Set(Box::new(kt)), h),
{
    let a = e->Keys_0;
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        h,
        env,
        XTy::Set(Box::new(kt)),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            lemma_map_parts(ms, mrows, env, l1, rows, kt, vt, enums);
            let bits = eval_src(e, se, sls)->Ok_0->Set_0;
            assert(bits.len() == rows.len());
            let vals = row_vals(rows, vt, enums);
            assert forall|j: int| 0 <= j < h.len() implies pure_below(#[trigger] h[j], l1.len()) && eval_l(h[j], env, l1)
                == Ok::<Value, ErrKind>(Value::Bool(bits[j])) by {
                assert(head_at(h[j], mrows[j]));
                assert(clean(mrows[j], env, l1) && slot_vals(mrows[j], env, l1) == vals[j]);
                assert(pure_below(mrows[j][0], l1.len()) && eval_l(mrows[j][0], env, l1) is Ok);
                assert(slot_vals(mrows[j], env, l1)[0] == eval_l(mrows[j][0], env, l1)->Ok_0);
                assert(vals[j] == row_slots(rows[j], vt, enums));
            }
            assert(slot_vals(h, env, l1) =~= enc(SVal::Set(bits), STy::Set(Box::new(kt)), enums));
        }
    }
}

/// Mapがキーを持つかは、キーの集合がキーを含むかである。
#[verifier::spinoff_prover]
proof fn lemma_has_key(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    present: Seq<Expr>,
    r: Expr,
    hit: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::HasKey(t, a, x) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(vt)), ms)
            && rank_lowers(*x, cx, sc, b1, b2, sty(t), r) && mparts_ok(
            ms,
            mrows,
            (1 + width(vt, cx.enums@)) as nat,
            keys_or_zero(sty(t), cx.enums@),
        ),
        extends(b0, b1),
        extends(b1, b2),
        heads_ok(present, mrows),
        present.len() <= 0x7fff_ffff,
        picks(hit, present, r),
        out == seq![and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let t = e->HasKey_0;
    let a = e->HasKey_1;
    let x = e->HasKey_2;
    let kt = sty(t);
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    let ek = TExpr::Keys(a);
    lemma_keys(ek, cx, sc, b0, b1, kt, vt, ms, mrows, present);
    let es = TExpr::SetContains(t, Box::new(ek), x);
    lemma_set_contains(es, t, ek, *x, cx, sc, b0, b1, b2, present, r, hit, out);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        if let Ok(m) = eval_src(*a, se, sls) {
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            if let Ok(y) = eval_src(*x, se, sls) {
                if member(y, kt, enums) {
                    lemma_rank_in_domain(y, kt, enums);
                }
            }
        }
        assert(eval_src(e, se, sls) == eval_src(es, se, sls));
    }
}

/// Mapからキーを除く。キーの番号の行だけを、有無が偽で値が既定値の行に置き換える。
#[verifier::spinoff_prover]
proof fn lemma_delete(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    vt: STy,
    ms: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    r: Expr,
    alt: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    res: Seq<Expr>,
)
    requires
        e matches TExpr::Delete(t, a, x) && lowers(*a, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(vt)), ms)
            && rank_lowers(*x, cx, sc, b1, b2, sty(t), r) && mparts_ok(
            ms,
            mrows,
            (1 + width(vt, cx.enums@)) as nat,
            keys_or_zero(sty(t), cx.enums@),
        ),
        extends(b0, b1),
        extends(b1, b2),
        mrows.len() <= 0x7fff_ffff,
        alt == seq![bool_lit(false)] + lits(enc(default_val(vt, cx.enums@), vt, cx.enums@)),
        ite_rows_ok(out, mrows, r, alt),
        res == flat(out),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Map(Box::new(sty(e->Delete_0)), Box::new(vt)), res),
{
    let t = e->Delete_0;
    let a = e->Delete_1;
    let x = e->Delete_2;
    let kt = sty(t);
    let mt = XTy::Map(Box::new(kt), Box::new(vt));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        res,
        env,
        mt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(*a, cx, sc, b0, b1, mt, ms, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(m) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(member(m, STy::Map(Box::new(kt), Box::new(vt)), enums));
            let rows = m->Map_0;
            assert(m == SVal::Map(rows));
            lemma_map_parts(ms, mrows, env, l1, rows, kt, vt, enums);
            assert(rank_result(eval_src(*x, se, sls), run(fresh(b1, b2), env, l1), r, env, kt, enums));
            if let Ok(y) = eval_src(*x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                lemma_rows_weaken(mrows, row_vals(rows, vt, enums), env, l1, l2);
                let mem = member(y, kt, enums);
                let rk: i64 = if mem {
                    rank(y, kt, enums) as i64
                } else {
                    -1i64
                };
                assert(at_rank(r, env, l2, rk));
                let av = row_slots(None, vt, enums);
                assert(lits(av) =~= alt);
                lemma_lits(av, env, l2);
                let vals = row_vals(rows, vt, enums);
                lemma_ite_rows(out, mrows, r, alt, vals, av, env, l2, rk);
                if mem {
                    lemma_rank_in_domain(y, kt, enums);
                    let rkk = rank(y, kt, enums) as int;
                    lemma_rows_update(rows, vt, enums, rkk, None);
                    let rows2 = rows.update(rkk, None);
                    assert(row_vals(rows2, vt, enums) =~= Seq::new(
                        mrows.len(),
                        |p: int| if p == rk { av } else { vals[p] },
                    ));
                    lemma_map_join(out, env, l2, rows2, kt, vt, enums);
                } else {
                    assert(vals =~= Seq::new(mrows.len(), |p: int| if p == rk { av } else { vals[p] }));
                    lemma_map_join(out, env, l2, rows, kt, vt, enums);
                }
            }
        }
    }
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

/// 純粋な条件とスロットから作った `ite` のスロットは純粋である。
proof fn lemma_ite_out_pure(c: Expr, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, n: nat)
    requires
        pure_below(c, n),
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == ite_s(c, xs[i], ys[i]),
        forall|i: int| 0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], n) && pure_below(ys[i], n),
    ensures
        all_pure(out, n),
{
    assert forall|i: int| 0 <= i < out.len() implies pure_below(#[trigger] out[i], n) by {
        assert(out[i] == ite_s(c, xs[i], ys[i]));
        assert(pure_below(xs[i], n) && pure_below(ys[i], n));
    }
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

/// 型の付く `ite` の条件と枝は、より深い位置でも前提を満たし、枝の型は `ite` の型である。
proof fn lemma_ite_tpre(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat, m: nat)
    requires
        e is Ite,
        tpre(e, cx, sc, n),
        n <= m,
    ensures
        tpre(*e->Ite_0, cx, sc, n),
        type_of(*e->Ite_0, sctx(cx), bound_tys(sc)) == Some(XTy::Bool),
        tpre(*e->Ite_1, cx, sc, m),
        tpre(*e->Ite_2, cx, sc, m),
        type_of(*e->Ite_1, sctx(cx), bound_tys(sc)) == type_of(e, sctx(cx), bound_tys(sc)),
        type_of(*e->Ite_2, sctx(cx), bound_tys(sc)) == type_of(e, sctx(cx), bound_tys(sc)),
{
    lemma_sc_wf_mono(sc, n, m, cx.enums@);
}

/// 束縛を持つ `ite` の枝を、スロット `j` ごとにその位置の深さで単独に下ろし直し、`j` 番目のスロットを選ぶ式を束縛する。
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
    let ghost d = blk.depth_s();
    let ghost pre = tpre(*a, *cx, sc0, d as nat) && tpre(*b, *cx, sc0, d as nat) && type_of(*a, sctx(*cx), bound_tys(sc0))
        == Some(xty(*tx)) && type_of(*b, sctx(*cx), bound_tys(sc0)) == Some(xty(*tx)) && w == xwidth(xty(*tx), cx.enums@);
    let ghost mut fa: Seq<Seq<Expr>> = Seq::empty();
    let ghost mut fb: Seq<Seq<Expr>> = Seq::empty();
    let mut out: Vec<Expr> = Vec::new();
    proof {
        lemma_extends_refl(*blk);
    }
    let mut j = 0;
    while j < w
        invariant
            decreases_to!(*_parent => *a),
            decreases_to!(*_parent => *b),
            sc@ == sc0,
            j <= w,
            b2.wf(),
            d == b2.depth_s(),
            b2 == *old(blk),
            extends(b2, *blk),
            blk.base == b2.base,
            blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, j as nat),
            fa.len() == j,
            fb.len() == j,
            out@ == Seq::new(j as nat, |i: int| Expr::Local((d + i) as usize)),
            frag(*a) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*a, *cx, sc0, (d + i) as nat, xty(*tx), fa[i]),
            frag(*b) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(*b, *cx, sc0, (d + i) as nat, xty(*tx), fb[i]),
            forall|i: int| 0 <= i < fa.len() ==> i < (#[trigger] fa[i]).len(),
            forall|i: int| 0 <= i < fb.len() ==> i < (#[trigger] fb[i]).len(),
            sc0 == old(sc)@,
            pre == (tpre(*a, *cx, sc0, d as nat) && tpre(*b, *cx, sc0, d as nat) && type_of(*a, sctx(*cx), bound_tys(sc0))
                == Some(xty(*tx)) && type_of(*b, sctx(*cx), bound_tys(sc0)) == Some(xty(*tx)) && w == xwidth(xty(*tx), cx.enums@)),
        decreases w - j,
    {
        let dj = depth(blk);
        proof {
            if pre {
                lemma_sc_wf_mono(sc0, d as nat, dj as nat, cx.enums@);
            }
        }
        let (ta, xa) = closed_in(a, cx, sc, dj)?;
        let (tb, yb) = closed_in(b, cx, sc, dj)?;
        if !xtype_eq(&ta, tx) || !xtype_eq(&tb, tx) || j >= xa.len() || j >= yb.len() {
            return Err(Fail::Type);
        }
        proof {
            assert(dj == d + j);
        }
        let ghost bj = *blk;
        let o = bind(blk, ite(copy_expr(c), copy_expr(&xa[j]), copy_expr(&yb[j])))?;
        out.push(o);
        proof {
            lemma_extends_trans(b2, bj, *blk);
            let fa0 = fa;
            let fb0 = fb;
            fa = fa.push(xa@);
            fb = fb.push(yb@);
            lemma_ite_binds_push(*c, fa0, fb0, xa@, yb@, j as nat);
            assert(blk.binds@ == b2.binds@ + ite_binds(*c, fa, fb, (j + 1) as nat));
            assert(out@ =~= Seq::new((j + 1) as nat, |i: int| Expr::Local((d + i) as usize)));
            assert(fa[j as int] == xa@ && fb[j as int] == yb@);
            assert(j < xa@.len() && j < yb@.len());
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fa[i]).len() && i < fb[i].len() by {
                if i < j {
                    assert(fa[i] == fa0[i] && fb[i] == fb0[i]);
                    assert(i < fa0[i].len() && i < fb0[i].len());
                } else {
                    assert(fa[i] == xa@ && fb[i] == yb@);
                }
            }
            if frag(*a) {
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
            assert(forall|i: int| 0 <= i < j + 1 ==> i < (#[trigger] fa[i]).len() && i < fb[i].len());
        }
        j += 1;
    }
    Ok((out, Ghost(fa), Ghost(fb)))
}

/// 条件式。条件を束縛する。枝が束縛を持たなければ、スロットごとに `ite` で選ぶ。
/// 束縛を持つなら、スロットごとに、その位置の深さで枝を単独に評価する式に下ろし直して束縛する。
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

/// 空の `all` と `any` は、単位元になる。
proof fn lemma_fold_empty(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b: Block, out: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() == 0 && out == seq![bool_lit(all)],
    ensures
        lowers(e, cx, sc, b, b, XTy::Bool, out),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b, b), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        assert(fresh(b, b) =~= Seq::<Expr>::empty());
        assert(eval_fold(all, es@, se, sls) == Ok::<bool, ErrKind>(all));
        assert(eval_l(bool_lit(all), env, ls) == Ok::<Value, ErrKind>(Value::Bool(all)));
        lemma_one_denotes(bool_lit(all), env, ls, Value::Bool(all), XTy::Bool, se.enums);
    }
}

/// `let` の下ろし。束縛する値のスロットを局所変数の対応に加えて、本体を下ろす。
proof fn lemma_let(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    s0: Seq<Expr>,
    bound: Bound,
    tb: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Let(a, b) && lowers(*a, cx, sc, b0, b1, xty(bound.ty), s0) && lowers(
            *b,
            cx,
            sc.push(bound),
            b2,
            b3,
            tb,
            out,
        ),
        atoms_ok(s0, bound.slots@, b1, b2),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, tb, out),
{
    let a = e->Let_0;
    let b = e->Let_1;
    lemma_extends_trans(b1, b2, b3);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        tb,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, xty(bound.ty), s0, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b3, env, ls);
        lemma_run_fresh(b1, b2, b3, env, run(fresh(b0, b1), env, ls)->Ok_0);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(clean(s0, env, l1));
            assert(atoms_run(s0, bound.slots@, b1, b2, env, l1));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            let sc2 = sc.push(bound);
            let sls2 = sls.push(v);
            assert(denotes(bound.slots@, env, l2, v, xty(bound.ty), se.enums));
            assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(
                sc2[i].slots@,
                env,
                l2,
                sls2[i],
                xty(sc2[i].ty),
                se.enums,
            ) by {
                if i < sc.len() {
                    assert(sc2[i] == sc[i]);
                    assert(sls2[i] == sls[i]);
                }
            }
            assert(ctx_ok(cx, sc2, env, se, l2, sls2));
        }
    }
}

/// `all` と `any` の下ろし。先頭の項はスロットで、残りの項は単独に評価する式である。
proof fn lemma_fold(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, terms: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() >= 1 && terms.len() == es@.len() && lowers(
            es@[0],
            cx,
            sc,
            b0,
            b1,
            XTy::Bool,
            seq![terms[0]],
        ) && (forall|j: int|
            1 <= j < es@.len() ==> #[trigger] closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]))
            && b2.binds@ == b1.binds@.push(tree_s(terms, bool_lit(all), raw_join(all))),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    let joined = tree_s(terms, bool_lit(all), raw_join(all));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(es@[0], cx, sc, b0, b1, XTy::Bool, seq![terms[0]], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        match eval_src(es@[0], se, sls) {
            Err(k) => {
                lemma_fold_first_err(all, es@, se, sls, k);
            },
            Ok(v0) => {
                let l = run(fresh(b0, b1), env, ls)->Ok_0;
                lemma_denotes_one(terms[0], env, l, v0, XTy::Bool, se.enums);
                assert forall|j: int| 0 <= j < terms.len() implies #[trigger] as_bool(eval_l(terms[j], env, l)) == src_bool(
                    eval_src(es@[j], se, sls),
                ) && lift_bool(as_bool(eval_l(terms[j], env, l))) == eval_l(terms[j], env, l) by {
                    if j > 0 {
                        assert(closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]));
                        lemma_scalar_bool(eval_src(es@[j], se, sls), eval_l(terms[j], env, l), se.enums);
                    }
                }
                assert(bool_or_err(terms, env, l));
                lemma_fold_eq(all, es@, terms, se, sls, env, l);
                lemma_tree_sc(all, terms, env, l);
                lemma_run_one(b1, b2, joined, env, l);
                if let Ok(r) = eval_l(joined, env, l) {
                    lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
                }
            },
        }
    }
}

/// 条件式のスロットは、条件の真偽に応じて、片方の枝のスロットの値になる。
proof fn lemma_ite_slots(c: Expr, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, env: Env, l: Seq<Value>, pos: bool)
    requires
        pure_below(c, l.len()),
        eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(pos)),
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == ite_s(c, xs[j], ys[j]),
        forall|j: int| 0 <= j < xs.len() ==> pure_below(#[trigger] xs[j], l.len()) && pure_below(ys[j], l.len()),
        pos ==> clean(xs, env, l),
        !pos ==> clean(ys, env, l),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == if pos {
            slot_vals(xs, env, l)
        } else {
            slot_vals(ys, env, l)
        },
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == if pos {
        eval_l(xs[j], env, l)
    } else {
        eval_l(ys[j], env, l)
    } by {
        assert(pure_below(xs[j], l.len()));
    }
    if pos {
        assert(slot_vals(out, env, l) =~= slot_vals(xs, env, l));
    } else {
        assert(slot_vals(out, env, l) =~= slot_vals(ys, env, l));
    }
}

/// 条件式のスロットごとの束縛。`i` 番目は、条件で枝の `i` 番目のスロットを選ぶ。
spec fn ite_binds(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, n: nat) -> Seq<Expr> {
    Seq::new(n, |i: int| ite_s(c, fa[i][i], fb[i][i]))
}

proof fn lemma_ite_binds_push(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, xa: Seq<Expr>, yb: Seq<Expr>, j: nat)
    requires
        fa.len() == j,
        fb.len() == j,
    ensures
        ite_binds(c, fa.push(xa), fb.push(yb), j + 1) =~= ite_binds(c, fa, fb, j).push(ite_s(c, xa[j as int], yb[j as int])),
{
    assert forall|i: int| 0 <= i < j implies #[trigger] fa.push(xa)[i] == fa[i] && fb.push(yb)[i] == fb[i] by {}
}

/// 枝が束縛を持たない条件式の下ろし。
proof fn lemma_ite_simple(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        ba1.binds@.len() == 0,
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        bb1.binds@.len() == 0,
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == ite_s(c, xs[i], ys[i]),
        forall|i: int|
            0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], b2.depth_s()) && pure_below(ys[i], b2.depth_s()),
    ensures
        lowers(e, cx, sc, b0, b2, t, out),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*p, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
            let bv = v->Bool_0;
            lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            assert(fresh(ba0, ba1) =~= Seq::<Expr>::empty());
            assert(fresh(bb0, bb1) =~= Seq::<Expr>::empty());
            assert(run(Seq::<Expr>::empty(), env, l2) == Ok::<Seq<Value>, ErrKind>(l2));
            if bv {
                lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
                if let Ok(va) = eval_src(*a, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, true);
                }
            } else {
                lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
                if let Ok(vb) = eval_src(*b, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, false);
                }
            }
        }
    }
}

/// スロットごとの束縛の、先頭 `k` 個の評価。
#[verifier::spinoff_prover]
proof fn lemma_ite_prefix(
    br: TExpr,
    f: Seq<Seq<Expr>>,
    c: Expr,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    bv: bool,
    d: nat,
    w: nat,
    k: nat,
    cx: LowerCtx,
    sc: Seq<Bound>,
    t: XTy,
    env: Env,
    se: SEnv,
    l2: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        ctx_ok(cx, sc, env, se, l2, sls),
        l2.len() == d,
        pure_below(c, d),
        eval_l(c, env, l2) == Ok::<Value, ErrKind>(Value::Bool(bv)),
        f == if bv {
            fa
        } else {
            fb
        },
        fa.len() == w,
        fb.len() == w,
        k <= w,
        forall|i: int| 0 <= i < w ==> #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]),
        forall|i: int| 0 <= i < w ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
    ensures
        match eval_src(br, se, sls) {
            Err(kk) => k > 0 ==> run(ite_binds(c, fa, fb, k), env, l2) == Err::<Seq<Value>, ErrKind>(kk),
            Ok(v) => run(ite_binds(c, fa, fb, k), env, l2) matches Ok(lk) && lk.len() == d + k && prefix(l2, lk)
                && forall|i: int|
                0 <= i < k ==> #[trigger] lk[d + i] == slot_vals(f[i], env, lk.take(d + i))[i] && models(
                    slot_vals(f[i], env, lk.take(d + i)),
                    v,
                    t,
                    se.enums,
                ),
        },
    decreases k,
{
    if k == 0 {
        assert(ite_binds(c, fa, fb, 0) =~= Seq::<Expr>::empty());
        lemma_prefix_refl(l2);
    } else {
        let j = (k - 1) as nat;
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, j, cx, sc, t, env, se, l2, sls);
        let x = ite_s(c, fa[j as int][j as int], fb[j as int][j as int]);
        assert(ite_binds(c, fa, fb, k) =~= ite_binds(c, fa, fb, j).push(x));
        lemma_run_push(ite_binds(c, fa, fb, j), x, env, l2);
        let r = run(ite_binds(c, fa, fb, j), env, l2);
        if r is Ok {
            let lj = r->Ok_0;
            lemma_run_len(ite_binds(c, fa, fb, j), env, l2);
            lemma_weaken(c, env, l2, lj);
            lemma_ctx_weaken(cx, sc, env, se, l2, lj, sls);
            assert(closed_slots(br, cx, sc, (d + j) as nat, t, f[j as int]));
            assert(ctx_ok(cx, sc, env, se, lj, sls));
            assert(j < f[j as int].len());
            match eval_src(br, se, sls) {
                Ok(v) => {
                    let val = eval_l(f[j as int][j as int], env, lj)->Ok_0;
                    let lk = lj.push(val);
                    assert(lk.take((d + j) as int) =~= lj);
                    assert forall|i: int| 0 <= i < k implies #[trigger] lk[d + i] == slot_vals(
                        f[i],
                        env,
                        lk.take(d + i),
                    )[i] && models(slot_vals(f[i], env, lk.take(d + i)), v, t, se.enums) by {
                        if i < j {
                            assert(lk.take((d + i) as int) =~= lj.take((d + i) as int));
                            assert(lk[d + i] == lj[d + i]);
                        }
                    }
                    lemma_prefix_trans(l2, lj, lk);
                },
                Err(_) => {},
            }
        }
    }
}

/// 枝が束縛を持つ条件式の、1つの環境での評価。
proof fn lemma_ite_bound_at(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        result_ok(eval_src(e, se, sls), run(fresh(b0, b3), env, ls), out, env, t, se.enums),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    let d = b2.depth_s();
    let w = xs.len();
    lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
    lemma_extends_trans(b1, b2, b3);
    lemma_run_fresh(b0, b1, b3, env, ls);
    if let Ok(v) = eval_src(*p, se, sls) {
        let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
        lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
        let bv = v->Bool_0;
        lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
        lemma_run_fresh(b1, b2, b3, env, l1);
        lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
        assert(fresh(b2, b3) =~= ite_binds(c, fa, fb, w));
        let br = if bv {
            *a
        } else {
            *b
        };
        let f = if bv {
            fa
        } else {
            fb
        };
        assert forall|i: int| 0 <= i < w implies #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]) by {
            if bv {
                assert(closed_slots(*a, cx, sc, (d + i) as nat, t, fa[i]));
            } else {
                assert(closed_slots(*b, cx, sc, (d + i) as nat, t, fb[i]));
            }
        }
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, w, cx, sc, t, env, se, l2, sls);
        if bv {
            lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
        } else {
            lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
        }
        if let Ok(vv) = eval_src(br, se, sls) {
            let lw = run(ite_binds(c, fa, fb, w), env, l2)->Ok_0;
            if bv {
                let la = run(fresh(ba0, ba1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(xs, env, la), vv, t, se.enums);
            } else {
                let lb = run(fresh(bb0, bb1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(ys, env, lb), vv, t, se.enums);
            }
            assert(b3.wf());
            lemma_ite_out(f, out, d, w, vv, t, env, lw, se.enums);
        }
    }
}

/// スロットごとの束縛を評価し終えたときの、条件式のスロットの値。
proof fn lemma_ite_out(
    f: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    d: nat,
    w: nat,
    vv: SVal,
    t: XTy,
    env: Env,
    lw: Seq<Value>,
    enums: Seq<i64>,
)
    requires
        w > 0,
        w == xwidth(t, enums),
        lw.len() == d + w,
        d + w < usize::MAX,
        out == Seq::new(w, |i: int| Expr::Local((d + i) as usize)),
        forall|i: int|
            0 <= i < w ==> #[trigger] lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i] && models(
                slot_vals(f[i], env, lw.take(d + i)),
                vv,
                t,
                enums,
            ),
    ensures
        denotes(out, env, lw, vv, t, enums),
{
    let vs = Seq::new(w, |i: int| slot_vals(f[i], env, lw.take(d + i)));
    let r = slot_vals(out, env, lw);
    assert forall|i: int| 0 <= i < w implies #[trigger] models(vs[i], vv, t, enums) && vs[i].len() == w by {
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
        lemma_models_len(vs[i], vv, t, enums);
    }
    assert forall|i: int| 0 <= i < w implies #[trigger] r[i] == vs[i][i] by {
        assert(out[i] == Expr::Local((d + i) as usize));
        assert(((d + i) as usize) as int == d + i);
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
    }
    lemma_models_diag(vs, r, vv, t, enums);
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], lw.len()) && eval_l(
        out[j],
        env,
        lw,
    ) is Ok by {
        assert(out[j] == Expr::Local((d + j) as usize));
    }
}

/// 枝が束縛を持つ条件式の下ろし。
proof fn lemma_ite_bound(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_ite_bound_at(e, cx, sc, b0, b1, b2, b3, c0, c, ba0, ba1, bb0, bb1, t, xs, ys, fa, fb, out, env, se, ls, sls);
    }
}

/// 整数の演算と比較の下ろし。算術は束縛し、比較はそのままスロットにする。
proof fn lemma_bin(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    x: Expr,
    y: Expr,
    t: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Bin(op, a, b) && lowers(*a, cx, sc, b0, b1, XTy::Int, seq![x]) && lowers(
            *b,
            cx,
            sc,
            b1,
            b2,
            XTy::Int,
            seq![y],
        ) && if op is Add || op is Sub || op is Mul || op is Div || op is Mod {
            t == XTy::Int && b3.binds@ == b2.binds@.push(Expr::Bin(op, Box::new(x), Box::new(y))) && out == seq![
                Expr::Local(b2.depth_s() as usize),
            ]
        } else {
            (op is Lt || op is Le || op is Gt || op is Ge) && t == XTy::Bool && b3 == b2 && out == seq![
                Expr::Bin(op, Box::new(x), Box::new(y)),
            ]
        },
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    let op = e->Bin_0;
    let a = e->Bin_1;
    let b = e->Bin_2;
    let z = Expr::Bin(op, Box::new(x), Box::new(y));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_pair(*a, *b, cx, sc, b0, b1, b2, XTy::Int, seq![x], XTy::Int, seq![y], env, se, ls, sls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(va) = eval_src(*a, se, sls) {
            if let Ok(vb) = eval_src(*b, se, sls) {
                let l = run(fresh(b0, b2), env, ls)->Ok_0;
                lemma_denotes_one(x, env, l, va, XTy::Int, se.enums);
                lemma_denotes_one(y, env, l, vb, XTy::Int, se.enums);
                if t == XTy::Bool {
                    lemma_fresh_refl(b2);
                    assert(fresh(b2, b3) =~= Seq::<Expr>::empty());
                    lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
                } else {
                    lemma_run_one(b2, b3, z, env, l);
                    if let Ok(r) = eval_l(z, env, l) {
                        lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Int, se.enums);
                    }
                }
            }
        }
    }
}

/// 否定の下ろし。
proof fn lemma_not(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, x: Expr)
    requires
        e matches TExpr::Not(a) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![x]),
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, seq![Expr::Not(Box::new(x))]),
{
    let a = e->Not_0;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        seq![Expr::Not(Box::new(x))],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![x], env, se, ls, sls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(x, env, l, v, XTy::Bool, se.enums);
            let z = Expr::Not(Box::new(x));
            lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
        }
    }
}

/// 含意の下ろし。前件はスロットにし、後件は単独に評価する式にして、全体を束縛する。
proof fn lemma_implies(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, p: Expr, q: Expr)
    requires
        e matches TExpr::Implies(a, b) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![p]) && closed_lowers(
            *b,
            cx,
            sc,
            b1.depth_s(),
            XTy::Bool,
            q,
        ),
        extends(b0, b1),
        extends(b1, b2),
        b2.binds@ == b1.binds@.push(Expr::Implies(Box::new(p), Box::new(q))),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let a = e->Implies_0;
    let b = e->Implies_1;
    let z = Expr::Implies(Box::new(p), Box::new(q));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![p], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(p, env, l, v, XTy::Bool, se.enums);
            lemma_run_one(b1, b2, z, env, l);
            assert(ctx_ok(cx, sc, env, se, l, sls));
            if let Ok(r) = eval_l(z, env, l) {
                lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
            }
        }
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

/// 式の列を順に下ろすと、`b0` から `b1` までの束縛とスロットの列 `out` になり、値の列を表す。
pub open spec fn lowers_seq(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, out: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_seq(es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(vs) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && clean(out, env, l) && models_seq(slot_vals(out, env, l), vs, ts, se.enums),
        }
}

proof fn lemma_seq_base(cx: LowerCtx, sc: Seq<Bound>, b: Block)
    ensures
        lowers_seq(Seq::empty(), cx, sc, b, b, Seq::empty(), Seq::empty()),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_seq(Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(vs) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && clean(Seq::empty(), env, l) && models_seq(slot_vals(Seq::empty(), env, l), vs, Seq::empty(), se.enums),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        assert(slot_vals(Seq::empty(), env, ls) =~= Seq::<Value>::empty());
    }
}

/// 列の最後の式を下ろして、スロットの列の後ろに加える。
proof fn lemma_seq_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    ts: Seq<XTy>,
    out: Seq<Expr>,
    t: XTy,
    s: Seq<Expr>,
)
    requires
        es.len() > 0,
        lowers_seq(es.drop_last(), cx, sc, b0, b1, ts, out),
        lowers(es.last(), cx, sc, b1, b2, t, s),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers_seq(es, cx, sc, b0, b2, ts.push(t), out + s),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_seq(es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(vs) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && clean(out + s, env, l) && models_seq(slot_vals(out + s, env, l), vs, ts.push(t), se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(vs) = eval_seq(es.drop_last(), se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_one(es.last(), cx, sc, b1, b2, t, s, env, se, l1, sls);
            if let Ok(v) = eval_src(es.last(), se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_prefix_trans(ls, l1, l2);
                lemma_clean_weaken(out, env, l1, l2);
                lemma_clean_concat(out, s, env, l2);
                let a = slot_vals(out, env, l2);
                let c = slot_vals(s, env, l2);
                lemma_models_len(c, v, t, se.enums);
                let ts2 = ts.push(t);
                assert(ts2.drop_last() =~= ts);
                assert((a + c).take(a.len() as int) =~= a);
                assert((a + c).skip(a.len() as int) =~= c);
                assert(vs.push(v).drop_last() =~= vs);
                lemma_models_seq_len(a, vs, ts, se.enums);
            }
        }
    }
}

/// 組と構造体の下ろし。
proof fn lemma_tuple_done(e: TExpr, es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, out: Seq<Expr>)
    requires
        (e is Tuple && e->Tuple_0@ == es) || (e is Record && e->Record_1@ == es),
        lowers_seq(es, cx, sc, b0, b1, ts, out),
    ensures
        e is Tuple ==> lowers(e, cx, sc, b0, b1, XTy::Tuple(ts), out),
        e is Record ==> lowers(e, cx, sc, b0, b1, XTy::Record(e->Record_0@, ts), out),
{
}

/// 組の要素と構造体のフィールドの下ろし。
proof fn lemma_part(e: TExpr, a: TExpr, i: usize, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, ts: Seq<XTy>, slots: Seq<Expr>, x: Seq<Expr>)
    requires
        (e == TExpr::Nth(Box::new(a), i) && lowers(a, cx, sc, b0, b1, XTy::Tuple(ts), slots)) || (exists|nm: usize, names: Seq<usize>|
            e == TExpr::Field(Box::new(a), nm, i) && lowers(a, cx, sc, b0, b1, XTy::Record(names, ts), slots)),
        extends(b0, b1),
        i < ts.len(),
        split_ok(x, slots, ts, i as int, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b1, ts[i as int], x),
{
    let xt = if e is Nth {
        XTy::Tuple(ts)
    } else {
        let (nm, names) = choose|nm: usize, names: Seq<usize>| e == TExpr::Field(Box::new(a), nm, i) && lowers(a, cx, sc, b0, b1, XTy::Record(names, ts), slots);
        XTy::Record(names, ts)
    };
    assert(lowers(a, cx, sc, b0, b1, xt, slots));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        x,
        env,
        ts[i as int],
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, xt, slots, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_part(slots, env, l, v->Tuple_0, ts, i as int, se.enums);
        }
    }
}

/// 空のOptionの下ろし。
proof fn lemma_none(e: TExpr, st: STy, cx: LowerCtx, sc: Seq<Bound>, b: Block, out: Seq<Expr>)
    requires
        e is None && sty(e->None_0) == st,
        out == seq![bool_lit(false)] + lits(enc(default_val(st, cx.enums@), st, cx.enums@)),
    ensures
        lowers(e, cx, sc, b, b, XTy::Option(Box::new(to_xty(st))), out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b, b), env, ls),
        out,
        env,
        XTy::Option(Box::new(to_xty(st))),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        let dv = enc(default_val(st, enums), st, enums);
        lemma_lits(dv, env, ls);
        lemma_lits(seq![Value::Bool(false)], env, ls);
        assert(lits(seq![Value::Bool(false)]) =~= seq![bool_lit(false)]);
        lemma_clean_concat(seq![bool_lit(false)], lits(dv), env, ls);
        lemma_default_len(st, enums);
        lemma_xwidth_of(st, enums);
    }
}

/// 値のあるOptionの下ろし。
proof fn lemma_some(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, t: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        e == TExpr::Some(Box::new(a)),
        lowers(a, cx, sc, b0, b1, t, s),
        extends(b0, b1),
        out == seq![bool_lit(true)] + s,
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Option(Box::new(t)), out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        XTy::Option(Box::new(t)),
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, t, s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_lits(seq![Value::Bool(true)], env, l);
            assert(lits(seq![Value::Bool(true)]) =~= seq![bool_lit(true)]);
            lemma_clean_concat(seq![bool_lit(true)], s, env, l);
            lemma_models_len(slot_vals(s, env, l), v, t, se.enums);
            assert(slot_vals(out, env, l).drop_first() =~= slot_vals(s, env, l));
        }
    }
}

/// Optionの有無の下ろし。
proof fn lemma_is_some(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, t: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        (e == TExpr::IsSome(Box::new(a)) && out == seq![s[0]]) || (e == TExpr::IsNone(Box::new(a)) && out == seq![Expr::Not(Box::new(s[0]))]),
        lowers(a, cx, sc, b0, b1, t, s),
        t is Option,
        s.len() > 0,
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, t, s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let sv = slot_vals(s, env, l);
            assert(sv[0] == eval_l(s[0], env, l)->Ok_0);
            assert(pure_below(s[0], l.len()) && eval_l(s[0], env, l) is Ok);
            let b = v is Some;
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(b)));
            lemma_one_denotes(out[0], env, l, eval_l(out[0], env, l)->Ok_0, XTy::Bool, se.enums);
            assert(seq![out[0]] =~= out);
        }
    }
}

/// Optionの中身の取り出しの下ろし。空なら検査の束縛が失敗する。
proof fn lemma_unwrap(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, x: XTy, s: Seq<Expr>, out: Seq<Expr>)
    requires
        e == TExpr::Unwrap(Box::new(a)),
        lowers(a, cx, sc, b0, b1, XTy::Option(Box::new(x)), s),
        extends(b0, b1),
        extends(b1, b2),
        s.len() > 0,
        (s[0] == bool_lit(true) && b2.binds@ == b1.binds@) || b2.binds@ == b1.binds@.push(
            ite_s(s[0], bool_lit(true), Expr::Fail(Type::Bool, FAIL_NONE)),
        ),
        out == s.subrange(1, s.len() as int),
    ensures
        lowers(e, cx, sc, b0, b2, x, out),
{
    let c = ite_s(s[0], bool_lit(true), Expr::Fail(Type::Bool, FAIL_NONE));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        x,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, XTy::Option(Box::new(x)), s, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let sv = slot_vals(s, env, l);
            assert(sv[0] == eval_l(s[0], env, l)->Ok_0);
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(v is Some)));
            lemma_clean_sub(s, env, l, 1, s.len() as int);
            assert(slot_vals(out, env, l) =~= sv.drop_first());
            assert(eval_l(bool_lit(true), env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(eval_l(Expr::Fail(Type::Bool, FAIL_NONE), env, l) == Err::<Value, ErrKind>(ErrKind::Failed(FAIL_NONE)));
            if b2.binds@ == b1.binds@ {
                lemma_fresh_refl(b1);
                assert(fresh(b1, b2) =~= Seq::<Expr>::empty());
                assert(run(Seq::<Expr>::empty(), env, l) == Ok::<Seq<Value>, ErrKind>(l));
                assert(v is Some);
            } else {
                lemma_run_one(b1, b2, c, env, l);
                if v is Some {
                    assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
                    let l2 = l.push(Value::Bool(true));
                    assert(prefix(l, l2));
                    lemma_clean_weaken(out, env, l, l2);
                } else {
                    assert(eval_l(c, env, l) == Err::<Value, ErrKind>(ErrKind::Failed(FAIL_NONE)));
                }
            }
        }
    }
}

/// 検査の束縛。条件が真なら真を加え、偽なら `code` で失敗する。
pub open spec fn checked(b0: Block, b1: Block, cond: Expr, code: i64) -> bool {
    ||| cond == bool_lit(true) && b1.binds@ == b0.binds@
    ||| b1.binds@ == b0.binds@.push(ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code)))
}

proof fn lemma_check(b0: Block, b1: Block, cond: Expr, code: i64, env: Env, l: Seq<Value>, c: bool)
    requires
        checked(b0, b1, cond, code),
        extends(b0, b1),
        l.len() == b0.depth_s(),
        eval_l(cond, env, l) == Ok::<Value, ErrKind>(Value::Bool(c)),
    ensures
        c ==> (run(fresh(b0, b1), env, l) matches Ok(l2) && l2.len() == b1.depth_s() && prefix(l, l2)),
        !c ==> run(fresh(b0, b1), env, l) == Err::<Seq<Value>, ErrKind>(ErrKind::Failed(code)),
{
    lemma_run_fresh_ok(b0, b1, env, l);
    let x = ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code));
    assert(eval_l(bool_lit(true), env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
    assert(eval_l(Expr::Fail(Type::Bool, code), env, l) == Err::<Value, ErrKind>(ErrKind::Failed(code)));
    if cond == bool_lit(true) && b1.binds@ == b0.binds@ {
        lemma_fresh_refl(b0);
        assert(fresh(b0, b1) =~= Seq::<Expr>::empty());
        assert(run(Seq::<Expr>::empty(), env, l) == Ok::<Seq<Value>, ErrKind>(l));
    } else {
        lemma_run_one(b0, b1, x, env, l);
    }
}

/// Listの式を下ろした結果を、環境ごとに取り出す。
proof fn lemma_list_env(
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    env: Env,
    se: SEnv,
    l0: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        lowers(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        ctx_ok(cx, sc, env, se, l0, sls),
        l0.len() == b0.depth_s(),
    ensures
        match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b1), env, l0) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => v is List && (run(fresh(b0, b1), env, l0) matches Ok(l) && l.len() == b1.depth_s() && prefix(l0, l)
                && ctx_ok(cx, sc, env, se, l, sls) && v->List_0.len() <= max && list_items_member(v->List_0, st, se.enums)
                && pure_below(len, l.len()) && eval_l(len, env, l) == Ok::<Value, ErrKind>(
                Value::Int(v->List_0.len() as i64),
            ) && rows_at(rows, pad_vals(v->List_0, st, max as nat, se.enums), env, l)),
        },
{
    lemma_one(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls, env, se, l0, sls);
    if let Ok(v) = eval_src(a, se, sls) {
        let l = run(fresh(b0, b1), env, l0)->Ok_0;
        assert(member(v, STy::List(Box::new(st), max), se.enums));
        lemma_list_parts(ls, len, rows, env, l, v->List_0, st, max, se.enums);
    }
}

/// Listの添字の参照。添字が範囲外なら `FAIL_INDEX` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_at(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    x: Expr,
    y: Expr,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    cond: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::At(a, ix) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls) && lowers(
            *ix,
            cx,
            sc,
            b1,
            b2,
            XTy::Int,
            seq![x],
        ),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        added(b2, b3, x, y),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        cond == and_s(
            Expr::Bin(BinOp::Ge, Box::new(y), Box::new(Expr::Const(Value::Int(0)))),
            Expr::Bin(BinOp::Lt, Box::new(y), Box::new(len)),
        ),
        checked(b3, b4, cond, FAIL_INDEX),
        rows.len() > 0 ==> select_ok(rows, y, out),
    ensures
        lowers(e, cx, sc, b0, b4, to_xty(st), out),
{
    let a = e->At_0;
    let ix = e->At_1;
    let xt = XTy::List(Box::new(st), max);
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_run_fresh(b0, b3, b4, env, l0);
        lemma_extends_trans(b0, b1, b2);
        lemma_extends_trans(b0, b2, b3);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            lemma_one(*ix, cx, sc, b1, b2, XTy::Int, seq![x], env, se, l1, sls);
            if let Ok(vb) = eval_src(*ix, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                lemma_denotes_one(x, env, l2, vb, XTy::Int, enums);
                let n = vb->Int_0;
                lemma_added(b2, b3, x, y, env, l2, Value::Int(n));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_weaken(len, env, l1, l3);
                lemma_pure_mono(len, l1.len(), l3.len());
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                let g0 = Expr::Bin(BinOp::Ge, Box::new(y), Box::new(Expr::Const(Value::Int(0))));
                let g1 = Expr::Bin(BinOp::Lt, Box::new(y), Box::new(len));
                assert(eval_l(Expr::Const(Value::Int(0)), env, l3) == Ok::<Value, ErrKind>(Value::Int(0)));
                assert(eval_l(g0, env, l3) == Ok::<Value, ErrKind>(Value::Bool(n >= 0)));
                assert(eval_l(g1, env, l3) == Ok::<Value, ErrKind>(Value::Bool(n < items.len() as i64)));
                lemma_and(g0, g1, env, l3, n >= 0, n < items.len() as i64);
                let c = 0 <= n < items.len();
                lemma_check(b3, b4, cond, FAIL_INDEX, env, l3, c);
                if c {
                    let l4 = run(fresh(b3, b4), env, l3)->Ok_0;
                    lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l3, l4);
                    lemma_weaken(y, env, l3, l4);
                    lemma_pure_mono(y, l3.len(), l4.len());
                    assert(at_rank(y, env, l4, n));
                    lemma_select(rows, y, out, pad_vals(items, st, max as nat, enums), env, l4, n);
                    lemma_items_member(items, st, enums, n as int);
                    lemma_models_enc(items[n as int], st, enums);
                }
            }
        }
    }
}

/// Listの先頭。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_first(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::First(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        rows.len() > 0 ==> out == rows[0],
    ensures
        lowers(e, cx, sc, b0, b2, to_xty(st), out),
{
    let a = e->First_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(eval_l(Expr::Const(Value::Int(0)), env, l1) == Ok::<Value, ErrKind>(Value::Int(0)));
            assert(eval_l(cond, env, l1) == Ok::<Value, ErrKind>(Value::Bool(items.len() as i64 > 0)));
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l2);
                assert(clean(rows[0], env, l2));
                lemma_items_member(items, st, enums, 0);
                lemma_models_enc(items[0], st, enums);
            }
        }
    }
}

/// Listの末尾。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_last(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    i: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Last(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        i == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        rows.len() > 0 ==> select_ok(rows, i, out),
    ensures
        lowers(e, cx, sc, b0, b3, to_xty(st), out),
{
    let a = e->Last_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        out,
        env,
        to_xty(st),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(eval_l(Expr::Const(Value::Int(0)), env, l1) == Ok::<Value, ErrKind>(Value::Int(0)));
            assert(eval_l(cond, env, l1) == Ok::<Value, ErrKind>(Value::Bool(items.len() as i64 > 0)));
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                let n = (items.len() - 1) as i64;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                assert(eval_l(Expr::Const(Value::Int(1)), env, l2) == Ok::<Value, ErrKind>(Value::Int(1)));
                assert(eval_l(d, env, l2) == Ok::<Value, ErrKind>(Value::Int(n)));
                assert(pure_below(Expr::Const(Value::Int(1)), l2.len()));
                assert(pure_below(d, l2.len()));
                lemma_added(b2, b3, d, i, env, l2, Value::Int(n));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                assert(at_rank(i, env, l3, n));
                lemma_select(rows, i, out, pad_vals(items, st, max as nat, enums), env, l3, n);
                lemma_items_member(items, st, enums, n as int);
                lemma_models_enc(items[n as int], st, enums);
            }
        }
    }
}

pub open spec fn defaults_s(st: STy, enums: Seq<i64>) -> Seq<Expr> {
    lits(enc(default_val(st, enums), st, enums))
}

/// 長さの式が整数 `n` を表すなら、`n` を足し引きした式も表す。
proof fn lemma_len_step(len: Expr, op: BinOp, k: i64, env: Env, l: Seq<Value>, n: i64)
    requires
        pure_below(len, l.len()),
        eval_l(len, env, l) == Ok::<Value, ErrKind>(Value::Int(n)),
        0 <= n <= 0x7fff_ffff,
        0 <= k <= 1,
        op is Add || op is Sub,
    ensures
        pure_below(Expr::Bin(op, Box::new(len), Box::new(Expr::Const(Value::Int(k)))), l.len()),
        eval_l(Expr::Bin(op, Box::new(len), Box::new(Expr::Const(Value::Int(k)))), env, l) == Ok::<Value, ErrKind>(
            Value::Int(if op is Add { (n + k) as i64 } else { (n - k) as i64 }),
        ),
{
    assert(at_rank(len, env, l, n));
    lemma_bin_const(op, len, k, env, l, n);
}

/// `contains` の `q` 番目の項。`q` が長さより小さく、`q` 番目の要素が値に等しい。
pub open spec fn hit_at(h: Expr, row: Seq<Expr>, xv: Seq<Expr>, len: Expr, c: Expr, q: int, t: XTy, enums: Seq<i64>) -> bool {
    &&& h == and_s(Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(q as i64)))), c)
    &&& eq_ok(t, row, xv, c, enums)
}

/// Listが値を含むかは、長さより前のどれかの要素が値に等しいことである。
#[verifier::spinoff_prover]
proof fn lemma_list_contains(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    t: XTy,
    xv: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    hits: Seq<Expr>,
    cs: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::ListContains(a, x) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls) && lowers(
            *x,
            cx,
            sc,
            b1,
            b2,
            t,
            xv,
        ),
        extends(b0, b1),
        extends(b1, b2),
        t == to_xty(st),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        hits.len() == rows.len(),
        cs.len() == rows.len(),
        forall|q: int| 0 <= q < rows.len() ==> #[trigger] hit_at(hits[q], rows[q], xv, len, cs[q], q, t, cx.enums@),
        out == seq![tree_s(hits, bool_lit(false), Join::Or)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let a = e->ListContains_0;
    let x = e->ListContains_1;
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, l0),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            lemma_one(*x, cx, sc, b1, b2, t, xv, env, se, l1, sls);
            if let Ok(y) = eval_src(*x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                let n = l2.len();
                let vals = pad_vals(items, st, max as nat, enums);
                lemma_rows_weaken(rows, vals, env, l1, l2);
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), n);
                lemma_clean_pure(xv, env, l2);
                assert(at_rank(len, env, l2, m));
                assert forall|q: int| 0 <= q < hits.len() implies pure_below(#[trigger] hits[q], n) && eval_l(
                    hits[q],
                    env,
                    l2,
                ) == Ok::<Value, ErrKind>(Value::Bool(q < items.len() && items[q] == y)) by {
                    assert(hit_at(hits[q], rows[q], xv, len, cs[q], q, t, enums));
                    lemma_clean_pure(rows[q], env, l2);
                    assert(pure_below(cs[q], n));
                    let g = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(q as i64))));
                    lemma_bin_const(BinOp::Gt, len, q as i64, env, l2, m);
                    if q < items.len() {
                        lemma_items_member(items, st, enums, q);
                        assert(pad(items, st, max as nat, enums)[q] == items[q]);
                        lemma_models_enc(items[q], st, enums);
                        assert(denotes(rows[q], env, l2, items[q], t, enums));
                        assert(eval_l(cs[q], env, l2) == Ok::<Value, ErrKind>(Value::Bool(items[q] == y)));
                        lemma_and(g, cs[q], env, l2, true, items[q] == y);
                    } else if cs[q] == bool_lit(true) {
                        assert(hits[q] == g);
                    } else {
                        assert(hits[q] == Expr::And(Box::new(g), Box::new(cs[q])));
                    }
                }
                assert(all_pure(hits, n));
                lemma_tree_pure(hits, bool_lit(false), Join::Or, n);
                lemma_any_of(hits, env, l2);
                if items.contains(y) {
                    let k = choose|k: int| 0 <= k < items.len() && items[k] == y;
                    assert(eval_l(hits[k], env, l2) == Ok::<Value, ErrKind>(Value::Bool(true)));
                }
                if any_true(hits, env, l2) {
                    let k = choose|k: int| 0 <= k < hits.len() && #[trigger] eval_l(hits[k], env, l2) == Ok::<Value, ErrKind>(
                        Value::Bool(true),
                    );
                    assert(items[k] == y);
                }
                lemma_one_denotes(out[0], env, l2, Value::Bool(items.contains(y)), XTy::Bool, enums);
                assert(out == seq![out[0]]);
            }
        }
    }
}

/// Listの末尾に要素を加える。要素が型に属さなければ `FAIL_NOT_IN_DOMAIN`、満杯なら `FAIL_FULL` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_push(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    xs: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Push(t, n, a, x) && sty(t) == st && n == max && lowers(
            *a,
            cx,
            sc,
            b0,
            b1,
            XTy::List(Box::new(st), max),
            ls,
        ) && elem_lowers(*x, cx, sc, b1, b2, st, xs),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b2, b3, Expr::Bin(BinOp::Lt, Box::new(len), Box::new(Expr::Const(Value::Int(max as i64)))), FAIL_FULL),
        new_len == Expr::Local(b3.depth_s() as usize),
        b4.binds@ == b3.binds@.push(Expr::Bin(BinOp::Add, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        ite_rows_ok(out, rows, len, xs),
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b4, XTy::List(Box::new(st), max), r),
{
    let a = e->Push_2;
    let x = e->Push_3;
    let cond = Expr::Bin(BinOp::Lt, Box::new(len), Box::new(Expr::Const(Value::Int(max as i64))));
    let d = Expr::Bin(BinOp::Add, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_run_fresh(b0, b3, b4, env, l0);
        lemma_extends_trans(b0, b1, b2);
        lemma_extends_trans(b0, b2, b3);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(y) = eval_src(*x, se, sls) {
                if member(y, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_weaken(len, env, l1, l2);
                    lemma_pure_mono(len, l1.len(), l2.len());
                    lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l2);
                    assert(at_rank(len, env, l2, m));
                    lemma_bin_const(BinOp::Lt, len, max as i64, env, l2, m);
                    lemma_check(b2, b3, cond, FAIL_FULL, env, l2, items.len() < max);
                    if items.len() < max {
                        let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                        lemma_weaken(len, env, l2, l3);
                        lemma_pure_mono(len, l2.len(), l3.len());
                        lemma_len_step(len, BinOp::Add, 1, env, l3, m);
                        lemma_added(b3, b4, d, new_len, env, l3, Value::Int((m + 1) as i64));
                        let l4 = run(fresh(b3, b4), env, l3)->Ok_0;
                        lemma_prefix_trans(l2, l3, l4);
                        lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l2, l4);
                        lemma_clean_weaken(xs, env, l2, l4);
                        lemma_weaken(len, env, l3, l4);
                        lemma_pure_mono(len, l3.len(), l4.len());
                        lemma_ite_rows(out, rows, len, xs, pad_vals(items, st, max as nat, enums), enc(y, st, enums), env, l4, m);
                        let items2 = items.push(y);
                        assert(items2.drop_last() =~= items);
                        assert(list_items_member(items2, st, enums));
                        assert(pad_vals(items2, st, max as nat, enums) =~= Seq::new(
                            rows.len(),
                            |p: int| if p == m { enc(y, st, enums) } else { pad_vals(items, st, max as nat, enums)[p] },
                        ));
                        lemma_list_join(new_len, out, env, l4, items2, st, max, enums);
                    }
                }
            }
        }
    }
}

/// Listの末尾を除く。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_pop(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    defs: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Pop(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        new_len == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        defs == defaults_s(st, cx.enums@),
        ite_rows_ok(out, rows, new_len, defs),
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b3, XTy::List(Box::new(st), max), r),
{
    let a = e->Pop_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(at_rank(len, env, l1, m));
            lemma_bin_const(BinOp::Gt, len, 0, env, l1, m);
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                lemma_len_step(len, BinOp::Sub, 1, env, l2, m);
                lemma_added(b2, b3, d, new_len, env, l2, Value::Int((m - 1) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                lemma_rows_weaken(rows, pad_vals(items, st, max as nat, enums), env, l1, l3);
                let dv = enc(default_val(st, enums), st, enums);
                lemma_lits(dv, env, l3);
                lemma_ite_rows(out, rows, new_len, defs, pad_vals(items, st, max as nat, enums), dv, env, l3, (m - 1) as i64);
                let items2 = items.drop_last();
                assert(list_items_member(items2, st, enums));
                assert(pad_vals(items2, st, max as nat, enums) =~= Seq::new(
                    rows.len(),
                    |p: int| if p == m - 1 { dv } else { pad_vals(items, st, max as nat, enums)[p] },
                ));
                lemma_list_join(new_len, out, env, l3, items2, st, max, enums);
            }
        }
    }
}

/// Listの先頭を除く。空なら `FAIL_EMPTY` で失敗する。
#[verifier::spinoff_prover]
proof fn lemma_shift(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    st: STy,
    max: usize,
    ls: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    new_len: Expr,
    defs: Seq<Expr>,
    out: Seq<Seq<Expr>>,
    r: Seq<Expr>,
)
    requires
        e matches TExpr::Shift(a) && lowers(*a, cx, sc, b0, b1, XTy::List(Box::new(st), max), ls),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        max <= 0x7fff_ffff,
        parts_ok(ls, len, rows, width(st, cx.enums@), max as nat),
        checked(b1, b2, Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0)))), FAIL_EMPTY),
        new_len == Expr::Local(b2.depth_s() as usize),
        b3.binds@ == b2.binds@.push(Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))))),
        defs == defaults_s(st, cx.enums@),
        rows.len() > 0 ==> out.len() == rows.len() && out[rows.len() - 1] == defs && forall|q: int|
            0 <= q < rows.len() - 1 ==> #[trigger] out[q] == rows[q + 1],
        r == seq![new_len] + flat(out),
    ensures
        lowers(e, cx, sc, b0, b3, XTy::List(Box::new(st), max), r),
{
    let a = e->Shift_0;
    let cond = Expr::Bin(BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(0))));
    let d = Expr::Bin(BinOp::Sub, Box::new(len), Box::new(Expr::Const(Value::Int(1))));
    assert forall|env: Env, se: SEnv, l0: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, l0, sls) && l0.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, l0),
        r,
        env,
        XTy::List(Box::new(st), max),
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_list_env(*a, cx, sc, b0, b1, st, max, ls, len, rows, env, se, l0, sls);
        lemma_run_fresh(b0, b1, b2, env, l0);
        lemma_run_fresh(b0, b2, b3, env, l0);
        lemma_extends_trans(b0, b1, b2);
        if let Ok(va) = eval_src(*a, se, sls) {
            let items = va->List_0;
            let m = items.len() as i64;
            let l1 = run(fresh(b0, b1), env, l0)->Ok_0;
            assert(at_rank(len, env, l1, m));
            lemma_bin_const(BinOp::Gt, len, 0, env, l1, m);
            lemma_check(b1, b2, cond, FAIL_EMPTY, env, l1, items.len() > 0);
            if items.len() > 0 {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_weaken(len, env, l1, l2);
                lemma_pure_mono(len, l1.len(), l2.len());
                lemma_len_step(len, BinOp::Sub, 1, env, l2, m);
                lemma_added(b2, b3, d, new_len, env, l2, Value::Int((m - 1) as i64));
                let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                lemma_prefix_trans(l1, l2, l3);
                let vals = pad_vals(items, st, max as nat, enums);
                lemma_rows_weaken(rows, vals, env, l1, l3);
                let dv = enc(default_val(st, enums), st, enums);
                lemma_lits(dv, env, l3);
                let items2 = items.drop_first();
                let nv = pad_vals(items2, st, max as nat, enums);
                assert(nv =~= Seq::new(rows.len(), |p: int| if p < rows.len() - 1 { vals[p + 1] } else { dv }));
                assert forall|p: int| 0 <= p < out.len() implies clean(#[trigger] out[p], env, l3) && slot_vals(out[p], env, l3)
                    == nv[p] by {
                    if p < rows.len() - 1 {
                        assert(out[p] == rows[p + 1]);
                    }
                }
                assert(list_items_member(items2, st, enums)) by {
                    lemma_items_drop_first(items, st, enums);
                }
                lemma_list_join(new_len, out, env, l3, items2, st, max, enums);
            }
        }
    }
}

proof fn lemma_items_drop_first(items: Seq<SVal>, st: STy, enums: Seq<i64>)
    requires
        list_items_member(items, st, enums),
        items.len() > 0,
    ensures
        list_items_member(items.drop_first(), st, enums),
    decreases items.len(),
{
    if items.len() > 1 {
        lemma_items_drop_first(items.drop_last(), st, enums);
        assert(items.drop_first().drop_last() =~= items.drop_last().drop_first());
        assert(items.drop_first().last() == items.last());
    } else {
        assert(items.drop_first() =~= Seq::<SVal>::empty());
    }
}

/// Listのリテラルの要素を順に下ろすと、`out` は長さのスロットと要素のスロットの列を表す。
pub open spec fn listlit_ok(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, n: i64, out: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_elements(st, es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(items) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && items.len() == es.len() && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
                out,
                env,
                l,
            ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
        }
}

proof fn lemma_listlit_base(cx: LowerCtx, sc: Seq<Bound>, b: Block, st: STy, n: i64, out: Seq<Expr>)
    requires
        out == seq![Expr::Const(Value::Int(n))],
    ensures
        listlit_ok(Seq::empty(), cx, sc, b, b, st, n, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_elements(st, Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(items) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && items.len() == 0 && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
            out,
            env,
            l,
        ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        assert(out[0] == Expr::Const(Value::Int(n)));
        assert(slot_vals(out, env, ls) =~= seq![Value::Int(n)] + enc_items(Seq::empty(), st, se.enums));
    }
}

/// Listのリテラルに要素を1つ加える。
#[verifier::spinoff_prover]
proof fn lemma_listlit_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    n: i64,
    o1: Seq<Expr>,
    x: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        es.len() > 0,
        listlit_ok(es.drop_last(), cx, sc, b0, b1, st, n, o1),
        elem_lowers(es.last(), cx, sc, b1, b2, st, x),
        extends(b0, b1),
        extends(b1, b2),
        out == o1 + x,
    ensures
        listlit_ok(es, cx, sc, b0, b2, st, n, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_elements(st, es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(items) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && items.len() == es.len() && list_items_member(items, st, se.enums) && clean(out, env, l) && slot_vals(
            out,
            env,
            l,
        ) == seq![Value::Int(n)] + enc_items(items, st, se.enums),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(vs) = eval_elements(st, es.drop_last(), se, sls) {
            let enums = se.enums;
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(v) = eval_src(es.last(), se, sls) {
                if member(v, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_prefix_trans(ls, l1, l2);
                    lemma_clean_weaken(o1, env, l1, l2);
                    lemma_clean_concat(o1, x, env, l2);
                    let items = vs.push(v);
                    assert(items.drop_last() =~= vs);
                    assert(items.last() == v);
                    assert(enc_items(items, st, enums) == enc_items(vs, st, enums) + enc(v, st, enums));
                    assert(slot_vals(out, env, l2) =~= seq![Value::Int(n)] + enc_items(items, st, enums));
                }
            }
        }
    }
}

/// Listのリテラルの残りを既定値で埋める。
#[verifier::spinoff_prover]
proof fn lemma_listlit_done(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    o2: Seq<Expr>,
    dv: Seq<Value>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::ListLit(t, m, es) && sty(t) == st && m == max && es@.len() <= max && listlit_ok(
            es@,
            cx,
            sc,
            b0,
            b1,
            st,
            es@.len() as i64,
            o2,
        ) && out == o2 + lits(enc_repeat(dv, (max - es@.len()) as nat)),
        dv == enc(default_val(st, cx.enums@), st, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::List(Box::new(st), max), out),
{
    let es = e->ListLit_2@;
    let xt = XTy::List(Box::new(st), max);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        if let Ok(items) = eval_elements(st, es, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let tail = enc_repeat(dv, (max - es.len()) as nat);
            lemma_lits(tail, env, l);
            lemma_clean_concat(o2, lits(tail), env, l);
            let v = SVal::List(items);
            assert(member(v, STy::List(Box::new(st), max), enums));
            assert(slot_vals(out, env, l) == enc(v, STy::List(Box::new(st), max), enums));
        }
    }
}

/// Setのリテラルの要素を順に下ろすと、`bits` は印の列を表す。
pub open spec fn setlit_ok(es: Seq<TExpr>, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, bits: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_set_items(st, es, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(p) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && keys(st, se.enums) == Some(p.len()) && clean(bits, env, l) && slot_vals(bits, env, l) == Seq::new(
                p.len(),
                |j: int| Value::Bool(p[j]),
            ),
        }
}

proof fn lemma_setlit_base(cx: LowerCtx, sc: Seq<Bound>, b: Block, st: STy, bits: Seq<Expr>)
    requires
        keys(st, cx.enums@) is Some,
        bits == Seq::new(keys_or_zero(st, cx.enums@), |_j: int| bool_lit(false)),
    ensures
        setlit_ok(Seq::empty(), cx, sc, b, b, st, bits),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match eval_set_items(st, Seq::empty(), se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(p) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && keys(st, se.enums) == Some(p.len()) && clean(bits, env, l) && slot_vals(bits, env, l) == Seq::new(
            p.len(),
            |j: int| Value::Bool(p[j]),
        ),
    } by {
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        let p = Seq::new(keys_or_zero(st, se.enums), |_i: int| false);
        assert forall|j: int| 0 <= j < bits.len() implies pure_below(#[trigger] bits[j], ls.len()) && eval_l(bits[j], env, ls) is Ok by {
            assert(bits[j] == bool_lit(false));
        }
        assert forall|j: int| 0 <= j < bits.len() implies #[trigger] slot_vals(bits, env, ls)[j] == Value::Bool(p[j]) by {
            assert(bits[j] == bool_lit(false));
        }
        assert(slot_vals(bits, env, ls) =~= Seq::new(p.len(), |j: int| Value::Bool(p[j])));
    }
}

/// Setのリテラルに要素を1つ加える。
proof fn lemma_setlit_step(
    es: Seq<TExpr>,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        es.len() > 0,
        setlit_ok(es.drop_last(), cx, sc, b0, b1, st, bits),
        elem_rank_lowers(es.last(), cx, sc, b1, b2, st, r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(true, bits[k], r, k as i64),
    ensures
        setlit_ok(es, cx, sc, b0, b2, st, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_set_items(st, es, se, sls) {
        Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(p) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && keys(st, se.enums) == Some(p.len()) && clean(out, env, l) && slot_vals(out, env, l) == Seq::new(
            p.len(),
            |j: int| Value::Bool(p[j]),
        ),
    } by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(p) = eval_set_items(st, es.drop_last(), se, sls) {
            let enums = se.enums;
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(ctx_ok(cx, sc, env, se, l1, sls));
            if let Ok(v) = eval_src(es.last(), se, sls) {
                if member(v, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_run_fresh_ok(b1, b2, env, l1);
                    lemma_prefix_trans(ls, l1, l2);
                    lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
                    lemma_clean_weaken(bits, env, l1, l2);
                    let i = rank(v, st, enums);
                    lemma_rank_in_domain(v, st, enums);
                    lemma_mark(true, bits, r, out, p, i as i64, env, l2);
                    assert(Seq::new(p.len(), |j: int| Value::Bool(p[j] || i as i64 == j)) =~= Seq::new(
                        p.update(i, true).len(),
                        |j: int| Value::Bool(p.update(i, true)[j]),
                    ));
                }
            }
        }
    }
}

/// Setに要素が含まれるかの下ろし。番号が負なら、印を評価せずに偽になる。
#[verifier::spinoff_prover]
proof fn lemma_set_contains(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    cs: Seq<Expr>,
    r: Expr,
    hit: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::SetContains(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        cs.len() <= 0x7fff_ffff,
        picks(hit, cs, r),
        out == seq![and_s(Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), hit)],
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let st = sty(t);
    let g = Expr::Bin(BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0))));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), cs, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(rank_result(eval_src(x, se, sls), run(fresh(b1, b2), env, l1), r, env, st, enums));
            if let Ok(y) = eval_src(x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                let bits = sv->Set_0;
                assert(slot_vals(cs, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                lemma_clean_weaken(cs, env, l1, l2);
                let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
                assert forall|j: int| 0 <= j < cs.len() implies pure_below(#[trigger] cs[j], l2.len()) && eval_l(cs[j], env, l2)
                    == Ok::<Value, ErrKind>(vals[j]) by {
                    assert(slot_vals(cs, env, l2)[j] == eval_l(cs[j], env, l2)->Ok_0);
                }
                assert(vals_at(cs, vals, env, l2));
                let m = member(y, st, enums);
                let i: i64 = if m { rank(y, st, enums) as i64 } else { -1i64 };
                assert(at_rank(r, env, l2, i));
                lemma_bin_const(BinOp::Ge, r, 0, env, l2, i);
                assert(all_pure(cs, l2.len()));
                assert(pure_below(hit, l2.len()));
                if m {
                    lemma_rank_in_domain(y, st, enums);
                    assert(eval_l(hit, env, l2) == Ok::<Value, ErrKind>(Value::Bool(bits[i as int])));
                    lemma_and(g, hit, env, l2, true, bits[i as int]);
                } else {
                    if hit == bool_lit(true) {
                        assert(and_s(g, hit) == g);
                    } else {
                        assert(and_s(g, hit) == Expr::And(Box::new(g), Box::new(hit)));
                    }
                }
                let z = and_s(g, hit);
                assert(pure_below(z, l2.len()));
                lemma_one_denotes(z, env, l2, eval_l(z, env, l2)->Ok_0, XTy::Bool, enums);
            }
        }
    }
}

/// Setに要素を加える下ろし。要素が型に属さなければ失敗する。
#[verifier::spinoff_prover]
proof fn lemma_insert(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Insert(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), bits),
        elem_rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(true, bits[k], r, k as i64),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Set(Box::new(sty(t))), out),
{
    let st = sty(t);
    let xt = XTy::Set(Box::new(st));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, xt, bits, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            if let Ok(y) = eval_src(x, se, sls) {
                if member(y, st, enums) {
                    let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                    lemma_run_fresh_ok(b1, b2, env, l1);
                    let p = sv->Set_0;
                    assert(slot_vals(bits, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                    lemma_clean_weaken(bits, env, l1, l2);
                    let i = rank(y, st, enums);
                    lemma_rank_in_domain(y, st, enums);
                    lemma_mark(true, bits, r, out, p, i as i64, env, l2);
                    let q = p.update(i, true);
                    assert(slot_vals(out, env, l2) =~= Seq::new(q.len(), |j: int| Value::Bool(q[j])));
                }
            }
        }
    }
}

/// Setから要素を除く下ろし。要素が型に属さなければ、番号は -1 でSetは変わらない。
#[verifier::spinoff_prover]
proof fn lemma_remove(
    e: TExpr,
    t: SType,
    a: TExpr,
    x: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    bits: Seq<Expr>,
    r: Expr,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Remove(t, Box::new(a), Box::new(x)),
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), bits),
        rank_lowers(x, cx, sc, b1, b2, sty(t), r),
        extends(b0, b1),
        extends(b1, b2),
        bits.len() <= 0x7fff_ffff,
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(false, bits[k], r, k as i64),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Set(Box::new(sty(t))), out),
{
    let st = sty(t);
    let xt = XTy::Set(Box::new(st));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        let enums = se.enums;
        lemma_one(a, cx, sc, b0, b1, xt, bits, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(sv) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(rank_result(eval_src(x, se, sls), run(fresh(b1, b2), env, l1), r, env, st, enums));
            if let Ok(y) = eval_src(x, se, sls) {
                let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                lemma_run_fresh_ok(b1, b2, env, l1);
                let p = sv->Set_0;
                assert(slot_vals(bits, env, l1) == enc(sv, STy::Set(Box::new(st)), enums));
                lemma_clean_weaken(bits, env, l1, l2);
                let m = member(y, st, enums);
                let i: i64 = if m { rank(y, st, enums) as i64 } else { -1i64 };
                lemma_mark(false, bits, r, out, p, i, env, l2);
                let q = if m { p.update(i as int, false) } else { p };
                if m {
                    lemma_rank_in_domain(y, st, enums);
                }
                assert(slot_vals(out, env, l2) =~= Seq::new(q.len(), |j: int| Value::Bool(q[j])));
            }
        }
    }
}

/// Setの要素の有無か、Mapの行の有無。
pub open spec fn size_bits(v: SVal) -> Seq<bool> {
    match v {
        SVal::Set(bits) => bits,
        SVal::Map(rows) => Seq::new(rows.len(), |i: int| rows[i] is Some),
        _ => Seq::empty(),
    }
}

/// `fs` は、SetかMapの式 `a` の要素の有無を表すBoolの式の列である。
pub open spec fn flags_ok(a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, fs: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
                && vals_at(fs, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
        }
}

proof fn lemma_count_add(a: Seq<bool>, b: Seq<bool>)
    ensures
        count_true(a + b) == count_true(a) + count_true(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_count_add(a, b.drop_last());
    }
}

proof fn lemma_count_le(a: Seq<bool>)
    ensures
        count_true(a) <= a.len(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_count_le(a.drop_last());
    }
}

proof fn lemma_count_pos(a: Seq<bool>, j: int)
    requires
        0 <= j < a.len(),
        a[j],
    ensures
        count_true(a) > 0,
    decreases a.len(),
{
    if j < a.len() - 1 {
        assert(a.drop_last()[j] == a[j]);
        lemma_count_pos(a.drop_last(), j);
    }
}

proof fn lemma_count_none(a: Seq<bool>)
    requires
        forall|j: int| 0 <= j < a.len() ==> !#[trigger] a[j],
    ensures
        count_true(a) == 0,
    decreases a.len(),
{
    if a.len() > 0 {
        assert forall|j: int| 0 <= j < a.len() - 1 implies !#[trigger] a.drop_last()[j] by {
            assert(a.drop_last()[j] == a[j]);
        }
        lemma_count_none(a.drop_last());
    }
}

proof fn lemma_count_some(rows: Seq<Option<SVal>>)
    ensures
        count_some(rows) == count_true(Seq::new(rows.len(), |i: int| rows[i] is Some)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let b = Seq::new(rows.len(), |i: int| rows[i] is Some);
        assert(b.drop_last() =~= Seq::new(rows.drop_last().len(), |i: int| rows.drop_last()[i] is Some));
        lemma_count_some(rows.drop_last());
    }
}

/// 有無を0と1にした式の和は、真の数である。
proof fn lemma_sum_codes(codes: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        codes.len() == bits.len(),
        bits.len() <= 0x7fff_ffff,
        forall|j: int| 0 <= j < codes.len() ==> pure_below(#[trigger] codes[j], l.len()) && eval_l(codes[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if bits[j] { 1 } else { 0 })),
    ensures
        pure_below(tree_s(codes, int_lit(0), Join::Add), l.len()),
        eval_l(tree_s(codes, int_lit(0), Join::Add), env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(bits) as i64)),
    decreases codes.len(),
{
    if codes.len() > 1 {
        let m = codes.len() / 2;
        let lc = codes.take(m as int);
        let rc = codes.skip(m as int);
        let lb = bits.take(m as int);
        let rb = bits.skip(m as int);
        assert forall|j: int| 0 <= j < lc.len() implies pure_below(#[trigger] lc[j], l.len()) && eval_l(lc[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if lb[j] { 1 } else { 0 })) by {
            assert(lc[j] == codes[j] && lb[j] == bits[j]);
        }
        assert forall|j: int| 0 <= j < rc.len() implies pure_below(#[trigger] rc[j], l.len()) && eval_l(rc[j], env, l)
            == Ok::<Value, ErrKind>(Value::Int(if rb[j] { 1 } else { 0 })) by {
            assert(rc[j] == codes[j + m] && rb[j] == bits[j + m]);
        }
        lemma_sum_codes(lc, lb, env, l);
        lemma_sum_codes(rc, rb, env, l);
        assert(bits =~= lb + rb);
        lemma_count_add(lb, rb);
        lemma_count_le(lb);
        lemma_count_le(rb);
        let x = tree_s(lc, int_lit(0), Join::Add);
        let y = tree_s(rc, int_lit(0), Join::Add);
        assert(tree_s(codes, int_lit(0), Join::Add) == Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)));
        assert(binop_spec(BinOp::Add, Value::Int(count_true(lb) as i64), Value::Int(count_true(rb) as i64))
            == Ok::<Value, ErrKind>(Value::Int(count_true(bits) as i64)));
        assert(eval_l(x, env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(lb) as i64)));
        assert(eval_l(y, env, l) == Ok::<Value, ErrKind>(Value::Int(count_true(rb) as i64)));
    } else if codes.len() == 1 {
        assert(bits.drop_last() =~= Seq::<bool>::empty());
        assert(tree_s(codes, int_lit(0), Join::Add) == codes[0]);
        assert(count_true(bits.drop_last()) == 0);
        assert(bits.last() == bits[0]);
    } else {
        assert(count_true(bits) == 0);
    }
}

/// Setのスロットは要素の有無である。
proof fn lemma_flags_set(a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, s: Seq<Expr>)
    requires
        lowers(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), s),
        extends(b0, b1),
    ensures
        flags_ok(a, cx, sc, b0, b1, s),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(a, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
            && vals_at(s, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
    } by {
        lemma_one(a, cx, sc, b0, b1, XTy::Set(Box::new(st)), s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = v->Set_0;
            assert(slot_vals(s, env, l) == enc(v, STy::Set(Box::new(st)), se.enums));
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], l.len()) && eval_l(s[j], env, l)
                == Ok::<Value, ErrKind>(vals[j]) by {
                assert(slot_vals(s, env, l)[j] == eval_l(s[j], env, l)->Ok_0);
            }
        }
    }
}

/// Mapのスロットの、各行の先頭は行の有無である。
#[verifier::spinoff_prover]
proof fn lemma_flags_map(
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sk: STy,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    n: nat,
)
    requires
        lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), cs),
        extends(b0, b1),
        keys(sk, cx.enums@) == Some(n),
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
    ensures
        flags_ok(a, cx, sc, b0, b1, fs),
{
    let xt = XTy::Map(Box::new(sk), Box::new(sv));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match eval_src(a, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => (v is Set || v is Map) && (run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s()
            && vals_at(fs, Seq::new(size_bits(v).len(), |j: int| Value::Bool(size_bits(v)[j])), env, l)),
    } by {
        lemma_one(a, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let rows = v->Map_0;
            let bits = Seq::new(rows.len(), |i: int| rows[i] is Some);
            assert(slot_vals(cs, env, l) == enc_rows(rows, sv, enums));
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert forall|q: int| 0 <= q < fs.len() implies pure_below(#[trigger] fs[q], l.len()) && eval_l(fs[q], env, l)
                == Ok::<Value, ErrKind>(vals[q]) by {
                lemma_enc_rows_index(rows, sv, enums, q, 0);
                let at = q * stride;
                assert(slot_vals(cs, env, l)[at] == eval_l(cs[at], env, l)->Ok_0);
                assert(row_slots(rows[q], sv, enums)[0] == Value::Bool(rows[q] is Some));
            }
            assert(vals_at(fs, vals, env, l));
        }
    }
}

/// SetかMapの大きさは、有無を0と1にした式の和である。
#[verifier::spinoff_prover]
proof fn lemma_size(
    e: TExpr,
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    fs: Seq<Expr>,
    codes: Seq<Expr>,
    x: Expr,
)
    requires
        e == TExpr::Size(Box::new(a)),
        flags_ok(a, cx, sc, b0, b1, fs),
        extends(b0, b1),
        extends(b1, b2),
        fs.len() <= 0x7fff_ffff,
        codes.len() == fs.len(),
        forall|q: int| 0 <= q < fs.len() ==> #[trigger] codes[q] == Expr::Code(Box::new(fs[q])),
        added(b1, b2, tree_s(codes, int_lit(0), Join::Add), x),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Int, seq![x]),
{
    let sm = tree_s(codes, int_lit(0), Join::Add);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![x],
        env,
        XTy::Int,
        se.enums,
    ) by {
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = size_bits(v);
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert(vals_at(fs, vals, env, l1));
            assert forall|j: int| 0 <= j < codes.len() implies pure_below(#[trigger] codes[j], l1.len()) && eval_l(
                codes[j],
                env,
                l1,
            ) == Ok::<Value, ErrKind>(Value::Int(if bits[j] { 1 } else { 0 })) by {
                assert(eval_l(fs[j], env, l1) == Ok::<Value, ErrKind>(vals[j]));
            }
            lemma_sum_codes(codes, bits, env, l1);
            lemma_count_le(bits);
            let c = Value::Int(count_true(bits) as i64);
            lemma_added(b1, b2, sm, x, env, l1, c);
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            if v is Map {
                lemma_count_some(v->Map_0);
            }
            lemma_one_denotes(x, env, l2, c, XTy::Int, se.enums);
        }
    }
}

/// SetかMapが空であることは、どの有無も真でないことである。
#[verifier::spinoff_prover]
proof fn lemma_is_empty(e: TExpr, a: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, fs: Seq<Expr>)
    requires
        e == TExpr::IsEmpty(Box::new(a)),
        flags_ok(a, cx, sc, b0, b1, fs),
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, seq![Expr::Not(Box::new(tree_s(fs, bool_lit(false), Join::Or)))]),
{
    let t = tree_s(fs, bool_lit(false), Join::Or);
    let z = Expr::Not(Box::new(t));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        seq![z],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = size_bits(v);
            let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
            assert(vals_at(fs, vals, env, l));
            assert forall|j: int| 0 <= j < fs.len() implies bool_val(#[trigger] eval_l(fs[j], env, l)) by {
                assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
            }
            assert(all_pure(fs, l.len()));
            lemma_any_of(fs, env, l);
            lemma_tree_pure(fs, bool_lit(false), Join::Or, l.len());
            if any_true(fs, env, l) {
                let j = choose|j: int| 0 <= j < fs.len() && #[trigger] eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(
                    Value::Bool(true),
                );
                assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
                lemma_count_pos(bits, j);
            } else {
                assert forall|j: int| 0 <= j < bits.len() implies !#[trigger] bits[j] by {
                    assert(eval_l(fs[j], env, l) == Ok::<Value, ErrKind>(vals[j]));
                }
                lemma_count_none(bits);
            }
            if v is Map {
                lemma_count_some(v->Map_0);
            }
            lemma_one_denotes(z, env, l, Value::Bool(!any_true(fs, env, l)), XTy::Bool, se.enums);
        }
    }
}

/// Listの大きさは先頭のスロットである。
#[verifier::spinoff_prover]
proof fn lemma_list_size(
    e: TExpr,
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: usize,
    s: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e == TExpr::Size(Box::new(a)) || e == TExpr::IsEmpty(Box::new(a)),
        lowers(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), s),
        extends(b0, b1),
        s.len() > 0,
        max <= 0x7fff_ffff,
        out == if e is Size {
            seq![s[0]]
        } else {
            seq![Expr::Bin(BinOp::Eq, Box::new(s[0]), Box::new(Expr::Const(Value::Int(0))))]
        },
    ensures
        lowers(e, cx, sc, b0, b1, if e is Size { XTy::Int } else { XTy::Bool }, out),
{
    let xt = if e is Size { XTy::Int } else { XTy::Bool };
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        out,
        env,
        xt,
        se.enums,
    ) by {
        lemma_one(a, cx, sc, b0, b1, XTy::List(Box::new(st), max), s, env, se, ls, sls);
        if let Ok(v) = eval_src(a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let items = v->List_0;
            assert(slot_vals(s, env, l) == enc(v, STy::List(Box::new(st), max), se.enums));
            assert(slot_vals(s, env, l)[0] == eval_l(s[0], env, l)->Ok_0);
            assert(eval_l(s[0], env, l) == Ok::<Value, ErrKind>(Value::Int(items.len() as i64)));
            assert(pure_below(s[0], l.len()));
            assert(items.len() <= max);
            if e is Size {
                lemma_one_denotes(out[0], env, l, Value::Int(items.len() as i64), XTy::Int, se.enums);
            } else {
                assert(binop_spec(BinOp::Eq, Value::Int(items.len() as i64), Value::Int(0)) == Ok::<Value, ErrKind>(
                    Value::Bool(items.len() == 0),
                ));
                let z = Expr::Bin(BinOp::Eq, Box::new(s[0]), Box::new(Expr::Const(Value::Int(0))));
                assert(out[0] == z);
                assert(pure_below(int_lit(0), l.len()));
                assert(eval_l(int_lit(0), env, l) == Ok::<Value, ErrKind>(Value::Int(0)));
                lemma_one_denotes(out[0], env, l, Value::Bool(items.len() == 0), XTy::Bool, se.enums);
            }
        }
    }
}

/// 等しさの下ろし。
#[verifier::spinoff_prover]
proof fn lemma_eq(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    x: Seq<Expr>,
    y: Seq<Expr>,
    c: Expr,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Eq(positive, a, b) && lowers(*a, cx, sc, b0, b1, t, x) && lowers(*b, cx, sc, b1, b2, t, y)
            && out == seq![if positive { c } else { Expr::Not(Box::new(c)) }],
        extends(b0, b1),
        extends(b1, b2),
        eq_ok(t, x, y, c, cx.enums@),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, out),
{
    let positive = e->Eq_0;
    let a = e->Eq_1;
    let b = e->Eq_2;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_pair(*a, *b, cx, sc, b0, b1, b2, t, x, t, y, env, se, ls, sls);
        if let Ok(va) = eval_src(*a, se, sls) {
            if let Ok(vb) = eval_src(*b, se, sls) {
                let l = run(fresh(b0, b2), env, ls)->Ok_0;
                lemma_clean_pure(x, env, l);
                lemma_clean_pure(y, env, l);
                assert(pure_below(c, l.len()));
                assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(va == vb)));
                lemma_one_denotes(out[0], env, l, Value::Bool((va == vb) == positive), XTy::Bool, se.enums);
            }
        }
    }
}

/// Setの演算の、要素ごとのスロットの式。
pub open spec fn setop_s(op: SetOp, x: Expr, y: Expr) -> Expr {
    match op {
        SetOp::Union => or_s(x, y),
        SetOp::Intersection => and_s(x, y),
        SetOp::Difference => and_s(x, Expr::Not(Box::new(y))),
        SetOp::Subset => implies_s(x, y),
    }
}

pub open spec fn setop_b(op: SetOp, a: bool, b: bool) -> bool {
    match op {
        SetOp::Union => a || b,
        SetOp::Intersection => a && b,
        SetOp::Difference => a && !b,
        SetOp::Subset => a ==> b,
    }
}

proof fn lemma_setop_eval(op: SetOp, x: Expr, y: Expr, env: Env, l: Seq<Value>, a: bool, b: bool)
    requires
        pure_below(x, l.len()),
        pure_below(y, l.len()),
        eval_l(x, env, l) == Ok::<Value, ErrKind>(Value::Bool(a)),
        eval_l(y, env, l) == Ok::<Value, ErrKind>(Value::Bool(b)),
    ensures
        pure_below(setop_s(op, x, y), l.len()),
        eval_l(setop_s(op, x, y), env, l) == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, a, b))),
{
    let n = l.len();
    match op {
        SetOp::Union => {
            lemma_or(x, y, env, l, a, b);
            assert(pure_below(Expr::Or(Box::new(x), Box::new(y)), n));
        },
        SetOp::Intersection => {
            lemma_and(x, y, env, l, a, b);
            assert(pure_below(Expr::And(Box::new(x), Box::new(y)), n));
        },
        SetOp::Difference => {
            let ny = Expr::Not(Box::new(y));
            assert(pure_below(ny, n));
            assert(eval_l(ny, env, l) == Ok::<Value, ErrKind>(Value::Bool(!b)));
            lemma_and(x, ny, env, l, a, !b);
            assert(pure_below(Expr::And(Box::new(x), Box::new(ny)), n));
        },
        SetOp::Subset => {
            let z = Expr::Implies(Box::new(x), Box::new(y));
            assert(pure_below(z, n));
            if y != bool_lit(true) {
                assert(eval_l(z, env, l) == Ok::<Value, ErrKind>(Value::Bool(a ==> b)));
            } else {
                assert(b);
            }
        },
    }
}

/// Setの演算の要素ごとのスロットの値。
proof fn lemma_setbin_vals(op: SetOp, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, p: Seq<bool>, q: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        clean(xs, env, l),
        clean(ys, env, l),
        slot_vals(xs, env, l) == Seq::new(p.len(), |i: int| Value::Bool(p[i])),
        slot_vals(ys, env, l) == Seq::new(q.len(), |i: int| Value::Bool(q[i])),
        p.len() == q.len(),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == setop_s(op, xs[j], ys[j]),
    ensures
        out.len() == p.len(),
        forall|j: int| 0 <= j < out.len() ==> pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
            == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, p[j], q[j]))),
{
    assert(slot_vals(xs, env, l).len() == xs.len());
    assert(slot_vals(ys, env, l).len() == ys.len());
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == Ok::<Value, ErrKind>(Value::Bool(setop_b(op, p[j], q[j]))) by {
        assert(out[j] == setop_s(op, xs[j], ys[j]));
        assert(slot_vals(xs, env, l)[j] == eval_l(xs[j], env, l)->Ok_0);
        assert(slot_vals(ys, env, l)[j] == eval_l(ys[j], env, l)->Ok_0);
        lemma_setop_eval(op, xs[j], ys[j], env, l, p[j], q[j]);
    }
}

/// 包含の判定は、すべての要素の含意である。
proof fn lemma_setbin_subset(out: Seq<Expr>, p: Seq<bool>, q: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        out.len() == p.len(),
        p.len() == q.len(),
        forall|j: int| 0 <= j < out.len() ==> pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
            == Ok::<Value, ErrKind>(Value::Bool(setop_b(SetOp::Subset, p[j], q[j]))),
    ensures
        denotes(
            seq![tree_s(out, bool_lit(true), Join::And)],
            env,
            l,
            SVal::Bool(forall|i: int| 0 <= i < p.len() ==> (p[i] ==> q[i])),
            XTy::Bool,
            enums,
        ),
{
    assert(all_bool(out, env, l));
    lemma_all_of(out, env, l);
    if all_true(out, env, l) {
        assert forall|i: int| 0 <= i < p.len() implies !p[i] || q[i] by {
            assert(eval_l(out[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
        }
    }
    if forall|i: int| 0 <= i < p.len() ==> (p[i] ==> q[i]) {
        assert forall|j: int| 0 <= j < out.len() implies #[trigger] eval_l(out[j], env, l) == Ok::<Value, ErrKind>(
            Value::Bool(true),
        ) by {
            assert(p[j] ==> q[j]);
        }
    }
    assert(all_pure(out, l.len()));
    lemma_tree_pure(out, bool_lit(true), Join::And, l.len());
    let z = tree_s(out, bool_lit(true), Join::And);
    lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, enums);
}

/// Setの和、積、差、包含の下ろし。
#[verifier::spinoff_prover]
proof fn lemma_setbin(
    e: TExpr,
    op: SetOp,
    a: TExpr,
    b: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e == TExpr::SetBin(op, Box::new(a), Box::new(b)),
        t is Set,
        lowers(a, cx, sc, b0, b1, t, xs),
        lowers(b, cx, sc, b1, b2, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|q: int| 0 <= q < out.len() ==> #[trigger] out[q] == setop_s(op, xs[q], ys[q]),
    ensures
        op is Subset ==> lowers(e, cx, sc, b0, b2, XTy::Bool, seq![tree_s(out, bool_lit(true), Join::And)]),
        !(op is Subset) ==> lowers(e, cx, sc, b0, b2, t, out),
{
    lemma_extends_trans(b0, b1, b2);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        if op is Subset { seq![tree_s(out, bool_lit(true), Join::And)] } else { out },
        env,
        if op is Subset { XTy::Bool } else { t },
        se.enums,
    ) by {
        lemma_setbin_at(e, op, a, b, cx, sc, b0, b1, b2, t, xs, ys, out, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_setbin_at(
    e: TExpr,
    op: SetOp,
    a: TExpr,
    b: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        e == TExpr::SetBin(op, Box::new(a), Box::new(b)),
        t is Set,
        lowers(a, cx, sc, b0, b1, t, xs),
        lowers(b, cx, sc, b1, b2, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        out.len() == if xs.len() < ys.len() { xs.len() } else { ys.len() },
        forall|q: int| 0 <= q < out.len() ==> #[trigger] out[q] == setop_s(op, xs[q], ys[q]),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        result_ok(
            eval_src(e, se, sls),
            run(fresh(b0, b2), env, ls),
            if op is Subset { seq![tree_s(out, bool_lit(true), Join::And)] } else { out },
            env,
            if op is Subset { XTy::Bool } else { t },
            se.enums,
        ),
{
    let st = *t->Set_0;
    let stt = STy::Set(Box::new(st));
    lemma_pair(a, b, cx, sc, b0, b1, b2, t, xs, t, ys, env, se, ls, sls);
    if let Ok(va) = eval_src(a, se, sls) {
        if let Ok(vb) = eval_src(b, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b2), env, ls)->Ok_0;
            let p = va->Set_0;
            let q = vb->Set_0;
            assert(slot_vals(xs, env, l) == enc(va, stt, enums));
            assert(slot_vals(ys, env, l) == enc(vb, stt, enums));
            lemma_setbin_vals(op, xs, ys, out, p, q, env, l);
            if op is Subset {
                lemma_setbin_subset(out, p, q, env, l, enums);
            } else {
                let bits = Seq::new(p.len(), |i: int| setop_b(op, p[i], q[i]));
                assert(slot_vals(out, env, l) =~= Seq::new(bits.len(), |i: int| Value::Bool(bits[i])));
                assert(eval_src(e, se, sls) == Ok::<SVal, ErrKind>(SVal::Set(bits))) by {
                    match op {
                        SetOp::Union => assert(bits =~= Seq::new(p.len(), |i: int| p[i] || q[i])),
                        SetOp::Intersection => assert(bits =~= Seq::new(p.len(), |i: int| p[i] && q[i])),
                        SetOp::Difference => assert(bits =~= Seq::new(p.len(), |i: int| p[i] && !q[i])),
                        SetOp::Subset => {},
                    }
                }
            }
        }
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

/// `qb` は、ガード `g` が真なら本体 `b` の真偽、偽なら `all` になる。
pub open spec fn combine_ok(all: bool, g: Expr, b: Expr, qb: Expr) -> bool {
    forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(qb, env, l)) == match as_bool(eval_l(g, env, l)) {
        Err(k) => Err(k),
        Ok(true) => as_bool(eval_l(b, env, l)),
        Ok(false) => Ok::<bool, ErrKind>(all),
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

pub open spec fn quant_s(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> Expr {
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

/// 量化でたどる値の列。値の意味論の `Quant` がたどる列である。
pub open spec fn src_items(over: Over, se: SEnv, sls: Seq<SVal>) -> Result<Seq<SVal>, ErrKind> {
    let enums = se.enums;
    match over {
        Over::Type(t) => Ok(domain(sty(t), enums)),
        Over::Set(t, s) => match eval_src(*s, se, sls) {
            Ok(SVal::Set(bits)) => Ok(select_bits(domain(sty(t), enums), bits)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::Map(t, m) => match eval_src(*m, se, sls) {
            Ok(SVal::Map(rows)) => Ok(
                select_bits(domain(sty(t), enums), Seq::new(rows.len(), |i: int| rows[i] is Some)),
            ),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => Ok(items),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
    }
}

/// 局所変数 `l` に位置 `x` を加えると、ガード `g` は `bits[x]` になる。
pub open spec fn guard_at(g: Expr, bits: Seq<bool>, env: Env, l: Seq<Value>) -> bool {
    forall|x: int|
        0 <= x < bits.len() ==> #[trigger] eval_l(g, env, l.push(Value::Int(x as i64))) == Ok::<Value, ErrKind>(
            Value::Bool(bits[x]),
        )
}

/// 局所変数 `l` に選ぶ位置 `x` を加えると、スロット `us` は `dom[x]` を表す。
pub open spec fn bound_at(us: Seq<Expr>, xt: XTy, dom: Seq<SVal>, bits: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>) -> bool {
    forall|x: int|
        0 <= x < bits.len() && bits[x] ==> #[trigger] denotes(us, env, l.push(Value::Int(x as i64)), dom[x], xt, enums)
}

/// 位置の列 `dom` から `bits` で選ぶと、たどる値の列 `xs` になる。ガードと束縛する値のスロットは、位置ごとにそれを表す。
pub open spec fn sel_ok(
    xs: Seq<SVal>,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    n: nat,
    g: Expr,
    us: Seq<Expr>,
    xt: XTy,
    env: Env,
    l: Seq<Value>,
    enums: Seq<i64>,
) -> bool {
    &&& bits.len() == n
    &&& dom.len() == n
    &&& select_bits(dom, bits) == xs
    &&& guard_at(g, bits, env, l)
    &&& bound_at(us, xt, dom, bits, env, l, enums)
}

/// 位置の列。型の全体、Set、Mapでは型の正規順の列、ListではListの要素を長さ `n` に埋めた列。
pub open spec fn over_dom(over: Over, se: SEnv, sls: Seq<SVal>, n: nat) -> Seq<SVal> {
    match over {
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => list_dom(items, n),
            _ => Seq::empty(),
        },
        _ => domain(over_sty(over), se.enums),
    }
}

/// 選ぶ位置。
pub open spec fn over_sel(over: Over, se: SEnv, sls: Seq<SVal>, n: nat) -> Seq<bool> {
    match over {
        Over::Type(_) => Seq::new(n, |i: int| true),
        Over::Set(_, s) => match eval_src(*s, se, sls) {
            Ok(SVal::Set(bits)) => bits,
            _ => Seq::empty(),
        },
        Over::Map(_, m) => match eval_src(*m, se, sls) {
            Ok(SVal::Map(rows)) => Seq::new(rows.len(), |i: int| rows[i] is Some),
            _ => Seq::empty(),
        },
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => Seq::new(n, |i: int| i < items.len()),
            _ => Seq::empty(),
        },
    }
}

pub open spec fn over_sty(over: Over) -> STy {
    match over {
        Over::Type(t) => sty(t),
        Over::Set(t, _) => sty(t),
        Over::Map(t, _) => sty(t),
        Over::List(_) => STy::Bool,
    }
}

/// 対象を `b0` から `b1` までに下ろした結果。成功すれば、位置の列と選ぶ位置が [`sel_ok`] を満たす。
pub open spec fn over_at(
    over: Over,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    xt: XTy,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
) -> bool {
    match src_items(over, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(xs) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && sel_ok(xs, over_dom(over, se, sls, n), over_sel(over, se, sls, n), n, g, us, xt, env, l, se.enums),
    }
}

pub open spec fn over_ok(over: Over, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, g: Expr, n: nat, us: Seq<Expr>, xt: XTy) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> over_at(
            over,
            cx,
            sc,
            b0,
            b1,
            g,
            n,
            us,
            xt,
            env,
            se,
            ls,
            sls,
        )
}

/// 番号から作ったスロットは、正規順でその番号の値を表す。
proof fn lemma_unrank_bound(st: STy, n: nat, us: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        unrank_ok(st, Expr::Local(l.len() as usize), us, enums),
        keys(st, enums) == Some(n),
        n <= 0x7fff_ffff,
        l.len() < usize::MAX,
        bits.len() == n,
    ensures
        bound_at(us, to_xty(st), domain(st, enums), bits, env, l, enums),
{
    assert forall|x: int| 0 <= x < bits.len() && bits[x] implies #[trigger] denotes(
        us,
        env,
        l.push(Value::Int(x as i64)),
        domain(st, enums)[x],
        to_xty(st),
        enums,
    ) by {
        let lx = l.push(Value::Int(x as i64));
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
        lemma_domain_rank(st, enums, x);
        lemma_models_enc(domain(st, enums)[x], st, enums);
    }
}
/// 型の全体をたどる量化のガードは、つねに真である。
proof fn lemma_over_type(over: Over, cx: LowerCtx, sc: Seq<Bound>, b: Block, n: nat, us: Seq<Expr>)
    requires
        over is Type,
        keys(sty(over->Type_0), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        b.depth_s() < usize::MAX,
        unrank_ok(sty(over->Type_0), Expr::Local(b.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b, b, bool_lit(true), n, us, to_xty(sty(over->Type_0))),
{
    let st = sty(over->Type_0);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies over_at(
        over,
        cx,
        sc,
        b,
        b,
        bool_lit(true),
        n,
        us,
        to_xty(st),
        env,
        se,
        ls,
        sls,
    ) by {
        let enums = se.enums;
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        let bits = Seq::new(n, |i: int| true);
        lemma_select_all(dom, n);
        assert(dom.take(n as int) =~= dom);
        assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(
            bool_lit(true),
            env,
            ls.push(Value::Int(x as i64)),
        ) == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {}
        lemma_unrank_bound(st, n, us, bits, env, ls, enums);
        assert(sel_ok(dom, dom, bits, n, bool_lit(true), us, to_xty(st), env, ls, enums));
    }
}
/// 下ろした式の列 `fs` が印 `bits` を表すなら、位置を選ぶ式 `g` は位置ごとのガードになる。
proof fn lemma_guard_pick(g: Expr, fs: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        picks(g, fs, Expr::Local(l.len() as usize)),
        vals_at(fs, Seq::new(bits.len(), |j: int| Value::Bool(bits[j])), env, l),
        l.len() < usize::MAX,
        bits.len() <= 0x7fff_ffff,
    ensures
        guard_at(g, bits, env, l),
{
    let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
    assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(g, env, l.push(Value::Int(x as i64)))
        == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {
        let lx = l.push(Value::Int(x as i64));
        assert(prefix(l, lx));
        lemma_vals_weaken(fs, vals, env, l, lx);
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
    }
}
/// Setの要素をたどる量化のガード。
proof fn lemma_over_set(
    over: Over,
    t: SType,
    s: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    cs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
)
    requires
        over == Over::Set(t, Box::new(s)),
        lowers(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        cs.len() == n,
        picks(g, cs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t))),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        n,
        us,
        to_xty(sty(t)),
        env,
        se,
        ls,
        sls,
    ) by {
        lemma_over_set_at(over, t, s, cx, sc, b0, b1, cs, g, n, us, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_over_set_at(
    over: Over,
    t: SType,
    s: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    cs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        over == Over::Set(t, Box::new(s)),
        lowers(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        cs.len() == n,
        picks(g, cs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        over_at(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t)), env, se, ls, sls),
{
    let st = sty(t);
    lemma_one(s, cx, sc, b0, b1, XTy::Set(Box::new(st)), cs, env, se, ls, sls);
    if let Ok(v) = eval_src(s, se, sls) {
        let enums = se.enums;
        let l = run(fresh(b0, b1), env, ls)->Ok_0;
        let bits = v->Set_0;
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        assert(slot_vals(cs, env, l) == enc(v, STy::Set(Box::new(st)), enums));
        let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
        assert forall|j: int| 0 <= j < cs.len() implies pure_below(#[trigger] cs[j], l.len()) && eval_l(cs[j], env, l)
            == Ok::<Value, ErrKind>(vals[j]) by {
            assert(slot_vals(cs, env, l)[j] == eval_l(cs[j], env, l)->Ok_0);
        }
        assert(vals_at(cs, vals, env, l));
        lemma_guard_pick(g, cs, bits, env, l);
        lemma_unrank_bound(st, n, us, bits, env, l, enums);
        assert(sel_ok(select_bits(dom, bits), dom, bits, n, g, us, to_xty(st), env, l, enums));
    }
}
/// Mapのキーをたどる量化のガード。`fs` は各行の有無のスロットである。
proof fn lemma_over_map(
    over: Over,
    t: SType,
    m: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
)
    requires
        over == Over::Map(t, Box::new(m)),
        lowers(m, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(sv)), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
        picks(g, fs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t))),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        n,
        us,
        to_xty(sty(t)),
        env,
        se,
        ls,
        sls,
    ) by {
        lemma_over_map_at(over, t, m, cx, sc, b0, b1, sv, stride, cs, fs, g, n, us, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_over_map_at(
    over: Over,
    t: SType,
    m: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        over == Over::Map(t, Box::new(m)),
        lowers(m, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(sv)), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
        picks(g, fs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        over_at(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t)), env, se, ls, sls),
{
    let st = sty(t);
    let xt = XTy::Map(Box::new(st), Box::new(sv));
    lemma_one(m, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
    if let Ok(v) = eval_src(m, se, sls) {
        let enums = se.enums;
        let l = run(fresh(b0, b1), env, ls)->Ok_0;
        let rows = v->Map_0;
        let bits = Seq::new(rows.len(), |i: int| rows[i] is Some);
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        assert(slot_vals(cs, env, l) == enc_rows(rows, sv, enums));
        let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
        assert forall|q: int| 0 <= q < fs.len() implies pure_below(#[trigger] fs[q], l.len()) && eval_l(fs[q], env, l)
            == Ok::<Value, ErrKind>(vals[q]) by {
            lemma_enc_rows_index(rows, sv, enums, q, 0);
            let at = q * stride;
            assert(slot_vals(cs, env, l)[at] == eval_l(cs[at], env, l)->Ok_0);
            assert(row_slots(rows[q], sv, enums)[0] == Value::Bool(rows[q] is Some));
        }
        assert(vals_at(fs, vals, env, l));
        lemma_guard_pick(g, fs, bits, env, l);
        lemma_unrank_bound(st, n, us, bits, env, l, enums);
        assert(sel_ok(select_bits(dom, bits), dom, bits, n, g, us, to_xty(st), env, l, enums));
    }
}
/// Listの要素のスロットの列のうち、各要素の `j` 番目のスロット。
pub open spec fn list_col(cs: Seq<Expr>, w: int, max: nat, j: int) -> Seq<Expr> {
    Seq::new(max, |k: int| cs[1 + k * w + j])
}

/// Listの要素の位置の列。長さ `max` に足りない分は使わない値で埋める。
pub open spec fn list_dom(items: Seq<SVal>, max: nat) -> Seq<SVal> {
    Seq::new(max, |i: int| if i < items.len() { items[i] } else { SVal::Bool(false) })
}

/// Listの要素をたどる量化。位置は添字で、ガードは添字が長さより小さいことである。
proof fn lemma_over_list(
    over: Over,
    li: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: nat,
    w: int,
    cs: Seq<Expr>,
    us: Seq<Expr>,
    g: Expr,
)
    requires
        over == Over::List(Box::new(li)),
        lowers(li, cx, sc, b0, b1, XTy::List(Box::new(st), max as usize), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        max <= 0x7fff_ffff,
        w == width(st, cx.enums@),
        cs.len() > 0,
        us.len() == w,
        forall|j: int| 0 <= j < w ==> #[trigger] picks(us[j], list_col(cs, w, max, j), Expr::Local(b1.depth_s() as usize)),
        g == Expr::Bin(BinOp::Lt, Box::new(Expr::Local(b1.depth_s() as usize)), Box::new(cs[0])),
    ensures
        over_ok(over, cx, sc, b0, b1, g, max, us, to_xty(st)),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        max,
        us,
        to_xty(st),
        env,
        se,
        ls,
        sls,
    ) by {
        let xt = XTy::List(Box::new(st), max as usize);
        lemma_one(li, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
        if let Ok(v) = eval_src(li, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let items = v->List_0;
            let len = items.len();
            let dom = list_dom(items, max);
            let bits = Seq::new(max, |i: int| i < len);
            lemma_list_quant_at(st, max, w, cs, us, g, items, env, l, enums);
            lemma_select_prefix(dom, max, len);
            assert(dom.take(len as int) =~= items);
            assert(sel_ok(items, dom, bits, max, g, us, to_xty(st), env, l, enums));
        }
    }
}
/// Listの値を表すスロットから選んだガードと要素のスロット。
proof fn lemma_list_quant_at(
    st: STy,
    max: nat,
    w: int,
    cs: Seq<Expr>,
    us: Seq<Expr>,
    g: Expr,
    items: Seq<SVal>,
    env: Env,
    l: Seq<Value>,
    enums: Seq<i64>,
)
    requires
        denotes(cs, env, l, SVal::List(items), XTy::List(Box::new(st), max as usize), enums),
        l.len() < usize::MAX,
        max <= 0x7fff_ffff,
        w == width(st, enums),
        us.len() == w,
        forall|j: int| 0 <= j < w ==> #[trigger] picks(us[j], list_col(cs, w, max, j), Expr::Local(l.len() as usize)),
        g == Expr::Bin(BinOp::Lt, Box::new(Expr::Local(l.len() as usize)), Box::new(cs[0])),
    ensures
        items.len() <= max,
        guard_at(g, Seq::new(max, |i: int| i < items.len()), env, l),
        bound_at(us, to_xty(st), list_dom(items, max), Seq::new(max, |i: int| i < items.len()), env, l, enums),
{
    let lt = STy::List(Box::new(st), max as usize);
    let len = items.len();
    let bits = Seq::new(max, |i: int| i < len);
    let dom = list_dom(items, max);
    let sv = slot_vals(cs, env, l);
    let ei = enc_items(items, st, enums);
    let pad = enc_repeat(enc(default_val(st, enums), st, enums), (max - len) as nat);
    assert(member(SVal::List(items), lt, enums));
    assert(sv == seq![Value::Int(len as i64)] + ei + pad);
    lemma_enc_items_len(items, st, enums);
    lemma_default_len(st, enums);
    lemma_repeat_len(enc(default_val(st, enums), st, enums), (max - len) as nat);
    assert(sv.len() == 1 + max * w) by (nonlinear_arith)
        requires
            sv.len() == 1 + len * w + (max - len) * w,
            len <= max,
    ;
    assert(sv[0] == Value::Int(len as i64));
    assert(eval_l(cs[0], env, l) == Ok::<Value, ErrKind>(Value::Int(len as i64)));
    assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(g, env, l.push(Value::Int(x as i64)))
        == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {
        let lx = l.push(Value::Int(x as i64));
        lemma_weaken(cs[0], env, l, lx);
        assert(eval_l(Expr::Local(l.len() as usize), env, lx) == Ok::<Value, ErrKind>(Value::Int(x as i64)));
    }
    assert forall|x: int| 0 <= x < bits.len() && bits[x] implies #[trigger] denotes(
        us,
        env,
        l.push(Value::Int(x as i64)),
        dom[x],
        to_xty(st),
        enums,
    ) by {
        let lx = l.push(Value::Int(x as i64));
        assert(prefix(l, lx));
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
        let item = items[x];
        assert(dom[x] == item);
        assert forall|j: int| 0 <= j < us.len() implies pure_below(#[trigger] us[j], lx.len()) && eval_l(us[j], env, lx)
            == Ok::<Value, ErrKind>(enc(item, st, enums)[j]) by {
            let col = list_col(cs, w, max, j);
            let vals = Seq::new(max, |k: int| sv[1 + k * w + j]);
            assert forall|k: int| 0 <= k < col.len() implies pure_below(#[trigger] col[k], l.len()) && eval_l(col[k], env, l)
                == Ok::<Value, ErrKind>(vals[k]) by {
                assert(0 <= 1 + k * w + j < 1 + max * w) by (nonlinear_arith)
                    requires
                        0 <= k < max,
                        0 <= j < w,
                ;
                assert(sv[1 + k * w + j] == eval_l(cs[1 + k * w + j], env, l)->Ok_0);
            }
            assert(vals_at(col, vals, env, l));
            lemma_vals_weaken(col, vals, env, l, lx);
            lemma_items_index(items, st, enums, x, j);
            assert(sv[1 + x * w + j] == ei[x * w + j]);
            assert forall|k: int| 0 <= k < col.len() implies pure_below(#[trigger] col[k], lx.len()) by {
                lemma_pure_mono(col[k], l.len(), lx.len());
            }
            assert(all_pure(col, lx.len()));
            let r = Expr::Local(l.len() as usize);
            assert(pure_below(r, lx.len()));
            assert(picks(us[j], col, r));
            assert(pure_below(us[j], lx.len()));
            assert(at_rank(r, env, lx, x as i64));
            assert(eval_l(us[j], env, lx) == Ok::<Value, ErrKind>(vals[x]));
            assert(vals[x] == sv[1 + x * w + j]);
        }
        lemma_items_member(items, st, enums, x);
        lemma_enc_len(item, st, enums);
        assert(slot_vals(us, env, lx) =~= enc(item, st, enums));
        lemma_models_enc(item, st, enums);
    }
}

/// 量化の値の意味論を、たどる値の列で書き直す。
proof fn lemma_quant_src(e: TExpr, all: bool, over: Over, body: TExpr, se: SEnv, sls: Seq<SVal>)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
    ensures
        eval_src(e, se, sls) == match src_items(over, se, sls) {
            Err(k) => Err(k),
            Ok(xs) => match eval_quant(all, xs, body, se, sls) {
                Err(k) => Err(k),
                Ok(b) => Ok(SVal::Bool(b)),
            },
        },
{
}

/// 位置 `x` を束縛した文脈。
proof fn lemma_quant_ctx(cx: LowerCtx, sc: Seq<Bound>, bd: Bound, env: Env, se: SEnv, l: Seq<Value>, sls: Seq<SVal>, x: int, v: SVal)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        denotes(bd.slots@, env, l.push(Value::Int(x as i64)), v, xty(bd.ty), se.enums),
    ensures
        ctx_ok(cx, sc.push(bd), env, se, l.push(Value::Int(x as i64)), sls.push(v)),
{
    let lx = l.push(Value::Int(x as i64));
    let enums = se.enums;
    assert(prefix(l, lx));
    lemma_ctx_weaken(cx, sc, env, se, l, lx, sls);
    let sc2 = sc.push(bd);
    let sls2 = sls.push(v);
    assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(sc2[i].slots@, env, lx, sls2[i], xty(sc2[i].ty), enums) by {
        if i < sc.len() {
            assert(sc2[i] == sc[i] && sls2[i] == sls[i]);
        }
    }
}

/// 位置 `x` での量化の本体の真偽。
proof fn lemma_quant_step(
    all: bool,
    g: Expr,
    b: Expr,
    qb: Expr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    bd: Bound,
    body: TExpr,
    env: Env,
    se: SEnv,
    l: Seq<Value>,
    sls: Seq<SVal>,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    x: int,
)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        guard_at(g, bits, env, l),
        bound_at(bd.slots@, xty(bd.ty), dom, bits, env, l, se.enums),
        combine_ok(all, g, b, qb),
        closed_lowers(body, cx, sc.push(bd), l.len() + 1, XTy::Bool, b),
        0 <= x < bits.len(),
    ensures
        as_bool(eval_l(qb, env, l.push(Value::Int(x as i64)))) == if bits[x] {
            src_bool(eval_src(body, se, sls.push(dom[x])))
        } else {
            Ok::<bool, ErrKind>(all)
        },
{
    let lx = l.push(Value::Int(x as i64));
    assert(eval_l(g, env, lx) == Ok::<Value, ErrKind>(Value::Bool(bits[x])));
    assert(as_bool(eval_l(qb, env, lx)) == match as_bool(eval_l(g, env, lx)) {
        Err(k) => Err(k),
        Ok(true) => as_bool(eval_l(b, env, lx)),
        Ok(false) => Ok::<bool, ErrKind>(all),
    });
    if bits[x] {
        let sls2 = sls.push(dom[x]);
        assert(denotes(bd.slots@, env, lx, dom[x], xty(bd.ty), se.enums));
        lemma_quant_ctx(cx, sc, bd, env, se, l, sls, x, dom[x]);
        assert(ctx_ok(cx, sc.push(bd), env, se, lx, sls2));
        lemma_scalar_bool(eval_src(body, se, sls2), eval_l(b, env, lx), se.enums);
    }
}

/// 量化の下ろし。対象を下ろし、位置を1つの整数でたどる量化を束縛する。
proof fn lemma_quant(
    e: TExpr,
    all: bool,
    over: Over,
    body: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    n: nat,
    g: Expr,
    bd: Bound,
    b: Expr,
    qb: Expr,
    q: Expr,
)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
        over_ok(over, cx, sc, b0, b1, g, n, bd.slots@, xty(bd.ty)),
        n <= 0x7fff_ffff,
        closed_lowers(body, cx, sc.push(bd), b1.depth_s() + 1, XTy::Bool, b),
        combine_ok(all, g, b, qb),
        q == quant_s(all, Type::Int(0, if n == 0 { 0i64 } else { (n - 1) as i64 }), 0, (n - 1) as i64, qb),
        b2.binds@ == b1.binds@.push(q),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let z = Expr::Local(b1.depth_s() as usize);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![z],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_quant_src(e, all, over, body, se, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(xs) = src_items(over, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let dom = over_dom(over, se, sls, n);
            let bits = over_sel(over, se, sls, n);
            assert forall|x: int| 0 <= x < bits.len() implies #[trigger] as_bool(
                eval_l(qb, env, l.push(Value::Int(x as i64))),
            ) == if bits[x] {
                src_bool(eval_src(body, se, sls.push(dom[x])))
            } else {
                Ok::<bool, ErrKind>(all)
            } by {
                lemma_quant_step(all, g, b, qb, cx, sc, bd, body, env, se, l, sls, dom, bits, x);
            }
            assert(q_step_ok(all, qb, env, l, bits, dom, body, se, sls));
            let ty = Type::Int(0, if n == 0 { 0 } else { (n - 1) as i64 });
            assert(bits.take(0) =~= Seq::<bool>::empty());
            assert(qprefix(all, dom, bits, 0, body, se, sls) == Ok::<bool, ErrKind>(all));
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, 0);
            assert(bits.take(bits.len() as int) =~= bits);
            let res = eval_quant(all, xs, body, se, sls);
            assert(eval_l(q, env, l) == lift_bool(res));
            lemma_run_one(b1, b2, q, env, l);
            if let Ok(bv) = res {
                lemma_one_denotes(z, env, l.push(Value::Bool(bv)), Value::Bool(bv), XTy::Bool, se.enums);
            }
        }
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

pub open spec fn mark_s(on: bool, bit: Expr, r: Expr, k: i64) -> Expr {
    if on {
        or_s(bit, Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    } else {
        and_s(bit, Expr::Bin(BinOp::Ne, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    }
}

/// 番号 `i` の位置を `on` にしたSetのスロットの値。
proof fn lemma_mark(on: bool, bits: Seq<Expr>, r: Expr, out: Seq<Expr>, p: Seq<bool>, i: i64, env: Env, l: Seq<Value>)
    requires
        clean(bits, env, l),
        slot_vals(bits, env, l) == Seq::new(p.len(), |j: int| Value::Bool(p[j])),
        p.len() <= 0x7fff_ffff,
        pure_below(r, l.len()),
        eval_l(r, env, l) == Ok::<Value, ErrKind>(Value::Int(i)),
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(on, bits[k], r, k as i64),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == Seq::new(p.len(), |j: int| Value::Bool(if on { p[j] || i == j } else { p[j] && i != j })),
{
    assert(slot_vals(bits, env, l).len() == bits.len());
    assert(at_rank(r, env, l, i));
    assert forall|k: int| 0 <= k < out.len() implies pure_below(#[trigger] out[k], l.len()) && eval_l(out[k], env, l)
        == Ok::<Value, ErrKind>(Value::Bool(if on { p[k] || i == k } else { p[k] && i != k })) by {
        assert(slot_vals(bits, env, l)[k] == eval_l(bits[k], env, l)->Ok_0);
        let c = if on { BinOp::Eq } else { BinOp::Ne };
        lemma_bin_const(c, r, k as i64, env, l, i);
        let y = Expr::Bin(c, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64))));
        if on {
            lemma_or(bits[k], y, env, l, p[k], i == k);
            assert(pure_below(Expr::Or(Box::new(bits[k]), Box::new(y)), l.len()));
        } else {
            lemma_and(bits[k], y, env, l, p[k], i != k);
            assert(pure_below(Expr::And(Box::new(bits[k]), Box::new(y)), l.len()));
        }
    }
    assert(slot_vals(out, env, l) =~= Seq::new(p.len(), |j: int| Value::Bool(if on { p[j] || i == j } else { p[j] && i != j })));
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

/// `Map#get` の下ろしの正しさ（[`low_get`]）。
#[verifier::spinoff_prover]
proof fn lemma_get(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    a: TExpr,
    x: TExpr,
    ms: Seq<Expr>,
    sk: STy,
    sv: STy,
    rr: Expr,
    rank_local: usize,
    c: Expr,
    slots: Seq<Expr>,
    fallback: Seq<Expr>,
    rows: usize,
    wd: usize,
)
    requires
        e matches TExpr::Get(t, ea, ex) && *ea == a && *ex == x && sty(t) == sk,
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), ms),
        rank_lowers(x, cx, sc, b1, b2, sk, rr),
        added(b2, b3, rr, Expr::Local(rank_local)),
        fresh(b3, b4) == seq![c],
        rows == keys_or_zero(sk, cx.enums@),
        wd == width(sv, cx.enums@),
        fallback == lits(enc(default_val(sv, cx.enums@), sv, cx.enums@)),
        slots.len() == wd,
        forall|n: nat| #[trigger] all_pure(ms, n) && rank_local < n && all_pure(fallback, n) ==> all_pure(slots, n),
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int && (key_rank(locals, rank_local) < 0
                || key_rank(locals, rank_local) < rows <= i64::MAX) ==> #[trigger] eval_l(c, env, locals) == if key_rank(
                locals,
                rank_local,
            ) < 0 {
                Err(ErrKind::Failed(MISSING_KEY))
            } else {
                match as_bool(flat_slot(ms, wd, 0, key_rank(locals, rank_local), env, locals)) {
                    Ok(true) => Ok(Value::Bool(true)),
                    Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                    Err(error) => Err(error),
                }
            },
        forall|i: int, env: Env, locals: Seq<Value>|
            0 <= i < wd && rank_local < locals.len() && locals[rank_local as int] is Int && 0 <= key_rank(
                locals,
                rank_local,
            ) < rows <= i64::MAX ==> #[trigger] eval_l(slots[i], env, locals) == flat_slot_int(
                ms,
                wd,
                i + 1,
                key_rank(locals, rank_local),
                env,
                locals,
            ),
    ensures
        lowers(e, cx, sc, b0, b4, to_xty(sv), slots),
{
    let enums = cx.enums@;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, ls),
        slots,
        env,
        to_xty(sv),
        se.enums,
    ) by {
        lemma_run_fresh(b0, b1, b4, env, ls);
        lemma_run_len(fresh(b0, b1), env, ls);
        match eval_src(a, se, sls) {
            Err(_) => {},
            Ok(m) => {
                let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                assert(denotes(ms, env, l1, m, XTy::Map(Box::new(sk), Box::new(sv)), enums));
                lemma_ctx_weaken(cx, sc, env, se, ls, l1, sls);
                assert(ctx_ok(cx, sc, env, se, l1, sls));
                lemma_run_fresh(b1, b2, b4, env, l1);
                lemma_run_len(fresh(b1, b2), env, l1);
                match eval_src(x, se, sls) {
                    Err(_) => {},
                    Ok(y) => {
                        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                        let rows_v = m->Map_0;
                        let mem = member(y, sk, enums);
                        let rk: i64 = if mem {
                            rank(y, sk, enums) as i64
                        } else {
                            -1i64
                        };
                        assert(eval_l(rr, env, l2) == Ok::<Value, ErrKind>(Value::Int(rk)));
                        lemma_added(b2, b3, rr, Expr::Local(rank_local), env, l2, Value::Int(rk));
                        lemma_run_fresh(b2, b3, b4, env, l2);
                        let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                        assert(rank_local < l3.len() && l3[rank_local as int] == Value::Int(rk));
                        assert(key_rank(l3, rank_local) == rk as int);
                        lemma_run_push(Seq::empty(), c, env, l3);
                        assert(seq![c] =~= Seq::<Expr>::empty().push(c));
                        lemma_prefix_trans(ls, l1, l2);
                        lemma_prefix_trans(l1, l2, l3);
                        assert(keys(sk, enums) == Some(rows_v.len()));
                        if mem {
                            lemma_rank_in_domain(y, sk, enums);
                            let rkk = rank(y, sk, enums);
                            assert(0 <= rkk < rows);
                            let w1 = 1 + wd;
                            lemma_enc_rows_index(rows_v, sv, enums, rkk, 0);
                            let pos = rkk * w1;
                            assert(clean(ms, env, l1));
                            lemma_weaken(ms[pos], env, l1, l3);
                            assert(eval_l(ms[pos], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[pos]));
                            assert(slot_vals(ms, env, l1) == enc_rows(rows_v, sv, enums));
                            assert(flat_slot(ms, wd, 0, rkk, env, l3) == Ok::<Value, ErrKind>(
                                Value::Bool(rows_v[rkk] is Some),
                            ));
                            match rows_v[rkk] {
                                None => {},
                                Some(val) => {
                                    let l4 = l3.push(Value::Bool(true));
                                    lemma_prefix_trans(l3, l3, l4);
                                    lemma_prefix_trans(l1, l3, l4);
                                    assert(key_rank(l4, rank_local) == rkk);
                                    lemma_map_rows_member_index(rows_v, sv, enums, rkk);
                                    lemma_enc_len(val, sv, enums);
                                    lemma_models_enc(val, sv, enums);
                                    lemma_clean_pure(ms, env, l1);
                                    assert(all_pure(ms, l4.len())) by {
                                        assert forall|j: int| 0 <= j < ms.len() implies pure_below(#[trigger] ms[j], l4.len()) by {
                                            lemma_pure_mono(ms[j], l1.len(), l4.len());
                                        }
                                    }
                                    lemma_lits(enc(default_val(sv, enums), sv, enums), env, l4);
                                    assert(all_pure(fallback, l4.len()));
                                    assert(all_pure(slots, l4.len()));
                                    assert forall|i: int| 0 <= i < slots.len() implies pure_below(#[trigger] slots[i], l4.len())
                                        && eval_l(slots[i], env, l4) == Ok::<Value, ErrKind>(enc(val, sv, enums)[i]) by {
                                        lemma_enc_rows_index(rows_v, sv, enums, rkk, i + 1);
                                        let q = rkk * w1 + i + 1;
                                        lemma_weaken(ms[q], env, l1, l4);
                                        assert(eval_l(ms[q], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[q]));
                                        assert(eval_l(slots[i], env, l4) == flat_slot_int(ms, wd, i + 1, rkk, env, l4));
                                    }
                                    assert(slot_vals(slots, env, l4) =~= enc(val, sv, enums));
                                },
                            }
                        }
                    },
                }
            },
        }
    }
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
