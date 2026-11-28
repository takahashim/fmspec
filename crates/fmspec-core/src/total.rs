//! 下ろしの全域性の仕様（計画書 docs/plans/lowering_totality.md の手順2〜4）。
//!
//! 下ろしの文脈 [`LowerCtx`] と局所変数の束縛から、型付けの文脈 [`SCtx`] と局所変数の型を作る（[`sctx`]、[`bound_tys`]）。
//! 文脈が整形式で（[`cx_wf`]、[`sc_wf`]）、式に型が付き、式の部分の型が大きさの条件を満たすなら（[`lim_ok`]）、
//! 下ろしは `Fail::Type` で失敗せず、型の幅だけの純粋なスロットを返す（[`low_post`]）。

#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, lemma_xwidth_of, sty, to_xty, to_xtys, wf_stype, wf_stypes, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{wf_xtypes, width, xty, xwidth, xwidth_sum, XTy, XType};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, ite_s, mark_s, pure_below, setop_s};
#[cfg(verus_keep_ghost)]
use crate::infer::{ir_type_of, items_typed, lemma_items_typed_iff, SCtx};
#[cfg(verus_keep_ghost)]
use crate::limits::{lim_s, lim_ss, lim_xs};
#[cfg(verus_keep_ghost)]
use crate::lists::{picks, select_ok};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{Bound, Constant, Fail, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{layout_tys, ok_x, sc_wf, shaped};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::lemma_pure_mono;
#[cfg(verus_keep_ghost)]
use crate::rows::row_at;
#[cfg(verus_keep_ghost)]
use crate::rows::{col, flat, head_at, heads_ok, ite_row, ite_rows_ok, mparts_ok, mrow_at, parts_ok};
#[cfg(verus_keep_ghost)]
use crate::source::{Item, Over, SetOp, TExpr};
use vstd::prelude::*;

verus! {

// ---- 文脈の対応 ----

pub open spec fn const_tys(cs: Seq<Constant>) -> Seq<STy> {
    Seq::new(cs.len(), |i: int| sty(cs[i].ty))
}

/// 局所変数の束縛の型。
pub open spec fn bound_tys(sc: Seq<Bound>) -> Seq<XTy> {
    Seq::new(sc.len(), |i: int| xty(sc[i].ty))
}

/// 下ろしの文脈に対応する型付けの文脈。
pub open spec fn sctx(cx: LowerCtx) -> SCtx {
    SCtx {
        enums: cx.enums@,
        states: match cx.states {
            Some(st) => Some(layout_tys(st@)),
            None => None,
        },
        args: layout_tys(cx.args@),
        next: cx.next,
        out: match cx.out {
            Some(t) => Some(sty(t)),
            None => None,
        },
        consts: const_tys(cx.consts@),
    }
}

// ---- 整形式性 ----

/// 格納の型が整形式で、大きさの条件を満たす。
pub open spec fn ok_s(t: STy, enums: Seq<i64>) -> bool {
    wf_stype(t, enums) && lim_s(t, enums)
}

/// [`ok_s`] の不透明な形。ループの不変条件で、展開されないように使う。
#[verifier::opaque]
pub open spec fn ok_s_o(t: STy, enums: Seq<i64>) -> bool {
    ok_s(t, enums)
}

pub open spec fn layout_wf(l: Layout, enums: Seq<i64>) -> bool {
    ok_s(sty(l.ty), enums) && l.offset + width(sty(l.ty), enums) <= usize::MAX
}

/// 下ろしの文脈が整形式である。出力はスカラーで、定数のスロットは型の幅だけある。
pub open spec fn cx_wf(cx: LowerCtx) -> bool {
    let enums = cx.enums@;
    &&& match cx.states {
        Some(st) => forall|i: int| 0 <= i < st@.len() ==> #[trigger] layout_wf(st@[i], enums),
        None => true,
    }
    &&& forall|i: int| 0 <= i < cx.args@.len() ==> #[trigger] layout_wf(cx.args@[i], enums)
    &&& match cx.out {
        Some(t) => ok_s(sty(t), enums) && width(sty(t), enums) == 1 && xwidth(to_xty(sty(t)), enums) == 1,
        None => true,
    }
    &&& forall|i: int|
        0 <= i < cx.consts@.len() ==> ok_s(sty(#[trigger] cx.consts@[i].ty), enums) && cx.consts@[i].slots@.len()
            == width(sty(cx.consts@[i].ty), enums)
}

pub proof fn lemma_all_pure_mono(s: Seq<Expr>, n: nat, m: nat)
    requires
        all_pure(s, n),
        n <= m,
    ensures
        all_pure(s, m),
{
    assert forall|j: int| 0 <= j < s.len() implies crate::expr_build::pure_below(#[trigger] s[j], m) by {
        lemma_pure_mono(s[j], n, m);
    }
}

pub proof fn lemma_sc_wf_mono(sc: Seq<Bound>, n: nat, m: nat, enums: Seq<i64>)
    requires
        sc_wf(sc, n, enums),
        n <= m,
    ensures
        sc_wf(sc, m, enums),
{
    assert forall|i: int| 0 <= i < sc.len() implies ok_x(xty(#[trigger] sc[i].ty), enums) && shaped(
        sc[i].slots@,
        xty(sc[i].ty),
        m,
        enums,
    ) by {
        lemma_all_pure_mono(sc[i].slots@, n, m);
    }
}

/// 格納の型が条件を満たせば、それから作った式の型も満たす。
pub proof fn lemma_ok_to_x(t: STy, enums: Seq<i64>)
    requires
        ok_s(t, enums),
    ensures
        ok_x(to_xty(t), enums),
    decreases t, 1nat,
{
    lemma_xwidth_of(t, enums);
    match t {
        STy::Tuple(ts) => lemma_ok_to_xs(ts, enums),
        STy::Record(_, ts) => lemma_ok_to_xs(ts, enums),
        STy::Option(x) => lemma_ok_to_x(*x, enums),
        _ => {},
    }
}

pub proof fn lemma_ok_to_xs(ts: Seq<STy>, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
        lim_ss(ts, enums),
    ensures
        wf_xtypes(to_xtys(ts), enums),
        lim_xs(to_xtys(ts), enums),
        to_xtys(ts).len() == ts.len(),
        xwidth_sum(to_xtys(ts), enums) == crate::encoding::width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_ok_to_xs(ts.drop_last(), enums);
        lemma_ok_to_x(ts.last(), enums);
        lemma_xwidth_of(ts.last(), enums);
        assert(to_xtys(ts).drop_last() == to_xtys(ts.drop_last()));
        assert(to_xtys(ts).last() == to_xty(ts.last()));
    }
}

// ---- 行の形 ----

/// 各行の長さが `w` で純粋なら、つないだ列の長さは行の数と `w` の積で、純粋である。
pub proof fn lemma_flat_shape(rows: Seq<Seq<Expr>>, w: nat, n: nat)
    requires
        forall|p: int| 0 <= p < rows.len() ==> (#[trigger] rows[p]).len() == w && all_pure(rows[p], n),
    ensures
        flat(rows).len() == rows.len() * w,
        all_pure(flat(rows), n),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let pre = rows.drop_last();
        assert forall|p: int| 0 <= p < pre.len() implies (#[trigger] pre[p]).len() == w && all_pure(pre[p], n) by {
            assert(pre[p] == rows[p]);
        }
        lemma_flat_shape(pre, w, n);
        let last = rows.last();
        assert(rows[rows.len() - 1] == last);
        assert(flat(rows) == flat(pre) + last);
        assert((rows.len() - 1) * w + w == rows.len() * w) by (nonlinear_arith);
        assert forall|j: int| 0 <= j < flat(rows).len() implies pure_below(#[trigger] flat(rows)[j], n) by {
            if j < flat(pre).len() {
                assert(flat(rows)[j] == flat(pre)[j]);
            } else {
                assert(flat(rows)[j] == last[j - flat(pre).len()]);
            }
        }
    }
}

/// Mapのスロットを行に分けると、各行は長さ `w` で、元のスロットが純粋なら純粋である。
pub proof fn lemma_mrows_shape(slots: Seq<Expr>, rows: Seq<Seq<Expr>>, w: nat, k: nat, n: nat)
    requires
        mparts_ok(slots, rows, w, k),
        all_pure(slots, n),
    ensures
        forall|p: int| 0 <= p < rows.len() ==> (#[trigger] rows[p]).len() == w && all_pure(rows[p], n),
{
    assert forall|p: int| 0 <= p < rows.len() implies (#[trigger] rows[p]).len() == w && all_pure(rows[p], n) by {
        assert(mrow_at(rows[p], slots, p, w));
        let base = p * w;
        assert(rows[p] == slots.subrange(base, base + w));
        assert forall|j: int| 0 <= j < rows[p].len() implies pure_below(#[trigger] rows[p][j], n) by {
            assert(rows[p][j] == slots[base + j]);
            assert(pure_below(slots[base + j], n));
        }
    }
}

/// 番号 `k` の行だけを `alt` に置き換えた行は、`k`、`alt`、元の行が純粋なら純粋である。
pub proof fn lemma_ite_rows_shape(out: Seq<Seq<Expr>>, rows: Seq<Seq<Expr>>, k: Expr, alt: Seq<Expr>, n: nat)
    requires
        ite_rows_ok(out, rows, k, alt),
        pure_below(k, n),
        all_pure(alt, n),
        forall|p: int| 0 <= p < rows.len() ==> all_pure(#[trigger] rows[p], n),
    ensures
        out.len() == rows.len(),
        forall|p: int| 0 <= p < out.len() ==> (#[trigger] out[p]).len() == alt.len() && all_pure(out[p], n),
{
    assert forall|p: int| 0 <= p < out.len() implies (#[trigger] out[p]).len() == alt.len() && all_pure(out[p], n) by {
        assert(ite_row(out[p], rows[p], k, alt, p));
        assert(all_pure(rows[p], n));
        assert forall|j: int| 0 <= j < out[p].len() implies pure_below(#[trigger] out[p][j], n) by {
            assert(pure_below(alt[j], n));
            assert(pure_below(rows[p][j], n));
            let c = Expr::Bin(BinOp::Eq, Box::new(k), Box::new(Expr::Const(Value::Int(p as i64))));
            assert(pure_below(Expr::Const(Value::Int(p as i64)), n));
            assert(pure_below(c, n));
            assert(out[p][j] == ite_s(c, alt[j], rows[p][j]));
        }
    }
}

/// Mapの式の型が条件を満たせば、Mapの格納の型も満たす。
pub proof fn lemma_ok_map(k: STy, v: STy, enums: Seq<i64>)
    requires
        ok_x(XTy::Map(Box::new(k), Box::new(v)), enums),
    ensures
        ok_s(STy::Map(Box::new(k), Box::new(v)), enums),
        ok_s_o(STy::Map(Box::new(k), Box::new(v)), enums),
{
    reveal(ok_s_o);
    assert(xwidth(XTy::Map(Box::new(k), Box::new(v)), enums) == width(STy::Map(Box::new(k), Box::new(v)), enums));
}

/// Listの式の型が条件を満たせば、Listの格納の型と要素の型も満たす。
pub proof fn lemma_ok_list(e: STy, max: usize, enums: Seq<i64>)
    requires
        ok_x(XTy::List(Box::new(e), max), enums),
    ensures
        ok_s(STy::List(Box::new(e), max), enums),
        ok_s(e, enums),
{
    assert(xwidth(XTy::List(Box::new(e), max), enums) == width(STy::List(Box::new(e), max), enums));
}

/// Listのスロットを行に分けると、長さのスロットと各行は、元のスロットが純粋なら純粋である。
pub proof fn lemma_list_rows_shape(slots: Seq<Expr>, len: Expr, rows: Seq<Seq<Expr>>, w: nat, max: nat, n: nat)
    requires
        parts_ok(slots, len, rows, w, max),
        all_pure(slots, n),
    ensures
        pure_below(len, n),
        rows.len() == max,
        forall|p: int| 0 <= p < rows.len() ==> (#[trigger] rows[p]).len() == w && all_pure(rows[p], n),
{
    assert(pure_below(slots[0], n));
    assert forall|p: int| 0 <= p < rows.len() implies (#[trigger] rows[p]).len() == w && all_pure(rows[p], n) by {
        assert(row_at(rows[p], slots, p, w));
        let base = 1 + p * w;
        assert(rows[p] == slots.subrange(base, base + w));
        assert forall|j: int| 0 <= j < rows[p].len() implies pure_below(#[trigger] rows[p][j], n) by {
            assert(rows[p][j] == slots[base + j]);
            assert(pure_below(slots[base + j], n));
        }
    }
}

/// Setどうしの演算のスロットは、両方のスロットが純粋なら純粋である。
pub proof fn lemma_setop_pure(op: SetOp, x: Expr, y: Expr, n: nat)
    requires
        pure_below(x, n),
        pure_below(y, n),
    ensures
        pure_below(setop_s(op, x, y), n),
{
    assert(pure_below(Expr::Not(Box::new(y)), n));
    assert(pure_below(Expr::Or(Box::new(x), Box::new(y)), n));
    assert(pure_below(Expr::And(Box::new(x), Box::new(y)), n));
    assert(pure_below(Expr::And(Box::new(x), Box::new(Expr::Not(Box::new(y)))), n));
    assert(pure_below(Expr::Implies(Box::new(x), Box::new(y)), n));
}

/// 行を選んだスロットは、行の長さだけあり、行と添字が純粋なら純粋である。
pub proof fn lemma_select_shape(rows: Seq<Seq<Expr>>, idx: Expr, out: Seq<Expr>, w: nat, n: nat)
    requires
        select_ok(rows, idx, out),
        forall|p: int| 0 <= p < rows.len() ==> (#[trigger] rows[p]).len() == w && all_pure(rows[p], n),
        pure_below(idx, n),
    ensures
        out.len() == w,
        all_pure(out, n),
{
    assert(rows[0].len() == out.len());
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], n) by {
        assert(picks(out[j], col(rows, j), idx));
        assert(all_pure(col(rows, j), n)) by {
            assert forall|t: int| 0 <= t < col(rows, j).len() implies pure_below(#[trigger] col(rows, j)[t], n) by {
                assert(col(rows, j)[t] == rows[t][j]);
                assert(all_pure(rows[t], n));
            }
        }
    }
}

/// 各行の先頭は、行が純粋なら純粋である。
pub proof fn lemma_heads_pure(h: Seq<Expr>, rows: Seq<Seq<Expr>>, n: nat)
    requires
        heads_ok(h, rows),
        forall|p: int| 0 <= p < rows.len() ==> all_pure(#[trigger] rows[p], n),
    ensures
        all_pure(h, n),
        h.len() == rows.len(),
{
    assert forall|q: int| 0 <= q < h.len() implies pure_below(#[trigger] h[q], n) by {
        assert(head_at(h[q], rows[q]));
        assert(all_pure(rows[q], n));
    }
}

/// Setの印付けの結果は、元のスロットと番号が純粋なら純粋である。
pub proof fn lemma_mark_pure(on: bool, bits: Seq<Expr>, r: Expr, out: Seq<Expr>, n: nat)
    requires
        out.len() == bits.len(),
        forall|k: int| 0 <= k < bits.len() ==> #[trigger] out[k] == mark_s(on, bits[k], r, k as i64),
        all_pure(bits, n),
        pure_below(r, n),
    ensures
        all_pure(out, n),
{
    assert forall|k: int| 0 <= k < out.len() implies pure_below(#[trigger] out[k], n) by {
        assert(out[k] == mark_s(on, bits[k], r, k as i64));
        assert(pure_below(bits[k], n));
        assert(pure_below(Expr::Const(Value::Int(k as i64)), n));
        let ce = Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64))));
        let cn = Expr::Bin(BinOp::Ne, Box::new(r), Box::new(Expr::Const(Value::Int(k as i64))));
        assert(pure_below(ce, n));
        assert(pure_below(cn, n));
        assert(pure_below(Expr::Or(Box::new(bits[k]), Box::new(ce)), n));
        assert(pure_below(Expr::And(Box::new(bits[k]), Box::new(cn)), n));
    }
}

// ---- 式の大きさの条件 ----

/// 量化でたどる値の型（[`ir_type_of`] の量化の規則と同じ）。
pub open spec fn quant_bound(over: Over, c: SCtx, lt: Seq<XTy>) -> Option<XTy> {
    match over {
        Over::Type(t) => if wf_stype(sty(t), c.enums) && keys(sty(t), c.enums) is Some {
            Some(to_xty(sty(t)))
        } else {
            None
        },
        Over::Set(t, s) => if ir_type_of(*s, c, lt) == Some(XTy::Set(Box::new(sty(t)))) {
            Some(to_xty(sty(t)))
        } else {
            None
        },
        Over::Map(t, m) => match ir_type_of(*m, c, lt) {
            Some(XTy::Map(k, _)) => if *k == sty(t) {
                Some(to_xty(sty(t)))
            } else {
                None
            },
            _ => None,
        },
        Over::List(l) => match ir_type_of(*l, c, lt) {
            Some(XTy::List(t, _)) => Some(to_xty(*t)),
            _ => None,
        },
    }
}

/// 型が付くなら、その型は整形式で大きさの条件を満たす。
pub open spec fn here_ok(e: TExpr, c: SCtx, lt: Seq<XTy>) -> bool {
    match ir_type_of(e, c, lt) {
        Some(x) => ok_x(x, c.enums),
        None => true,
    }
}

/// 式とその部分式の型が、整形式で大きさの条件を満たす。
/// 量化で型の全体をたどるときは、その型も条件を満たす。
pub open spec fn lim_ok(e: TExpr, c: SCtx, lt: Seq<XTy>) -> bool
    decreases e, 0nat,
{
    &&& here_ok(e, c, lt)
    &&& match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_)
        | TExpr::Const(_) | TExpr::None(_) => true,
        TExpr::Bin(_, a, b) | TExpr::Eq(_, a, b) | TExpr::Implies(a, b) | TExpr::SetBin(_, a, b) | TExpr::At(a, b)
        | TExpr::ListContains(a, b) | TExpr::SetContains(_, a, b) | TExpr::Insert(_, a, b) | TExpr::Remove(_, a, b)
        | TExpr::HasKey(_, a, b) | TExpr::Get(_, a, b) | TExpr::Delete(_, a, b) | TExpr::Push(_, _, a, b) => lim_ok(
            *a,
            c,
            lt,
        ) && lim_ok(*b, c, lt),
        TExpr::Not(a) | TExpr::Some(a) | TExpr::IsSome(a) | TExpr::IsNone(a) | TExpr::Unwrap(a) | TExpr::Size(a)
        | TExpr::IsEmpty(a) | TExpr::Keys(a) | TExpr::First(a) | TExpr::Last(a) | TExpr::Pop(a) | TExpr::Shift(a)
        | TExpr::Nth(a, _) | TExpr::Field(a, _, _) => lim_ok(*a, c, lt),
        TExpr::Ite(p, a, b) => lim_ok(*p, c, lt) && lim_ok(*a, c, lt) && lim_ok(*b, c, lt),
        TExpr::Put(_, _, a, x, y) => lim_ok(*a, c, lt) && lim_ok(*x, c, lt) && lim_ok(*y, c, lt),
        TExpr::Let(a, b) => lim_ok(*a, c, lt) && match ir_type_of(*a, c, lt) {
            Some(x) => lim_ok(*b, c, lt.push(x)),
            None => true,
        },
        TExpr::Fold(_, es) | TExpr::Tuple(es) | TExpr::Record(_, es) | TExpr::SetLit(_, es) | TExpr::ListLit(
            _,
            _,
            es,
        ) => lim_ok_seq(es@, c, lt),
        TExpr::MapLit(_, _, items) => lim_ok_items(items@, c, lt),
        TExpr::Quant(_, over, body) => {
            &&& match over {
                Over::Type(t) => lim_s(sty(t), c.enums),
                Over::Set(_, s) => lim_ok(*s, c, lt),
                Over::Map(_, m) => lim_ok(*m, c, lt),
                Over::List(l) => lim_ok(*l, c, lt),
            }
            &&& match quant_bound(over, c, lt) {
                Some(x) => lim_ok(*body, c, lt.push(x)),
                None => true,
            }
        },
    }
}

pub open spec fn lim_ok_seq(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>) -> bool
    decreases es, 1nat,
{
    if es.len() == 0 {
        true
    } else {
        lim_ok_seq(es.drop_last(), c, lt) && lim_ok(es.last(), c, lt)
    }
}

pub open spec fn lim_ok_items(items: Seq<Item>, c: SCtx, lt: Seq<XTy>) -> bool
    decreases items, 1nat,
{
    if items.len() == 0 {
        true
    } else {
        lim_ok_items(items.drop_last(), c, lt) && lim_ok(items.last().key, c, lt) && lim_ok(items.last().value, c, lt)
    }
}

pub proof fn lemma_lim_ok_seq_at(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>, i: int)
    requires
        lim_ok_seq(es, c, lt),
        0 <= i < es.len(),
    ensures
        lim_ok(es[i], c, lt),
    decreases es.len(),
{
    if i < es.len() - 1 {
        assert(es.drop_last()[i] == es[i]);
        lemma_lim_ok_seq_at(es.drop_last(), c, lt, i);
    }
}

pub proof fn lemma_lim_ok_items_at(items: Seq<Item>, c: SCtx, lt: Seq<XTy>, i: int)
    requires
        lim_ok_items(items, c, lt),
        0 <= i < items.len(),
    ensures
        lim_ok(items[i].key, c, lt),
        lim_ok(items[i].value, c, lt),
    decreases items.len(),
{
    if i < items.len() - 1 {
        assert(items.drop_last()[i] == items[i]);
        lemma_lim_ok_items_at(items.drop_last(), c, lt, i);
    }
}

/// Mapのリテラルの項目のキーと値に型が付き、大きさの条件を満たす。
#[verifier::opaque]
pub open spec fn items_ok(items: Seq<Item>, c: SCtx, bt: Seq<XTy>, kt: STy, vt: STy) -> bool {
    forall|j: int|
        0 <= j < items.len() ==> ir_type_of((#[trigger] items[j]).key, c, bt) == Some(to_xty(kt)) && ir_type_of(
            items[j].value,
            c,
            bt,
        ) == Some(to_xty(vt)) && lim_ok(items[j].key, c, bt) && lim_ok(items[j].value, c, bt)
}

pub proof fn lemma_items_ok_intro(items: Seq<Item>, c: SCtx, bt: Seq<XTy>, kt: STy, vt: STy)
    requires
        items_typed(items, to_xty(kt), to_xty(vt), c, bt),
        lim_ok_items(items, c, bt),
    ensures
        items_ok(items, c, bt, kt, vt),
{
    reveal(items_ok);
    lemma_items_typed_iff(items, to_xty(kt), to_xty(vt), c, bt);
    assert forall|j: int| 0 <= j < items.len() implies ir_type_of((#[trigger] items[j]).key, c, bt) == Some(to_xty(kt))
        && ir_type_of(items[j].value, c, bt) == Some(to_xty(vt)) && lim_ok(items[j].key, c, bt) && lim_ok(
        items[j].value,
        c,
        bt,
    ) by {
        lemma_lim_ok_items_at(items, c, bt, j);
    }
}

pub proof fn lemma_items_ok_at(items: Seq<Item>, c: SCtx, bt: Seq<XTy>, kt: STy, vt: STy, j: int)
    requires
        items_ok(items, c, bt, kt, vt),
        0 <= j < items.len(),
    ensures
        ir_type_of(items[j].key, c, bt) == Some(to_xty(kt)),
        ir_type_of(items[j].value, c, bt) == Some(to_xty(vt)),
        lim_ok(items[j].key, c, bt),
        lim_ok(items[j].value, c, bt),
{
    reveal(items_ok);
}

// ---- 下ろしの前提と結論 ----

/// 下ろしの全域性の前提。`n` は束縛の列の深さ。
pub open spec fn tpre(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat) -> bool {
    &&& cx_wf(cx)
    &&& sc_wf(sc, n, cx.enums@)
    &&& ir_type_of(e, sctx(cx), bound_tys(sc)) is Some
    &&& lim_ok(e, sctx(cx), bound_tys(sc))
}

/// [`put_pre`] を部品から組み立てる。
pub proof fn lemma_put_pre(key: TExpr, value: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat, kt: STy, vt: STy, ms: Seq<Expr>)
    requires
        tpre(key, cx, sc, n),
        tpre(value, cx, sc, n),
        ir_type_of(key, sctx(cx), bound_tys(sc)) == Some(to_xty(kt)),
        ir_type_of(value, sctx(cx), bound_tys(sc)) == Some(to_xty(vt)),
        ok_s_o(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
        ms.len() == width(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
        all_pure(ms, n),
    ensures
        put_pre(key, value, cx, sc, n, kt, vt, ms),
{
    reveal(put_pre);
    reveal(ok_s_o);
}

/// [`crate::lowering`] の `put` の前提。Mapのスロット `ms` は型の幅だけあって純粋で、キーと値の式に型が付く。
#[verifier::opaque]
pub open spec fn put_pre(key: TExpr, value: TExpr, cx: LowerCtx, sc: Seq<Bound>, n: nat, kt: STy, vt: STy, ms: Seq<Expr>) -> bool {
    let mt = STy::Map(Box::new(kt), Box::new(vt));
    &&& tpre(key, cx, sc, n)
    &&& tpre(value, cx, sc, n)
    &&& ir_type_of(key, sctx(cx), bound_tys(sc)) == Some(to_xty(kt))
    &&& ir_type_of(value, sctx(cx), bound_tys(sc)) == Some(to_xty(vt))
    &&& ok_s(mt, cx.enums@)
    &&& ms.len() == width(mt, cx.enums@)
    &&& all_pure(ms, n)
}

/// Setの型 `x` の要素の型は `t` で、要素の型は値の数を持つ。
pub open spec fn n_ok_set(x: XTy, t: STy, enums: Seq<i64>) -> bool {
    x == XTy::Set(Box::new(t)) ==> keys(t, enums) is Some
}

/// 失敗するなら、束縛の深さが上限に達したためである。
pub open spec fn deep<T>(r: Result<T, Fail>) -> bool {
    match r {
        Err(f) => f == Fail::Depth,
        Ok(_) => true,
    }
}

pub open spec fn scalar_x(t: XTy) -> bool {
    t is Bool || t is Int || t is Enum
}

/// 下ろしの全域性の結論。`Fail::Type` で失敗せず、成功したら型は `ir_type_of` の値で、スロットは深さ `m` で整形式である。
pub open spec fn low_post(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, m: nat, r: Result<(XType, Vec<Expr>), Fail>) -> bool {
    match r {
        Err(f) => f == Fail::Depth,
        Ok((t, slots)) => Some(xty(t)) == ir_type_of(e, sctx(cx), bound_tys(sc)) && shaped(slots@, xty(t), m, cx.enums@),
    }
}

pub proof fn lemma_lim_ok_seq_intro(es: Seq<TExpr>, c: crate::infer::SCtx, lt: Seq<XTy>)
    requires
        forall|i: int| 0 <= i < es.len() ==> lim_ok(#[trigger] es[i], c, lt),
    ensures
        lim_ok_seq(es, c, lt),
    decreases es.len(),
{
    if es.len() > 0 {
        assert forall|i: int| 0 <= i < es.len() - 1 implies lim_ok(#[trigger] es.drop_last()[i], c, lt) by {
            assert(es.drop_last()[i] == es[i]);
        }
        lemma_lim_ok_seq_intro(es.drop_last(), c, lt);
    }
}

pub proof fn lemma_lim_ok_items_intro(items: Seq<Item>, c: crate::infer::SCtx, lt: Seq<XTy>)
    requires
        forall|i: int| 0 <= i < items.len() ==> lim_ok((#[trigger] items[i]).key, c, lt) && lim_ok(items[i].value, c, lt),
    ensures
        lim_ok_items(items, c, lt),
    decreases items.len(),
{
    if items.len() > 0 {
        assert forall|i: int| 0 <= i < items.len() - 1 implies lim_ok((#[trigger] items.drop_last()[i]).key, c, lt)
            && lim_ok(items.drop_last()[i].value, c, lt) by {
            assert(items.drop_last()[i] == items[i]);
        }
        lemma_lim_ok_items_intro(items.drop_last(), c, lt);
    }
}

} // verus!
