//! 下ろした中核の式の型（計画書 docs/plans/lowering_totality.md の手順6b）。
//!
//! 下ろしの文脈 [`LowerCtx`] から中核の型検査の文脈 [`lenv`] を作る。
//! 式の型 `t` のスロットの中核の型は [`xetys`] で、格納の型のスロットの型 [`slot_tys`] の中核の型と一致する。
//! 束縛の列の局所変数の型は [`lts`] で、外側の局所変数の型に、各束縛の式の型を順に加えたものである。

#[cfg(verus_keep_ghost)]
use crate::encoding::{keys_or_zero, sty, to_xty, to_xtys, wf_xtype, width, width_sum, STy, XTy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{xty, xwidth, xwidth_sum};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, pure_below};
#[cfg(verus_keep_ghost)]
use crate::limits::lim_x;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{Block, Bound, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::typing::{ety_of, type_l, ETy, TyEnv};
use vstd::prelude::*;

verus! {

// ---- 型の列 ----

/// スロットの型の列の中核の型。
pub open spec fn etys(ts: Seq<Type>) -> Seq<ETy> {
    Seq::new(ts.len(), |i: int| ety_of(ts[i]))
}

/// 列 `xs` を `n` 回つなげた列。
pub open spec fn ety_repeat(xs: Seq<ETy>, n: nat) -> Seq<ETy>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        ety_repeat(xs, (n - 1) as nat) + xs
    }
}

/// 式の型 `t` の各スロットの中核の型。
pub open spec fn xetys(t: XTy, enums: Seq<i64>) -> Seq<ETy>
    decreases t,
{
    match t {
        XTy::Bool => seq![ETy::Bool],
        XTy::Int => seq![ETy::Int],
        XTy::Enum(id) => seq![ETy::Enum(id)],
        XTy::Tuple(ts) => xetys_seq(ts, enums),
        XTy::Record(_, ts) => xetys_seq(ts, enums),
        XTy::Option(x) => seq![ETy::Bool] + xetys(*x, enums),
        XTy::Set(e) => etys(slot_tys(STy::Set(e), enums)),
        XTy::Map(k, v) => etys(slot_tys(STy::Map(k, v), enums)),
        XTy::List(e, max) => etys(slot_tys(STy::List(e, max), enums)),
    }
}

pub open spec fn xetys_seq(ts: Seq<XTy>, enums: Seq<i64>) -> Seq<ETy>
    decreases ts,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        xetys_seq(ts.drop_last(), enums) + xetys(ts.last(), enums)
    }
}


pub proof fn lemma_etys_concat(a: Seq<Type>, b: Seq<Type>)
    ensures
        etys(a + b) == etys(a) + etys(b),
{
    assert(etys(a + b) =~= etys(a) + etys(b));
}

/// 式の型のスロットの数は、式の型の幅である。
pub proof fn lemma_xetys_len(t: XTy, enums: Seq<i64>)
    ensures
        xetys(t, enums).len() == xwidth(t, enums),
    decreases t, 1nat,
{
    match t {
        XTy::Tuple(ts) => lemma_xetys_seq_len(ts, enums),
        XTy::Record(_, ts) => lemma_xetys_seq_len(ts, enums),
        XTy::Option(x) => lemma_xetys_len(*x, enums),
        XTy::Set(e) => lemma_slot_tys_len(STy::Set(e), enums),
        XTy::Map(k, v) => lemma_slot_tys_len(STy::Map(k, v), enums),
        XTy::List(e, max) => lemma_slot_tys_len(STy::List(e, max), enums),
        _ => {},
    }
}

pub proof fn lemma_xetys_seq_len(ts: Seq<XTy>, enums: Seq<i64>)
    ensures
        xetys_seq(ts, enums).len() == xwidth_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_xetys_seq_len(ts.drop_last(), enums);
        lemma_xetys_len(ts.last(), enums);
    }
}

/// 格納の型の式の型のスロットの中核の型は、格納の型のスロットの型の中核の型である。
pub proof fn lemma_xetys_of(t: STy, enums: Seq<i64>)
    ensures
        xetys(to_xty(t), enums) == etys(slot_tys(t, enums)),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_xetys_seq_of(ts, enums),
        STy::Record(_, ts) => lemma_xetys_seq_of(ts, enums),
        STy::Option(x) => {
            lemma_xetys_of(*x, enums);
            lemma_etys_concat(seq![Type::Bool], slot_tys(*x, enums));
            assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
        },
        STy::Bool => assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]),
        STy::Int(lo, hi) => assert(etys(seq![Type::Int(lo, hi)]) =~= seq![ETy::Int]),
        STy::Enum(id) => assert(etys(seq![Type::Enum(id)]) =~= seq![ETy::Enum(id)]),
        _ => {},
    }
}

pub proof fn lemma_xetys_seq_of(ts: Seq<STy>, enums: Seq<i64>)
    ensures
        xetys_seq(to_xtys(ts), enums) == etys(slot_tys_seq(ts, enums)),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let a = ts.drop_last();
        lemma_xetys_seq_of(a, enums);
        lemma_xetys_of(ts.last(), enums);
        assert(to_xtys(ts).drop_last() == to_xtys(a));
        assert(to_xtys(ts).last() == to_xty(ts.last()));
        lemma_etys_concat(slot_tys_seq(a, enums), slot_tys(ts.last(), enums));
    } else {
        assert(etys(Seq::<Type>::empty()) =~= Seq::<ETy>::empty());
    }
}



/// 式の型が格納の型に合うなら、スロットの中核の型は等しい。
pub proof fn lemma_fits_etys(t: XTy, st: STy, enums: Seq<i64>)
    requires
        crate::fits::fits_s(t, st),
    ensures
        xetys(t, enums) == etys(slot_tys(st, enums)),
    decreases t, 1nat,
{
    match (t, st) {
        (XTy::Tuple(xs), STy::Tuple(ts)) => lemma_fits_etys_seq(xs, ts, enums),
        (XTy::Record(_, xs), STy::Record(_, ts)) => lemma_fits_etys_seq(xs, ts, enums),
        (XTy::Option(x), STy::Option(u)) => {
            lemma_fits_etys(*x, *u, enums);
            lemma_etys_concat(seq![Type::Bool], slot_tys(*u, enums));
            assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
        },
        (XTy::Bool, STy::Bool) => assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]),
        (XTy::Int, STy::Int(lo, hi)) => assert(etys(seq![Type::Int(lo, hi)]) =~= seq![ETy::Int]),
        (XTy::Enum(id), STy::Enum(_)) => assert(etys(seq![Type::Enum(id)]) =~= seq![ETy::Enum(id)]),
        _ => {},
    }
}

pub proof fn lemma_fits_etys_seq(xs: Seq<XTy>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        crate::fits::fits_all_s(xs, ts),
    ensures
        xetys_seq(xs, enums) == etys(slot_tys_seq(ts, enums)),
    decreases xs, 0nat,
{
    if xs.len() > 0 {
        lemma_fits_etys_seq(xs.drop_last(), ts.drop_last(), enums);
        lemma_fits_etys(xs.last(), ts.last(), enums);
        lemma_etys_concat(slot_tys_seq(ts.drop_last(), enums), slot_tys(ts.last(), enums));
    } else {
        assert(etys(Seq::<Type>::empty()) =~= Seq::<ETy>::empty());
    }
}

// ---- スロットの列の型 ----

pub proof fn lemma_typed_sub(xs: Seq<Expr>, ys: Seq<ETy>, t: TyEnv, lt: Seq<ETy>, lo: int, hi: int)
    requires
        typed(xs, ys, t, lt),
        0 <= lo <= hi <= xs.len(),
    ensures
        typed(xs.subrange(lo, hi), ys.subrange(lo, hi), t, lt),
{
    assert forall|i: int| 0 <= i < hi - lo implies #[trigger] has_ty(xs.subrange(lo, hi)[i], t, lt, ys.subrange(lo, hi)[i]) by {
        assert(has_ty(xs[lo + i], t, lt, ys[lo + i]));
    }
}

pub proof fn lemma_typed_concat(a: Seq<Expr>, ya: Seq<ETy>, b: Seq<Expr>, yb: Seq<ETy>, t: TyEnv, lt: Seq<ETy>)
    requires
        typed(a, ya, t, lt),
        typed(b, yb, t, lt),
    ensures
        typed(a + b, ya + yb, t, lt),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies #[trigger] has_ty((a + b)[i], t, lt, (ya + yb)[i]) by {
        if i < a.len() {
            assert(has_ty(a[i], t, lt, ya[i]));
        } else {
            assert(has_ty(b[i - a.len()], t, lt, yb[i - a.len()]));
        }
    }
}

/// 型の列の `k` 番目の型のスロットは、全体のスロットの、位置 `xoff` からの部分である。
pub proof fn lemma_xetys_part(ts: Seq<XTy>, k: int, enums: Seq<i64>)
    requires
        0 <= k < ts.len(),
    ensures
        xwidth_sum(ts.take(k), enums) + xwidth(ts[k], enums) <= xetys_seq(ts, enums).len(),
        xetys_seq(ts, enums).subrange(
            xwidth_sum(ts.take(k), enums) as int,
            (xwidth_sum(ts.take(k), enums) + xwidth(ts[k], enums)) as int,
        ) == xetys(ts[k], enums),
    decreases ts.len(),
{
    let a = ts.drop_last();
    lemma_xetys_seq_len(a, enums);
    lemma_xetys_len(ts.last(), enums);
    lemma_xetys_seq_len(ts, enums);
    if k == ts.len() - 1 {
        assert(ts.take(k) =~= a);
        assert(xetys_seq(ts, enums).subrange(xwidth_sum(a, enums) as int, xetys_seq(ts, enums).len() as int)
            =~= xetys(ts.last(), enums));
    } else {
        lemma_xetys_part(a, k, enums);
        assert(a.take(k) =~= ts.take(k));
        assert(a[k] == ts[k]);
        assert(xetys_seq(ts, enums).subrange(
            xwidth_sum(ts.take(k), enums) as int,
            (xwidth_sum(ts.take(k), enums) + xwidth(ts[k], enums)) as int,
        ) =~= xetys_seq(a, enums).subrange(
            xwidth_sum(ts.take(k), enums) as int,
            (xwidth_sum(ts.take(k), enums) + xwidth(ts[k], enums)) as int,
        ));
    }
}

/// 型の列をつなげた列。
pub open spec fn econcat(yss: Seq<Seq<ETy>>) -> Seq<ETy>
    decreases yss.len(),
{
    if yss.len() == 0 {
        Seq::empty()
    } else {
        econcat(yss.drop_last()) + yss.last()
    }
}

pub proof fn lemma_concat_typed(xss: Seq<Seq<Expr>>, yss: Seq<Seq<ETy>>, t: TyEnv, lt: Seq<ETy>)
    requires
        xss.len() == yss.len(),
        forall|k: int| 0 <= k < xss.len() ==> #[trigger] typed(xss[k], yss[k], t, lt),
    ensures
        typed(crate::expr_build::concat(xss), econcat(yss), t, lt),
    decreases xss.len(),
{
    if xss.len() > 0 {
        let a = xss.drop_last();
        let b = yss.drop_last();
        assert forall|k: int| 0 <= k < a.len() implies #[trigger] typed(a[k], b[k], t, lt) by {
            assert(typed(xss[k], yss[k], t, lt));
        }
        lemma_concat_typed(a, b, t, lt);
        assert(typed(xss[xss.len() - 1], yss[yss.len() - 1], t, lt));
        lemma_typed_concat(crate::expr_build::concat(a), econcat(b), xss.last(), yss.last(), t, lt);
    }
}

/// スロットの型に属する値のリテラルは、その中核の型を持つ。
pub proof fn lemma_lits_typed(vs: Seq<crate::model::Value>, tys: Seq<Type>, t: TyEnv, lt: Seq<ETy>)
    requires
        crate::lower_types::in_slots(vs, tys, t.enums),
    ensures
        typed(crate::expr_build::lits(vs), etys(tys), t, lt),
{
    assert forall|i: int| 0 <= i < vs.len() implies #[trigger] has_ty(crate::expr_build::lits(vs)[i], t, lt, etys(tys)[i]) by {
        assert(crate::lower_types::in_slot(tys[i], vs[i], t.enums));
    }
}

/// Bool の式の木は Bool の型を持つ。和の木は Int の型を持つ。
pub proof fn lemma_tree_typed(items: Seq<Expr>, unit: Expr, k: crate::expr_build::Join, t: TyEnv, lt: Seq<ETy>, y: ETy)
    requires
        y == (if k is Add { ETy::Int } else { ETy::Bool }),
        has_ty(unit, t, lt, y),
        forall|i: int| 0 <= i < items.len() ==> #[trigger] has_ty(items[i], t, lt, y),
    ensures
        has_ty(crate::expr_build::tree_s(items, unit, k), t, lt, y),
    decreases items.len(),
{
    if items.len() > 1 {
        let m = items.len() / 2;
        let a = items.take(m as int);
        let b = items.skip(m as int);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] has_ty(a[i], t, lt, y) by {
            assert(has_ty(items[i], t, lt, y));
        }
        assert forall|i: int| 0 <= i < b.len() implies #[trigger] has_ty(b[i], t, lt, y) by {
            assert(has_ty(items[m + i], t, lt, y));
        }
        lemma_tree_typed(a, unit, k, t, lt, y);
        lemma_tree_typed(b, unit, k, t, lt, y);
    } else if items.len() == 1 {
        assert(has_ty(items[0], t, lt, y));
    }
}



pub proof fn lemma_smalls_at(ts: Seq<STy>, i: int)
    requires
        crate::limits::smalls(ts),
        0 <= i < ts.len(),
    ensures
        crate::limits::small(ts[i]),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        lemma_smalls_at(ts.drop_last(), i);
    }
}

/// 型の列の各型のスロットの型をつなげた列は、型の列のスロットの型である。
pub proof fn lemma_econcat_xetys(ts: Seq<XTy>, enums: Seq<i64>)
    ensures
        econcat(Seq::new(ts.len(), |k: int| xetys(ts[k], enums))) == xetys_seq(ts, enums),
    decreases ts.len(),
{
    let yss = Seq::new(ts.len(), |k: int| xetys(ts[k], enums));
    if ts.len() > 0 {
        let a = ts.drop_last();
        lemma_econcat_xetys(a, enums);
        assert(yss.drop_last() =~= Seq::new(a.len(), |k: int| xetys(a[k], enums)));
    } else {
        assert(yss =~= Seq::<Seq<ETy>>::empty());
    }
}

// ---- 文脈 ----

/// 下ろしの文脈に対応する中核の型検査の文脈。
pub open spec fn lenv(cx: LowerCtx) -> TyEnv {
    TyEnv {
        enums: cx.enums@,
        st_tys: match cx.states {
            Some(st) => slot_tys_seq(layout_tys(st@), cx.enums@),
            None => Seq::empty(),
        },
        arg_tys: slot_tys_seq(layout_tys(cx.args@), cx.enums@),
        next: cx.next,
        out: match cx.out {
            Some(t) => Some(ety_of(slot_tys(crate::encoding::sty(t), cx.enums@)[0])),
            None => None,
        },
    }
}

// ---- 式の型 ----

/// 式 `e` は型 `y` を持つ。
pub open spec fn has_ty(e: Expr, t: TyEnv, lt: Seq<ETy>, y: ETy) -> bool {
    type_l(e, t, lt) == Some(y)
}

/// 式の列 `xs` の各式は、どれも型 `y` を持つ。
pub open spec fn all_ty(xs: Seq<Expr>, y: ETy, t: TyEnv, lt: Seq<ETy>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] has_ty(xs[i], t, lt, y)
}

/// スロットの式の列 `xs` は、それぞれ型 `ys` を持つ。
pub open spec fn typed(xs: Seq<Expr>, ys: Seq<ETy>, t: TyEnv, lt: Seq<ETy>) -> bool {
    &&& xs.len() == ys.len()
    &&& forall|i: int| 0 <= i < xs.len() ==> #[trigger] has_ty(xs[i], t, lt, ys[i])
}

/// 深さ `n` 未満の局所変数だけを参照する純粋な式の型は、局所変数の型の列の先頭 `n` 個だけで決まる。
pub proof fn lemma_pure_type(e: Expr, t: TyEnv, l1: Seq<ETy>, l2: Seq<ETy>, n: nat)
    requires
        pure_below(e, n),
        n <= l1.len(),
        n <= l2.len(),
        l1.take(n as int) == l2.take(n as int),
    ensures
        type_l(e, t, l1) == type_l(e, t, l2),
    decreases e,
{
    match e {
        Expr::Local(i) => {
            assert(l1[i as int] == l1.take(n as int)[i as int]);
            assert(l2[i as int] == l2.take(n as int)[i as int]);
        },
        Expr::Bin(_, a, b) => {
            lemma_pure_type(*a, t, l1, l2, n);
            lemma_pure_type(*b, t, l1, l2, n);
        },
        Expr::And(a, b) => {
            lemma_pure_type(*a, t, l1, l2, n);
            lemma_pure_type(*b, t, l1, l2, n);
        },
        Expr::Or(a, b) => {
            lemma_pure_type(*a, t, l1, l2, n);
            lemma_pure_type(*b, t, l1, l2, n);
        },
        Expr::Implies(a, b) => {
            lemma_pure_type(*a, t, l1, l2, n);
            lemma_pure_type(*b, t, l1, l2, n);
        },
        Expr::Not(a) => lemma_pure_type(*a, t, l1, l2, n),
        Expr::Code(a) => lemma_pure_type(*a, t, l1, l2, n),
        Expr::Ite(c, a, b) => {
            lemma_pure_type(*c, t, l1, l2, n);
            lemma_pure_type(*a, t, l1, l2, n);
            lemma_pure_type(*b, t, l1, l2, n);
        },
        _ => {},
    }
}

/// 局所変数の型の列を後ろに伸ばしても、純粋なスロットの型は変わらない。
pub proof fn lemma_typed_ext(xs: Seq<Expr>, ys: Seq<ETy>, t: TyEnv, l1: Seq<ETy>, l2: Seq<ETy>, n: nat)
    requires
        typed(xs, ys, t, l1),
        forall|i: int| 0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], n),
        n <= l1.len(),
        n <= l2.len(),
        l1.take(n as int) == l2.take(n as int),
    ensures
        typed(xs, ys, t, l2),
{
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] has_ty(xs[i], t, l2, ys[i]) by {
        assert(has_ty(xs[i], t, l1, ys[i]));
        lemma_pure_type(xs[i], t, l1, l2, n);
    }
}

// ---- 束縛の列 ----

/// 束縛の列 `b` の後の局所変数の型。
pub open spec fn blt(b: Block, cx: LowerCtx) -> Seq<ETy> {
    lts(b.outer@, b.binds@, lenv(cx))
}

/// 外側の局所変数の型 `outer` の下で、束縛の列 `binds` を順に束縛した後の局所変数の型。
/// 型の付かない束縛の型は Bool とする（[`binds_typed`] が成り立てば現れない）。
pub open spec fn lts(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv) -> Seq<ETy>
    decreases binds.len(),
{
    if binds.len() == 0 {
        outer
    } else {
        let pre = lts(outer, binds.drop_last(), t);
        pre.push(
            match type_l(binds.last(), t, pre) {
                Some(y) => y,
                None => ETy::Bool,
            },
        )
    }
}

/// 束縛の列の各式に型が付く。
pub open spec fn binds_typed(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv) -> bool {
    forall|i: int| 0 <= i < binds.len() ==> #[trigger] type_l(binds[i], t, lts(outer, binds.take(i), t)) is Some
}

pub proof fn lemma_lts_len(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv)
    ensures
        lts(outer, binds, t).len() == outer.len() + binds.len(),
    decreases binds.len(),
{
    if binds.len() > 0 {
        lemma_lts_len(outer, binds.drop_last(), t);
    }
}

/// 束縛の列の先頭部分の局所変数の型は、全体の局所変数の型の先頭部分である。
pub proof fn lemma_lts_prefix(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv, k: int)
    requires
        0 <= k <= binds.len(),
    ensures
        lts(outer, binds, t).take(outer.len() + k) == lts(outer, binds.take(k), t),
    decreases binds.len(),
{
    lemma_lts_len(outer, binds, t);
    lemma_lts_len(outer, binds.take(k), t);
    if k == binds.len() {
        assert(binds.take(k) =~= binds);
        assert(lts(outer, binds, t).take(outer.len() + k) =~= lts(outer, binds, t));
    } else {
        let a = binds.drop_last();
        lemma_lts_prefix(outer, a, t, k);
        assert(a.take(k) =~= binds.take(k));
        lemma_lts_len(outer, a, t);
        assert(lts(outer, binds, t).take(outer.len() + k) =~= lts(outer, a, t).take(outer.len() + k));
    }
}

/// 束縛の `i` 番目の局所変数の型は、その束縛の式の型である。
pub proof fn lemma_lts_at(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv, i: int)
    requires
        0 <= i < binds.len(),
        binds_typed(outer, binds, t),
    ensures
        type_l(binds[i], t, lts(outer, binds.take(i), t)) == Some(lts(outer, binds, t)[outer.len() + i]),
{
    lemma_lts_prefix(outer, binds, t, i + 1);
    let b = binds.take(i + 1);
    assert(b.drop_last() =~= binds.take(i));
    assert(b.last() == binds[i]);
    let pre = lts(outer, binds.take(i), t);
    assert(type_l(binds[i], t, pre) is Some);
    let y = type_l(binds[i], t, pre)->Some_0;
    assert(lts(outer, b, t) == lts(outer, b.drop_last(), t).push(
        match type_l(b.last(), t, lts(outer, b.drop_last(), t)) {
            Some(y) => y,
            None => ETy::Bool,
        },
    ));
    assert(lts(outer, b, t) == pre.push(y));
    lemma_lts_len(outer, binds.take(i), t);
    lemma_lts_len(outer, binds, t);
    assert(lts(outer, b, t)[outer.len() + i] == y);
    assert(lts(outer, binds, t).take(outer.len() + i + 1)[outer.len() + i] == lts(outer, binds, t)[outer.len() + i]);
}

/// 型の付く束縛を1つ加えても、束縛の列は型が付く。
pub proof fn lemma_binds_push(outer: Seq<ETy>, binds: Seq<Expr>, t: TyEnv, e: Expr)
    requires
        binds_typed(outer, binds, t),
        type_l(e, t, lts(outer, binds, t)) is Some,
    ensures
        binds_typed(outer, binds.push(e), t),
        lts(outer, binds.push(e), t) == lts(outer, binds, t).push(type_l(e, t, lts(outer, binds, t))->Some_0),
{
    let b = binds.push(e);
    assert(b.drop_last() =~= binds);
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] type_l(b[i], t, lts(outer, b.take(i), t)) is Some by {
        if i < binds.len() {
            assert(b.take(i) =~= binds.take(i));
            assert(b[i] == binds[i]);
        } else {
            assert(b.take(i) =~= binds);
        }
    }
}


// ---- 下ろしの文脈の型 ----

/// 局所変数の束縛（値の上の局所変数）のスロットは、式の型のスロットの型を持つ。
pub open spec fn sc_typed(sc: Seq<crate::lower_ctx::Bound>, cx: LowerCtx, lt: Seq<ETy>) -> bool {
    forall|i: int|
        0 <= i < sc.len() ==> #[trigger] typed(
            sc[i].slots@,
            xetys(crate::encoding::xty(sc[i].ty), cx.enums@),
            lenv(cx),
            lt,
        )
}

/// 定数のスロットの値は、スロットの型の値である。
pub open spec fn consts_typed(cx: LowerCtx) -> bool {
    forall|i: int|
        0 <= i < cx.consts@.len() ==> #[trigger] crate::lower_types::in_slots(
            cx.consts@[i].slots@,
            slot_tys(crate::encoding::sty(cx.consts@[i].ty), cx.enums@),
            cx.enums@,
        )
}

/// 下ろしの前提のうち型についてのもの。束縛の列と局所変数の束縛と定数に型が付く。
pub open spec fn tok(cx: LowerCtx, sc: Seq<crate::lower_ctx::Bound>, b: Block) -> bool {
    &&& b.outer@.len() == b.base
    &&& binds_typed(b.outer@, b.binds@, lenv(cx))
    &&& sc_typed(sc, cx, blt(b, cx))
    &&& cx_tok(cx)
}

/// 下ろしの文脈の前提のうち型についてのもの。状態と引数の位置は型の列の位置で、定数に型が付く。
pub open spec fn cx_tok(cx: LowerCtx) -> bool {
    &&& cx.states matches Some(st) ==> crate::lower_ctx::layouts_at(st@, layout_tys(st@), cx.enums@)
    &&& crate::lower_ctx::layouts_at(cx.args@, layout_tys(cx.args@), cx.enums@)
    &&& consts_typed(cx)
}

/// 外側の局所変数の型 `outer` の下で単独に評価する式についての前提。
pub open spec fn tok_in(cx: LowerCtx, sc: Seq<crate::lower_ctx::Bound>, outer: Seq<ETy>, depth: nat) -> bool {
    &&& outer.len() == depth
    &&& sc_typed(sc, cx, outer)
    &&& cx_tok(cx)
}

/// 下ろしの事後条件のうち型についてのもの。束縛の列に型が付き、スロットは式の型のスロットの型を持つ。
pub open spec fn ty_post(cx: LowerCtx, b: Block, r: Result<(crate::encoding::XType, Vec<Expr>), crate::lower_ctx::Fail>) -> bool {
    &&& binds_typed(b.outer@, b.binds@, lenv(cx))
    &&& r matches Ok((t, slots)) ==> typed(slots@, xetys(crate::encoding::xty(t), cx.enums@), lenv(cx), blt(b, cx))
}

/// 束縛の列を伸ばしても、それまでの純粋なスロットの型は変わらない。
pub proof fn lemma_typed_blk(xs: Seq<Expr>, ys: Seq<ETy>, cx: LowerCtx, b0: Block, b1: Block)
    requires
        typed(xs, ys, lenv(cx), blt(b0, cx)),
        crate::expr_build::all_pure(xs, b0.depth_s()),
        crate::lower_ctx::extends(b0, b1),
        b0.outer@.len() == b0.base,
    ensures
        typed(xs, ys, lenv(cx), blt(b1, cx)),
{
    let n = b0.depth_s();
    lemma_lts_len(b0.outer@, b0.binds@, lenv(cx));
    lemma_lts_len(b1.outer@, b1.binds@, lenv(cx));
    lemma_lts_prefix(b1.outer@, b1.binds@, lenv(cx), b0.binds@.len() as int);
    assert(b1.binds@.take(b0.binds@.len() as int) =~= b0.binds@);
    assert(blt(b0, cx).take(n as int) =~= blt(b0, cx));
    assert forall|i: int| 0 <= i < xs.len() implies crate::expr_build::pure_below(#[trigger] xs[i], n) by {}
    lemma_typed_ext(xs, ys, lenv(cx), blt(b0, cx), blt(b1, cx), n);
}

/// 束縛の列を伸ばしても、型についての前提は保たれる。
pub proof fn lemma_tok_ext(cx: LowerCtx, sc: Seq<crate::lower_ctx::Bound>, b0: Block, b1: Block)
    requires
        tok(cx, sc, b0),
        crate::lower_ctx::extends(b0, b1),
        binds_typed(b1.outer@, b1.binds@, lenv(cx)),
        crate::lower_types::sc_wf(sc, b0.depth_s(), cx.enums@),
    ensures
        tok(cx, sc, b1),
{
    assert forall|i: int| 0 <= i < sc.len() implies #[trigger] typed(
        sc[i].slots@,
        xetys(crate::encoding::xty(sc[i].ty), cx.enums@),
        lenv(cx),
        blt(b1, cx),
    ) by {
        assert(typed(sc[i].slots@, xetys(crate::encoding::xty(sc[i].ty), cx.enums@), lenv(cx), blt(b0, cx)));
        assert(crate::lower_types::shaped(sc[i].slots@, crate::encoding::xty(sc[i].ty), b0.depth_s(), cx.enums@));
        lemma_typed_blk(sc[i].slots@, xetys(crate::encoding::xty(sc[i].ty), cx.enums@), cx, b0, b1);
    }
}

/// 型の付く式を [`crate::lower_ctx::added`] で加えると、束縛の列は型が付き、`x` は同じ型を持つ。
pub proof fn lemma_added_typed(b0: Block, b1: Block, e: Expr, x: Expr, cx: LowerCtx, y: ETy)
    requires
        crate::lower_ctx::added(b0, b1, e, x),
        crate::lower_ctx::extends(b0, b1),
        b0.outer@.len() == b0.base,
        binds_typed(b0.outer@, b0.binds@, lenv(cx)),
        has_ty(e, lenv(cx), blt(b0, cx), y),
    ensures
        binds_typed(b1.outer@, b1.binds@, lenv(cx)),
        has_ty(x, lenv(cx), blt(b1, cx), y),
        blt(b1, cx).take(b0.depth_s() as int) == blt(b0, cx),
{
    lemma_lts_len(b0.outer@, b0.binds@, lenv(cx));
    if b1.binds@ == b0.binds@ {
        assert(blt(b1, cx) == blt(b0, cx));
        assert(blt(b0, cx).take(b0.depth_s() as int) =~= blt(b0, cx));
    } else {
        lemma_binds_push(b0.outer@, b0.binds@, lenv(cx), e);
        assert(blt(b1, cx) == blt(b0, cx).push(y));
        assert(blt(b1, cx)[b0.depth_s() as int] == y);
        assert(blt(b0, cx).push(y).take(b0.depth_s() as int) =~= blt(b0, cx));
    }
}


/// 位置の列の `i` 番目の型のスロットへの参照は、スロットの型を持つ。
pub proof fn lemma_kind_typed(
    ls: Seq<crate::lower_ctx::Layout>,
    i: int,
    kind: u8,
    out: Seq<Expr>,
    t: TyEnv,
    lt: Seq<ETy>,
)
    requires
        crate::lower_ctx::layouts_at(ls, layout_tys(ls), t.enums),
        0 <= i < ls.len(),
        out.len() == crate::encoding::width(crate::encoding::sty(ls[i].ty), t.enums),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == crate::expr_build::kind_expr(kind, (ls[i].offset + j) as usize),
        kind <= 2,
        kind == 2 ==> t.arg_tys == slot_tys_seq(layout_tys(ls), t.enums),
        kind != 2 ==> t.st_tys == slot_tys_seq(layout_tys(ls), t.enums),
        kind == 1 ==> t.next,
    ensures
        typed(out, xetys(to_xty(crate::encoding::sty(ls[i].ty)), t.enums), t, lt),
{
    let ts = layout_tys(ls);
    let st = crate::encoding::sty(ls[i].ty);
    assert(crate::lower_ctx::layout_at(ls[i], ts, i, t.enums));
    crate::lower_types::lemma_slot_tys_seq_sub(ts, i, t.enums);
    lemma_xetys_of(st, t.enums);
    lemma_slot_tys_len(st, t.enums);
    crate::lower_types::lemma_slot_tys_seq_len(ts, t.enums);
    let off = ls[i].offset as int;
    let w = crate::encoding::width(st, t.enums);
    assert(off == crate::encoding::width_sum(ts.take(i), t.enums));
    assert(ts[i] == st);
    assert forall|j: int| 0 <= j < out.len() implies #[trigger] has_ty(out[j], t, lt, xetys(to_xty(st), t.enums)[j]) by {
        assert(slot_tys_seq(ts, t.enums).subrange(off, off + w)[j] == slot_tys_seq(ts, t.enums)[off + j]);
        assert(slot_tys_seq(ts, t.enums)[off + j] == slot_tys(st, t.enums)[j]);
        assert(off + j < slot_tys_seq(ts, t.enums).len());
        assert(((ls[i].offset + j) as usize) as int == off + j);
        assert(xetys(to_xty(st), t.enums)[j] == ety_of(slot_tys(st, t.enums)[j]));
        let k = ((ls[i].offset + j) as usize);
        assert(out[j] == crate::expr_build::kind_expr(kind, k));
        assert(kind != 2 ==> (k as int) < t.st_tys.len());
        assert(kind == 2 ==> (k as int) < t.arg_tys.len());
        assert(kind != 2 ==> t.st_tys[k as int] == slot_tys(st, t.enums)[j]);
        assert(kind == 2 ==> t.arg_tys[k as int] == slot_tys(st, t.enums)[j]);
        if kind == 0 {
            assert(out[j] == Expr::Var(k));
            assert(type_l(out[j], t, lt) == crate::typing::var_ety(t.st_tys, k));
            assert(crate::typing::var_ety(t.st_tys, k) == Some(ety_of(t.st_tys[k as int])));
        } else if kind == 1 {
            assert(out[j] == Expr::Next(k));
            assert(type_l(out[j], t, lt) == crate::typing::var_ety(t.st_tys, k));
            assert(crate::typing::var_ety(t.st_tys, k) == Some(ety_of(t.st_tys[k as int])));
        } else {
            assert(out[j] == Expr::Arg(k));
            assert(type_l(out[j], t, lt) == crate::typing::var_ety(t.arg_tys, k));
            assert(crate::typing::var_ety(t.arg_tys, k) == Some(ety_of(t.arg_tys[k as int])));
        }
        assert(type_l(out[j], t, lt) == Some(ety_of(slot_tys(st, t.enums)[j])));
    }
}


/// 束縛の列を伸ばしても、純粋な式の型は変わらない。
pub proof fn lemma_has_ty_blk(x: Expr, y: ETy, cx: LowerCtx, b0: Block, b1: Block)
    requires
        has_ty(x, lenv(cx), blt(b0, cx), y),
        crate::expr_build::pure_below(x, b0.depth_s()),
        crate::lower_ctx::extends(b0, b1),
        b0.outer@.len() == b0.base,
    ensures
        has_ty(x, lenv(cx), blt(b1, cx), y),
{
    assert(typed(seq![x], seq![y], lenv(cx), blt(b0, cx)));
    assert(crate::expr_build::all_pure(seq![x], b0.depth_s()));
    lemma_typed_blk(seq![x], seq![y], cx, b0, b1);
    assert(has_ty(seq![x][0], lenv(cx), blt(b1, cx), seq![y][0]));
}

/// [`crate::slots::bind`] で束縛した式の局所変数は、その式の型を持つ。
pub proof fn lemma_bind_typed(b0: Block, b1: Block, e: Expr, x: Expr, cx: LowerCtx, y: ETy)
    requires
        x == Expr::Local(b0.depth_s() as usize),
        b1.binds@ == b0.binds@.push(e),
        crate::lower_ctx::extends(b0, b1),
        b0.outer@.len() == b0.base,
        binds_typed(b0.outer@, b0.binds@, lenv(cx)),
        has_ty(e, lenv(cx), blt(b0, cx), y),
    ensures
        binds_typed(b1.outer@, b1.binds@, lenv(cx)),
        has_ty(x, lenv(cx), blt(b1, cx), y),
{
    lemma_added_typed(b0, b1, e, x, cx, y);
}


/// 格納の型の式の型が大きさの条件を満たせば、格納の型の List の長さの上限は小さい。
pub proof fn lemma_lim_x_small(t: STy, enums: Seq<i64>)
    requires
        crate::limits::lim_x(to_xty(t), enums),
    ensures
        crate::limits::small(t),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_lim_xs_smalls(ts, enums),
        STy::Record(_, ts) => lemma_lim_xs_smalls(ts, enums),
        STy::Option(x) => lemma_lim_x_small(*x, enums),
        STy::Map(_, v) => crate::limits::lemma_lim_small(*v, enums),
        STy::List(e, _) => crate::limits::lemma_lim_small(*e, enums),
        _ => {},
    }
}

pub proof fn lemma_lim_xs_smalls(ts: Seq<STy>, enums: Seq<i64>)
    requires
        crate::limits::lim_xs(to_xtys(ts), enums),
    ensures
        crate::limits::smalls(ts),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let a = ts.drop_last();
        crate::encoding::lemma_to_xtys(ts);
        crate::encoding::lemma_to_xtys(a);
        assert(to_xtys(ts).drop_last() == to_xtys(a));
        assert(to_xtys(ts).last() == to_xty(ts.last()));
        lemma_lim_xs_smalls(a, enums);
        lemma_lim_x_small(ts.last(), enums);
    }
}


/// [`crate::slots::check`] の後も、束縛の列は型が付く。
pub proof fn lemma_check_typed(b0: Block, b1: Block, cond: Expr, code: i64, cx: LowerCtx)
    requires
        (cond == crate::expr_build::bool_lit(true) && b1.binds@ == b0.binds@) || b1.binds@ == b0.binds@.push(
            crate::expr_build::ite_s(cond, crate::expr_build::bool_lit(true), Expr::Fail(Type::Bool, code)),
        ),
        crate::lower_ctx::extends(b0, b1),
        b0.outer@.len() == b0.base,
        binds_typed(b0.outer@, b0.binds@, lenv(cx)),
        has_ty(cond, lenv(cx), blt(b0, cx), ETy::Bool),
    ensures
        binds_typed(b1.outer@, b1.binds@, lenv(cx)),
{
    if b1.binds@ != b0.binds@ {
        let e = crate::expr_build::ite_s(cond, crate::expr_build::bool_lit(true), Expr::Fail(Type::Bool, code));
        assert(has_ty(crate::expr_build::bool_lit(true), lenv(cx), blt(b0, cx), ETy::Bool));
        assert(crate::typing::type_ok(lenv(cx).enums, Type::Bool));
        assert(has_ty(Expr::Fail(Type::Bool, code), lenv(cx), blt(b0, cx), ETy::Bool));
        assert(has_ty(e, lenv(cx), blt(b0, cx), ETy::Bool));
        lemma_binds_push(b0.outer@, b0.binds@, lenv(cx), e);
    }
}


// ---- 行の列の型 ----

/// Mapのスロットの各行は、行の型を持つ。
pub proof fn lemma_mrows_typed(slots: Seq<Expr>, rows: Seq<Seq<Expr>>, rt: Seq<Type>, n: nat, t: TyEnv, lt: Seq<ETy>)
    requires
        crate::rows::mparts_ok(slots, rows, rt.len(), n),
        typed(slots, etys(crate::lower_types::ty_repeat(rt, n)), t, lt),
    ensures
        forall|p: int| 0 <= p < n ==> #[trigger] typed(rows[p], etys(rt), t, lt),
{
    assert forall|p: int| 0 <= p < n implies #[trigger] typed(rows[p], etys(rt), t, lt) by {
        let w = rt.len();
        assert(crate::rows::mrow_at(rows[p], slots, p, w));
        crate::lower_types::lemma_ty_repeat_sub(rt, n, p);
        crate::lower_types::lemma_etys_sub(crate::lower_types::ty_repeat(rt, n), p * w, p * w + w);
        lemma_typed_sub(slots, etys(crate::lower_types::ty_repeat(rt, n)), t, lt, p * w, p * w + w);
    }
}

/// Listのスロットの長さは Int で、各行は要素の型を持つ。
pub proof fn lemma_lrows_typed(
    slots: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    et: Seq<Type>,
    max: nat,
    t: TyEnv,
    lt: Seq<ETy>,
)
    requires
        crate::rows::parts_ok(slots, len, rows, et.len(), max),
        max <= i64::MAX,
        typed(slots, etys(seq![Type::Int(0, max as i64)] + crate::lower_types::ty_repeat(et, max)), t, lt),
    ensures
        has_ty(len, t, lt, ETy::Int),
        forall|p: int| 0 <= p < max ==> #[trigger] typed(rows[p], etys(et), t, lt),
{
    let all = etys(seq![Type::Int(0, max as i64)] + crate::lower_types::ty_repeat(et, max));
    lemma_etys_concat(seq![Type::Int(0, max as i64)], crate::lower_types::ty_repeat(et, max));
    assert(etys(seq![Type::Int(0, max as i64)]) =~= seq![ETy::Int]);
    assert(has_ty(slots[0], t, lt, all[0]));
    assert forall|p: int| 0 <= p < max implies #[trigger] typed(rows[p], etys(et), t, lt) by {
        let w = et.len();
        assert(crate::rows::row_at(rows[p], slots, p, w));
        crate::lower_types::lemma_ty_repeat_sub(et, max, p);
        crate::lower_types::lemma_etys_sub(crate::lower_types::ty_repeat(et, max), p * w, p * w + w);
        lemma_typed_sub(slots, all, t, lt, 1 + p * w, 1 + p * w + w);
        assert(all.subrange(1 + p * w, 1 + p * w + w) =~= etys(crate::lower_types::ty_repeat(et, max)).subrange(p * w, p * w + w));
    }
}

/// 型 `rt` の行をつなげた列は、型 `rt` を繰り返した列の型を持つ。
pub proof fn lemma_flat_typed(rows: Seq<Seq<Expr>>, rt: Seq<Type>, t: TyEnv, lt: Seq<ETy>)
    requires
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] typed(rows[p], etys(rt), t, lt),
    ensures
        typed(crate::expr_build::concat(rows), etys(crate::lower_types::ty_repeat(rt, rows.len())), t, lt),
    decreases rows.len(),
{
    if rows.len() == 0 {
        assert(etys(crate::lower_types::ty_repeat(rt, 0)) =~= Seq::<ETy>::empty());
    } else {
        let a = rows.drop_last();
        assert forall|p: int| 0 <= p < a.len() implies #[trigger] typed(a[p], etys(rt), t, lt) by {
            assert(typed(rows[p], etys(rt), t, lt));
        }
        lemma_flat_typed(a, rt, t, lt);
        assert(typed(rows[rows.len() - 1], etys(rt), t, lt));
        lemma_typed_concat(crate::expr_build::concat(a), etys(crate::lower_types::ty_repeat(rt, a.len())), rows.last(), etys(rt), t, lt);
        lemma_etys_concat(crate::lower_types::ty_repeat(rt, a.len()), rt);
    }
}

/// 番号 `k` の行だけを置き換えた行は、行の型を持つ。
pub proof fn lemma_ite_rows_typed(
    out: Seq<Seq<Expr>>,
    rows: Seq<Seq<Expr>>,
    k: Expr,
    alt: Seq<Expr>,
    rt: Seq<ETy>,
    t: TyEnv,
    lt: Seq<ETy>,
)
    requires
        crate::rows::ite_rows_ok(out, rows, k, alt),
        has_ty(k, t, lt, ETy::Int),
        typed(alt, rt, t, lt),
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] typed(rows[p], rt, t, lt),
    ensures
        forall|p: int| 0 <= p < out.len() ==> #[trigger] typed(out[p], rt, t, lt),
{
    assert forall|p: int| 0 <= p < out.len() implies #[trigger] typed(out[p], rt, t, lt) by {
        assert(crate::rows::ite_row(out[p], rows[p], k, alt, p));
        assert(typed(rows[p], rt, t, lt));
        assert forall|j: int| 0 <= j < out[p].len() implies #[trigger] has_ty(out[p][j], t, lt, rt[j]) by {
            let q = Expr::Bin(crate::model::BinOp::Eq, Box::new(k), Box::new(Expr::Const(Value::Int(p as i64))));
            assert(out[p][j] == crate::expr_build::ite_s(q, alt[j], rows[p][j]));
            assert(has_ty(alt[j], t, lt, rt[j]));
            assert(has_ty(rows[p][j], t, lt, rt[j]));
            assert(has_ty(Expr::Const(Value::Int(p as i64)), t, lt, ETy::Int));
            assert(has_ty(q, t, lt, ETy::Bool));
        }
    }
}


/// Bool の式の列は、Set のスロットの型を持つ。
pub proof fn lemma_bools_typed(xs: Seq<Expr>, n: nat, t: TyEnv, lt: Seq<ETy>)
    requires
        xs.len() == n,
        all_ty(xs, ETy::Bool, t, lt),
    ensures
        typed(xs, etys(crate::lower_types::ty_repeat(seq![Type::Bool], n)), t, lt),
{
    let b = seq![Type::Bool];
    assert(b.len() == 1);
    crate::lower_types::lemma_ty_repeat_len(b, n);
    assert(n * 1 == n);
    assert forall|j: int| 0 <= j < xs.len() implies #[trigger] has_ty(xs[j], t, lt, etys(crate::lower_types::ty_repeat(b, n))[j]) by {
        crate::lower_types::lemma_ty_repeat_sub(b, n, j);
        assert(j * 1 == j);
        assert(crate::lower_types::ty_repeat(b, n).subrange(j, j + 1)[0] == crate::lower_types::ty_repeat(b, n)[j]);
        assert(crate::lower_types::ty_repeat(b, n)[j] == Type::Bool);
        assert(has_ty(xs[j], t, lt, ETy::Bool));
    }
}

/// Set のスロットの型を持つ列の各式は Bool の型を持つ。
pub proof fn lemma_typed_bools(xs: Seq<Expr>, n: nat, t: TyEnv, lt: Seq<ETy>)
    requires
        typed(xs, etys(crate::lower_types::ty_repeat(seq![Type::Bool], n)), t, lt),
    ensures
        xs.len() == n,
        all_ty(xs, ETy::Bool, t, lt),
{
    let b = seq![Type::Bool];
    assert(b.len() == 1);
    crate::lower_types::lemma_ty_repeat_len(b, n);
    assert(n * 1 == n);
    assert forall|j: int| 0 <= j < xs.len() implies #[trigger] has_ty(xs[j], t, lt, ETy::Bool) by {
        crate::lower_types::lemma_ty_repeat_sub(b, n, j);
        assert(j * 1 == j);
        assert(crate::lower_types::ty_repeat(b, n).subrange(j, j + 1)[0] == crate::lower_types::ty_repeat(b, n)[j]);
        assert(crate::lower_types::ty_repeat(b, n)[j] == Type::Bool);
        assert(has_ty(xs[j], t, lt, etys(crate::lower_types::ty_repeat(b, n))[j]));
    }
}

/// Bool の式の [`crate::expr_build::and_s`] は Bool の型を持つ。
pub proof fn lemma_and_typed(x: Expr, y: Expr, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(x, t, lt, ETy::Bool),
        has_ty(y, t, lt, ETy::Bool),
    ensures
        has_ty(crate::expr_build::and_s(x, y), t, lt, ETy::Bool),
{
}

/// `r >= 0` は、`r` が Int なら Bool の型を持つ。
pub proof fn lemma_ge0_typed(r: Expr, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(r, t, lt, ETy::Int),
    ensures
        has_ty(Expr::Bin(crate::model::BinOp::Ge, Box::new(r), Box::new(Expr::Const(Value::Int(0)))), t, lt, ETy::Bool),
{
    assert(has_ty(Expr::Const(Value::Int(0)), t, lt, ETy::Int));
}

/// `len > k` は、`len` が Int なら Bool の型を持つ。
pub proof fn lemma_gt_typed(len: Expr, k: i64, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(len, t, lt, ETy::Int),
    ensures
        has_ty(Expr::Bin(crate::model::BinOp::Gt, Box::new(len), Box::new(Expr::Const(Value::Int(k)))), t, lt, ETy::Bool),
{
    assert(has_ty(Expr::Const(Value::Int(k)), t, lt, ETy::Int));
}

/// Mapのスロットの各行の先頭は Bool の型を持つ。
pub proof fn lemma_map_flags_typed(
    s: Seq<Expr>,
    fs: Seq<Expr>,
    row: Seq<Type>,
    n: nat,
    stride: int,
    t: TyEnv,
    lt: Seq<ETy>,
)
    requires
        typed(s, etys(crate::lower_types::ty_repeat(row, n)), t, lt),
        row.len() == stride,
        stride > 0,
        row[0] == Type::Bool,
        fs.len() <= n,
        forall|q: int| 0 <= q < fs.len() ==> #[trigger] fs[q] == s[q * stride],
    ensures
        all_ty(fs, ETy::Bool, t, lt),
{
    assert forall|q: int| 0 <= q < fs.len() implies #[trigger] has_ty(fs[q], t, lt, ETy::Bool) by {
        crate::lower_types::lemma_ty_repeat_sub(row, n, q);
        let rr = crate::lower_types::ty_repeat(row, n);
        assert(rr.subrange(q * stride, q * stride + stride)[0] == rr[q * stride]);
        assert(rr[q * stride] == Type::Bool);
        assert(etys(rr)[q * stride] == ety_of(Type::Bool));
        assert(has_ty(s[q * stride], t, lt, etys(rr)[q * stride]));
    }
}

/// Mapのスロットの各列は、行の型のその列の型を持つ。
pub proof fn lemma_cols_typed(ms: Seq<Expr>, row: Seq<Type>, rows: usize, width: usize, t: TyEnv, lt: Seq<ETy>)
    requires
        typed(ms, etys(crate::lower_types::ty_repeat(row, rows as nat)), t, lt),
        row.len() == 1 + width,
    ensures
        forall|c: int| 0 <= c <= width ==> #[trigger] crate::lower_types::col_ty(ms, rows, width, c, etys(row)[c], t, lt),
{
    assert forall|c: int| 0 <= c <= width implies #[trigger] crate::lower_types::col_ty(ms, rows, width, c, etys(row)[c], t, lt) by {
        assert forall|j: int| 0 <= j < rows implies #[trigger] has_ty(ms[j * (1 + width as int) + c], t, lt, etys(row)[c]) by {
            crate::lower_types::lemma_ty_repeat_sub(row, rows as nat, j);
            let rr = crate::lower_types::ty_repeat(row, rows as nat);
            let w1 = row.len() as int;
            assert(rr.subrange(j * w1, j * w1 + w1)[c] == rr[j * w1 + c]);
            assert(etys(rr)[j * w1 + c] == ety_of(row[c]));
            assert(has_ty(ms[j * w1 + c], t, lt, etys(rr)[j * w1 + c]));
        }
    }
}

/// Mapのスロットの行は行の型を持ち、行の先頭は Bool の型を持つ。
pub proof fn lemma_map_rows_typed(
    ms: Seq<Expr>,
    rows: Seq<Seq<Expr>>,
    k: STy,
    v: STy,
    t: TyEnv,
    lt: Seq<ETy>,
)
    requires
        crate::rows::mparts_ok(
            ms,
            rows,
            (1 + crate::encoding::width(v, t.enums)) as nat,
            crate::encoding::keys_or_zero(k, t.enums),
        ),
        typed(ms, xetys(XTy::Map(Box::new(k), Box::new(v)), t.enums), t, lt),
    ensures
        rows.len() == crate::encoding::keys_or_zero(k, t.enums),
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] typed(rows[p], etys(seq![Type::Bool] + slot_tys(v, t.enums)), t, lt),
        forall|h: Seq<Expr>| #[trigger] crate::rows::heads_ok(h, rows) ==> all_ty(h, ETy::Bool, t, lt),
{
    let mt = STy::Map(Box::new(k), Box::new(v));
    let row = seq![Type::Bool] + slot_tys(v, t.enums);
    let n = crate::encoding::keys_or_zero(k, t.enums);
    lemma_xetys_of(mt, t.enums);
    lemma_slot_tys_len(v, t.enums);
    assert(to_xty(mt) == XTy::Map(Box::new(k), Box::new(v)));
    assert(slot_tys(mt, t.enums) == crate::lower_types::ty_repeat(row, n));
    lemma_mrows_typed(ms, rows, row, n, t, lt);
    assert forall|h: Seq<Expr>| #[trigger] crate::rows::heads_ok(h, rows) implies all_ty(h, ETy::Bool, t, lt) by {
        assert forall|q: int| 0 <= q < h.len() implies #[trigger] has_ty(h[q], t, lt, ETy::Bool) by {
            assert(crate::rows::head_at(h[q], rows[q]));
            assert(typed(rows[q], etys(row), t, lt));
            assert(etys(row)[0] == ETy::Bool);
            assert(has_ty(rows[q][0], t, lt, etys(row)[0]));
        }
    }
}

/// `x < y` は、`x` と `y` が Int なら Bool の型を持つ。
pub proof fn lemma_lt_typed(x: Expr, y: Expr, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(x, t, lt, ETy::Int),
        has_ty(y, t, lt, ETy::Int),
    ensures
        has_ty(Expr::Bin(crate::model::BinOp::Lt, Box::new(x), Box::new(y)), t, lt, ETy::Bool),
{
}

/// `x - k` は、`x` が Int なら Int の型を持つ。
pub proof fn lemma_sub_typed(x: Expr, k: i64, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(x, t, lt, ETy::Int),
    ensures
        has_ty(Expr::Bin(crate::model::BinOp::Sub, Box::new(x), Box::new(Expr::Const(Value::Int(k)))), t, lt, ETy::Int),
{
    assert(has_ty(Expr::Const(Value::Int(k)), t, lt, ETy::Int));
}

/// `x + k` は、`x` が Int なら Int の型を持つ。
pub proof fn lemma_add_typed(x: Expr, k: i64, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(x, t, lt, ETy::Int),
    ensures
        has_ty(Expr::Bin(crate::model::BinOp::Add, Box::new(x), Box::new(Expr::Const(Value::Int(k)))), t, lt, ETy::Int),
{
    assert(has_ty(Expr::Const(Value::Int(k)), t, lt, ETy::Int));
}

/// 長さと要素の型の行をつなげた列は、Listのスロットの型を持つ。
pub proof fn lemma_list_join_typed(len: Expr, rows: Seq<Seq<Expr>>, et: Seq<Type>, max: nat, t: TyEnv, lt: Seq<ETy>)
    requires
        has_ty(len, t, lt, ETy::Int),
        rows.len() == max,
        max <= i64::MAX,
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] typed(rows[p], etys(et), t, lt),
    ensures
        typed(seq![len] + crate::expr_build::concat(rows), etys(seq![Type::Int(0, max as i64)] + crate::lower_types::ty_repeat(et, max)), t, lt),
{
    lemma_flat_typed(rows, et, t, lt);
    assert(typed(seq![len], etys(seq![Type::Int(0, max as i64)]), t, lt)) by {
        assert(etys(seq![Type::Int(0, max as i64)]) =~= seq![ETy::Int]);
        assert(seq![len][0] == len);
    }
    lemma_typed_concat(seq![len], etys(seq![Type::Int(0, max as i64)]), crate::expr_build::concat(rows), etys(crate::lower_types::ty_repeat(et, max)), t, lt);
    lemma_etys_concat(seq![Type::Int(0, max as i64)], crate::lower_types::ty_repeat(et, max));
}

/// Listのスロットの `j` 番目の列の式は、要素の型の `j` 番目の型を持つ。
pub proof fn lemma_list_col_typed(cs: Seq<Expr>, et: Seq<Type>, max: nat, j: int, t: TyEnv, lt: Seq<ETy>)
    requires
        typed(cs, etys(seq![Type::Int(0, max as i64)] + crate::lower_types::ty_repeat(et, max)), t, lt),
        0 <= j < et.len(),
    ensures
        forall|k: int| 0 <= k < max ==> #[trigger] has_ty(cs[1 + k * et.len() + j], t, lt, etys(et)[j]),
{
    let w = et.len() as int;
    let all = seq![Type::Int(0, max as i64)] + crate::lower_types::ty_repeat(et, max);
    assert forall|k: int| 0 <= k < max implies #[trigger] has_ty(cs[1 + k * w + j], t, lt, etys(et)[j]) by {
        crate::lower_types::lemma_ty_repeat_sub(et, max, k);
        let rr = crate::lower_types::ty_repeat(et, max);
        assert(rr.subrange(k * w, k * w + w)[j] == rr[k * w + j]);
        assert(all[1 + k * w + j] == rr[k * w + j]);
        assert(has_ty(cs[1 + k * w + j], t, lt, etys(all)[1 + k * w + j]));
    }
}

/// 束縛の列の型の後ろに型を加えても、深さ未満の純粋な式の型は変わらない。
pub proof fn lemma_has_ty_push(x: Expr, y: ETy, t: TyEnv, lt: Seq<ETy>, z: ETy)
    requires
        has_ty(x, t, lt, y),
        pure_below(x, lt.len()),
    ensures
        has_ty(x, t, lt.push(z), y),
{
    assert(lt.push(z).take(lt.len() as int) =~= lt.take(lt.len() as int));
    lemma_pure_type(x, t, lt, lt.push(z), lt.len());
}

/// 束縛の列の型の長さは深さで、その次の局所変数は、Int を加えた型の列で Int の型を持つ。
pub proof fn lemma_top_typed(b: Block, cx: LowerCtx)
    requires
        b.outer@.len() == b.base,
        b.wf(),
    ensures
        blt(b, cx).len() == b.depth_s(),
        has_ty(Expr::Local(b.depth_s() as usize), lenv(cx), blt(b, cx).push(ETy::Int), ETy::Int),
{
    lemma_lts_len(b.outer@, b.binds@, lenv(cx));
    let lt = blt(b, cx).push(ETy::Int);
    let i = b.depth_s() as usize;
    assert(i as int == b.depth_s());
    assert(lt[i as int] == ETy::Int);
}

/// 純粋な式の列の型は、束縛の列の型の後ろに型を加えても変わらない。
pub proof fn lemma_all_ty_push(xs: Seq<Expr>, y: ETy, t: TyEnv, lt: Seq<ETy>, z: ETy)
    requires
        all_ty(xs, y, t, lt),
        crate::expr_build::all_pure(xs, lt.len()),
    ensures
        all_ty(xs, y, t, lt.push(z)),
{
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] has_ty(xs[i], t, lt.push(z), y) by {
        assert(pure_below(xs[i], lt.len()));
        lemma_has_ty_push(xs[i], y, t, lt, z);
    }
}

/// 位置の列の `i` 番目の型の `k` 番目のスロットの型。
pub proof fn lemma_layout_slot(ls: Seq<crate::lower_ctx::Layout>, i: int, k: int, enums: Seq<i64>)
    requires
        crate::lower_ctx::layouts_at(ls, layout_tys(ls), enums),
        0 <= i < ls.len(),
        0 <= k < crate::encoding::width(crate::encoding::sty(ls[i].ty), enums),
    ensures
        ls[i].offset + k < slot_tys_seq(layout_tys(ls), enums).len(),
        slot_tys_seq(layout_tys(ls), enums)[ls[i].offset + k] == slot_tys(crate::encoding::sty(ls[i].ty), enums)[k],
{
    let ts = layout_tys(ls);
    let st = crate::encoding::sty(ls[i].ty);
    assert(crate::lower_ctx::layout_at(ls[i], ts, i, enums));
    crate::lower_types::lemma_slot_tys_seq_sub(ts, i, enums);
    lemma_slot_tys_len(st, enums);
    crate::lower_types::lemma_slot_tys_seq_len(ts, enums);
    let off = ls[i].offset as int;
    let w = crate::encoding::width(st, enums);
    assert(ts[i] == st);
    assert(slot_tys_seq(ts, enums).subrange(off, off + w)[k] == slot_tys_seq(ts, enums)[off + k]);
}

/// 型の列 `xs` を `n` 回つなげた列。
pub open spec fn ty_repeat(xs: Seq<Type>, n: nat) -> Seq<Type>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        ty_repeat(xs, (n - 1) as nat) + xs
    }
}

/// 格納の型 `t` の各スロットの中核の型。
/// Listの長さのスロットは `0..=max` の整数で、Setの要素とMapのキーの有無はBoolである。
pub open spec fn slot_tys(t: STy, enums: Seq<i64>) -> Seq<Type>
    decreases t,
{
    match t {
        STy::Bool => seq![Type::Bool],
        STy::Int(lo, hi) => seq![Type::Int(lo, hi)],
        STy::Enum(id) => seq![Type::Enum(id)],
        STy::Tuple(ts) => slot_tys_seq(ts, enums),
        STy::Record(_, ts) => slot_tys_seq(ts, enums),
        STy::Option(x) => seq![Type::Bool] + slot_tys(*x, enums),
        STy::Set(e) => ty_repeat(seq![Type::Bool], keys_or_zero(*e, enums)),
        STy::Map(k, v) => ty_repeat(seq![Type::Bool] + slot_tys(*v, enums), keys_or_zero(*k, enums)),
        STy::List(e, max) => seq![Type::Int(0, max as i64)] + ty_repeat(slot_tys(*e, enums), max as nat),
    }
}

/// 型の列の各型のスロットの型を、順につなげた列。
pub open spec fn slot_tys_seq(ts: Seq<STy>, enums: Seq<i64>) -> Seq<Type>
    decreases ts,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        slot_tys_seq(ts.drop_last(), enums) + slot_tys(ts.last(), enums)
    }
}

/// 値 `x` は、スロットの型 `ty` の値である。
pub open spec fn in_slot(ty: Type, x: Value, enums: Seq<i64>) -> bool {
    match (ty, x) {
        (Type::Bool, Value::Bool(_)) => true,
        (Type::Int(lo, hi), Value::Int(k)) => lo <= k <= hi,
        (Type::Enum(id), Value::Enum(j, k)) => j == id && id < enums.len() && 0 <= k < enums[id as int],
        _ => false,
    }
}

/// 値の列 `xs` の各値は、対応するスロットの型の値である。
pub open spec fn in_slots(xs: Seq<Value>, tys: Seq<Type>, enums: Seq<i64>) -> bool {
    &&& xs.len() == tys.len()
    &&& forall|j: int| 0 <= j < xs.len() ==> #[trigger] in_slot(tys[j], xs[j], enums)
}

pub proof fn lemma_ty_repeat_len(xs: Seq<Type>, n: nat)
    ensures
        ty_repeat(xs, n).len() == n * xs.len(),
    decreases n,
{
    if n == 0 {
        assert(0 * xs.len() == 0) by (nonlinear_arith);
    } else {
        let m = (n - 1) as nat;
        lemma_ty_repeat_len(xs, m);
        assert(m * xs.len() + xs.len() == n * xs.len()) by (nonlinear_arith)
            requires
                m + 1 == n,
        ;
    }
}

/// `n` 回つなげた列の `p` 番目の部分は、もとの列である。
pub proof fn lemma_ty_repeat_sub(xs: Seq<Type>, n: nat, p: int)
    requires
        0 <= p < n,
    ensures
        0 <= p * xs.len(),
        p * xs.len() + xs.len() <= n * xs.len(),
        ty_repeat(xs, n).len() == n * xs.len(),
        ty_repeat(xs, n).subrange(p * xs.len(), p * xs.len() + xs.len()) == xs,
    decreases n,
{
    let w = xs.len();
    let m = (n - 1) as nat;
    lemma_ty_repeat_len(xs, n);
    lemma_ty_repeat_len(xs, m);
    assert(0 <= p * w) by (nonlinear_arith)
        requires
            0 <= p,
    ;
    assert(p * w + w <= n * w) by (nonlinear_arith)
        requires
            0 <= p < n,
    ;
    let s = ty_repeat(xs, n);
    assert(s == ty_repeat(xs, m) + xs);
    if p == m {
        assert(s.subrange(p * w, p * w + w) =~= xs);
    } else {
        lemma_ty_repeat_sub(xs, m, p);
        assert(p * w + w <= m * w) by (nonlinear_arith)
            requires
                0 <= p < m,
        ;
        assert(s.subrange(p * w, p * w + w) =~= ty_repeat(xs, m).subrange(p * w, p * w + w));
    }
}

/// スロットの型の数は、型の幅である。
pub proof fn lemma_slot_tys_len(t: STy, enums: Seq<i64>)
    ensures
        slot_tys(t, enums).len() == width(t, enums),
    decreases t,
{
    match t {
        STy::Tuple(ts) => lemma_slot_tys_seq_len(ts, enums),
        STy::Record(_, ts) => lemma_slot_tys_seq_len(ts, enums),
        STy::Option(x) => lemma_slot_tys_len(*x, enums),
        STy::Set(e) => {
            let n = keys_or_zero(*e, enums);
            lemma_ty_repeat_len(seq![Type::Bool], n);
            assert(n * 1 == n);
        },
        STy::Map(k, v) => {
            let n = keys_or_zero(*k, enums);
            let row = seq![Type::Bool] + slot_tys(*v, enums);
            lemma_slot_tys_len(*v, enums);
            lemma_ty_repeat_len(row, n);
            assert(row.len() == 1 + width(*v, enums));
            assert(ty_repeat(row, n).len() == n * (1 + width(*v, enums)));
        },
        STy::List(e, max) => {
            lemma_slot_tys_len(*e, enums);
            lemma_ty_repeat_len(slot_tys(*e, enums), max as nat);
        },
        _ => {},
    }
}

pub proof fn lemma_slot_tys_seq_len(ts: Seq<STy>, enums: Seq<i64>)
    ensures
        slot_tys_seq(ts, enums).len() == width_sum(ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        lemma_slot_tys_seq_len(ts.drop_last(), enums);
        lemma_slot_tys_len(ts.last(), enums);
    }
}

/// 列の `i` 番目の型のスロットの型は、つなげた列の部分である。
pub proof fn lemma_slot_tys_seq_sub(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        0 <= i < ts.len(),
    ensures
        width_sum(ts.take(i), enums) + width(ts[i], enums) <= width_sum(ts, enums),
        slot_tys_seq(ts, enums).subrange(
            width_sum(ts.take(i), enums) as int,
            (width_sum(ts.take(i), enums) + width(ts[i], enums)) as int,
        ) == slot_tys(ts[i], enums),
    decreases ts.len(),
{
    let n = ts.len() - 1;
    let a = ts.drop_last();
    lemma_slot_tys_seq_len(ts, enums);
    lemma_slot_tys_seq_len(a, enums);
    lemma_slot_tys_len(ts[i], enums);
    let s = slot_tys_seq(ts, enums);
    assert(s == slot_tys_seq(a, enums) + slot_tys(ts.last(), enums));
    if i == n {
        assert(ts.take(i) =~= a);
        assert(s.subrange(width_sum(a, enums) as int, s.len() as int) =~= slot_tys(ts.last(), enums));
    } else {
        lemma_slot_tys_seq_sub(a, i, enums);
        assert(a.take(i) =~= ts.take(i));
        assert(a[i] == ts[i]);
        let lo = width_sum(ts.take(i), enums) as int;
        let hi = lo + width(ts[i], enums);
        assert(s.subrange(lo, hi) =~= slot_tys_seq(a, enums).subrange(lo, hi));
    }
}

pub proof fn lemma_etys_sub(xs: Seq<Type>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= xs.len(),
    ensures
        etys(xs.subrange(lo, hi)) == etys(xs).subrange(lo, hi),
{
    assert(etys(xs.subrange(lo, hi)) =~= etys(xs).subrange(lo, hi));
}

/// 行の列 `flat` の各行の列 `column` の式は、型 `y` を持つ。
pub open spec fn col_ty(flat: Seq<Expr>, rows: usize, width: usize, column: int, y: ETy, tv: TyEnv, lt: Seq<ETy>) -> bool {
    forall|j: int| 0 <= j < rows ==> #[trigger] has_ty(flat[j * (1 + width as int) + column], tv, lt, y)
}

/// 式の型が整形式で、大きさの条件を満たす。
pub open spec fn ok_x(t: XTy, enums: Seq<i64>) -> bool {
    wf_xtype(t, enums) && lim_x(t, enums)
}

/// スロットの列は型 `t` の幅だけあり、深さ `n` 未満の局所変数だけを参照する純粋な式である。
pub open spec fn shaped(slots: Seq<Expr>, t: XTy, n: nat, enums: Seq<i64>) -> bool {
    slots.len() == xwidth(t, enums) && all_pure(slots, n)
}

pub open spec fn layout_tys(ls: Seq<Layout>) -> Seq<STy> {
    Seq::new(ls.len(), |i: int| sty(ls[i].ty))
}

/// 局所変数の束縛が整形式である。
pub open spec fn sc_wf(sc: Seq<Bound>, n: nat, enums: Seq<i64>) -> bool {
    forall|i: int|
        0 <= i < sc.len() ==> ok_x(xty(#[trigger] sc[i].ty), enums) && shaped(sc[i].slots@, xty(sc[i].ty), n, enums)
}

} // verus!
