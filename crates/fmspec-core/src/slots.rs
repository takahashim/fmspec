//! 下ろしで使う、スロットの式の組み立て。
//!
//! 下ろしは、IRの式の値を、スロットごとの中核の式の列にする（[`crate::encoding`] の符号化）。
//! ここにあるのは、その部品である。部品は、長さや型の合わない入力には `None` を返す。
//! 下ろしは `None` を `Fail::Type`（内部エラー）にするので、`None` を返すことは健全性を損なわない。

use crate::bindings::wrap_bindings;
use crate::encoding::XType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_xtys, sty, xty, xtys, xwidth, xwidth_sum};
use crate::equality::small_stype;
#[cfg(verus_keep_ghost)]
use crate::equality::{eq_ok, eq_seq_ok, lemma_eq_coll, lemma_eq_option, lemma_eq_parts};
#[cfg(verus_keep_ghost)]
use crate::equality::{lemma_eq_scalar, lemma_eq_tuple};
#[cfg(verus_keep_ghost)]
use crate::eval::{Env, eval_l};
use crate::expr_build::{all_of, and, cb, ci, eq, implies, is_bool_lit, ite, Join, split, sub_exprs};
use crate::expr_build::tree;
#[cfg(verus_keep_ghost)]
use crate::expr_build::{bool_lit, int_lit, ite_s, split_ok, tree_s};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::*;
#[cfg(verus_keep_ghost)]
use crate::lists::{picks, rows_view, select_ok};
use crate::lower_ctx::{binds, Block, Fail};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{added, extends};
#[cfg(verus_keep_ghost)]
use crate::lower_types::*;
use crate::model::{BinOp, Expr, Type};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
use crate::quant::pick_slot;
#[cfg(verus_keep_ghost)]
use crate::rows::{col, flat, head_at, heads_ok, ite_row, ite_rows_ok};
use crate::typing::ETy;
#[cfg(verus_keep_ghost)]
use crate::typing::TyEnv;
use vstd::prelude::*;

verus! {

// ---- 中核の式の組み立て ----

pub fn not(x: Expr) -> (r: Expr)
    ensures
        r == Expr::Not(Box::new(x)),
{
    Expr::Not(Box::new(x))
}

/// 式の列の複製。
pub fn copy_exprs(xs: &Vec<Expr>) -> (r: Vec<Expr>)
    ensures
        r@ == xs@,
{
    sub_exprs(xs, 0, xs.len())
}

// ---- 平衡した二分木 ----

/// どれかが真。
pub fn any_of(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, bool_lit(false), Join::Or),
{
    tree(items, cb(false), Join::Or)
}

/// 整数の和。
pub fn sum(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, int_lit(0), Join::Add),
{
    tree(items, ci(0), Join::Add)
}

// ---- 式の性質 ----

/// 評価が失敗しうる。整数の演算は、値によってはオーバーフローするので失敗しうるとみなす。
pub open spec fn may_fail_s(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Bin(op, x, y) => op is Add || op is Sub || op is Mul || op is Div || op is Mod || may_fail_s(*x)
            || may_fail_s(*y),
        Expr::Fail(_, _) => true,
        Expr::Not(x) => may_fail_s(*x),
        Expr::Code(x) => may_fail_s(*x),
        Expr::And(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Or(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Implies(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Let(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Ite(c, x, y) => may_fail_s(*c) || may_fail_s(*x) || may_fail_s(*y),
        Expr::Forall(_, _, _, body) => may_fail_s(*body),
        Expr::Exists(_, _, _, body) => may_fail_s(*body),
        _ => false,
    }
}

pub fn may_fail(e: &Expr) -> (r: bool)
    ensures
        r == may_fail_s(*e),
    decreases e,
{
    match e {
        Expr::Bin(op, x, y) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => true,
            _ => may_fail(x) || may_fail(y),
        },
        Expr::Fail(_, _) => true,
        Expr::Not(x) => may_fail(x),
        Expr::Code(x) => may_fail(x),
        Expr::And(x, y) => may_fail(x) || may_fail(y),
        Expr::Or(x, y) => may_fail(x) || may_fail(y),
        Expr::Implies(x, y) => may_fail(x) || may_fail(y),
        Expr::Let(x, y) => may_fail(x) || may_fail(y),
        Expr::Ite(c, x, y) => may_fail(c) || may_fail(x) || may_fail(y),
        Expr::Forall(_, _, _, body) => may_fail(body),
        Expr::Exists(_, _, _, body) => may_fail(body),
        _ => false,
    }
}

pub open spec fn atomic_s(e: Expr) -> bool {
    e is Const || e is Var || e is Arg || e is Next || e is Out || e is Local
}

pub fn atomic(e: &Expr) -> (r: bool)
    ensures
        r == atomic_s(*e),
{
    match e {
        Expr::Const(_) | Expr::Var(_) | Expr::Arg(_) | Expr::Next(_) | Expr::Out | Expr::Local(_) => true,
        _ => false,
    }
}

// ---- 束縛の列 ----

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

// ---- 型の大きさ ----

pub fn is_scalar(t: &XType) -> (r: bool)
    ensures
        r == (xty(*t) is Bool || xty(*t) is Int || xty(*t) is Enum),
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => true,
        _ => false,
    }
}

// ---- スロットの操作 ----

/// 添字 `idx` の行を選ぶ。行がなければ `fallback`。
pub fn select(rows: &Vec<Vec<Expr>>, idx: &Expr, fallback: &Vec<Expr>) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(out) ==> rows@.len() > 0 ==> select_ok(rows_view(rows@), *idx, out@),
        r matches Some(out) ==> rows@.len() == 0 ==> out@ == fallback@,
        rows@.len() <= 0x7fff_ffff && (forall|t: int| 0 <= t < rows@.len() ==> (#[trigger] rows@[t])@.len() == rows@[0]@.len())
            ==> r is Some,
{
    if rows.len() == 0 {
        return Some(copy_exprs(fallback));
    }
    if rows.len() > 0x7fff_ffffusize {
        return None;
    }
    let ghost rv = rows_view(rows@);
    let ghost pre = forall|t: int| 0 <= t < rows@.len() ==> (#[trigger] rows@[t])@.len() == rows@[0]@.len();
    let n = rows[0].len();
    let mut k = 0;
    while k < rows.len()
        invariant
            k <= rows@.len(),
            rv == rows_view(rows@),
            forall|t: int| 0 <= t < k ==> (#[trigger] rv[t]).len() == n,
            n == rows@[0]@.len(),
            pre == forall|t: int| 0 <= t < rows@.len() ==> (#[trigger] rows@[t])@.len() == rows@[0]@.len(),
        decreases rows.len() - k,
    {
        proof {
            if pre {
                assert(rows@[k as int]@.len() == rows@[0]@.len());
            }
        }
        if rows[k].len() != n {
            return None;
        }
        k += 1;
    }
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < n
        invariant
            0 < rows@.len() <= 0x7fff_ffff,
            rv == rows_view(rows@),
            forall|t: int| 0 <= t < rows@.len() ==> (#[trigger] rv[t]).len() == n,
            j <= n,
            out@.len() == j,
            forall|q: int| 0 <= q < j ==> #[trigger] picks(out@[q], col(rv, q), *idx),
        decreases n - j,
    {
        let mut c: Vec<Expr> = Vec::new();
        let mut t = 0;
        while t < rows.len()
            invariant
                0 < rows@.len() <= 0x7fff_ffff,
                rv == rows_view(rows@),
                forall|u: int| 0 <= u < rows@.len() ==> (#[trigger] rv[u]).len() == n,
                j < n,
                t <= rows@.len(),
                c@.len() == t,
                forall|u: int| 0 <= u < t ==> #[trigger] c@[u] == rv[u][j as int],
            decreases rows.len() - t,
        {
            proof {
                assert(rv[t as int] == rows@[t as int]@);
            }
            c.push(copy_expr(&rows[t][j]));
            t += 1;
        }
        proof {
            assert(c@ =~= col(rv, j as int));
        }
        out.push(pick_slot(&c, idx));
        j += 1;
    }
    Some(out)
}

/// 構造の等しさ。Option が空なら中身は比べない。
pub fn eq_slots(t: &XType, x: &Vec<Expr>, y: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(c) ==> eq_ok(xty(*t), x@, y@, c, enums@),
        x@.len() == xwidth(xty(*t), enums@) && y@.len() == xwidth(xty(*t), enums@) && lim_x(xty(*t), enums@) ==> r is Some,
    decreases t, 1nat,
{
    proof {
        if lim_x(xty(*t), enums@) {
            if t is Map {
                lemma_lim_small(sty(*t->Map_1), enums@);
            }
            if t is List {
                lemma_lim_small(sty(*t->List_0), enums@);
            }
        }
    }
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => {
            if x.len() == 0 || y.len() == 0 {
                return None;
            }
            proof {
                lemma_eq_scalar(xty(*t), x@, y@, enums@);
            }
            Some(eq(copy_expr(&x[0]), copy_expr(&y[0])))
        },
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            let c = eq_parts(t, ts, x, y, enums)?;
            proof {
                lemma_eq_tuple(xty(*t), xtys(ts@), x@, y@, c, enums@);
            }
            Some(c)
        },
        XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            let c = eq_parts(t, ts, x, y, enums)?;
            proof {
                lemma_eq_tuple(xty(*t), xtys(ts@), x@, y@, c, enums@);
            }
            Some(c)
        },
        XType::Option(inner) => {
            if x.len() == 0 || y.len() == 0 {
                return None;
            }
            let rest = eq_slots(inner, &sub_exprs(x, 1, x.len()), &sub_exprs(y, 1, y.len()), enums)?;
            proof {
                lemma_eq_option(xty(**inner), x@, y@, rest, enums@);
            }
            Some(and(eq(copy_expr(&x[0]), copy_expr(&y[0])), implies(copy_expr(&x[0]), rest)))
        },
        // Set、Map、List は正規形なので、スロットの一致が値の一致である。
        // Listの長さは整数のスロットに入るので、長さの上限が大きすぎる型は扱わない。
        XType::Set(_) | XType::Map(_, _) | XType::List(_, _) => {
            let fits = match t {
                XType::Map(_, v) => small_stype(v),
                XType::List(e, max) => *max <= 0x7fff_ffffusize && small_stype(e),
                _ => true,
            };
            if !fits {
                return None;
            }
            let n = if x.len() < y.len() {
                x.len()
            } else {
                y.len()
            };
            let mut items: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= x.len(),
                    n <= y.len(),
                    i <= n,
                    items@.len() == i,
                    forall|q: int| 0 <= q < i ==> #[trigger] items@[q] == Expr::Bin(BinOp::Eq, Box::new(x@[q]), Box::new(y@[q])),
                decreases n - i,
            {
                items.push(eq(copy_expr(&x[i]), copy_expr(&y[i])));
                i += 1;
            }
            proof {
                lemma_eq_coll(xty(*t), x@, y@, items@, enums@);
            }
            Some(all_of(&items))
        },
    }
}

fn eq_parts(_parent: &XType, ts: &Vec<XType>, x: &Vec<Expr>, y: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<
    Expr,
>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r matches Some(c) ==> eq_seq_ok(xtys(ts@), x@, y@, c, enums@),
        x@.len() == xwidth_sum(xtys(ts@), enums@) && y@.len() == xwidth_sum(xtys(ts@), enums@) && lim_xs(xtys(ts@), enums@)
            && xwidth_sum(xtys(ts@), enums@) <= lim() ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = x@.len() == xwidth_sum(xtys(ts@), enums@) && y@.len() == xwidth_sum(xtys(ts@), enums@) && lim_xs(
        xtys(ts@),
        enums@,
    ) && xwidth_sum(xtys(ts@), enums@) <= lim();
    let xs = split(ts, x, enums)?;
    let ys = split(ts, y, enums)?;
    if xs.len() != ts.len() || ys.len() != ts.len() {
        return None;
    }
    proof {
        lemma_xtys(ts@);
    }
    let ghost tt = xtys(ts@);
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            xs.len() == ts.len(),
            ys.len() == ts.len(),
            tt == xtys(ts@),
            tt.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] tt[j] == xty(ts@[j]),
            i <= ts.len(),
            items@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] eq_ok(tt[k], xs@[k]@, ys@[k]@, items@[k], enums@),
            forall|k: int| 0 <= k < ts@.len() ==> #[trigger] split_ok(xs@[k]@, x@, tt, k, enums@),
            forall|k: int| 0 <= k < ts@.len() ==> #[trigger] split_ok(ys@[k]@, y@, tt, k, enums@),
            pre == (x@.len() == xwidth_sum(xtys(ts@), enums@) && y@.len() == xwidth_sum(xtys(ts@), enums@) && lim_xs(
                xtys(ts@),
                enums@,
            ) && xwidth_sum(xtys(ts@), enums@) <= lim()),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            assert(split_ok(xs@[i as int]@, x@, tt, i as int, enums@));
            assert(split_ok(ys@[i as int]@, y@, tt, i as int, enums@));
            if pre {
                lemma_lim_xs_at(tt, enums@, i as int);
            }
        }
        let c = eq_slots(&ts[i], &xs[i], &ys[i], enums)?;
        items.push(c);
        proof {
            assert(tt[i as int] == xty(ts@[i as int]));
            assert(eq_ok(tt[i as int], xs@[i as int]@, ys@[i as int]@, items@[i as int], enums@));
        }
        i += 1;
    }
    proof {
        let px = Seq::new(xs@.len(), |k: int| xs@[k]@);
        let py = Seq::new(ys@.len(), |k: int| ys@[k]@);
        assert forall|k: int| 0 <= k < tt.len() implies #[trigger] eq_ok(tt[k], px[k], py[k], items@[k], enums@) by {
            assert(eq_ok(tt[k], xs@[k]@, ys@[k]@, items@[k], enums@));
        }
        assert forall|k: int| 0 <= k < tt.len() implies #[trigger] split_ok(px[k], x@, tt, k, enums@) by {
            assert(split_ok(xs@[k]@, x@, tt, k, enums@));
        }
        assert forall|k: int| 0 <= k < tt.len() implies #[trigger] split_ok(py[k], y@, tt, k, enums@) by {
            assert(split_ok(ys@[k]@, y@, tt, k, enums@));
        }
        lemma_eq_parts(tt, x@, y@, px, py, items@, enums@);
    }
    Some(all_of(&items))
}

pub fn heads(rows: &Vec<Vec<Expr>>) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(h) ==> heads_ok(h@, rows_view(rows@)),
        (forall|q: int| 0 <= q < rows@.len() ==> (#[trigger] rows@[q])@.len() > 0) ==> r is Some,
{
    let mut h: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < rows.len()
        invariant
            i <= rows@.len(),
            h@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] head_at(h@[q], rows@[q]@),
        decreases rows.len() - i,
    {
        if rows[i].len() == 0 {
            return None;
        }
        let ghost h1 = h@;
        let x = copy_expr(&rows[i][0]);
        h.push(x);
        proof {
            assert(x == rows@[i as int]@[0]);
            assert forall|q: int| 0 <= q <= i implies #[trigger] head_at(h@[q], rows@[q]@) by {
                if q < i {
                    assert(h@[q] == h1[q]);
                }
            }
        }
        i += 1;
    }
    proof {
        let rv = rows_view(rows@);
        assert forall|q: int| 0 <= q < rv.len() implies #[trigger] head_at(h@[q], rv[q]) by {
            assert(rv[q] == rows@[q]@);
        }
    }
    Some(h)
}

/// 各行のスロットを、`k` が行の番号なら `alt` のスロットに置き換える。
pub fn ite_rows(rows: &Vec<Vec<Expr>>, k: &Expr, alt: &Vec<Expr>) -> (r: Option<Vec<Vec<Expr>>>)
    ensures
        r matches Some(out) ==> ite_rows_ok(rows_view(out@), rows_view(rows@), *k, alt@),
        rows@.len() <= 0x7fff_ffff && (forall|q: int| 0 <= q < rows@.len() ==> (#[trigger] rows@[q])@.len() == alt@.len())
            ==> r is Some,
{
    if rows.len() > 0x7fff_ffffusize {
        return None;
    }
    let mut out: Vec<Vec<Expr>> = Vec::new();
    let mut p = 0;
    while p < rows.len()
        invariant
            rows@.len() <= 0x7fff_ffff,
            p <= rows@.len(),
            out@.len() == p,
            forall|q: int| 0 <= q < p ==> #[trigger] ite_row(out@[q]@, rows@[q]@, *k, alt@, q),
        decreases rows.len() - p,
    {
        if rows[p].len() != alt.len() {
            return None;
        }
        let mut vs: Vec<Expr> = Vec::new();
        let mut j = 0;
        while j < alt.len()
            invariant
                p < rows@.len(),
                rows@.len() <= 0x7fff_ffff,
                rows@[p as int]@.len() == alt@.len(),
                j <= alt@.len(),
                vs@.len() == j,
                forall|i: int|
                    0 <= i < j ==> #[trigger] vs@[i] == ite_s(
                        Expr::Bin(BinOp::Eq, Box::new(*k), Box::new(Expr::Const(Value::Int(p as i64)))),
                        alt@[i],
                        rows@[p as int]@[i],
                    ),
            decreases alt.len() - j,
        {
            vs.push(ite(eq(copy_expr(k), ci(p as i64)), copy_expr(&alt[j]), copy_expr(&rows[p][j])));
            j += 1;
        }
        let ghost o1 = out@;
        out.push(vs);
        proof {
            assert(ite_row(out@[p as int]@, rows@[p as int]@, *k, alt@, p as int));
            assert forall|q: int| 0 <= q < p implies #[trigger] ite_row(out@[q]@, rows@[q]@, *k, alt@, q) by {
                assert(out@[q] == o1[q]);
            }
        }
        p += 1;
    }
    proof {
        let ov = rows_view(out@);
        let rv = rows_view(rows@);
        assert forall|q: int| 0 <= q < rv.len() implies #[trigger] ite_row(ov[q], rv[q], *k, alt@, q) by {
            assert(ov[q] == out@[q]@);
            assert(rv[q] == rows@[q]@);
        }
    }
    Some(out)
}

/// 行をつなげる。
pub fn join_rows(items: &Vec<Vec<Expr>>) -> (r: Vec<Expr>)
    ensures
        r@ == flat(rows_view(items@)),
{
    let ghost rv = rows_view(items@);
    let mut out: Vec<Expr> = Vec::new();
    proof {
        assert(rv.take(0) =~= Seq::<Seq<Expr>>::empty());
        assert(out@ =~= flat(rv.take(0)));
    }
    let mut i = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            rv == rows_view(items@),
            out@ == flat(rv.take(i as int)),
        decreases items.len() - i,
    {
        let ghost o1 = out@;
        let mut j = 0;
        while j < items[i].len()
            invariant
                i < items.len(),
                j <= items@[i as int]@.len(),
                out@ == o1 + items@[i as int]@.take(j as int),
            decreases items@[i as int]@.len() - j,
        {
            out.push(copy_expr(&items[i][j]));
            proof {
                assert(o1 + items@[i as int]@.take(j + 1) =~= (o1 + items@[i as int]@.take(j as int)).push(
                    items@[i as int]@[j as int],
                ));
            }
            j += 1;
        }
        proof {
            assert(rv.take(i + 1).drop_last() =~= rv.take(i as int));
            assert(rv.take(i + 1).last() == items@[i as int]@);
            assert(items@[i as int]@.take(items@[i as int]@.len() as int) =~= items@[i as int]@);
        }
        i += 1;
    }
    proof {
        assert(rv.take(items@.len() as int) =~= rv);
    }
    out
}

pub fn list_join(len: Expr, items: &Vec<Vec<Expr>>) -> (r: Vec<Expr>)
    ensures
        r@ == seq![len] + flat(rows_view(items@)),
{
    let ghost l0 = len;
    let ghost rv = rows_view(items@);
    let mut out: Vec<Expr> = Vec::new();
    out.push(len);
    proof {
        assert(rv.take(0) =~= Seq::<Seq<Expr>>::empty());
        assert(out@ =~= seq![l0] + flat(rv.take(0)));
    }
    let mut i = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            rv == rows_view(items@),
            out@ == seq![l0] + flat(rv.take(i as int)),
        decreases items.len() - i,
    {
        let ghost o1 = out@;
        let mut j = 0;
        while j < items[i].len()
            invariant
                i < items.len(),
                j <= items@[i as int]@.len(),
                out@ == o1 + items@[i as int]@.take(j as int),
            decreases items@[i as int]@.len() - j,
        {
            out.push(copy_expr(&items[i][j]));
            proof {
                assert(o1 + items@[i as int]@.take(j + 1) =~= (o1 + items@[i as int]@.take(j as int)).push(
                    items@[i as int]@[j as int],
                ));
            }
            j += 1;
        }
        proof {
            assert(rv.take(i + 1).drop_last() =~= rv.take(i as int));
            assert(rv.take(i + 1).last() == items@[i as int]@);
            assert(items@[i as int]@.take(items@[i as int]@.len() as int) =~= items@[i as int]@);
            assert(seq![l0] + flat(rv.take(i + 1)) =~= (seq![l0] + flat(rv.take(i as int))) + items@[i as int]@);
        }
        i += 1;
    }
    proof {
        assert(rv.take(items@.len() as int) =~= rv);
    }
    out
}

} // verus!
