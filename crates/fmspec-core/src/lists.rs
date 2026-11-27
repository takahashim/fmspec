//! Listのスロットの補題。
//!
//! 長さの上限が `max` のListは、長さのスロットの後に `max` 個の行を並べて符号化する。
//! 長さより前の行は要素の符号化で、後ろの行は要素の型の既定値の符号化である（[`pad`]）。
//! 下ろしは、スロットの列を行に区切り（[`parts_ok`]）、行を選び（[`select_ok`]）、
//! 行をつなぎ直す（[`flat`]）。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_items, enc_repeat, lemma_default_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{list_items_member, member, width, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::quant::{at_rank, lemma_bin_const, lemma_items_member, picks, vals_at};
#[cfg(verus_keep_ghost)]
use crate::slots::ite_s;
use vstd::prelude::*;

verus! {

// ---- 値の列 ----

/// 要素の列を、長さ `max` まで既定値で埋めた列。
pub open spec fn pad(items: Seq<SVal>, st: STy, max: nat, enums: Seq<i64>) -> Seq<SVal> {
    Seq::new(max, |k: int| if k < items.len() { items[k] } else { default_val(st, enums) })
}

/// 各要素の符号化の長さは、型の幅である。
pub open spec fn widths(xs: Seq<SVal>, st: STy, enums: Seq<i64>) -> bool {
    forall|k: int| 0 <= k < xs.len() ==> #[trigger] enc(xs[k], st, enums).len() == width(st, enums)
}

proof fn lemma_pad_rec(items: Seq<SVal>, st: STy, n: nat, enums: Seq<i64>)
    ensures
        enc_items(items, st, enums) + enc_repeat(enc(default_val(st, enums), st, enums), n) == enc_items(
            pad(items, st, items.len() + n, enums),
            st,
            enums,
        ),
    decreases n,
{
    let d = enc(default_val(st, enums), st, enums);
    if n == 0 {
        assert(pad(items, st, items.len(), enums) =~= items);
        assert(enc_items(items, st, enums) + enc_repeat(d, 0) =~= enc_items(items, st, enums));
    } else {
        let m = (n - 1) as nat;
        lemma_pad_rec(items, st, m, enums);
        let p = pad(items, st, items.len() + n, enums);
        assert(p.drop_last() =~= pad(items, st, items.len() + m, enums));
        assert(p.last() == default_val(st, enums));
        assert(enc_items(items, st, enums) + (enc_repeat(d, m) + d) =~= (enc_items(items, st, enums) + enc_repeat(d, m))
            + d);
    }
}

/// Listの符号化は、長さのスロットと、既定値で埋めた列の要素の符号化をつなげたものである。
pub proof fn lemma_enc_pad(items: Seq<SVal>, st: STy, max: usize, enums: Seq<i64>)
    requires
        items.len() <= max,
        list_items_member(items, st, enums),
    ensures
        enc(SVal::List(items), STy::List(Box::new(st), max), enums) == seq![Value::Int(items.len() as i64)] + enc_items(
            pad(items, st, max as nat, enums),
            st,
            enums,
        ),
        widths(pad(items, st, max as nat, enums), st, enums),
{
    let n = (max - items.len()) as nat;
    lemma_pad_rec(items, st, n, enums);
    assert(items.len() + n == max);
    let p = pad(items, st, max as nat, enums);
    let h = seq![Value::Int(items.len() as i64)];
    assert(h + enc_items(items, st, enums) + enc_repeat(enc(default_val(st, enums), st, enums), n) =~= h + (enc_items(
        items,
        st,
        enums,
    ) + enc_repeat(enc(default_val(st, enums), st, enums), n)));
    assert forall|k: int| 0 <= k < p.len() implies #[trigger] enc(p[k], st, enums).len() == width(st, enums) by {
        if k < items.len() {
            lemma_items_member(items, st, enums, k);
            lemma_enc_len(items[k], st, enums);
        } else {
            lemma_default_len(st, enums);
        }
    }
}

pub proof fn lemma_items_len(xs: Seq<SVal>, st: STy, enums: Seq<i64>)
    requires
        widths(xs, st, enums),
    ensures
        enc_items(xs, st, enums).len() == xs.len() * width(st, enums),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let a = xs.drop_last();
        assert forall|k: int| 0 <= k < a.len() implies #[trigger] enc(a[k], st, enums).len() == width(st, enums) by {
            assert(a[k] == xs[k]);
        }
        lemma_items_len(a, st, enums);
        assert(enc(xs[xs.len() - 1], st, enums).len() == width(st, enums));
        let n = xs.len() as int;
        let w = width(st, enums) as int;
        assert((n - 1) * w + w == n * w) by (nonlinear_arith);
    }
}

/// 要素の符号化をつなげた列の、`k` 番目の要素の部分。
pub proof fn lemma_items_slice(xs: Seq<SVal>, st: STy, enums: Seq<i64>, k: int)
    requires
        widths(xs, st, enums),
        0 <= k < xs.len(),
    ensures
        0 <= k * width(st, enums),
        k * width(st, enums) + width(st, enums) <= enc_items(xs, st, enums).len(),
        enc_items(xs, st, enums).subrange(k * width(st, enums), k * width(st, enums) + width(st, enums)) == enc(
            xs[k],
            st,
            enums,
        ),
    decreases xs.len(),
{
    let n = xs.len() as int;
    let w = width(st, enums) as int;
    let a = xs.drop_last();
    assert forall|q: int| 0 <= q < a.len() implies #[trigger] enc(a[q], st, enums).len() == width(st, enums) by {
        assert(a[q] == xs[q]);
    }
    lemma_items_len(xs, st, enums);
    lemma_items_len(a, st, enums);
    assert(0 <= k * w) by (nonlinear_arith)
        requires
            0 <= k,
            0 <= w,
    ;
    assert(k * w + w <= n * w) by (nonlinear_arith)
        requires
            0 <= k < n,
            0 <= w,
    ;
    assert(enc(xs[n - 1], st, enums).len() == w);
    let s = enc_items(xs, st, enums);
    assert(s == enc_items(a, st, enums) + enc(xs.last(), st, enums));
    if k == n - 1 {
        assert(s.subrange(k * w, k * w + w) =~= enc(xs[k], st, enums));
    } else {
        lemma_items_slice(a, st, enums, k);
        assert(a[k] == xs[k]);
        assert(k * w + w <= (n - 1) * w) by (nonlinear_arith)
            requires
                0 <= k < n - 1,
                0 <= w,
        ;
        assert(s.subrange(k * w, k * w + w) =~= enc_items(a, st, enums).subrange(k * w, k * w + w));
    }
}

// ---- 行に区切ったスロット ----

/// `rows` は、Listのスロット `slots` を、長さのスロット `len` と幅 `w` の `max` 個の行に区切ったものである。
pub open spec fn parts_ok(slots: Seq<Expr>, len: Expr, rows: Seq<Seq<Expr>>, w: nat, max: nat) -> bool {
    &&& slots.len() > 0
    &&& len == slots[0]
    &&& rows.len() == max
    &&& forall|p: int| 0 <= p < max ==> #[trigger] row_at(rows[p], slots, p, w)
}

/// `row` は、スロット `slots` の `p` 番目の行である。
pub open spec fn row_at(row: Seq<Expr>, slots: Seq<Expr>, p: int, w: nat) -> bool {
    1 + p * w + w <= slots.len() && row == slots.subrange(1 + p * w, 1 + p * w + w)
}

/// 各行のスロットは純粋で、値は `vals` である。
pub open spec fn rows_at(rows: Seq<Seq<Expr>>, vals: Seq<Seq<Value>>, env: Env, l: Seq<Value>) -> bool {
    &&& rows.len() == vals.len()
    &&& forall|p: int| 0 <= p < rows.len() ==> clean(#[trigger] rows[p], env, l) && slot_vals(rows[p], env, l) == vals[p]
}

/// 埋めた列の各要素の符号化。
pub open spec fn pad_vals(items: Seq<SVal>, st: STy, max: nat, enums: Seq<i64>) -> Seq<Seq<Value>> {
    Seq::new(max, |p: int| enc(pad(items, st, max, enums)[p], st, enums))
}

/// 区切った行は、既定値で埋めた列の要素の符号化を表す。長さのスロットは要素の数である。
pub proof fn lemma_list_parts(
    slots: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    env: Env,
    l: Seq<Value>,
    items: Seq<SVal>,
    st: STy,
    max: usize,
    enums: Seq<i64>,
)
    requires
        denotes(slots, env, l, SVal::List(items), XTy::List(Box::new(st), max), enums),
        parts_ok(slots, len, rows, width(st, enums), max as nat),
    ensures
        items.len() <= max,
        list_items_member(items, st, enums),
        pure_below(len, l.len()),
        eval_l(len, env, l) == Ok::<Value, ErrKind>(Value::Int(items.len() as i64)),
        rows_at(rows, pad_vals(items, st, max as nat, enums), env, l),
{
    let w = width(st, enums) as int;
    let p = pad(items, st, max as nat, enums);
    let sv = slot_vals(slots, env, l);
    assert(member(SVal::List(items), STy::List(Box::new(st), max), enums));
    lemma_enc_pad(items, st, max, enums);
    assert(sv == seq![Value::Int(items.len() as i64)] + enc_items(p, st, enums));
    assert(sv[0] == eval_l(slots[0], env, l)->Ok_0);
    assert(pure_below(slots[0], l.len()));
    let vals = pad_vals(items, st, max as nat, enums);
    assert forall|q: int| 0 <= q < rows.len() implies clean(#[trigger] rows[q], env, l) && slot_vals(rows[q], env, l)
        == vals[q] by {
        assert(row_at(rows[q], slots, q, width(st, enums)));
        lemma_items_slice(p, st, enums, q);
        lemma_clean_sub(slots, env, l, 1 + q * w, 1 + q * w + w);
        assert(sv.subrange(1 + q * w, 1 + q * w + w) =~= enc_items(p, st, enums).subrange(q * w, q * w + w));
    }
}

pub proof fn lemma_rows_weaken(rows: Seq<Seq<Expr>>, vals: Seq<Seq<Value>>, env: Env, l: Seq<Value>, l2: Seq<Value>)
    requires
        rows_at(rows, vals, env, l),
        prefix(l, l2),
    ensures
        rows_at(rows, vals, env, l2),
{
    assert forall|p: int| 0 <= p < rows.len() implies clean(#[trigger] rows[p], env, l2) && slot_vals(rows[p], env, l2)
        == vals[p] by {
        lemma_clean_weaken(rows[p], env, l, l2);
    }
}

// ---- 行をつなぎ直したスロット ----

/// 行をつなげた列。
pub open spec fn flat(rows: Seq<Seq<Expr>>) -> Seq<Expr>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        flat(rows.drop_last()) + rows.last()
    }
}

/// 行の列を、`Vec` の列から作る。
pub open spec fn rows_view(rows: Seq<Vec<Expr>>) -> Seq<Seq<Expr>> {
    Seq::new(rows.len(), |i: int| rows[i]@)
}

pub proof fn lemma_flat(rows: Seq<Seq<Expr>>, xs: Seq<SVal>, st: STy, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        rows_at(rows, Seq::new(xs.len(), |p: int| enc(xs[p], st, enums)), env, l),
    ensures
        clean(flat(rows), env, l),
        slot_vals(flat(rows), env, l) == enc_items(xs, st, enums),
    decreases rows.len(),
{
    if rows.len() == 0 {
        assert(slot_vals(flat(rows), env, l) =~= Seq::<Value>::empty());
    } else {
        let a = rows.drop_last();
        let b = xs.drop_last();
        assert forall|p: int| 0 <= p < a.len() implies clean(#[trigger] a[p], env, l) && slot_vals(a[p], env, l) == Seq::new(
            b.len(),
            |q: int| enc(b[q], st, enums),
        )[p] by {
            assert(a[p] == rows[p]);
            assert(b[p] == xs[p]);
        }
        lemma_flat(a, b, st, env, l, enums);
        assert(clean(rows[rows.len() - 1], env, l));
        lemma_clean_concat(flat(a), rows.last(), env, l);
    }
}

/// 長さの式と、埋めた列の各要素の符号化を表す行をつなげると、Listを表す。
pub proof fn lemma_list_join(
    len: Expr,
    rows: Seq<Seq<Expr>>,
    env: Env,
    l: Seq<Value>,
    items: Seq<SVal>,
    st: STy,
    max: usize,
    enums: Seq<i64>,
)
    requires
        items.len() <= max,
        list_items_member(items, st, enums),
        pure_below(len, l.len()),
        eval_l(len, env, l) == Ok::<Value, ErrKind>(Value::Int(items.len() as i64)),
        rows_at(rows, pad_vals(items, st, max as nat, enums), env, l),
    ensures
        denotes(seq![len] + flat(rows), env, l, SVal::List(items), XTy::List(Box::new(st), max), enums),
{
    let p = pad(items, st, max as nat, enums);
    assert(pad_vals(items, st, max as nat, enums) =~= Seq::new(p.len(), |q: int| enc(p[q], st, enums)));
    lemma_flat(rows, p, st, env, l, enums);
    lemma_enc_pad(items, st, max, enums);
    assert(clean(seq![len], env, l));
    assert(slot_vals(seq![len], env, l) =~= seq![Value::Int(items.len() as i64)]);
    lemma_clean_concat(seq![len], flat(rows), env, l);
}

// ---- 行を置き換える ----

/// `o` は、行 `r` の各スロットを、`k` が `p` なら `alt` のスロットに置き換える式の列である。
pub open spec fn ite_row(o: Seq<Expr>, r: Seq<Expr>, k: Expr, alt: Seq<Expr>, p: int) -> bool {
    &&& o.len() == alt.len()
    &&& r.len() == alt.len()
    &&& forall|j: int|
        0 <= j < o.len() ==> #[trigger] o[j] == ite_s(
            Expr::Bin(BinOp::Eq, Box::new(k), Box::new(Expr::Const(Value::Int(p as i64)))),
            alt[j],
            r[j],
        )
}

pub open spec fn ite_rows_ok(out: Seq<Seq<Expr>>, rows: Seq<Seq<Expr>>, k: Expr, alt: Seq<Expr>) -> bool {
    &&& out.len() == rows.len()
    &&& forall|p: int| 0 <= p < rows.len() ==> #[trigger] ite_row(out[p], rows[p], k, alt, p)
}

/// `k` が `n` なら、`n` 番目の行だけが `alt` の値になる。
pub proof fn lemma_ite_rows(
    out: Seq<Seq<Expr>>,
    rows: Seq<Seq<Expr>>,
    k: Expr,
    alt: Seq<Expr>,
    vals: Seq<Seq<Value>>,
    av: Seq<Value>,
    env: Env,
    l: Seq<Value>,
    n: i64,
)
    requires
        ite_rows_ok(out, rows, k, alt),
        rows_at(rows, vals, env, l),
        rows.len() <= 0x7fff_ffff,
        clean(alt, env, l),
        slot_vals(alt, env, l) == av,
        at_rank(k, env, l, n),
    ensures
        rows_at(out, Seq::new(rows.len(), |p: int| if p == n { av } else { vals[p] }), env, l),
{
    let nv = Seq::new(rows.len(), |p: int| if p == n { av } else { vals[p] });
    assert forall|p: int| 0 <= p < out.len() implies clean(#[trigger] out[p], env, l) && slot_vals(out[p], env, l)
        == nv[p] by {
        assert(ite_row(out[p], rows[p], k, alt, p));
        assert(clean(rows[p], env, l) && slot_vals(rows[p], env, l) == vals[p]);
        let c = Expr::Bin(BinOp::Eq, Box::new(k), Box::new(Expr::Const(Value::Int(p as i64))));
        lemma_bin_const(BinOp::Eq, k, p as i64, env, l, n);
        assert(eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(n == p as i64)));
        assert forall|j: int| 0 <= j < out[p].len() implies pure_below(#[trigger] out[p][j], l.len()) && eval_l(
            out[p][j],
            env,
            l,
        ) == Ok::<Value, ErrKind>(nv[p][j]) by {
            assert(out[p][j] == ite_s(c, alt[j], rows[p][j]));
            assert(pure_below(alt[j], l.len()) && eval_l(alt[j], env, l) is Ok);
            assert(pure_below(rows[p][j], l.len()) && eval_l(rows[p][j], env, l) is Ok);
            assert(slot_vals(alt, env, l)[j] == eval_l(alt[j], env, l)->Ok_0);
            assert(slot_vals(rows[p], env, l)[j] == eval_l(rows[p][j], env, l)->Ok_0);
        }
        assert(slot_vals(out[p], env, l) =~= nv[p]);
    }
}

// ---- 行を選ぶ ----

/// 各行の `j` 番目のスロットの列。
pub open spec fn col(rows: Seq<Seq<Expr>>, j: int) -> Seq<Expr> {
    Seq::new(rows.len(), |t: int| rows[t][j])
}

/// `out` は、添字 `idx` の行を選ぶスロットの列である。
pub open spec fn select_ok(rows: Seq<Seq<Expr>>, idx: Expr, out: Seq<Expr>) -> bool {
    &&& rows.len() > 0
    &&& forall|t: int| 0 <= t < rows.len() ==> (#[trigger] rows[t]).len() == out.len()
    &&& forall|j: int| 0 <= j < out.len() ==> #[trigger] picks(out[j], col(rows, j), idx)
}

/// 添字が範囲内なら、選んだスロットはその行の値になる。
pub proof fn lemma_select(
    rows: Seq<Seq<Expr>>,
    idx: Expr,
    out: Seq<Expr>,
    vals: Seq<Seq<Value>>,
    env: Env,
    l: Seq<Value>,
    k: i64,
)
    requires
        select_ok(rows, idx, out),
        rows_at(rows, vals, env, l),
        at_rank(idx, env, l, k),
        0 <= k < rows.len(),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == vals[k as int],
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == Ok::<Value, ErrKind>(vals[k as int][j]) by {
        let c = col(rows, j);
        let cv = Seq::new(rows.len(), |t: int| vals[t][j]);
        assert forall|t: int| 0 <= t < c.len() implies pure_below(#[trigger] c[t], l.len()) && eval_l(c[t], env, l)
            == Ok::<Value, ErrKind>(cv[t]) by {
            assert(clean(rows[t], env, l));
            assert(rows[t].len() == out.len());
            assert(slot_vals(rows[t], env, l)[j] == eval_l(rows[t][j], env, l)->Ok_0);
        }
        assert(vals_at(c, cv, env, l));
        assert(picks(out[j], c, idx));
        assert(all_pure(c, l.len()));
        assert(clean(rows[k as int], env, l));
        assert(slot_vals(rows[k as int], env, l).len() == rows[k as int].len());
    }
    let r = rows[k as int];
    assert(r.len() == out.len());
    assert(clean(r, env, l) && slot_vals(r, env, l) == vals[k as int]);
    assert(vals[k as int].len() == out.len());
    assert(slot_vals(out, env, l) =~= vals[k as int]);
}

} // verus!
