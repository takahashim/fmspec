//! List と Map のスロットの、行への区切り。区切りの仕様（`parts_ok`、`mparts_ok`、`rows_view` など）と、行の先頭、行ごとの条件式、行のつなぎ直しの実行関数。区切る実行関数は `lists` と `maps` にある。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::Env;
use crate::kernel::expr_copy::copy_expr;
use crate::kernel::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::kernel::model::{BinOp, Value};
use crate::slot::expr_build::{ci, eq, ite};
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::{concat, ite_s};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{clean, slot_vals};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::width;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{default_val, enc, enc_rows, lemma_default_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_enc_rows_len, lemma_map_rows_member_index, map_rows_member, STy, SVal};
use vstd::prelude::*;

verus! {

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

/// 各行の `j` 番目のスロットの列。
pub open spec fn col(rows: Seq<Seq<Expr>>, j: int) -> Seq<Expr> {
    Seq::new(rows.len(), |t: int| rows[t][j])
}

/// `rows` は、Mapのスロット `slots` を、幅 `w` の `n` 個の行に区切ったものである。
pub open spec fn mparts_ok(slots: Seq<Expr>, rows: Seq<Seq<Expr>>, w: nat, n: nat) -> bool {
    &&& slots.len() == n * w
    &&& rows.len() == n
    &&& forall|p: int| 0 <= p < n ==> #[trigger] mrow_at(rows[p], slots, p, w)
}

/// `row` は、スロット `slots` の `p` 番目の行である。
pub open spec fn mrow_at(row: Seq<Expr>, slots: Seq<Expr>, p: int, w: nat) -> bool {
    0 <= p * w && p * w + w <= slots.len() && row == slots.subrange(p * w, p * w + w)
}

/// 各行の先頭のスロット。
pub open spec fn heads_ok(h: Seq<Expr>, rows: Seq<Seq<Expr>>) -> bool {
    &&& h.len() == rows.len()
    &&& forall|q: int| 0 <= q < rows.len() ==> #[trigger] head_at(h[q], rows[q])
}

pub open spec fn head_at(x: Expr, row: Seq<Expr>) -> bool {
    row.len() > 0 && x == row[0]
}

/// Mapの行の符号化。有無のBoolと、値（ない行は既定値）の符号化。
pub open spec fn row_slots(o: Option<SVal>, t: STy, enums: Seq<i64>) -> Seq<Value> {
    match o {
        Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
        None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
    }
}

/// Mapの符号化の `r` 行目の `i` 番目のスロット。
pub proof fn lemma_enc_rows_index(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>, r: int, i: int)
    requires
        map_rows_member(rows, t, enums),
        0 <= r < rows.len(),
        0 <= i <= width(t, enums),
    ensures
        enc_rows(rows, t, enums).len() == rows.len() * (1 + width(t, enums)),
        0 <= r * (1 + width(t, enums)) + i < rows.len() * (1 + width(t, enums)),
        row_slots(rows[r], t, enums).len() == 1 + width(t, enums),
        enc_rows(rows, t, enums)[r * (1 + width(t, enums)) + i] == row_slots(rows[r], t, enums)[i],
    decreases rows.len(),
{
    let w = 1 + width(t, enums);
    let n = rows.len() as int;
    lemma_enc_rows_len(rows, t, enums);
    lemma_map_rows_member_index(rows, t, enums, r);
    match rows[r] {
        Some(x) => lemma_enc_len(x, t, enums),
        None => lemma_default_len(t, enums),
    }
    assert(0 <= r * w) by (nonlinear_arith)
        requires
            0 <= r,
            0 <= w,
    ;
    assert(r * w + i < n * w) by (nonlinear_arith)
        requires
            0 <= r < n,
            0 <= i < w,
    ;
    let pre = rows.drop_last();
    lemma_enc_rows_len(pre, t, enums);
    let p = enc_rows(pre, t, enums);
    assert(p.len() == (n - 1) * w);
    if r < n - 1 {
        lemma_enc_rows_index(pre, t, enums, r, i);
        assert(pre[r] == rows[r]);
        assert(r * w + i < (n - 1) * w) by (nonlinear_arith)
            requires
                0 <= r < n - 1,
                0 <= i < w,
        ;
    } else {
        assert(r * w == (n - 1) * w);
        assert(rows.last() == rows[r]);
    }
}

/// 各行のスロットは純粋で、値は `vals` である。
pub open spec fn rows_at(rows: Seq<Seq<Expr>>, vals: Seq<Seq<Value>>, env: Env, l: Seq<Value>) -> bool {
    &&& rows.len() == vals.len()
    &&& forall|p: int| 0 <= p < rows.len() ==> clean(#[trigger] rows[p], env, l) && slot_vals(rows[p], env, l) == vals[p]
}

/// 行の列を、`Vec` の列から作る。
pub open spec fn rows_view(rows: Seq<Vec<Expr>>) -> Seq<Seq<Expr>> {
    Seq::new(rows.len(), |i: int| rows[i]@)
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
        r@ == concat(rows_view(items@)),
{
    let ghost rv = rows_view(items@);
    let mut out: Vec<Expr> = Vec::new();
    proof {
        assert(rv.take(0) =~= Seq::<Seq<Expr>>::empty());
        assert(out@ =~= concat(rv.take(0)));
    }
    let mut i = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            rv == rows_view(items@),
            out@ == concat(rv.take(i as int)),
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
        r@ == seq![len] + concat(rows_view(items@)),
{
    let ghost l0 = len;
    let ghost rv = rows_view(items@);
    let mut out: Vec<Expr> = Vec::new();
    out.push(len);
    proof {
        assert(rv.take(0) =~= Seq::<Seq<Expr>>::empty());
        assert(out@ =~= seq![l0] + concat(rv.take(0)));
    }
    let mut i = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            rv == rows_view(items@),
            out@ == seq![l0] + concat(rv.take(i as int)),
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
            assert(seq![l0] + concat(rv.take(i + 1)) =~= (seq![l0] + concat(rv.take(i as int))) + items@[i as int]@);
        }
        i += 1;
    }
    proof {
        assert(rv.take(items@.len() as int) =~= rv);
    }
    out
}

} // verus!
