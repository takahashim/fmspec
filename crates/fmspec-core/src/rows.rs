//! List と Map のスロットの、行への区切りの仕様（`parts_ok`、`mparts_ok` など）。exec の区切りは `lists` と `maps` にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::width;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_rows, lemma_default_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_rows_len, lemma_map_rows_member_index, map_rows_member, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::expr_build::ite_s;
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
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

} // verus!
