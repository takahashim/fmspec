//! List と Map のスロットの、行への区切りの仕様（`parts_ok`、`mparts_ok` など）。exec の区切りは `lists` と `maps` にある。

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

} // verus!
