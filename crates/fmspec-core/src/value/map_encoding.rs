//! キーに番号（rank）を付けたあとの、Mapの符号化。
//!
//! 各行の値の符号が値の符号化なら、[`encode_map_rows`] の結果はMapの符号化 `enc_rows` の符号である
//! （[`lemma_encodes_enc_rows`]）。

#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{codes, default_val, enc, enc_rows, lemma_codes_concat, STy, SVal};
use vstd::prelude::*;

verus! {

pub open spec fn row_codes(row: Option<Vec<i64>>, default: Seq<i64>) -> Seq<i64> {
    match row {
        Some(payload) => seq![1i64] + payload@,
        None => seq![0i64] + default,
    }
}

pub open spec fn prefix_fits(rows: Seq<Option<Vec<i64>>>, width: nat, count: int) -> bool {
    forall|i: int| 0 <= i < count ==> match #[trigger] rows[i] {
        Some(payload) => payload@.len() == width,
        None => true,
    }
}

pub open spec fn encodes_rows(
    rows: Seq<Option<Vec<i64>>>, default: Seq<i64>, flat: Seq<i64>, count: int,
) -> bool {
    let stride = 1 + default.len() as int;
    &&& flat.len() == count * stride
    &&& forall|r: int, col: int| 0 <= r < count && 0 <= col < stride ==>
        #[trigger] flat[r * stride + col] == row_codes(rows[r], default)[col]
}

fn append_row(out: &mut Vec<i64>, present: bool, payload: &Vec<i64>)
    ensures
        final(out)@ == old(out)@ + (seq![if present { 1i64 } else { 0i64 }] + payload@),
{
    let ghost prefix = out@;
    let tag: i64 = if present { 1 } else { 0 };
    out.push(tag);
    let mut col = 0;
    while col < payload.len()
        invariant
            col <= payload@.len(),
            out@ == prefix + (seq![tag] + payload@.take(col as int)),
        decreases payload@.len() - col,
    {
        out.push(payload[col]);
        col = col + 1;
        proof {
            assert(out@ =~= prefix + (seq![tag] + payload@.take(col as int)));
        }
    }
    proof {
        assert(payload@.take(col as int) =~= payload@);
    }
}

/// 番号の順に並べた行を、有無のスロットと値のスロットの列にする。
pub fn encode_map_rows(rows: &Vec<Option<Vec<i64>>>, default: &Vec<i64>) -> (out: Option<Vec<i64>>)
    ensures
        out is Some <==> prefix_fits(rows@, default@.len(), rows@.len() as int),
        out matches Some(flat) ==> encodes_rows(rows@, default@, flat@, rows@.len() as int),
{
    let mut flat: Vec<i64> = Vec::new();
    let mut row = 0;
    while row < rows.len()
        invariant
            row <= rows@.len(),
            prefix_fits(rows@, default@.len(), row as int),
            encodes_rows(rows@, default@, flat@, row as int),
        decreases rows@.len() - row,
    {
        let ghost before = flat@;
        match &rows[row] {
            Some(payload) => {
                if payload.len() != default.len() {
                    return None;
                }
                append_row(&mut flat, true, payload);
            },
            None => append_row(&mut flat, false, default),
        }
        proof {
            let stride = 1 + default@.len() as int;
            assert(flat@ == before + row_codes(rows@[row as int], default@));
            assert(row_codes(rows@[row as int], default@).len() == stride);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride, row as int, 1);
            assert forall|r: int, col: int| 0 <= r < row + 1 && 0 <= col < stride
                implies #[trigger] flat@[r * stride + col] == row_codes(rows@[r], default@)[col] by {
                if r < row {
                    vstd::arithmetic::mul::lemma_mul_inequality(r + 1, row as int, stride);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride, r, 1);
                    assert(0 <= r * stride + col < before.len()) by (nonlinear_arith)
                        requires stride > 0, r >= 0, col >= 0,
                            col < stride, (r + 1) * stride <= before.len();
                    assert(before[r * stride + col] == row_codes(rows@[r], default@)[col]);
                }
            }
        }
        row = row + 1;
    }
    Some(flat)
}

/// 番号 `rank` の行の値のスロット。位置の計算は `Map#get` の下ろしと同じである。
pub open spec fn encoded_payload(flat: Seq<i64>, width: nat, rank: int) -> Option<Seq<i64>> {
    let base = rank * (1 + width as int);
    if flat[base] == 0 {
        None
    } else {
        Some(flat.subrange(base + 1, base + 1 + width as int))
    }
}

pub proof fn encoded_payload_matches_row(
    rows: Seq<Option<Vec<i64>>>, default: Seq<i64>, flat: Seq<i64>, rank: int,
)
    requires
        0 <= rank < rows.len(),
        prefix_fits(rows, default.len(), rows.len() as int),
        encodes_rows(rows, default, flat, rows.len() as int),
    ensures
        encoded_payload(flat, default.len(), rank) == match rows[rank] {
            Some(payload) => Some(payload@),
            None => None,
        },
{
    let stride = 1 + default.len() as int;
    let base = rank * stride;
    vstd::arithmetic::mul::lemma_mul_inequality(0, rank, stride);
    vstd::arithmetic::mul::lemma_mul_inequality(rank + 1, rows.len() as int, stride);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride, rank, 1);
    assert(base + stride <= flat.len());
    assert(flat[base + 0] == row_codes(rows[rank], default)[0]);
    if let Some(payload) = rows[rank] {
        let slots = flat.subrange(base + 1, base + stride);
        assert forall|i: int| 0 <= i < payload@.len() implies #[trigger] slots[i] == payload@[i] by {
            assert(flat[base + (i + 1)] == row_codes(rows[rank], default)[i + 1]);
        }
        assert(slots =~= payload@);
    }
}

/// 行 `rows` の値の符号が、Mapの行 `vals` の値の符号化の符号である。
pub open spec fn rows_encode(rows: Seq<Option<Vec<i64>>>, vals: Seq<Option<SVal>>, t: STy, enums: Seq<i64>) -> bool {
    &&& rows.len() == vals.len()
    &&& forall|r: int| 0 <= r < rows.len() ==> match (#[trigger] rows[r], vals[r]) {
        (Some(p), Some(v)) => p@ == codes(enc(v, t, enums)),
        (None, None) => true,
        _ => false,
    }
}

/// 各行の値の符号が値の符号化で、`default` が既定値の符号化なら、行の列の符号はMapの符号化の符号である。
pub proof fn lemma_encodes_enc_rows(
    rows: Seq<Option<Vec<i64>>>,
    vals: Seq<Option<SVal>>,
    t: STy,
    enums: Seq<i64>,
    default: Seq<i64>,
    flat: Seq<i64>,
)
    requires
        prefix_fits(rows, default.len(), rows.len() as int),
        rows_encode(rows, vals, t, enums),
        default == codes(enc(default_val(t, enums), t, enums)),
        encodes_rows(rows, default, flat, rows.len() as int),
    ensures
        flat == codes(enc_rows(vals, t, enums)),
{
    lemma_encodes_prefix(rows, vals, t, enums, default, flat, rows.len() as int);
    assert(vals.take(rows.len() as int) =~= vals);
    let stride = 1 + default.len() as int;
    assert(flat.take(rows.len() * stride) =~= flat);
}

proof fn lemma_encodes_prefix(
    rows: Seq<Option<Vec<i64>>>,
    vals: Seq<Option<SVal>>,
    t: STy,
    enums: Seq<i64>,
    default: Seq<i64>,
    flat: Seq<i64>,
    n: int,
)
    requires
        0 <= n <= rows.len(),
        prefix_fits(rows, default.len(), rows.len() as int),
        rows_encode(rows, vals, t, enums),
        default == codes(enc(default_val(t, enums), t, enums)),
        encodes_rows(rows, default, flat, rows.len() as int),
    ensures
        flat.take(n * (1 + default.len() as int)) == codes(enc_rows(vals.take(n), t, enums)),
    decreases n,
{
    let stride = 1 + default.len() as int;
    if n == 0 {
        assert(n * stride == 0) by (nonlinear_arith)
            requires
                n == 0,
        ;
        assert(flat.take(0) =~= codes(enc_rows(vals.take(0), t, enums)));
    } else {
        let m = n - 1;
        lemma_encodes_prefix(rows, vals, t, enums, default, flat, m);
        let vs = vals.take(n);
        assert(vs.drop_last() =~= vals.take(m));
        assert(vs.last() == vals[m]);
        let row = match vals[m] {
            Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
            None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
        };
        lemma_codes_concat(enc_rows(vals.take(m), t, enums), row);
        // 行 m の符号は row_codes(rows[m], default) である。
        let rc = row_codes(rows[m], default);
        match vals[m] {
            Some(x) => {
                lemma_codes_concat(seq![Value::Bool(true)], enc(x, t, enums));
                assert(codes(seq![Value::Bool(true)]) =~= seq![1i64]);
                assert(codes(row) =~= rc);
            },
            None => {
                lemma_codes_concat(seq![Value::Bool(false)], enc(default_val(t, enums), t, enums));
                assert(codes(seq![Value::Bool(false)]) =~= seq![0i64]);
                assert(codes(row) =~= rc);
            },
        }
        assert(rc.len() == stride);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(stride, m, 1);
        vstd::arithmetic::mul::lemma_mul_inequality(n, rows.len() as int, stride);
        vstd::arithmetic::mul::lemma_mul_inequality(0, m, stride);
        let a = flat.take(m * stride);
        let b = flat.subrange(m * stride, n * stride);
        assert forall|col: int| 0 <= col < stride implies #[trigger] b[col] == rc[col] by {
            assert(flat[m * stride + col] == row_codes(rows[m], default)[col]);
        }
        assert(b =~= rc);
        assert(flat.take(n * stride) =~= a + b);
        assert(enc_rows(vs, t, enums) == enc_rows(vals.take(m), t, enums) + row);
        assert(flat.take(n * stride) =~= codes(enc_rows(vs, t, enums)));
    }
}

} // verus!
