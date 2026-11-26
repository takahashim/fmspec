//! Encoding of a finite map after assigning each key its rank.

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

/// Encode ranked rows with one presence slot followed by the payload slots.
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

/// Read a row by rank using the same flat offsets as Map#get lowering.
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

} // verus!
