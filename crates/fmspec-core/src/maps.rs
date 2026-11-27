//! Mapのスロットの補題。
//!
//! キーの数が `n` のMapは、キーの番号の順に `n` 個の行を並べて符号化する。
//! 行は、有無のBoolと値のスロットである（[`row_slots`]）。
//! 下ろしは、スロットの列を行に区切り（[`mparts_ok`]）、行を置き換え、行をつなぎ直す（[`flat`]）。

#[cfg(verus_keep_ghost)]
use crate::encoding::{enc_rows, keys, map_rows_member, member, width, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::Env;
#[cfg(verus_keep_ghost)]
use crate::lists::{flat, rows_at};
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
use vstd::prelude::*;

verus! {

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

/// Mapの各行の符号化。
pub open spec fn row_vals(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>) -> Seq<Seq<Value>> {
    Seq::new(rows.len(), |p: int| row_slots(rows[p], t, enums))
}

/// 区切った行は、Mapの各行の符号化を表す。
pub proof fn lemma_map_parts(
    slots: Seq<Expr>,
    mrows: Seq<Seq<Expr>>,
    env: Env,
    l: Seq<Value>,
    rows: Seq<Option<SVal>>,
    kt: STy,
    vt: STy,
    enums: Seq<i64>,
)
    requires
        denotes(slots, env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), enums),
        mparts_ok(slots, mrows, (1 + width(vt, enums)) as nat, rows.len()),
    ensures
        keys(kt, enums) == Some(rows.len()),
        map_rows_member(rows, vt, enums),
        rows_at(mrows, row_vals(rows, vt, enums), env, l),
{
    let w = 1 + width(vt, enums);
    let sv = slot_vals(slots, env, l);
    assert(member(SVal::Map(rows), STy::Map(Box::new(kt), Box::new(vt)), enums));
    assert(sv == enc_rows(rows, vt, enums));
    let vals = row_vals(rows, vt, enums);
    assert forall|p: int| 0 <= p < mrows.len() implies clean(#[trigger] mrows[p], env, l) && slot_vals(mrows[p], env, l)
        == vals[p] by {
        assert(mrow_at(mrows[p], slots, p, w as nat));
        lemma_clean_sub(slots, env, l, p * w, p * w + w);
        lemma_enc_rows_index(rows, vt, enums, p, 0);
        assert forall|j: int| 0 <= j < w implies #[trigger] sv.subrange(p * w, p * w + w)[j] == vals[p][j] by {
            lemma_enc_rows_index(rows, vt, enums, p, j);
        }
        assert(sv.subrange(p * w, p * w + w) =~= vals[p]);
    }
}

/// 各行の符号化を表す行をつなげると、Mapの行の符号化を表す。
pub proof fn lemma_flat_rows(mrows: Seq<Seq<Expr>>, rows: Seq<Option<SVal>>, t: STy, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        rows_at(mrows, row_vals(rows, t, enums), env, l),
    ensures
        clean(flat(mrows), env, l),
        slot_vals(flat(mrows), env, l) == enc_rows(rows, t, enums),
    decreases mrows.len(),
{
    if mrows.len() == 0 {
        assert(slot_vals(flat(mrows), env, l) =~= Seq::<Value>::empty());
    } else {
        let a = mrows.drop_last();
        let b = rows.drop_last();
        assert forall|p: int| 0 <= p < a.len() implies clean(#[trigger] a[p], env, l) && slot_vals(a[p], env, l)
            == row_vals(b, t, enums)[p] by {
            assert(a[p] == mrows[p]);
            assert(b[p] == rows[p]);
        }
        lemma_flat_rows(a, b, t, env, l, enums);
        assert(clean(mrows[mrows.len() - 1], env, l));
        lemma_clean_concat(flat(a), mrows.last(), env, l);
        assert(row_vals(rows, t, enums)[rows.len() - 1] == row_slots(rows.last(), t, enums));
        assert(enc_rows(rows, t, enums) == enc_rows(b, t, enums) + row_slots(rows.last(), t, enums));
    }
}

/// 各行の符号化を表す行をつなげると、Mapを表す。
pub proof fn lemma_map_join(
    mrows: Seq<Seq<Expr>>,
    env: Env,
    l: Seq<Value>,
    rows: Seq<Option<SVal>>,
    kt: STy,
    vt: STy,
    enums: Seq<i64>,
)
    requires
        keys(kt, enums) == Some(rows.len()),
        map_rows_member(rows, vt, enums),
        rows_at(mrows, row_vals(rows, vt, enums), env, l),
    ensures
        denotes(flat(mrows), env, l, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), enums),
{
    lemma_flat_rows(mrows, rows, vt, env, l, enums);
}

/// どのキーもないMapの行は、型に属する。
pub proof fn lemma_none_rows(n: nat, t: STy, enums: Seq<i64>)
    ensures
        map_rows_member(Seq::new(n, |_i: int| None::<SVal>), t, enums),
    decreases n,
{
    if n > 0 {
        lemma_none_rows((n - 1) as nat, t, enums);
        assert(Seq::new(n, |_i: int| None::<SVal>).drop_last() =~= Seq::new((n - 1) as nat, |_i: int| None::<SVal>));
    }
}

/// 行を置き換えても、各行の値は型に属する。
pub proof fn lemma_rows_update(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>, r: int, o: Option<SVal>)
    requires
        map_rows_member(rows, t, enums),
        0 <= r < rows.len(),
        o matches Some(x) ==> member(x, t, enums),
    ensures
        map_rows_member(rows.update(r, o), t, enums),
        row_vals(rows.update(r, o), t, enums) =~= Seq::new(
            rows.len(),
            |p: int| if p == r { row_slots(o, t, enums) } else { row_vals(rows, t, enums)[p] },
        ),
    decreases rows.len(),
{
    let u = rows.update(r, o);
    if r < rows.len() - 1 {
        lemma_rows_update(rows.drop_last(), t, enums, r, o);
        assert(u.drop_last() =~= rows.drop_last().update(r, o));
        assert(u.last() == rows.last());
    } else {
        assert(u.drop_last() =~= rows.drop_last());
        assert(u.last() == o);
    }
}

} // verus!
