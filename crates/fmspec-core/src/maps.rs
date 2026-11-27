//! Mapのスロットの補題。
//!
//! キーの数が `n` のMapは、キーの番号の順に `n` 個の行を並べて符号化する。
//! 行は、有無のBoolと値のスロットである（[`row_slots`]）。
//! 下ろしは、スロットの列を行に区切り（[`mparts_ok`]）、行を置き換え、行をつなぎ直す（[`flat`]）。

use crate::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::encoding::XTy;
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc_rows, keys, keys_or_zero, map_rows_member, member, sty, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::eval::Env;
use crate::expr_build::{keys_or_zero_exec, stype_width, sub_exprs};
#[cfg(verus_keep_ghost)]
use crate::limits::lim_s;
#[cfg(verus_keep_ghost)]
use crate::lists::{rows_at, rows_view};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{flat, mparts_ok, mrow_at};
use crate::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::model::Value;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
use vstd::prelude::*;

verus! {

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

/// Mapのスロットの行。行は、有無のBoolと値のスロットである。
pub fn map_rows(k: &SType, v: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Vec<Vec<Expr>>>)
    ensures
        r matches Some(rows) ==> mparts_ok(
            slots@,
            rows_view(rows@),
            (1 + width(sty(*v), enums@)) as nat,
            keys_or_zero(sty(*k), enums@),
        ),
        lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
            STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
            enums@,
        ) ==> r is Some,
{
    let ghost pre = lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
        STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
        enums@,
    );
    let n = keys_or_zero_exec(k, enums);
    let w = stype_width(v, enums)?;
    proof {
        assert(usize::MAX >= 0xffff_ffff);
        if pre {
            assert(lim_s(sty(*v), enums@));
            assert(n * (w + 1) == width(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@));
        }
    }
    let stride = w.checked_add(1)?;
    let size = n.checked_mul(stride)?;
    if size != slots.len() {
        return None;
    }
    let mut rows: Vec<Vec<Expr>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            stride == w + 1,
            size == n * stride,
            size == slots@.len(),
            i <= n,
            rows@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] mrow_at(rows@[q]@, slots@, q, stride as nat),
            pre ==> size <= 0x7fff_ffff,
            pre == (lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
                STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
                enums@,
            )),
        decreases n - i,
    {
        proof {
            assert((i + 1) * stride <= n * stride) by (nonlinear_arith)
                requires
                    i < n,
            ;
            assert(i * stride + stride == (i + 1) * stride) by (nonlinear_arith);
            assert(usize::MAX >= 0xffff_ffff);
        }
        let at = i.checked_mul(stride)?;
        let end = at.checked_add(stride)?;
        if end > slots.len() {
            return None;
        }
        let ghost r1 = rows@;
        rows.push(sub_exprs(slots, at, end));
        proof {
            assert forall|q: int| 0 <= q <= i implies #[trigger] mrow_at(rows@[q]@, slots@, q, stride as nat) by {
                if q < i {
                    assert(rows@[q] == r1[q]);
                }
            }
        }
        i += 1;
    }
    proof {
        let rv = rows_view(rows@);
        assert forall|q: int| 0 <= q < n implies #[trigger] mrow_at(rv[q], slots@, q, stride as nat) by {
            assert(rv[q] == rows@[q]@);
        }
    }
    Some(rows)
}

} // verus!
