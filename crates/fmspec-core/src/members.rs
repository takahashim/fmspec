//! 値の符号化が型に属すこと（`member`）と、スロットの値の列との対応の補題。型に属する値の符号化と、型に属さない値の符号化を扱う。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::{has_xtype, has_xtypes, keys, keys_or_zero, lemma_default_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_default_vals_len, lemma_enc_items_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_rows_len, lemma_enc_seq_len, lemma_repeat_len, lemma_to_xtys};
#[cfg(verus_keep_ghost)]
use crate::encoding::{list_items_member, map_rows_member, member, members, models, models_seq, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, to_xtys, wf_stype, wf_stypes, width, width_sum, xwidth, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, lits, pure_below};
#[cfg(verus_keep_ghost)]
use crate::limits::{small, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{etys, lemma_lits_typed, typed};
#[cfg(verus_keep_ghost)]
use crate::maps::lemma_none_rows;
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::lemma_members;
#[cfg(verus_keep_ghost)]
use crate::slot_types::{in_slot, in_slots, lemma_bools, lemma_in_slots_concat, lemma_slot_tys_len};
#[cfg(verus_keep_ghost)]
use crate::slot_types::{lemma_slot_tys_seq_len, lemma_ty_repeat_add, lemma_ty_repeat_len, slot_tys};
#[cfg(verus_keep_ghost)]
use crate::slot_types::{slot_tys_seq, ty_repeat};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

/// 整形式の型の既定値は、その型に属する。
pub proof fn lemma_default_member(t: STy, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
    ensures
        member(default_val(t, enums), t, enums),
    decreases t,
{
    match t {
        STy::Tuple(ts) => lemma_default_vals_member(ts, enums),
        STy::Record(_, ts) => lemma_default_vals_member(ts, enums),
        STy::Map(k, x) => lemma_none_rows(keys_or_zero(*k, enums), *x, enums),
        STy::Set(e) => {
            let bits = Seq::new(keys_or_zero(*e, enums), |_i: int| false);
            assert(default_val(t, enums) == SVal::Set(bits));
            assert(keys(*e, enums) == Some(bits.len()));
        },
        STy::List(e, _) => {
            assert(default_val(t, enums) == SVal::List(Seq::empty()));
            assert(list_items_member(Seq::<SVal>::empty(), *e, enums));
        },
        _ => {},
    }
}

pub proof fn lemma_default_vals_member(ts: Seq<STy>, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
    ensures
        members(default_vals(ts, enums), ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        lemma_default_vals_member(ts.drop_last(), enums);
        lemma_default_member(ts.last(), enums);
        lemma_default_vals_len(ts, enums);
        let d = default_vals(ts, enums);
        assert(d.drop_last() == default_vals(ts.drop_last(), enums));
    }
}

/// 型に属する値の符号化の各スロットは、スロットの型の値である。
pub proof fn lemma_member_in(v: SVal, t: STy, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        small(t),
        member(v, t, enums),
    ensures
        in_slots(enc(v, t, enums), slot_tys(t, enums), enums),
    decreases t, 1nat,
{
    let s = enc(v, t, enums);
    let tys = slot_tys(t, enums);
    match t {
        STy::Bool => assert(in_slot(tys[0], s[0], enums)),
        STy::Int(_, _) => assert(in_slot(tys[0], s[0], enums)),
        STy::Enum(_) => assert(in_slot(tys[0], s[0], enums)),
        STy::Tuple(ts) => lemma_seq_in(v->Tuple_0, ts, enums),
        STy::Record(_, ts) => lemma_seq_in(v->Tuple_0, ts, enums),
        STy::Option(x) => {
            let w = match v {
                SVal::Some(w) => *w,
                _ => default_val(*x, enums),
            };
            if !(v is Some) {
                lemma_default_member(*x, enums);
            }
            lemma_member_in(w, *x, enums);
            let b = seq![Value::Bool(v is Some)];
            assert(in_slots(b, seq![Type::Bool], enums)) by {
                assert(in_slot(Type::Bool, b[0], enums));
            }
            assert(s == b + enc(w, *x, enums));
            lemma_in_slots_concat(b, seq![Type::Bool], enc(w, *x, enums), slot_tys(*x, enums), enums);
        },
        STy::Set(e) => {
            let bits = v->Set_0;
            lemma_bools(bits.len());
            assert forall|j: int| 0 <= j < s.len() implies #[trigger] in_slot(tys[j], s[j], enums) by {
                assert(tys[j] == Type::Bool);
                assert(s[j] == Value::Bool(bits[j]));
            }
        },
        STy::Map(k, x) => {
            let rows = v->Map_0;
            lemma_rows_in(rows, *x, enums);
        },
        STy::List(e, max) => {
            let items = v->List_0;
            let n = items.len();
            let m = (max - n) as nat;
            let et = slot_tys(*e, enums);
            let d = enc(default_val(*e, enums), *e, enums);
            lemma_items_in(items, *e, enums);
            lemma_default_member(*e, enums);
            lemma_member_in(default_val(*e, enums), *e, enums);
            lemma_repeat_in(d, et, m, enums);
            lemma_ty_repeat_add(et, n, m);
            assert(n + m == max as nat);
            lemma_slot_tys_len(*e, enums);
            lemma_enc_items_len(items, *e, enums);
            lemma_ty_repeat_len(et, n);
            lemma_in_slots_concat(enc_items(items, *e, enums), ty_repeat(et, n), enc_repeat(d, m), ty_repeat(et, m), enums);
            let h = seq![Value::Int(n as i64)];
            assert(in_slots(h, seq![Type::Int(0, max as i64)], enums)) by {
                assert(in_slot(Type::Int(0, max as i64), h[0], enums));
            }
            let body = enc_items(items, *e, enums) + enc_repeat(d, m);
            lemma_in_slots_concat(h, seq![Type::Int(0, max as i64)], body, ty_repeat(et, max as nat), enums);
            assert(s =~= h + body);
        },
    }
}

pub proof fn lemma_seq_in(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
        smalls(ts),
        members(vs, ts, enums),
    ensures
        in_slots(enc_seq(vs, ts, enums), slot_tys_seq(ts, enums), enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let a = vs.drop_last();
        lemma_seq_in(a, ts.drop_last(), enums);
        lemma_member_in(vs.last(), ts.last(), enums);
        lemma_enc_seq_len(a, ts.drop_last(), enums);
        lemma_slot_tys_seq_len(ts.drop_last(), enums);
        lemma_in_slots_concat(
            enc_seq(a, ts.drop_last(), enums),
            slot_tys_seq(ts.drop_last(), enums),
            enc(vs.last(), ts.last(), enums),
            slot_tys(ts.last(), enums),
            enums,
        );
    } else {
        assert(enc_seq(vs, ts, enums) =~= Seq::<Value>::empty());
    }
}

pub(crate) proof fn lemma_rows_in(rows: Seq<Option<SVal>>, x: STy, enums: Seq<i64>)
    requires
        wf_stype(x, enums),
        small(x),
        map_rows_member(rows, x, enums),
    ensures
        in_slots(enc_rows(rows, x, enums), ty_repeat(seq![Type::Bool] + slot_tys(x, enums), rows.len()), enums),
    decreases x, rows.len() + 1,
{
    if rows.len() > 0 {
        let a = rows.drop_last();
        let row = seq![Type::Bool] + slot_tys(x, enums);
        lemma_rows_in(a, x, enums);
        let w = match rows.last() {
            Some(w) => w,
            None => default_val(x, enums),
        };
        if rows.last() is None {
            lemma_default_member(x, enums);
        }
        lemma_member_in(w, x, enums);
        let b = seq![Value::Bool(rows.last() is Some)];
        assert(in_slots(b, seq![Type::Bool], enums)) by {
            assert(in_slot(Type::Bool, b[0], enums));
        }
        lemma_in_slots_concat(b, seq![Type::Bool], enc(w, x, enums), slot_tys(x, enums), enums);
        lemma_enc_rows_len(a, x, enums);
        lemma_slot_tys_len(x, enums);
        lemma_ty_repeat_len(row, a.len());
        lemma_in_slots_concat(enc_rows(a, x, enums), ty_repeat(row, a.len()), b + enc(w, x, enums), row, enums);
        assert(enc_rows(rows, x, enums) == enc_rows(a, x, enums) + (b + enc(w, x, enums)));
        assert(ty_repeat(row, rows.len()) == ty_repeat(row, a.len()) + row);
    } else {
        assert(enc_rows(rows, x, enums) =~= Seq::<Value>::empty());
    }
}

pub(crate) proof fn lemma_items_in(items: Seq<SVal>, e: STy, enums: Seq<i64>)
    requires
        wf_stype(e, enums),
        small(e),
        list_items_member(items, e, enums),
    ensures
        in_slots(enc_items(items, e, enums), ty_repeat(slot_tys(e, enums), items.len()), enums),
    decreases e, items.len() + 1,
{
    if items.len() > 0 {
        let a = items.drop_last();
        let et = slot_tys(e, enums);
        lemma_items_in(a, e, enums);
        lemma_member_in(items.last(), e, enums);
        lemma_enc_items_len(a, e, enums);
        lemma_slot_tys_len(e, enums);
        lemma_ty_repeat_len(et, a.len());
        lemma_in_slots_concat(enc_items(a, e, enums), ty_repeat(et, a.len()), enc(items.last(), e, enums), et, enums);
        assert(ty_repeat(et, items.len()) == ty_repeat(et, a.len()) + et);
    } else {
        assert(enc_items(items, e, enums) =~= Seq::<Value>::empty());
    }
}

pub(crate) proof fn lemma_repeat_in(d: Seq<Value>, tys: Seq<Type>, n: nat, enums: Seq<i64>)
    requires
        in_slots(d, tys, enums),
    ensures
        in_slots(enc_repeat(d, n), ty_repeat(tys, n), enums),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_repeat_in(d, tys, m, enums);
        lemma_repeat_len(d, m);
        lemma_ty_repeat_len(tys, m);
        lemma_in_slots_concat(enc_repeat(d, m), ty_repeat(tys, m), d, tys, enums);
    } else {
        assert(enc_repeat(d, n) =~= Seq::<Value>::empty());
    }
}

pub proof fn lemma_lits_pure(vs: Seq<Value>, n: nat)
    ensures
        all_pure(lits(vs), n),
{
    assert forall|j: int| 0 <= j < lits(vs).len() implies pure_below(#[trigger] lits(vs)[j], n) by {
        assert(lits(vs)[j] == Expr::Const(vs[j]));
    }
}

/// スロットの値の列が値を表すなら、値はその式の型を持つ。
pub proof fn lemma_models_has(s: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        models(s, v, t, enums),
    ensures
        has_xtype(v, t, enums),
    decreases t,
{
    match t {
        XTy::Tuple(ts) => lemma_models_has_seq(s, v->Tuple_0, ts, enums),
        XTy::Record(_, ts) => lemma_models_has_seq(s, v->Tuple_0, ts, enums),
        XTy::Option(x) => match v {
            SVal::Some(w) => lemma_models_has(s.drop_first(), *w, *x, enums),
            _ => {},
        },
        _ => {},
    }
}

pub proof fn lemma_models_has_seq(s: Seq<Value>, vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>)
    requires
        models_seq(s, vs, ts, enums),
    ensures
        has_xtypes(vs, ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        let w = xwidth(ts.last(), enums);
        let cut = s.len() - w;
        lemma_models_has_seq(s.take(cut), vs.drop_last(), ts.drop_last(), enums);
        lemma_models_has(s.skip(cut), vs.last(), ts.last(), enums);
    }
}

/// 格納の型の式の型を持つ値の符号化の長さは、型の幅である。
pub proof fn lemma_shaped_len(v: SVal, t: STy, enums: Seq<i64>)
    requires
        has_xtype(v, to_xty(t), enums),
    ensures
        enc(v, t, enums).len() == width(t, enums),
    decreases t,
{
    match t {
        STy::Tuple(ts) => lemma_shaped_seq_len(v->Tuple_0, ts, enums),
        STy::Record(_, ts) => lemma_shaped_seq_len(v->Tuple_0, ts, enums),
        STy::Option(x) => match v {
            SVal::Some(w) => lemma_shaped_len(*w, *x, enums),
            _ => lemma_default_len(*x, enums),
        },
        STy::Set(_) => lemma_enc_len(v, t, enums),
        STy::Map(_, _) => lemma_enc_len(v, t, enums),
        STy::List(_, _) => lemma_enc_len(v, t, enums),
        _ => {},
    }
}

pub proof fn lemma_shaped_seq_len(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        has_xtypes(vs, to_xtys(ts), enums),
    ensures
        enc_seq(vs, ts, enums).len() == width_sum(ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        let xs = to_xtys(ts);
        assert(xs.drop_last() == to_xtys(ts.drop_last()));
        assert(xs.last() == to_xty(ts.last()));
        lemma_shaped_seq_len(vs.drop_last(), ts.drop_last(), enums);
        lemma_shaped_len(vs.last(), ts.last(), enums);
    } else {
        lemma_to_xtys(ts);
    }
}

/// 格納の型の式の型を持つ値の符号化の各スロットが、スロットの型の値なら、値は型に属する。
/// 型に属さない値は、どれかのスロットが、スロットの型の値でない（整数の範囲外）。
pub proof fn lemma_in_member(v: SVal, t: STy, enums: Seq<i64>)
    requires
        has_xtype(v, to_xty(t), enums),
        in_slots(enc(v, t, enums), slot_tys(t, enums), enums),
    ensures
        member(v, t, enums),
    decreases t,
{
    let s = enc(v, t, enums);
    let tys = slot_tys(t, enums);
    match t {
        STy::Int(_, _) => assert(in_slot(tys[0], s[0], enums)),
        STy::Enum(_) => assert(in_slot(tys[0], s[0], enums)),
        STy::Tuple(ts) => lemma_in_members(v->Tuple_0, ts, enums),
        STy::Record(_, ts) => lemma_in_members(v->Tuple_0, ts, enums),
        STy::Option(x) => match v {
            SVal::Some(w) => {
                lemma_slot_tys_len(*x, enums);
                lemma_in_slots_concat(seq![Value::Bool(true)], seq![Type::Bool], enc(*w, *x, enums), slot_tys(*x, enums), enums);
                lemma_in_member(*w, *x, enums);
            },
            _ => {},
        },
        _ => {},
    }
}

pub proof fn lemma_in_members(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        has_xtypes(vs, to_xtys(ts), enums),
        in_slots(enc_seq(vs, ts, enums), slot_tys_seq(ts, enums), enums),
    ensures
        members(vs, ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        let xs = to_xtys(ts);
        assert(xs.drop_last() == to_xtys(ts.drop_last()));
        assert(xs.last() == to_xty(ts.last()));
        let a = vs.drop_last();
        lemma_shaped_seq_len(a, ts.drop_last(), enums);
        lemma_slot_tys_seq_len(ts.drop_last(), enums);
        lemma_in_slots_concat(
            enc_seq(a, ts.drop_last(), enums),
            slot_tys_seq(ts.drop_last(), enums),
            enc(vs.last(), ts.last(), enums),
            slot_tys(ts.last(), enums),
            enums,
        );
        lemma_in_members(a, ts.drop_last(), enums);
        lemma_in_member(vs.last(), ts.last(), enums);
    } else {
        lemma_to_xtys(ts);
    }
}

/// 型の既定値のリテラルは、スロットの型の中核の型を持つ。
pub proof fn lemma_defaults_typed(st: STy, t: TyEnv, lt: Seq<ETy>)
    requires
        crate::encoding::wf_stype(st, t.enums),
        crate::limits::small(st),
    ensures
        typed(
            crate::expr_build::lits(crate::encoding::enc(crate::encoding::default_val(st, t.enums), st, t.enums)),
            etys(slot_tys(st, t.enums)),
            t,
            lt,
        ),
{
    crate::members::lemma_default_member(st, t.enums);
    crate::members::lemma_member_in(crate::encoding::default_val(st, t.enums), st, t.enums);
    lemma_lits_typed(crate::encoding::enc(crate::encoding::default_val(st, t.enums), st, t.enums), slot_tys(st, t.enums), t, lt);
}

pub proof fn lemma_wf_index(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
        smalls(ts),
        0 <= i < ts.len(),
    ensures
        wf_stype(ts[i], enums),
        small(ts[i]),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        lemma_wf_index(ts.drop_last(), i, enums);
        assert(ts.drop_last()[i] == ts[i]);
    }
}

/// 組の符号化の `i` 番目の部分は、`i` 番目の要素の符号化である。
pub proof fn lemma_enc_seq_sub(vs: Seq<SVal>, ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
        0 <= i < ts.len(),
    ensures
        width_sum(ts.take(i), enums) + width(ts[i], enums) <= enc_seq(vs, ts, enums).len(),
        enc_seq(vs, ts, enums).subrange(
            width_sum(ts.take(i), enums) as int,
            (width_sum(ts.take(i), enums) + width(ts[i], enums)) as int,
        ) == enc(vs[i], ts[i], enums),
    decreases ts.len(),
{
    let n = ts.len() - 1;
    let a = ts.drop_last();
    let b = vs.drop_last();
    lemma_enc_seq_len(vs, ts, enums);
    lemma_enc_seq_len(b, a, enums);
    lemma_members(vs, ts, enums);
    lemma_enc_len(vs[i], ts[i], enums);
    let s = enc_seq(vs, ts, enums);
    assert(s == enc_seq(b, a, enums) + enc(vs.last(), ts.last(), enums));
    if i == n {
        assert(ts.take(i) =~= a);
        assert(s.subrange(width_sum(a, enums) as int, s.len() as int) =~= enc(vs.last(), ts.last(), enums));
    } else {
        lemma_enc_seq_sub(b, a, i, enums);
        assert(a.take(i) =~= ts.take(i));
        assert(a[i] == ts[i]);
        assert(b[i] == vs[i]);
        let lo = width_sum(ts.take(i), enums) as int;
        let hi = lo + width(ts[i], enums);
        assert(s.subrange(lo, hi) =~= enc_seq(b, a, enums).subrange(lo, hi));
    }
}

} // verus!
