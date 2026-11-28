//! スロットの型と、正規形の判定。
//!
//! 格納の型の値の符号化は、スロットごとに中核の型（[`crate::lower_types::slot_tys`]）を持つ。
//! 状態変数と引数の符号化列は、スロットごとにこの型の値を取る。
//! 引数はスロットごとに値をたどるので、どの値の符号化でもない組（正規形でない組）も現れる。
//! [`canon_ok`] は、スロットの値の列がある値の正規形の符号化であることで、
//! [`canonical`] は、それを判定する中核の式を作る。

use crate::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::{has_xtype, has_xtypes, keys, keys_or_zero, lemma_default_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_default_vals_len, lemma_enc_items_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_rows_len, lemma_enc_seq_len, lemma_repeat_len, lemma_stys};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_to_xtys, lemma_xtys, lemma_xwidth_of, lemma_xwidths_of};
#[cfg(verus_keep_ghost)]
use crate::encoding::{list_items_member, map_rows_member, member, members, models, models_seq, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{sty, stys, SVal, to_xty, to_xtys, wf_stype, wf_stypes, width, width_sum, XTy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{xty, xtys, xwidth, xwidth_sum};
#[cfg(verus_keep_ghost)]
use crate::eval::{Env, ErrKind, eval_l};
use crate::expr_build::{all_of, bin, cb, ci, defaults, eq, is_bool_lit, ite, split, sub_exprs};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, concat, int_lit, ite_s, Join, lemma_xoff_step, lits};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{pure_below, split_ok, tree_s, xoff};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::*;
use crate::lists::list_parts;
#[cfg(verus_keep_ghost)]
use crate::lists::{lemma_items_member, lemma_list_join, lemma_list_parts, pad, pad_vals, rows_at};
#[cfg(verus_keep_ghost)]
use crate::lists::rows_view;
#[cfg(verus_keep_ghost)]
use crate::lower_types::*;
use crate::maps::map_rows;
#[cfg(verus_keep_ghost)]
use crate::maps::{lemma_map_join, lemma_map_parts, lemma_none_rows, row_vals};
use crate::model::{BinOp, Expr, Type};
#[cfg(verus_keep_ghost)]
use crate::model::Value;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::rows::{flat, mparts_ok, mrow_at, parts_ok, row_at};
use crate::stype_exec::{keys_or_zero_exec, to_xtype};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

// ---- スロットの型 ----

/// スロットの値の列 `xs` は、型 `t` のある値の正規形の符号化である。
pub open spec fn canon_ok(xs: Seq<Value>, t: STy, enums: Seq<i64>) -> bool {
    exists|v: SVal| member(v, t, enums) && #[trigger] enc(v, t, enums) == xs
}

// ---- スロットの型の補題 ----

pub proof fn lemma_ty_repeat_add(xs: Seq<Type>, a: nat, b: nat)
    ensures
        ty_repeat(xs, a + b) == ty_repeat(xs, a) + ty_repeat(xs, b),
    decreases b,
{
    if b == 0 {
        assert(ty_repeat(xs, a) + ty_repeat(xs, 0) =~= ty_repeat(xs, a));
    } else {
        let c = (b - 1) as nat;
        lemma_ty_repeat_add(xs, a, c);
        assert(ty_repeat(xs, a + b) == ty_repeat(xs, a + c) + xs);
        assert(ty_repeat(xs, a) + ty_repeat(xs, c) + xs =~= ty_repeat(xs, a) + (ty_repeat(xs, c) + xs));
    }
}

pub proof fn lemma_bools(n: nat)
    ensures
        ty_repeat(seq![Type::Bool], n) == Seq::new(n, |_i: int| Type::Bool),
    decreases n,
{
    if n > 0 {
        lemma_bools((n - 1) as nat);
        assert(ty_repeat(seq![Type::Bool], n) =~= Seq::new(n, |_i: int| Type::Bool));
    } else {
        assert(ty_repeat(seq![Type::Bool], n) =~= Seq::new(n, |_i: int| Type::Bool));
    }
}

// ---- スロットの値の補題 ----

/// つなげた列の各値がスロットの型の値であることは、それぞれの列についてそうであることである。
pub proof fn lemma_in_slots_concat(a: Seq<Value>, ta: Seq<Type>, b: Seq<Value>, tb: Seq<Type>, enums: Seq<i64>)
    requires
        a.len() == ta.len(),
    ensures
        in_slots(a + b, ta + tb, enums) <==> (in_slots(a, ta, enums) && in_slots(b, tb, enums)),
{
    if in_slots(a, ta, enums) && in_slots(b, tb, enums) {
        assert forall|j: int| 0 <= j < (a + b).len() implies #[trigger] in_slot((ta + tb)[j], (a + b)[j], enums) by {
            if j < a.len() {
                assert(in_slot(ta[j], a[j], enums));
            } else {
                assert(in_slot(tb[j - a.len()], b[j - a.len()], enums));
            }
        }
    }
    if in_slots(a + b, ta + tb, enums) {
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] in_slot(ta[j], a[j], enums) by {
            assert(in_slot((ta + tb)[j], (a + b)[j], enums));
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] in_slot(tb[j], b[j], enums) by {
            assert(in_slot((ta + tb)[j + a.len()], (a + b)[j + a.len()], enums));
        }
    }
}

pub proof fn lemma_in_slots_sub(xs: Seq<Value>, tys: Seq<Type>, lo: int, hi: int, enums: Seq<i64>)
    requires
        in_slots(xs, tys, enums),
        0 <= lo <= hi <= xs.len(),
    ensures
        in_slots(xs.subrange(lo, hi), tys.subrange(lo, hi), enums),
{
    assert forall|j: int| 0 <= j < hi - lo implies #[trigger] in_slot(
        tys.subrange(lo, hi)[j],
        xs.subrange(lo, hi)[j],
        enums,
    ) by {
        assert(in_slot(tys[lo + j], xs[lo + j], enums));
    }
}

/// 同じスロットの型の値は、同じ種類である。
pub proof fn lemma_in_slot_kind(ty: Type, x: Value, y: Value, enums: Seq<i64>)
    requires
        in_slot(ty, x, enums),
        in_slot(ty, y, enums),
    ensures
        crate::eval::same_kind(x, y),
{
}

// ---- 型に属する値の符号化 ----

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

proof fn lemma_rows_in(rows: Seq<Option<SVal>>, x: STy, enums: Seq<i64>)
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

proof fn lemma_items_in(items: Seq<SVal>, e: STy, enums: Seq<i64>)
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

proof fn lemma_repeat_in(d: Seq<Value>, tys: Seq<Type>, n: nat, enums: Seq<i64>)
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

// ---- 型に属さない値の符号化 ----

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

// ---- 列の補題 ----

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

pub proof fn lemma_items_member_all(items: Seq<SVal>, t: STy, enums: Seq<i64>)
    requires
        forall|k: int| 0 <= k < items.len() ==> member(#[trigger] items[k], t, enums),
    ensures
        list_items_member(items, t, enums),
    decreases items.len(),
{
    if items.len() > 0 {
        let a = items.drop_last();
        assert forall|k: int| 0 <= k < a.len() implies member(#[trigger] a[k], t, enums) by {
            assert(a[k] == items[k]);
        }
        lemma_items_member_all(a, t, enums);
        assert(member(items[items.len() - 1], t, enums));
    }
}

pub proof fn lemma_rows_member_all(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>)
    requires
        forall|k: int| 0 <= k < rows.len() ==> (#[trigger] rows[k] matches Some(x) ==> member(x, t, enums)),
    ensures
        map_rows_member(rows, t, enums),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let a = rows.drop_last();
        assert forall|k: int| 0 <= k < a.len() implies (#[trigger] a[k] matches Some(x) ==> member(x, t, enums)) by {
            assert(a[k] == rows[k]);
        }
        lemma_rows_member_all(a, t, enums);
        assert(rows[rows.len() - 1] matches Some(x) ==> member(x, t, enums));
    }
}

/// 幅 `w` の行に区切った列をつなげ直すと、もとの列になる。
pub proof fn lemma_flat_split(s: Seq<Expr>, rows: Seq<Seq<Expr>>, w: nat)
    requires
        s.len() == rows.len() * w,
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] rows[p] == s.subrange(p * w, p * w + w),
    ensures
        flat(rows) == s,
    decreases rows.len(),
{
    if rows.len() == 0 {
        assert(s =~= Seq::<Expr>::empty());
    } else {
        let n = rows.len() - 1;
        let a = rows.drop_last();
        let c = n * w;
        assert(c + w == rows.len() * w) by (nonlinear_arith)
            requires
                n + 1 == rows.len(),
                c == n * w,
        ;
        assert(0 <= c) by (nonlinear_arith)
            requires
                0 <= n,
                c == n * w,
        ;
        let t = s.take(c);
        assert forall|p: int| 0 <= p < a.len() implies #[trigger] a[p] == t.subrange(p * w, p * w + w) by {
            assert(p * w + w <= c) by (nonlinear_arith)
                requires
                    0 <= p < n,
                    c == n * w,
            ;
            assert(0 <= p * w) by (nonlinear_arith)
                requires
                    0 <= p,
            ;
            assert(a[p] == rows[p]);
            assert(t.subrange(p * w, p * w + w) =~= s.subrange(p * w, p * w + w));
        }
        lemma_flat_split(t, a, w);
        assert(rows[n] == s.subrange(c, c + w));
        assert(s =~= t + s.subrange(c, c + w));
    }
}

/// 要素の位置で区切った部分をつなげ直すと、もとの列になる。
pub proof fn lemma_concat_split(slots: Seq<Expr>, parts: Seq<Seq<Expr>>, ts: Seq<XTy>, enums: Seq<i64>)
    requires
        parts.len() == ts.len(),
        slots.len() == xwidth_sum(ts, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] split_ok(parts[i], slots, ts, i, enums),
    ensures
        concat(parts) == slots,
    decreases ts.len(),
{
    if ts.len() == 0 {
        assert(slots =~= Seq::<Expr>::empty());
    } else {
        let n = ts.len() - 1;
        let a = ts.drop_last();
        let c = xoff(ts, n, enums);
        assert(ts.take(n) =~= a);
        let s0 = slots.take(c);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] split_ok(parts.drop_last()[i], s0, a, i, enums) by {
            assert(split_ok(parts[i], slots, ts, i, enums));
            assert(a.take(i) =~= ts.take(i));
            assert(a[i] == ts[i]);
            lemma_xoff_step(ts, i, enums);
            lemma_xoff_mono(ts, i + 1, n, enums);
            let lo = xoff(ts, i, enums);
            let hi = lo + xwidth(ts[i], enums);
            assert(s0.subrange(lo, hi) =~= slots.subrange(lo, hi));
        }
        lemma_concat_split(s0, parts.drop_last(), a, enums);
        assert(split_ok(parts[n], slots, ts, n, enums));
        assert(concat(parts) == concat(parts.drop_last()) + parts.last());
        assert(slots =~= s0 + slots.subrange(c, slots.len() as int));
    }
}

proof fn lemma_xoff_mono(ts: Seq<XTy>, i: int, j: int, enums: Seq<i64>)
    requires
        0 <= i <= j <= ts.len(),
    ensures
        xoff(ts, i, enums) <= xoff(ts, j, enums),
    decreases j - i,
{
    if i < j {
        lemma_xoff_mono(ts, i, j - 1, enums);
        lemma_xoff_step(ts, j - 1, enums);
    }
}

/// 格納の型の列の、`i` 番目の要素のスロットの位置と幅。
pub proof fn lemma_xoff_to(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        0 <= i < ts.len(),
    ensures
        to_xtys(ts).len() == ts.len(),
        xoff(to_xtys(ts), i, enums) == width_sum(ts.take(i), enums),
        xwidth(to_xtys(ts)[i], enums) == width(ts[i], enums),
        xwidth_sum(to_xtys(ts), enums) == width_sum(ts, enums),
{
    lemma_to_xtys(ts);
    lemma_to_xtys(ts.take(i));
    assert(to_xtys(ts).take(i) =~= to_xtys(ts.take(i)));
    lemma_xwidths_of(ts.take(i), enums);
    lemma_xwidths_of(ts, enums);
    lemma_xwidth_of(ts[i], enums);
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

// ---- 等しさの式 ----

/// 対応するスロットの等しさの項。
pub open spec fn eq_items(xs: Seq<Expr>, ys: Seq<Expr>) -> Seq<Expr> {
    Seq::new(
        if xs.len() < ys.len() {
            xs.len()
        } else {
            ys.len()
        },
        |i: int| Expr::Bin(BinOp::Eq, Box::new(xs[i]), Box::new(ys[i])),
    )
}

pub open spec fn eq_all_s(xs: Seq<Expr>, ys: Seq<Expr>) -> Expr {
    tree_s(eq_items(xs, ys), bool_lit(true), Join::And)
}

/// `xs` と `ys` の対応するスロットが等しい。
fn eq_all(xs: &Vec<Expr>, ys: &Vec<Expr>) -> (r: Expr)
    ensures
        r == eq_all_s(xs@, ys@),
{
    let n = if xs.len() < ys.len() {
        xs.len()
    } else {
        ys.len()
    };
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            n == eq_items(xs@, ys@).len(),
            n <= xs.len(),
            n <= ys.len(),
            i <= n,
            items@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] items@[j] == eq_items(xs@, ys@)[j],
        decreases n - i,
    {
        items.push(eq(copy_expr(&xs[i]), copy_expr(&ys[i])));
        i += 1;
    }
    proof {
        assert(items@ =~= eq_items(xs@, ys@));
    }
    all_of(&items)
}

pub proof fn lemma_eq_all_pure(xs: Seq<Expr>, ys: Seq<Expr>, n: nat)
    requires
        all_pure(xs, n),
        all_pure(ys, n),
    ensures
        pure_below(eq_all_s(xs, ys), n),
{
    let items = eq_items(xs, ys);
    assert forall|j: int| 0 <= j < items.len() implies pure_below(#[trigger] items[j], n) by {
        assert(pure_below(xs[j], n));
        assert(pure_below(ys[j], n));
    }
    assert(pure_below(bool_lit(true), n));
    lemma_tree_pure(items, bool_lit(true), Join::And, n);
}

/// スロットの値がスロットの型の値なら、既定値の符号化との等しさの式の値は、等しいことである。
pub proof fn lemma_eq_default(xs: Seq<Expr>, t: STy, env: Env, ls: Seq<Value>, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        small(t),
        clean(xs, env, ls),
        in_slots(slot_vals(xs, env, ls), slot_tys(t, enums), enums),
    ensures
        eval_l(eq_all_s(xs, lits(enc(default_val(t, enums), t, enums))), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(slot_vals(xs, env, ls) == enc(default_val(t, enums), t, enums)),
        ),
{
    let d = enc(default_val(t, enums), t, enums);
    let xv = slot_vals(xs, env, ls);
    let tys = slot_tys(t, enums);
    lemma_default_member(t, enums);
    lemma_member_in(default_val(t, enums), t, enums);
    let ys = lits(d);
    let items = eq_items(xs, ys);
    assert(items.len() == xs.len());
    assert forall|j: int| 0 <= j < items.len() implies #[trigger] eval_l(items[j], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(xv[j] == d[j]),
    ) by {
        assert(pure_below(xs[j], ls.len()) && eval_l(xs[j], env, ls) is Ok);
        assert(eval_l(xs[j], env, ls) == Ok::<Value, ErrKind>(xv[j]));
        assert(ys[j] == Expr::Const(d[j]));
        assert(items[j] == Expr::Bin(BinOp::Eq, Box::new(xs[j]), Box::new(ys[j])));
        assert(eval_l(ys[j], env, ls) == Ok::<Value, ErrKind>(d[j]));
        assert(in_slot(tys[j], xv[j], enums));
        assert(in_slot(tys[j], d[j], enums));
        lemma_in_slot_kind(tys[j], xv[j], d[j], enums);
        assert(crate::eval::binop_spec(BinOp::Eq, xv[j], d[j]) == Ok::<Value, ErrKind>(Value::Bool(xv[j] == d[j])));
    }
    assert forall|j: int| 0 <= j < items.len() implies bool_val(#[trigger] eval_l(items[j], env, ls)) by {}
    lemma_all_of(items, env, ls);
    if all_true(items, env, ls) {
        assert forall|j: int| 0 <= j < xv.len() implies xv[j] == d[j] by {
            assert(eval_l(items[j], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
        }
        assert(xv =~= d);
    }
    if xv == d {
        assert forall|j: int| 0 <= j < items.len() implies #[trigger] eval_l(items[j], env, ls) == Ok::<
            Value,
            ErrKind,
        >(Value::Bool(true)) by {}
    }
}

// ---- 正規形の判定 ----

/// 同じ型のスロットの列の比較は Bool の型を持つ。
pub proof fn lemma_eq_all_typed(xs: Seq<Expr>, ys: Seq<Expr>, es: Seq<ETy>, tv: TyEnv, lt: Seq<ETy>)
    requires
        typed(xs, es, tv, lt),
        typed(ys, es, tv, lt),
    ensures
        has_ty(eq_all_s(xs, ys), tv, lt, ETy::Bool),
{
    let items = eq_items(xs, ys);
    assert forall|i: int| 0 <= i < items.len() implies #[trigger] has_ty(items[i], tv, lt, ETy::Bool) by {
        assert(has_ty(xs[i], tv, lt, es[i]) && has_ty(ys[i], tv, lt, es[i]));
    }
    lemma_tree_typed(items, bool_lit(true), Join::And, tv, lt, ETy::Bool);
}

/// 型の既定値のリテラルの比較は Bool の型を持つ。
pub proof fn lemma_eq_default_typed(xs: Seq<Expr>, x: STy, tv: TyEnv, lt: Seq<ETy>)
    requires
        wf_stype(x, tv.enums),
        small(x),
        typed(xs, etys(slot_tys(x, tv.enums)), tv, lt),
    ensures
        has_ty(eq_all_s(xs, lits(enc(default_val(x, tv.enums), x, tv.enums))), tv, lt, ETy::Bool),
{
    lemma_defaults_typed(x, tv, lt);
    lemma_eq_all_typed(xs, lits(enc(default_val(x, tv.enums), x, tv.enums)), etys(slot_tys(x, tv.enums)), tv, lt);
}

/// [`canonical`] の結果 `c` の性質。`c` は純粋で、スロットの値がスロットの型の値なら、
/// `c` の値は、スロットの値が型 `t` の正規形の符号化であることである。
pub open spec fn canon_spec(t: STy, slots: Seq<Expr>, enums: Seq<i64>, c: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(c, n)
    &&& forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(t, enums) && small(t) && #[trigger] typed(slots, etys(slot_tys(t, enums)), tv, lt)
            ==> has_ty(c, tv, lt, ETy::Bool)
    &&& forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) ==> eval_l(
            c,
            env,
            ls,
        ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums)))
}

/// 整形式の型 `t` で、Listの長さの上限が小さければ、`c` は [`canon_spec`] を満たす。
pub open spec fn canon_wf(t: STy, slots: Seq<Expr>, enums: Seq<i64>, c: Expr) -> bool {
    wf_stype(t, enums) && small(t) ==> canon_spec(t, slots, enums, c)
}

/// Bool、Int、Enum、Setは、スロットの型の値ならどれも正規形である。
proof fn lemma_canon_scalar(t: STy, slots: Seq<Expr>, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        t is Bool || t is Int || t is Enum || t is Set,
    ensures
        canon_spec(t, slots, enums, bool_lit(true)),
{
    assert forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) implies eval_l(
        bool_lit(true),
        env,
        ls,
    ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums))) by {
        let xs = slot_vals(slots, env, ls);
        let tys = slot_tys(t, enums);
        match t {
            STy::Bool => {
                assert(in_slot(tys[0], xs[0], enums));
                let v = SVal::Bool(xs[0]->Bool_0);
                assert(enc(v, t, enums) =~= xs);
                assert(member(v, t, enums));
            },
            STy::Int(_, _) => {
                assert(in_slot(tys[0], xs[0], enums));
                let v = SVal::Int(xs[0]->Int_0);
                assert(enc(v, t, enums) =~= xs);
                assert(member(v, t, enums));
            },
            STy::Enum(id) => {
                assert(in_slot(tys[0], xs[0], enums));
                let v = SVal::Enum(id, xs[0]->Enum_1);
                assert(enc(v, t, enums) =~= xs);
                assert(member(v, t, enums));
            },
            STy::Set(e) => {
                let n = keys_or_zero(*e, enums);
                lemma_bools(n);
                let bits = Seq::new(n, |i: int| xs[i]->Bool_0);
                assert forall|i: int| 0 <= i < n implies xs[i] == Value::Bool(bits[i]) by {
                    assert(in_slot(tys[i], xs[i], enums));
                }
                let v = SVal::Set(bits);
                assert(enc(v, t, enums) =~= xs);
                assert(member(v, t, enums));
            },
            _ => {},
        }
    }
}

/// Recordの正規形は、要素の型の組の正規形と同じである。
proof fn lemma_canon_record(names: Seq<usize>, ts: Seq<STy>, slots: Seq<Expr>, enums: Seq<i64>, c: Expr)
    requires
        canon_spec(STy::Tuple(ts), slots, enums, c),
    ensures
        canon_spec(STy::Record(names, ts), slots, enums, c),
{
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(STy::Record(names, ts), enums) && small(STy::Record(names, ts)) && #[trigger] typed(
            slots,
            etys(slot_tys(STy::Record(names, ts), enums)),
            tv,
            lt,
        ) implies has_ty(c, tv, lt, ETy::Bool) by {
        assert(slot_tys(STy::Record(names, ts), enums) == slot_tys(STy::Tuple(ts), enums));
        assert(wf_stype(STy::Tuple(ts), enums) && small(STy::Tuple(ts)));
        assert(typed(slots, etys(slot_tys(STy::Tuple(ts), enums)), tv, lt));
    }
    let r = STy::Record(names, ts);
    let u = STy::Tuple(ts);
    assert forall|xs: Seq<Value>| canon_ok(xs, r, enums) == canon_ok(xs, u, enums) by {
        if canon_ok(xs, r, enums) {
            let v = choose|v: SVal| member(v, r, enums) && #[trigger] enc(v, r, enums) == xs;
            assert(member(v, u, enums) && enc(v, u, enums) == xs);
        }
        if canon_ok(xs, u, enums) {
            let v = choose|v: SVal| member(v, u, enums) && #[trigger] enc(v, u, enums) == xs;
            assert(member(v, r, enums) && enc(v, r, enums) == xs);
        }
    }
    assert(slot_tys(r, enums) == slot_tys(u, enums));
}

/// Optionの値の列が正規形であることは、有無に応じて、中身が正規形か既定値であることである。
proof fn lemma_canon_option_vals(xs: Seq<Value>, x: STy, enums: Seq<i64>)
    requires
        xs.len() >= 1,
        xs[0] is Bool,
    ensures
        canon_ok(xs, STy::Option(Box::new(x)), enums) == if xs[0]->Bool_0 {
            canon_ok(xs.drop_first(), x, enums)
        } else {
            xs.drop_first() == enc(default_val(x, enums), x, enums)
        },
{
    let t = STy::Option(Box::new(x));
    let pv = xs.drop_first();
    let b = xs[0]->Bool_0;
    assert(xs =~= seq![Value::Bool(b)] + pv);
    if canon_ok(xs, t, enums) {
        let v = choose|v: SVal| member(v, t, enums) && #[trigger] enc(v, t, enums) == xs;
        match v {
            SVal::Some(w) => {
                assert(enc(v, t, enums) == seq![Value::Bool(true)] + enc(*w, x, enums));
                assert(enc(*w, x, enums) =~= pv);
                assert(member(*w, x, enums));
            },
            _ => {
                assert(enc(v, t, enums) == seq![Value::Bool(false)] + enc(default_val(x, enums), x, enums));
                assert(enc(default_val(x, enums), x, enums) =~= pv);
            },
        }
    }
    if b && canon_ok(pv, x, enums) {
        let w = choose|w: SVal| member(w, x, enums) && #[trigger] enc(w, x, enums) == pv;
        let v = SVal::Some(Box::new(w));
        assert(enc(v, t, enums) =~= xs);
        assert(member(v, t, enums));
    }
    if !b && pv == enc(default_val(x, enums), x, enums) {
        let v = SVal::None;
        assert(enc(v, t, enums) =~= xs);
        assert(member(v, t, enums));
    }
}

proof fn lemma_canon_option(x: STy, slots: Seq<Expr>, enums: Seq<i64>, inner: Expr, empty: Expr, r: Expr)
    requires
        wf_stype(x, enums),
        small(x),
        slots.len() > 0,
        canon_spec(x, slots.subrange(1, slots.len() as int), enums, inner),
        empty == eq_all_s(slots.subrange(1, slots.len() as int), lits(enc(default_val(x, enums), x, enums))),
        (r == bool_lit(true) && inner == bool_lit(true) && empty == bool_lit(true)) || r == ite_s(slots[0], inner, empty),
    ensures
        canon_spec(STy::Option(Box::new(x)), slots, enums, r),
{
    let t = STy::Option(Box::new(x));
    let payload = slots.subrange(1, slots.len() as int);
    let d = enc(default_val(x, enums), x, enums);
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(t, enums) && small(t) && #[trigger] typed(slots, etys(slot_tys(t, enums)), tv, lt)
            implies has_ty(r, tv, lt, ETy::Bool) by {
        let ys = etys(slot_tys(x, enums));
        lemma_etys_concat(seq![Type::Bool], slot_tys(x, enums));
        assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
        assert(etys(slot_tys(t, enums)) == seq![ETy::Bool] + ys);
        assert((seq![ETy::Bool] + ys)[0] == ETy::Bool);
        assert(has_ty(slots[0], tv, lt, (seq![ETy::Bool] + ys)[0]));
        lemma_typed_sub(slots, seq![ETy::Bool] + ys, tv, lt, 1, slots.len() as int);
        assert((seq![ETy::Bool] + ys).subrange(1, slots.len() as int) =~= ys);
        assert(typed(payload, ys, tv, lt));
        assert(has_ty(inner, tv, lt, ETy::Bool));
        lemma_eq_default_typed(payload, x, tv, lt);
    }
    assert forall|n: nat| #[trigger] all_pure(slots, n) implies pure_below(r, n) by {
        lemma_sub_pure(slots, 1, slots.len() as int, n);
        lemma_lits_pure(d, n);
        lemma_eq_all_pure(payload, lits(d), n);
        assert(pure_below(slots[0], n));
    }
    assert forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) implies eval_l(
        r,
        env,
        ls,
    ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums))) by {
        let xs = slot_vals(slots, env, ls);
        lemma_clean_sub(slots, env, ls, 1, slots.len() as int);
        let pv = slot_vals(payload, env, ls);
        assert(pv =~= xs.drop_first());
        lemma_slot_tys_len(x, enums);
        assert(xs =~= seq![xs[0]] + pv);
        assert(slot_tys(t, enums) == seq![Type::Bool] + slot_tys(x, enums));
        assert(in_slot(slot_tys(t, enums)[0], xs[0], enums));
        lemma_in_slots_concat(seq![xs[0]], seq![Type::Bool], pv, slot_tys(x, enums), enums);
        assert(in_slot(Type::Bool, seq![xs[0]][0], enums));
        assert(in_slots(pv, slot_tys(x, enums), enums));
        lemma_eq_default(payload, x, env, ls, enums);
        lemma_canon_option_vals(xs, x, enums);
        assert(eval_l(inner, env, ls) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(pv, x, enums))));
        assert(eval_l(slots[0], env, ls) == Ok::<Value, ErrKind>(xs[0]));
    }
}

/// Mapの行が正規形である。キーがあれば値が正規形で、なければ値が既定値である。
pub open spec fn map_row_ok(row: Seq<Value>, x: STy, enums: Seq<i64>) -> bool {
    if row[0] == Value::Bool(true) {
        canon_ok(row.subrange(1, row.len() as int), x, enums)
    } else {
        row.subrange(1, row.len() as int) == enc(default_val(x, enums), x, enums)
    }
}

/// Mapの行の判定の項。
pub open spec fn map_item_ok(item: Expr, c: Expr, row: Seq<Expr>, x: STy, enums: Seq<i64>) -> bool {
    &&& row.len() >= 1
    &&& item == ite_s(
        row[0],
        c,
        eq_all_s(row.subrange(1, row.len() as int), lits(enc(default_val(x, enums), x, enums))),
    )
    &&& canon_wf(x, row.subrange(1, row.len() as int), enums, c)
}

proof fn lemma_canon_map(
    slots: Seq<Expr>,
    rows: Seq<Seq<Expr>>,
    items: Seq<Expr>,
    cs: Seq<Expr>,
    k: STy,
    x: STy,
    enums: Seq<i64>,
)
    requires
        wf_stype(STy::Map(Box::new(k), Box::new(x)), enums),
        small(x),
        mparts_ok(slots, rows, (1 + width(x, enums)) as nat, keys_or_zero(k, enums)),
        items.len() == rows.len(),
        cs.len() == rows.len(),
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] map_item_ok(items[p], cs[p], rows[p], x, enums),
    ensures
        canon_spec(STy::Map(Box::new(k), Box::new(x)), slots, enums, tree_s(items, bool_lit(true), Join::And)),
{
    let t = STy::Map(Box::new(k), Box::new(x));
    let s = (1 + width(x, enums)) as nat;
    let d = enc(default_val(x, enums), x, enums);
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(t, enums) && small(t) && #[trigger] typed(slots, etys(slot_tys(t, enums)), tv, lt)
            implies has_ty(tree_s(items, bool_lit(true), Join::And), tv, lt, ETy::Bool) by {
        let rowt = seq![Type::Bool] + slot_tys(x, enums);
        let ys = etys(slot_tys(x, enums));
        lemma_slot_tys_len(x, enums);
        assert(rowt.len() == s);
        lemma_etys_concat(seq![Type::Bool], slot_tys(x, enums));
        assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
        assert forall|p: int| 0 <= p < items.len() implies #[trigger] has_ty(items[p], tv, lt, ETy::Bool) by {
            assert(map_item_ok(items[p], cs[p], rows[p], x, enums));
            assert(mrow_at(rows[p], slots, p, s));
            let n = keys_or_zero(k, enums);
            lemma_ty_repeat_sub(rowt, n, p);
            lemma_etys_sub(ty_repeat(rowt, n), p * s, p * s + s);
            lemma_typed_sub(slots, etys(slot_tys(t, enums)), tv, lt, p * s, p * s + s);
            let row = rows[p];
            assert(typed(row, seq![ETy::Bool] + ys, tv, lt));
            assert((seq![ETy::Bool] + ys)[0] == ETy::Bool);
            assert(has_ty(row[0], tv, lt, (seq![ETy::Bool] + ys)[0]));
            lemma_typed_sub(row, seq![ETy::Bool] + ys, tv, lt, 1, row.len() as int);
            assert((seq![ETy::Bool] + ys).subrange(1, row.len() as int) =~= ys);
            assert(canon_wf(x, row.subrange(1, row.len() as int), enums, cs[p]));
            assert(has_ty(cs[p], tv, lt, ETy::Bool));
            lemma_eq_default_typed(row.subrange(1, row.len() as int), x, tv, lt);
        }
        lemma_tree_typed(items, bool_lit(true), Join::And, tv, lt, ETy::Bool);
    }
    assert forall|n: nat| #[trigger] all_pure(slots, n) implies pure_below(tree_s(items, bool_lit(true), Join::And), n) by {
        assert forall|p: int| 0 <= p < items.len() implies pure_below(#[trigger] items[p], n) by {
            assert(map_item_ok(items[p], cs[p], rows[p], x, enums));
            assert(mrow_at(rows[p], slots, p, s));
            lemma_sub_pure(slots, p * s, p * s + s, n);
            let row = rows[p];
            lemma_sub_pure(row, 1, row.len() as int, n);
            lemma_lits_pure(d, n);
            lemma_eq_all_pure(row.subrange(1, row.len() as int), lits(d), n);
            assert(pure_below(row[0], n));
        }
        assert(pure_below(bool_lit(true), n));
        lemma_tree_pure(items, bool_lit(true), Join::And, n);
    }
    assert forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) implies eval_l(
        tree_s(items, bool_lit(true), Join::And),
        env,
        ls,
    ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums))) by {
        lemma_canon_map_eval(slots, rows, items, cs, k, x, enums, env, ls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_canon_map_eval(
    slots: Seq<Expr>,
    rows: Seq<Seq<Expr>>,
    items: Seq<Expr>,
    cs: Seq<Expr>,
    k: STy,
    x: STy,
    enums: Seq<i64>,
    env: Env,
    ls: Seq<Value>,
)
    requires
        wf_stype(STy::Map(Box::new(k), Box::new(x)), enums),
        small(x),
        mparts_ok(slots, rows, (1 + width(x, enums)) as nat, keys_or_zero(k, enums)),
        items.len() == rows.len(),
        cs.len() == rows.len(),
        forall|p: int| 0 <= p < rows.len() ==> #[trigger] map_item_ok(items[p], cs[p], rows[p], x, enums),
        clean(slots, env, ls),
        in_slots(slot_vals(slots, env, ls), slot_tys(STy::Map(Box::new(k), Box::new(x)), enums), enums),
    ensures
        eval_l(tree_s(items, bool_lit(true), Join::And), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(canon_ok(slot_vals(slots, env, ls), STy::Map(Box::new(k), Box::new(x)), enums)),
        ),
{
    let t = STy::Map(Box::new(k), Box::new(x));
    let s = (1 + width(x, enums)) as nat;
    let n = keys_or_zero(k, enums);
    let xs = slot_vals(slots, env, ls);
    let xt = slot_tys(x, enums);
    let rt = seq![Type::Bool] + xt;
    lemma_slot_tys_len(x, enums);
    assert(rt.len() == s);
    let rv = Seq::new(n, |p: int| slot_vals(rows[p], env, ls));
    assert forall|p: int| 0 <= p < n implies clean(#[trigger] rows[p], env, ls) && rv[p] == xs.subrange(p * s, p * s + s)
        && in_slots(rv[p], rt, enums) by {
        assert(mrow_at(rows[p], slots, p, s));
        lemma_clean_sub(slots, env, ls, p * s, p * s + s);
        lemma_ty_repeat_sub(rt, n, p);
        lemma_in_slots_sub(xs, slot_tys(t, enums), p * s, p * s + s, enums);
    }
    // 各行の項の値
    assert forall|p: int| 0 <= p < n implies #[trigger] eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(map_row_ok(rv[p], x, enums)),
    ) by {
        assert(map_item_ok(items[p], cs[p], rows[p], x, enums));
        let row = rows[p];
        let vals = row.subrange(1, row.len() as int);
        assert(clean(row, env, ls));
        lemma_clean_sub(row, env, ls, 1, row.len() as int);
        assert(rv[p] =~= seq![rv[p][0]] + rv[p].subrange(1, s as int));
        lemma_in_slots_concat(seq![rv[p][0]], seq![Type::Bool], rv[p].subrange(1, s as int), xt, enums);
        assert(rt =~= seq![Type::Bool] + xt);
        assert(in_slot(Type::Bool, seq![rv[p][0]][0], enums));
        assert(slot_vals(vals, env, ls) == rv[p].subrange(1, s as int));
        assert(in_slots(slot_vals(vals, env, ls), xt, enums));
        assert(eval_l(row[0], env, ls) == Ok::<Value, ErrKind>(rv[p][0]));
        lemma_eq_default(vals, x, env, ls, enums);
        assert(eval_l(cs[p], env, ls) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(vals, env, ls), x, enums))));
    }
    assert forall|p: int| 0 <= p < items.len() implies bool_val(#[trigger] eval_l(items[p], env, ls)) by {}
    lemma_all_of(items, env, ls);
    // 正規形であることと、各行が正規形であることは同じである。
    if all_true(items, env, ls) {
        let rs = Seq::new(
            n,
            |p: int|
                if rv[p][0] == Value::Bool(true) {
                    Some(choose|w: SVal| member(w, x, enums) && #[trigger] enc(w, x, enums) == rv[p].subrange(1, s as int))
                } else {
                    None
                },
        );
        assert forall|p: int| 0 <= p < n implies (#[trigger] rs[p] matches Some(w) ==> member(w, x, enums)) && row_slots(
            rs[p],
            x,
            enums,
        ) == rv[p] by {
            assert(eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(map_row_ok(rv[p], x, enums));
            assert(rv[p] =~= seq![rv[p][0]] + rv[p].subrange(1, s as int));
            assert(in_slot(rt[0], rv[p][0], enums));
            if rv[p][0] == Value::Bool(true) {
                assert(canon_ok(rv[p].subrange(1, s as int), x, enums));
            }
        }
        lemma_rows_member_all(rs, x, enums);
        assert(row_vals(rs, x, enums) =~= rv);
        assert(rows_at(rows, row_vals(rs, x, enums), env, ls));
        assert(keys(k, enums) == Some(n));
        lemma_map_join(rows, env, ls, rs, k, x, enums);
        assert forall|p: int| 0 <= p < rows.len() implies #[trigger] rows[p] == slots.subrange(p * s, p * s + s) by {
            assert(mrow_at(rows[p], slots, p, s));
        }
        lemma_flat_split(slots, rows, s);
        assert(member(SVal::Map(rs), t, enums) && enc(SVal::Map(rs), t, enums) == xs);
    }
    if canon_ok(xs, t, enums) {
        let v = choose|v: SVal| member(v, t, enums) && #[trigger] enc(v, t, enums) == xs;
        let rs = v->Map_0;
        assert(rs.len() == n);
        assert(denotes(slots, env, ls, v, XTy::Map(Box::new(k), Box::new(x)), enums));
        lemma_map_parts(slots, rows, env, ls, rs, k, x, enums);
        assert forall|p: int| 0 <= p < items.len() implies #[trigger] eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(true),
        ) by {
            assert(rv[p] == row_vals(rs, x, enums)[p]);
            crate::preserve::lemma_map_rows_member_index(rs, x, enums, p);
            match rs[p] {
                Some(w) => {
                    assert(rv[p].subrange(1, s as int) =~= enc(w, x, enums));
                },
                None => {
                    assert(rv[p].subrange(1, s as int) =~= enc(default_val(x, enums), x, enums));
                },
            }
        }
    }
}

/// Listの行が正規形である。長さより前なら要素が正規形で、後ろなら既定値である。
pub open spec fn list_row_ok(row: Seq<Value>, p: int, n: int, e: STy, enums: Seq<i64>) -> bool {
    if p < n {
        canon_ok(row, e, enums)
    } else {
        row == enc(default_val(e, enums), e, enums)
    }
}

/// Listの行の判定の項。
pub open spec fn list_item_ok(item: Expr, c: Expr, row: Seq<Expr>, len: Expr, p: int, e: STy, enums: Seq<i64>) -> bool {
    &&& item == ite_s(
        Expr::Bin(BinOp::Lt, Box::new(int_lit(p as i64)), Box::new(len)),
        c,
        eq_all_s(row, lits(enc(default_val(e, enums), e, enums))),
    )
    &&& canon_wf(e, row, enums, c)
}

proof fn lemma_canon_list(
    slots: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    items: Seq<Expr>,
    cs: Seq<Expr>,
    e: STy,
    max: usize,
    enums: Seq<i64>,
)
    requires
        wf_stype(e, enums),
        small(e),
        max <= 0x7fff_ffff,
        parts_ok(slots, len, rows, width(e, enums), max as nat),
        items.len() == max,
        cs.len() == max,
        forall|p: int| 0 <= p < max ==> #[trigger] list_item_ok(items[p], cs[p], rows[p], len, p, e, enums),
    ensures
        canon_spec(STy::List(Box::new(e), max), slots, enums, tree_s(items, bool_lit(true), Join::And)),
{
    let t = STy::List(Box::new(e), max);
    let w = width(e, enums);
    let d = enc(default_val(e, enums), e, enums);
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(t, enums) && small(t) && #[trigger] typed(slots, etys(slot_tys(t, enums)), tv, lt)
            implies has_ty(tree_s(items, bool_lit(true), Join::And), tv, lt, ETy::Bool) by {
        let et = slot_tys(e, enums);
        let ys = etys(et);
        lemma_slot_tys_len(e, enums);
        let all = etys(slot_tys(t, enums));
        lemma_etys_concat(seq![Type::Int(0, max as i64)], ty_repeat(et, max as nat));
        assert(etys(seq![Type::Int(0, max as i64)]) =~= seq![ETy::Int]);
        assert(all == seq![ETy::Int] + etys(ty_repeat(et, max as nat)));
        assert(has_ty(slots[0], tv, lt, all[0]));
        assert(has_ty(len, tv, lt, ETy::Int));
        assert forall|p: int| 0 <= p < items.len() implies #[trigger] has_ty(items[p], tv, lt, ETy::Bool) by {
            assert(list_item_ok(items[p], cs[p], rows[p], len, p, e, enums));
            assert(row_at(rows[p], slots, p, w));
            lemma_ty_repeat_sub(et, max as nat, p);
            lemma_etys_sub(ty_repeat(et, max as nat), p * w, p * w + w);
            lemma_typed_sub(slots, all, tv, lt, 1 + p * w, 1 + p * w + w);
            assert(all.subrange(1 + p * w, 1 + p * w + w) =~= etys(ty_repeat(et, max as nat)).subrange(p * w, p * w + w));
            assert(typed(rows[p], ys, tv, lt));
            assert(canon_wf(e, rows[p], enums, cs[p]));
            assert(has_ty(cs[p], tv, lt, ETy::Bool));
            lemma_eq_default_typed(rows[p], e, tv, lt);
            assert(has_ty(int_lit(p as i64), tv, lt, ETy::Int));
            assert(has_ty(Expr::Bin(BinOp::Lt, Box::new(int_lit(p as i64)), Box::new(len)), tv, lt, ETy::Bool));
        }
        lemma_tree_typed(items, bool_lit(true), Join::And, tv, lt, ETy::Bool);
    }
    assert forall|n: nat| #[trigger] all_pure(slots, n) implies pure_below(tree_s(items, bool_lit(true), Join::And), n) by {
        assert forall|p: int| 0 <= p < items.len() implies pure_below(#[trigger] items[p], n) by {
            assert(list_item_ok(items[p], cs[p], rows[p], len, p, e, enums));
            assert(row_at(rows[p], slots, p, w));
            assert(0 <= p * w) by (nonlinear_arith)
                requires
                    0 <= p,
            ;
            lemma_sub_pure(slots, 1 + p * w, 1 + p * w + w, n);
            assert(all_pure(rows[p], n));
            lemma_lits_pure(d, n);
            lemma_eq_all_pure(rows[p], lits(d), n);
            assert(pure_below(slots[0], n));
            assert(pure_below(len, n));
            assert(pure_below(int_lit(p as i64), n));
            assert(canon_spec(e, rows[p], enums, cs[p]));
            assert(pure_below(cs[p], n));
            assert(pure_below(eq_all_s(rows[p], lits(d)), n));
            assert(pure_below(Expr::Bin(BinOp::Lt, Box::new(int_lit(p as i64)), Box::new(len)), n));
        }
        assert(pure_below(bool_lit(true), n));
        lemma_tree_pure(items, bool_lit(true), Join::And, n);
    }
    assert forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) implies eval_l(
        tree_s(items, bool_lit(true), Join::And),
        env,
        ls,
    ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums))) by {
        lemma_canon_list_eval(slots, len, rows, items, cs, e, max, enums, env, ls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_canon_list_eval(
    slots: Seq<Expr>,
    len: Expr,
    rows: Seq<Seq<Expr>>,
    items: Seq<Expr>,
    cs: Seq<Expr>,
    e: STy,
    max: usize,
    enums: Seq<i64>,
    env: Env,
    ls: Seq<Value>,
)
    requires
        wf_stype(e, enums),
        small(e),
        max <= 0x7fff_ffff,
        parts_ok(slots, len, rows, width(e, enums), max as nat),
        items.len() == max,
        cs.len() == max,
        forall|p: int| 0 <= p < max ==> #[trigger] list_item_ok(items[p], cs[p], rows[p], len, p, e, enums),
        clean(slots, env, ls),
        in_slots(slot_vals(slots, env, ls), slot_tys(STy::List(Box::new(e), max), enums), enums),
    ensures
        eval_l(tree_s(items, bool_lit(true), Join::And), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(canon_ok(slot_vals(slots, env, ls), STy::List(Box::new(e), max), enums)),
        ),
{
    let t = STy::List(Box::new(e), max);
    let w = width(e, enums);
    let xs = slot_vals(slots, env, ls);
    let et = slot_tys(e, enums);
    let tys = slot_tys(t, enums);
    lemma_slot_tys_len(e, enums);
    lemma_slot_tys_len(t, enums);
    assert(in_slot(tys[0], xs[0], enums));
    let n = xs[0]->Int_0;
    assert(0 <= n <= max);
    assert(eval_l(len, env, ls) == Ok::<Value, ErrKind>(xs[0]));
    let rv = Seq::new(max as nat, |p: int| slot_vals(rows[p], env, ls));
    assert forall|p: int| 0 <= p < max implies clean(#[trigger] rows[p], env, ls) && rv[p] == xs.subrange(
        1 + p * w,
        1 + p * w + w,
    ) && in_slots(rv[p], et, enums) by {
        assert(row_at(rows[p], slots, p, w));
        assert(0 <= p * w) by (nonlinear_arith)
            requires
                0 <= p,
        ;
        lemma_clean_sub(slots, env, ls, 1 + p * w, 1 + p * w + w);
        lemma_ty_repeat_sub(et, max as nat, p);
        lemma_in_slots_sub(xs, tys, 1 + p * w, 1 + p * w + w, enums);
        assert(tys.subrange(1 + p * w, 1 + p * w + w) =~= ty_repeat(et, max as nat).subrange(p * w, p * w + w));
    }
    assert forall|p: int| 0 <= p < max implies #[trigger] eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(list_row_ok(rv[p], p, n as int, e, enums)),
    ) by {
        assert(list_item_ok(items[p], cs[p], rows[p], len, p, e, enums));
        assert(clean(rows[p], env, ls));
        assert(eval_l(int_lit(p as i64), env, ls) == Ok::<Value, ErrKind>(Value::Int(p as i64)));
        assert((p as i64) as int == p);
        let cond = Expr::Bin(BinOp::Lt, Box::new(int_lit(p as i64)), Box::new(len));
        assert(eval_l(cond, env, ls) == Ok::<Value, ErrKind>(Value::Bool(p < n)));
        assert(in_slots(slot_vals(rows[p], env, ls), et, enums));
        lemma_eq_default(rows[p], e, env, ls, enums);
        assert(canon_spec(e, rows[p], enums, cs[p]));
        assert(eval_l(cs[p], env, ls) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(rv[p], e, enums))));
    }
    assert forall|p: int| 0 <= p < items.len() implies bool_val(#[trigger] eval_l(items[p], env, ls)) by {}
    lemma_all_of(items, env, ls);
    if all_true(items, env, ls) {
        let its = Seq::new(
            n as nat,
            |p: int| choose|v: SVal| member(v, e, enums) && #[trigger] enc(v, e, enums) == rv[p],
        );
        assert forall|p: int| 0 <= p < n implies member(#[trigger] its[p], e, enums) && enc(its[p], e, enums) == rv[p] by {
            assert(eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(list_row_ok(rv[p], p, n as int, e, enums));
        }
        lemma_items_member_all(its, e, enums);
        let pv = pad_vals(its, e, max as nat, enums);
        assert forall|p: int| 0 <= p < max implies clean(#[trigger] rows[p], env, ls) && slot_vals(rows[p], env, ls)
            == pv[p] by {
            assert(eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
            assert(list_row_ok(rv[p], p, n as int, e, enums));
            if p < n {
                assert(pad(its, e, max as nat, enums)[p] == its[p]);
            } else {
                assert(pad(its, e, max as nat, enums)[p] == default_val(e, enums));
            }
        }
        assert(rows_at(rows, pv, env, ls));
        lemma_list_join(len, rows, env, ls, its, e, max, enums);
        let body = slots.subrange(1, slots.len() as int);
        assert forall|p: int| 0 <= p < rows.len() implies #[trigger] rows[p] == body.subrange(p * w, p * w + w) by {
            assert(row_at(rows[p], slots, p, w));
            assert(body.subrange(p * w, p * w + w) =~= slots.subrange(1 + p * w, 1 + p * w + w));
        }
        lemma_flat_split(body, rows, w);
        assert(slots =~= seq![len] + body);
        let v = SVal::List(its);
        assert(member(v, t, enums) && enc(v, t, enums) == xs);
    }
    if canon_ok(xs, t, enums) {
        let v = choose|v: SVal| member(v, t, enums) && #[trigger] enc(v, t, enums) == xs;
        let its = v->List_0;
        assert(denotes(slots, env, ls, v, XTy::List(Box::new(e), max), enums));
        lemma_list_parts(slots, len, rows, env, ls, its, e, max, enums);
        assert(n == its.len());
        assert forall|p: int| 0 <= p < items.len() implies #[trigger] eval_l(items[p], env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(true),
        ) by {
            assert(rv[p] == pad_vals(its, e, max as nat, enums)[p]);
            if p < n {
                lemma_items_member(its, e, enums, p);
                assert(pad(its, e, max as nat, enums)[p] == its[p]);
            } else {
                assert(pad(its, e, max as nat, enums)[p] == default_val(e, enums));
            }
        }
    }
}

proof fn lemma_canon_tuple(
    slots: Seq<Expr>,
    parts: Seq<Seq<Expr>>,
    cs: Seq<Expr>,
    ts: Seq<STy>,
    enums: Seq<i64>,
)
    requires
        wf_stypes(ts, enums),
        smalls(ts),
        parts.len() == ts.len(),
        cs.len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] split_ok(parts[i], slots, to_xtys(ts), i, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] canon_wf(ts[i], parts[i], enums, cs[i]),
    ensures
        canon_spec(STy::Tuple(ts), slots, enums, tree_s(cs, bool_lit(true), Join::And)),
{
    let t = STy::Tuple(ts);
    let xts = to_xtys(ts);
    lemma_to_xtys(ts);
    assert forall|tv: TyEnv, lt: Seq<ETy>|
        tv.enums == enums && wf_stype(t, enums) && small(t) && #[trigger] typed(slots, etys(slot_tys(t, enums)), tv, lt)
            implies has_ty(tree_s(cs, bool_lit(true), Join::And), tv, lt, ETy::Bool) by {
        lemma_xetys_seq_of(ts, enums);
        assert forall|i: int| 0 <= i < cs.len() implies #[trigger] has_ty(cs[i], tv, lt, ETy::Bool) by {
            assert(split_ok(parts[i], slots, xts, i, enums));
            lemma_wf_index(ts, i, enums);
            lemma_smalls_at(ts, i);
            assert(canon_wf(ts[i], parts[i], enums, cs[i]));
            lemma_xetys_part(xts, i, enums);
            lemma_xetys_of(ts[i], enums);
            let lo = xoff(xts, i, enums);
            let hi = lo + xwidth(xts[i], enums);
            lemma_typed_sub(slots, etys(slot_tys(t, enums)), tv, lt, lo, hi);
            assert(typed(parts[i], etys(slot_tys(ts[i], enums)), tv, lt));
        }
        lemma_tree_typed(cs, bool_lit(true), Join::And, tv, lt, ETy::Bool);
    }
    assert forall|n: nat| #[trigger] all_pure(slots, n) implies pure_below(tree_s(cs, bool_lit(true), Join::And), n) by {
        assert forall|i: int| 0 <= i < cs.len() implies pure_below(#[trigger] cs[i], n) by {
            assert(split_ok(parts[i], slots, xts, i, enums));
            lemma_wf_index(ts, i, enums);
            assert(canon_wf(ts[i], parts[i], enums, cs[i]));
            let lo = xoff(xts, i, enums);
            let hi = lo + xwidth(xts[i], enums);
            lemma_sub_pure(slots, lo, hi, n);
        }
        assert(pure_below(bool_lit(true), n));
        lemma_tree_pure(cs, bool_lit(true), Join::And, n);
    }
    assert forall|env: Env, ls: Seq<Value>|
        clean(slots, env, ls) && #[trigger] in_slots(slot_vals(slots, env, ls), slot_tys(t, enums), enums) implies eval_l(
        tree_s(cs, bool_lit(true), Join::And),
        env,
        ls,
    ) == Ok::<Value, ErrKind>(Value::Bool(canon_ok(slot_vals(slots, env, ls), t, enums))) by {
        lemma_canon_tuple_eval(slots, parts, cs, ts, enums, env, ls);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_canon_tuple_eval(
    slots: Seq<Expr>,
    parts: Seq<Seq<Expr>>,
    cs: Seq<Expr>,
    ts: Seq<STy>,
    enums: Seq<i64>,
    env: Env,
    ls: Seq<Value>,
)
    requires
        wf_stypes(ts, enums),
        smalls(ts),
        parts.len() == ts.len(),
        cs.len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] split_ok(parts[i], slots, to_xtys(ts), i, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] canon_wf(ts[i], parts[i], enums, cs[i]),
        clean(slots, env, ls),
        in_slots(slot_vals(slots, env, ls), slot_tys(STy::Tuple(ts), enums), enums),
    ensures
        eval_l(tree_s(cs, bool_lit(true), Join::And), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(canon_ok(slot_vals(slots, env, ls), STy::Tuple(ts), enums)),
        ),
{
    let t = STy::Tuple(ts);
    let xts = to_xtys(ts);
    let xs = slot_vals(slots, env, ls);
    lemma_to_xtys(ts);
    lemma_slot_tys_seq_len(ts, enums);
    let pv = Seq::new(ts.len(), |i: int| slot_vals(parts[i], env, ls));
    assert forall|i: int| 0 <= i < ts.len() implies clean(#[trigger] parts[i], env, ls) && pv[i] == xs.subrange(
        width_sum(ts.take(i), enums) as int,
        (width_sum(ts.take(i), enums) + width(ts[i], enums)) as int,
    ) && in_slots(pv[i], slot_tys(ts[i], enums), enums) by {
        assert(split_ok(parts[i], slots, xts, i, enums));
        lemma_xoff_to(ts, i, enums);
        let lo = width_sum(ts.take(i), enums) as int;
        let hi = (width_sum(ts.take(i), enums) + width(ts[i], enums)) as int;
        lemma_clean_sub(slots, env, ls, lo, hi);
        lemma_slot_tys_seq_sub(ts, i, enums);
        lemma_in_slots_sub(xs, slot_tys(t, enums), lo, hi, enums);
    }
    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] eval_l(cs[i], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(canon_ok(pv[i], ts[i], enums)),
    ) by {
        lemma_wf_index(ts, i, enums);
        assert(canon_wf(ts[i], parts[i], enums, cs[i]));
        assert(clean(parts[i], env, ls));
        assert(in_slots(slot_vals(parts[i], env, ls), slot_tys(ts[i], enums), enums));
    }
    assert forall|i: int| 0 <= i < cs.len() implies bool_val(#[trigger] eval_l(cs[i], env, ls)) by {}
    lemma_all_of(cs, env, ls);
    if all_true(cs, env, ls) {
        let vs = Seq::new(
            ts.len(),
            |i: int| choose|v: SVal| member(v, ts[i], enums) && #[trigger] enc(v, ts[i], enums) == pv[i],
        );
        assert forall|i: int| 0 <= i < ts.len() implies #[trigger] member(vs[i], ts[i], enums) && enc(vs[i], ts[i], enums)
            == pv[i] by {
            assert(eval_l(cs[i], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
        }
        lemma_members(vs, ts, enums);
        assert forall|j: int| 0 <= j < parts.len() implies #[trigger] clean(parts[j], env, ls) && slot_vals(parts[j], env, ls)
            == enc(vs[j], ts[j], enums) by {
            assert(member(vs[j], ts[j], enums));
        }
        lemma_concat_enc(parts, vs, ts, env, ls, enums);
        lemma_xwidths_of(ts, enums);
        lemma_concat_split(slots, parts, xts, enums);
        let v = SVal::Tuple(vs);
        assert(member(v, t, enums) && enc(v, t, enums) == xs);
    }
    if canon_ok(xs, t, enums) {
        let v = choose|v: SVal| member(v, t, enums) && #[trigger] enc(v, t, enums) == xs;
        let vs = v->Tuple_0;
        lemma_members(vs, ts, enums);
        assert forall|i: int| 0 <= i < cs.len() implies #[trigger] eval_l(cs[i], env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(true),
        ) by {
            lemma_enc_seq_sub(vs, ts, i, enums);
            assert(member(vs[i], ts[i], enums));
            assert(enc(vs[i], ts[i], enums) == pv[i]);
        }
    }
}

/// 型 `st` の値として正規形である（Option が空なら中身が既定値、など）。
/// 引数は、スロットごとに値を列挙するので、正規形でない組を除く。
pub fn canonical(st: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(c) ==> canon_wf(sty(*st), slots@, enums@, c),
        slots@.len() == width(sty(*st), enums@) && lim_s(sty(*st), enums@) ==> r is Some,
    decreases st, 1nat,
{
    match st {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) | SType::Set(_) => {
            proof {
                if wf_stype(sty(*st), enums@) {
                    lemma_canon_scalar(sty(*st), slots@, enums@);
                }
            }
            Some(cb(true))
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*st => *ts));
            }
            canonical_parts(st, ts, slots, enums)
        },
        SType::Record(_names, ts) => {
            proof {
                assert(decreases_to!(*st => *ts));
            }
            let r = canonical_parts(st, ts, slots, enums);
            proof {
                if r is Some && wf_stype(sty(*st), enums@) && small(sty(*st)) {
                    lemma_canon_record(_names@, stys(ts@), slots@, enums@, r->Some_0);
                }
            }
            r
        },
        SType::Option(t) => {
            proof {
                assert(decreases_to!(*st => **t));
            }
            canonical_option(st, t, slots, enums)
        },
        SType::Map(k, v) => {
            proof {
                assert(decreases_to!(*st => **v));
            }
            canonical_map(st, k, v, slots, enums)
        },
        SType::List(t, max) => {
            proof {
                assert(decreases_to!(*st => **t));
            }
            canonical_list(st, t, *max, slots, enums)
        },
    }
}

fn canonical_option(_parent: &SType, t: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    requires
        decreases_to!(*_parent => *t),
    ensures
        r matches Some(c) ==> canon_wf(STy::Option(Box::new(sty(*t))), slots@, enums@, c),
        slots@.len() == 1 + width(sty(*t), enums@) && lim_s(sty(*t), enums@) ==> r is Some,
    decreases _parent, 0nat,
{
    if slots.len() == 0 {
        return None;
    }
    let payload = sub_exprs(slots, 1, slots.len());
    let inner = canonical(t, &payload, enums)?;
    let empty = eq_all(&payload, &defaults(t, enums));
    let ghost gi = inner;
    let ghost ge = empty;
    let r = if is_bool_lit(&inner, true) && is_bool_lit(&empty, true) {
        cb(true)
    } else {
        ite(copy_expr(&slots[0]), inner, empty)
    };
    proof {
        if wf_stype(sty(*t), enums@) && small(sty(*t)) {
            lemma_canon_option(sty(*t), slots@, enums@, gi, ge, r);
        }
    }
    Some(r)
}

fn canonical_map(_parent: &SType, k: &SType, v: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    requires
        decreases_to!(*_parent => *v),
    ensures
        r matches Some(c) ==> canon_wf(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), slots@, enums@, c),
        lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
            STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
            enums@,
        ) ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
        STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
        enums@,
    );
    let rows = map_rows(k, v, slots, enums)?;
    let defs = defaults(v, enums);
    proof {
        if pre {
            assert(lim_s(sty(*v), enums@));
            assert forall|p: int| 0 <= p < rows@.len() implies (#[trigger] rows@[p])@.len() == 1 + width(sty(*v), enums@) by {
                assert(rows_view(rows@)[p] == rows@[p]@);
                assert(mrow_at(rows_view(rows@)[p], slots@, p, (1 + width(sty(*v), enums@)) as nat));
            }
        }
    }
    let mut items: Vec<Expr> = Vec::new();
    let ghost mut cs: Seq<Expr> = Seq::empty();
    let mut i = 0;
    while i < rows.len()
        invariant
            decreases_to!(*_parent => *v),
            defs@ == lits(enc(default_val(sty(*v), enums@), sty(*v), enums@)),
            i <= rows@.len(),
            items@.len() == i,
            cs.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] map_item_ok(items@[p], cs[p], rows@[p]@, sty(*v), enums@),
            pre == (lim_s(STy::Map(Box::new(sty(*k)), Box::new(sty(*v))), enums@) && slots@.len() == width(
                STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
                enums@,
            )),
            pre ==> lim_s(sty(*v), enums@) && forall|p: int| 0 <= p < rows@.len() ==> (#[trigger] rows@[p])@.len() == 1
                + width(sty(*v), enums@),
        decreases rows.len() - i,
    {
        let row = &rows[i];
        if row.len() == 0 {
            return None;
        }
        let vals = sub_exprs(row, 1, row.len());
        let c = canonical(v, &vals, enums)?;
        let empty = eq_all(&vals, &defs);
        proof {
            cs = cs.push(c);
        }
        items.push(ite(copy_expr(&row[0]), c, empty));
        proof {
            assert(map_item_ok(items@[i as int], cs[i as int], rows@[i as int]@, sty(*v), enums@));
        }
        i += 1;
    }
    let r = all_of(&items);
    proof {
        let t = STy::Map(Box::new(sty(*k)), Box::new(sty(*v)));
        if wf_stype(t, enums@) && small(t) {
            assert(rows_view(rows@).len() == rows@.len());
            assert forall|p: int| 0 <= p < rows@.len() implies #[trigger] map_item_ok(
                items@[p],
                cs[p],
                rows_view(rows@)[p],
                sty(*v),
                enums@,
            ) by {
                assert(rows_view(rows@)[p] == rows@[p]@);
            }
            lemma_canon_map(slots@, rows_view(rows@), items@, cs, sty(*k), sty(*v), enums@);
        }
    }
    Some(r)
}

fn canonical_list(_parent: &SType, t: &SType, max: usize, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    requires
        decreases_to!(*_parent => *t),
    ensures
        r matches Some(c) ==> canon_wf(STy::List(Box::new(sty(*t)), max), slots@, enums@, c),
        lim_s(STy::List(Box::new(sty(*t)), max), enums@) && slots@.len() == width(STy::List(Box::new(sty(*t)), max), enums@)
            ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = lim_s(STy::List(Box::new(sty(*t)), max), enums@) && slots@.len() == width(
        STy::List(Box::new(sty(*t)), max),
        enums@,
    );
    if max > 0x7fff_ffffusize {
        return None;
    }
    let (len, rows) = list_parts(t, max, slots, enums)?;
    proof {
        assert(rows_view(rows@).len() == rows@.len());
        if pre {
            assert(lim_s(sty(*t), enums@));
            assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == width(sty(*t), enums@) by {
                assert(rows_view(rows@)[q] == rows@[q]@);
                assert(row_at(rows_view(rows@)[q], slots@, q, width(sty(*t), enums@)));
            }
        }
    }
    let defs = defaults(t, enums);
    let mut items: Vec<Expr> = Vec::new();
    let ghost mut cs: Seq<Expr> = Seq::empty();
    let mut p = 0;
    while p < rows.len()
        invariant
            decreases_to!(*_parent => *t),
            defs@ == lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)),
            rows@.len() == max,
            max <= 0x7fff_ffffusize,
            p <= rows@.len(),
            items@.len() == p,
            cs.len() == p,
            forall|q: int| 0 <= q < p ==> #[trigger] list_item_ok(items@[q], cs[q], rows@[q]@, len, q, sty(*t), enums@),
            pre == (lim_s(STy::List(Box::new(sty(*t)), max), enums@) && slots@.len() == width(
                STy::List(Box::new(sty(*t)), max),
                enums@,
            )),
            pre ==> lim_s(sty(*t), enums@) && forall|q: int| 0 <= q < rows@.len() ==> (#[trigger] rows@[q])@.len() == width(
                sty(*t),
                enums@,
            ),
        decreases rows.len() - p,
    {
        let c = canonical(t, &rows[p], enums)?;
        let empty = eq_all(&rows[p], &defs);
        proof {
            cs = cs.push(c);
        }
        items.push(ite(bin(BinOp::Lt, ci(p as i64), copy_expr(&len)), c, empty));
        proof {
            assert(list_item_ok(items@[p as int], cs[p as int], rows@[p as int]@, len, p as int, sty(*t), enums@));
        }
        p += 1;
    }
    let r = all_of(&items);
    proof {
        let u = STy::List(Box::new(sty(*t)), max);
        if wf_stype(u, enums@) && small(u) {
            assert forall|q: int| 0 <= q < max implies #[trigger] list_item_ok(
                items@[q],
                cs[q],
                rows_view(rows@)[q],
                len,
                q,
                sty(*t),
                enums@,
            ) by {
                assert(rows_view(rows@)[q] == rows@[q]@);
            }
            lemma_canon_list(slots@, len, rows_view(rows@), items@, cs, sty(*t), max, enums@);
        }
    }
    Some(r)
}

fn canonical_parts(_parent: &SType, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r matches Some(c) ==> (wf_stypes(stys(ts@), enums@) && smalls(stys(ts@)) ==> canon_spec(
            STy::Tuple(stys(ts@)),
            slots@,
            enums@,
            c,
        )),
        lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim() && slots@.len() == width_sum(stys(ts@), enums@)
            ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim() && slots@.len() == width_sum(
        stys(ts@),
        enums@,
    );
    let mut xs: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            i <= ts@.len(),
            xs@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] xty(xs@[j]) == to_xty(sty(ts@[j])),
        decreases ts.len() - i,
    {
        xs.push(to_xtype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_to_xtys(stys(ts@));
        assert(xtys(xs@) =~= to_xtys(stys(ts@))) by {
            assert forall|j: int| 0 <= j < xs@.len() implies #[trigger] xtys(xs@)[j] == to_xtys(stys(ts@))[j] by {
                assert(xty(xs@[j]) == to_xty(sty(ts@[j])));
            }
        }
        if pre {
            lemma_lim_to_xs(stys(ts@), enums@);
        }
    }
    let parts = split(&xs, slots, enums)?;
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_to_xtys(stys(ts@));
        assert(xtys(xs@) =~= to_xtys(stys(ts@)));
    }
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            parts@.len() == ts@.len(),
            i <= ts@.len(),
            items@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] canon_wf(sty(ts@[j]), parts@[j]@, enums@, items@[j]),
            pre == (lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim() && slots@.len() == width_sum(
                stys(ts@),
                enums@,
            )),
            xtys(xs@) == to_xtys(stys(ts@)),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] split_ok(parts@[j]@, slots@, xtys(xs@), j, enums@),
        decreases ts.len() - i,
    {
        proof {
            lemma_stys(ts@);
            lemma_to_xtys(stys(ts@));
            if pre {
                assert(split_ok(parts@[i as int]@, slots@, xtys(xs@), i as int, enums@));
                lemma_lim_ss_at(stys(ts@), enums@, i as int);
                lemma_xwidth_of(sty(ts@[i as int]), enums@);
                assert(xtys(xs@)[i as int] == to_xty(sty(ts@[i as int])));
            }
        }
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        items.push(canonical(&ts[i], &parts[i], enums)?);
        i += 1;
    }
    let r = all_of(&items);
    proof {
        let ss = stys(ts@);
        if wf_stypes(ss, enums@) && smalls(ss) {
            let pv = rows_view(parts@);
            assert forall|j: int| 0 <= j < ss.len() implies #[trigger] split_ok(pv[j], slots@, to_xtys(ss), j, enums@) by {
                assert(pv[j] == parts@[j]@);
            }
            assert forall|j: int| 0 <= j < ss.len() implies #[trigger] canon_wf(ss[j], pv[j], enums@, items@[j]) by {
                assert(pv[j] == parts@[j]@);
            }
            lemma_canon_tuple(slots@, pv, items@, ss, enums@);
        }
    }
    Some(r)
}

// ---- スロットの型の実装 ----

/// `xs` を `n` 回、`out` の後ろに加える。
fn push_repeat(xs: &Vec<Type>, n: usize, out: &mut Vec<Type>)
    ensures
        final(out)@ == old(out)@ + ty_repeat(xs@, n as nat),
{
    let ghost prefix = out@;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            out@ == prefix + ty_repeat(xs@, k as nat),
        decreases n - k,
    {
        let ghost before = out@;
        let mut j: usize = 0;
        while j < xs.len()
            invariant
                j <= xs@.len(),
                out@ == before + xs@.take(j as int),
            decreases xs@.len() - j,
        {
            out.push(xs[j]);
            j += 1;
            proof {
                assert(out@ =~= before + xs@.take(j as int));
            }
        }
        proof {
            assert(xs@.take(j as int) =~= xs@);
            assert(ty_repeat(xs@, (k + 1) as nat) == ty_repeat(xs@, k as nat) + xs@);
            assert(out@ =~= prefix + ty_repeat(xs@, (k + 1) as nat));
        }
        k += 1;
    }
}

/// 型 `t` の各スロットの中核の型を、`out` の後ろに加える。
pub fn slot_types(t: &SType, enums: &Vec<i64>, out: &mut Vec<Type>)
    ensures
        final(out)@ == old(out)@ + slot_tys(sty(*t), enums@),
    decreases t, 1nat,
{
    let ghost prefix = out@;
    match t {
        SType::Bool => {
            out.push(Type::Bool);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Int(lo, hi) => {
            out.push(Type::Int(*lo, *hi));
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Enum(id) => {
            out.push(Type::Enum(*id));
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_seq(t, ts, enums, out);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_seq(t, ts, enums, out);
        },
        SType::Option(x) => {
            out.push(Type::Bool);
            slot_types(x, enums, out);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut row: Vec<Type> = Vec::new();
            row.push(Type::Bool);
            proof {
                assert(row@ =~= seq![Type::Bool]);
            }
            push_repeat(&row, n, out);
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let mut row: Vec<Type> = Vec::new();
            row.push(Type::Bool);
            slot_types(v, enums, &mut row);
            proof {
                assert(row@ =~= seq![Type::Bool] + slot_tys(sty(**v), enums@));
            }
            push_repeat(&row, n, out);
        },
        SType::List(e, max) => {
            out.push(Type::Int(0, *max as i64));
            let mut row: Vec<Type> = Vec::new();
            slot_types(e, enums, &mut row);
            proof {
                assert(row@ =~= slot_tys(sty(**e), enums@));
            }
            push_repeat(&row, *max, out);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
    }
}

fn slot_types_seq(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, out: &mut Vec<Type>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        final(out)@ == old(out)@ + slot_tys_seq(stys(ts@), enums@),
    decreases _parent, 0nat,
{
    let ghost prefix = out@;
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= prefix + slot_tys_seq(stys(ts@).take(0), enums@));
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            out@ == prefix + slot_tys_seq(stys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        slot_types(&ts[i], enums, out);
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
            assert(out@ =~= prefix + slot_tys_seq(xs.take(i + 1), enums@));
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
}

/// 型の列の各型のスロットの型を、順につなげた列。
pub fn slot_types_list(ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Vec<Type>)
    ensures
        r@ == slot_tys_seq(stys(ts@), enums@),
{
    let mut out: Vec<Type> = Vec::new();
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= slot_tys_seq(stys(ts@).take(0), enums@));
    }
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            out@ == slot_tys_seq(stys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        slot_types(&ts[i], enums, &mut out);
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    out
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
    crate::canon::lemma_default_member(st, t.enums);
    crate::canon::lemma_member_in(crate::encoding::default_val(st, t.enums), st, t.enums);
    lemma_lits_typed(crate::encoding::enc(crate::encoding::default_val(st, t.enums), st, t.enums), slot_tys(st, t.enums), t, lt);
}

} // verus!
