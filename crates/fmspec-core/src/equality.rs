//! 等しさの下ろしの補題。
//!
//! Set、Map、Listは正規形で符号化するので、型に属する2つの値が等しいことは、
//! 符号化したスロットの値の列が等しいことと同じである（[`lemma_enc_inj`]）。
//! ただし、Listの長さは整数のスロットに入るので、長さの上限が整数に収まる型に限る（[`small`]）。
//! また、同じ型の値の符号化は、位置ごとに同じ種類の値になる（[`lemma_kinds`]）。
//! そのため、スロットを位置ごとに比べる式は、型の不一致で失敗しない。

use crate::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq, keys_or_zero};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_default_len, lemma_default_vals_len, lemma_enc_items_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_rows_len, lemma_enc_seq_len, lemma_stys, list_items_member, map_rows_member};
#[cfg(verus_keep_ghost)]
use crate::encoding::{member, members, models, models_seq, sty, stys, width, width_sum, xtys, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, eval_l, same_kind, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::slots::{and_s, bool_lit, implies_s, split_ok, tree_s, Join};
use vstd::prelude::*;

verus! {

// ---- Listの長さの上限 ----

/// 型の中のどのListも、長さの上限が `0x7fff_ffff` 以下である。
pub open spec fn small(t: STy) -> bool
    decreases t,
{
    match t {
        STy::Tuple(ts) => smalls(ts),
        STy::Record(_, ts) => smalls(ts),
        STy::Option(x) => small(*x),
        STy::Map(_, x) => small(*x),
        STy::List(e, max) => max <= 0x7fff_ffff && small(*e),
        _ => true,
    }
}

pub open spec fn smalls(ts: Seq<STy>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        smalls(ts.drop_last()) && small(ts.last())
    }
}

proof fn lemma_smalls_at(ts: Seq<STy>, i: int)
    requires
        smalls(ts),
        0 <= i < ts.len(),
    ensures
        small(ts[i]),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        assert(ts.drop_last()[i] == ts[i]);
        lemma_smalls_at(ts.drop_last(), i);
    }
}

proof fn lemma_smalls(ts: Seq<STy>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> small(#[trigger] ts[i]),
    ensures
        smalls(ts),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_smalls(ts.drop_last());
    }
}

/// 型の中のどのListも、長さの上限が `0x7fff_ffff` 以下かを判定する。
pub fn small_stype(t: &SType) -> (r: bool)
    ensures
        r == small(sty(*t)),
    decreases t,
{
    match t {
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            small_stypes(t, ts)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            small_stypes(t, ts)
        },
        SType::Option(x) => small_stype(x),
        SType::Map(_, v) => small_stype(v),
        SType::List(e, max) => *max <= 0x7fff_ffffusize && small_stype(e),
        _ => true,
    }
}

fn small_stypes(_parent: &SType, ts: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == smalls(stys(ts@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_stys(ts@);
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            forall|j: int| 0 <= j < i ==> small(sty(#[trigger] ts@[j])),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !small_stype(&ts[i]) {
            proof {
                lemma_stys(ts@);
                if smalls(stys(ts@)) {
                    lemma_smalls_at(stys(ts@), i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys(ts@);
        let ss = stys(ts@);
        assert forall|j: int| 0 <= j < ss.len() implies small(#[trigger] ss[j]) by {
            assert(ss[j] == sty(ts@[j]));
        }
        lemma_smalls(ss);
    }
    true
}

// ---- 列の分割 ----

/// 長さの等しい前半どうしをつないだ列が等しければ、前半も後半も等しい。
pub proof fn lemma_split_eq(a1: Seq<Value>, b1: Seq<Value>, a2: Seq<Value>, b2: Seq<Value>)
    requires
        a1.len() == a2.len(),
        a1 + b1 == a2 + b2,
    ensures
        a1 == a2,
        b1 == b2,
{
    assert(a1 =~= (a1 + b1).subrange(0, a1.len() as int));
    assert(a2 =~= (a2 + b2).subrange(0, a2.len() as int));
    assert(b1 =~= (a1 + b1).subrange(a1.len() as int, (a1 + b1).len() as int));
    assert(b2 =~= (a2 + b2).subrange(a2.len() as int, (a2 + b2).len() as int));
}

// ---- 符号化の単射性 ----

/// 型に属する2つの値の符号化が等しければ、値も等しい。
pub proof fn lemma_enc_inj(v1: SVal, v2: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v1, t, enums),
        member(v2, t, enums),
        small(t),
        enc(v1, t, enums) == enc(v2, t, enums),
    ensures
        v1 == v2,
    decreases t, 2nat,
{
    let s1 = enc(v1, t, enums);
    let s2 = enc(v2, t, enums);
    match t {
        STy::Bool | STy::Int(_, _) | STy::Enum(_) => {
            assert(s1[0] == s2[0]);
        },
        STy::Tuple(ts) => {
            lemma_inj_seq(v1->Tuple_0, v2->Tuple_0, ts, enums);
        },
        STy::Record(_, ts) => {
            lemma_inj_seq(v1->Tuple_0, v2->Tuple_0, ts, enums);
        },
        STy::Option(x) => {
            assert(s1[0] == s2[0]);
            if let SVal::Some(w1) = v1 {
                assert(s1[0] == Value::Bool(true));
                if !(v2 is Some) {
                    assert(s2[0] == Value::Bool(false));
                }
                let w2 = v2->Some_0;
                assert(s1.drop_first() =~= enc(*w1, *x, enums));
                assert(s2.drop_first() =~= enc(*w2, *x, enums));
                lemma_enc_inj(*w1, *w2, *x, enums);
            }
        },
        STy::Set(_) => {
            let p1 = v1->Set_0;
            let p2 = v2->Set_0;
            assert(s1 == Seq::new(p1.len(), |j: int| Value::Bool(p1[j])));
            assert(s2 == Seq::new(p2.len(), |j: int| Value::Bool(p2[j])));
            assert(p1.len() == s1.len() && s1.len() == s2.len() && s2.len() == p2.len());
            assert forall|i: int| 0 <= i < p1.len() implies p1[i] == p2[i] by {
                assert(s1[i] == s2[i]);
                assert(s1[i] == Value::Bool(p1[i]));
                assert(s2[i] == Value::Bool(p2[i]));
            }
            assert(p1 =~= p2);
        },
        STy::Map(_, x) => {
            lemma_inj_rows(v1->Map_0, v2->Map_0, *x, enums);
        },
        STy::List(e, max) => {
            let i1 = v1->List_0;
            let i2 = v2->List_0;
            assert(s1[0] == s2[0]);
            assert(i1.len() == i2.len());
            lemma_enc_items_len(i1, *e, enums);
            lemma_enc_items_len(i2, *e, enums);
            let d = enc_repeat(enc(default_val(*e, enums), *e, enums), (max - i1.len()) as nat);
            lemma_split_eq(seq![Value::Int(i1.len() as i64)] + enc_items(i1, *e, enums), d, seq![Value::Int(i2.len() as i64)] + enc_items(i2, *e, enums), d);
            lemma_split_eq(seq![Value::Int(i1.len() as i64)], enc_items(i1, *e, enums), seq![Value::Int(i2.len() as i64)], enc_items(i2, *e, enums));
            lemma_inj_items(i1, i2, *e, enums);
        },
    }
}

proof fn lemma_inj_seq(vs1: Seq<SVal>, vs2: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        members(vs1, ts, enums),
        members(vs2, ts, enums),
        smalls(ts),
        enc_seq(vs1, ts, enums) == enc_seq(vs2, ts, enums),
    ensures
        vs1 == vs2,
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        assert(vs1 =~= vs2);
    } else {
        let a1 = vs1.drop_last();
        let a2 = vs2.drop_last();
        let ta = ts.drop_last();
        lemma_enc_seq_len(a1, ta, enums);
        lemma_enc_seq_len(a2, ta, enums);
        lemma_split_eq(enc_seq(a1, ta, enums), enc(vs1.last(), ts.last(), enums), enc_seq(a2, ta, enums), enc(vs2.last(), ts.last(), enums));
        lemma_inj_seq(a1, a2, ta, enums);
        lemma_enc_inj(vs1.last(), vs2.last(), ts.last(), enums);
        assert(vs1 =~= a1.push(vs1.last()));
        assert(vs2 =~= a2.push(vs2.last()));
    }
}

proof fn lemma_inj_rows(r1: Seq<Option<SVal>>, r2: Seq<Option<SVal>>, t: STy, enums: Seq<i64>)
    requires
        map_rows_member(r1, t, enums),
        map_rows_member(r2, t, enums),
        r1.len() == r2.len(),
        small(t),
        enc_rows(r1, t, enums) == enc_rows(r2, t, enums),
    ensures
        r1 == r2,
    decreases t, r1.len() + 3,
{
    if r1.len() == 0 {
        assert(r1 =~= r2);
    } else {
        let a1 = r1.drop_last();
        let a2 = r2.drop_last();
        lemma_enc_rows_len(a1, t, enums);
        lemma_enc_rows_len(a2, t, enums);
        let e1 = match r1.last() {
            Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
            None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
        };
        let e2 = match r2.last() {
            Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
            None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
        };
        lemma_split_eq(enc_rows(a1, t, enums), e1, enc_rows(a2, t, enums), e2);
        lemma_inj_rows(a1, a2, t, enums);
        assert(e1[0] == e2[0]);
        if let Some(x1) = r1.last() {
            let x2 = r2.last()->Some_0;
            assert(e1.drop_first() =~= enc(x1, t, enums));
            assert(e2.drop_first() =~= enc(x2, t, enums));
            lemma_enc_inj(x1, x2, t, enums);
        }
        assert(r1 =~= a1.push(r1.last()));
        assert(r2 =~= a2.push(r2.last()));
    }
}

proof fn lemma_inj_items(i1: Seq<SVal>, i2: Seq<SVal>, t: STy, enums: Seq<i64>)
    requires
        list_items_member(i1, t, enums),
        list_items_member(i2, t, enums),
        i1.len() == i2.len(),
        small(t),
        enc_items(i1, t, enums) == enc_items(i2, t, enums),
    ensures
        i1 == i2,
    decreases t, i1.len() + 3,
{
    if i1.len() == 0 {
        assert(i1 =~= i2);
    } else {
        let a1 = i1.drop_last();
        let a2 = i2.drop_last();
        lemma_enc_items_len(a1, t, enums);
        lemma_enc_items_len(a2, t, enums);
        lemma_split_eq(enc_items(a1, t, enums), enc(i1.last(), t, enums), enc_items(a2, t, enums), enc(i2.last(), t, enums));
        lemma_inj_items(a1, a2, t, enums);
        lemma_enc_inj(i1.last(), i2.last(), t, enums);
        assert(i1 =~= a1.push(i1.last()));
        assert(i2 =~= a2.push(i2.last()));
    }
}

// ---- 符号化の値の種類 ----

/// 値の種類。Boolは0、整数は1、列挙型は2に型の添字を足した数。
pub open spec fn kind(v: Value) -> int {
    match v {
        Value::Bool(_) => 0,
        Value::Int(_) => 1,
        Value::Enum(id, _) => 2 + id,
    }
}

pub open spec fn kinds_of(s: Seq<Value>) -> Seq<int> {
    Seq::new(s.len(), |i: int| kind(s[i]))
}

pub open spec fn repeat_k(xs: Seq<int>, n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        repeat_k(xs, (n - 1) as nat) + xs
    }
}

/// 型 `t` の値の符号化の、位置ごとの種類。
pub open spec fn kinds(t: STy, enums: Seq<i64>) -> Seq<int>
    decreases t, 0nat,
{
    match t {
        STy::Bool => seq![0int],
        STy::Int(_, _) => seq![1int],
        STy::Enum(id) => seq![2 + id],
        STy::Tuple(ts) => kinds_seq(ts, enums),
        STy::Record(_, ts) => kinds_seq(ts, enums),
        STy::Option(x) => seq![0int] + kinds(*x, enums),
        STy::Set(e) => Seq::new(keys_or_zero(*e, enums), |_i: int| 0int),
        STy::Map(k, x) => repeat_k(seq![0int] + kinds(*x, enums), keys_or_zero(*k, enums)),
        STy::List(e, max) => seq![1int] + repeat_k(kinds(*e, enums), max as nat),
    }
}

pub open spec fn kinds_seq(ts: Seq<STy>, enums: Seq<i64>) -> Seq<int>
    decreases ts, 0nat,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        kinds_seq(ts.drop_last(), enums) + kinds(ts.last(), enums)
    }
}

proof fn lemma_kinds_add(a: Seq<Value>, b: Seq<Value>)
    ensures
        kinds_of(a + b) == kinds_of(a) + kinds_of(b),
{
    assert(kinds_of(a + b) =~= kinds_of(a) + kinds_of(b));
}

proof fn lemma_repeat_k_add(xs: Seq<int>, n: nat, m: nat)
    ensures
        repeat_k(xs, n) + repeat_k(xs, m) == repeat_k(xs, n + m),
    decreases m,
{
    if m == 0 {
        assert(repeat_k(xs, n) + repeat_k(xs, 0) =~= repeat_k(xs, n));
    } else {
        lemma_repeat_k_add(xs, n, (m - 1) as nat);
        assert(repeat_k(xs, n) + (repeat_k(xs, (m - 1) as nat) + xs) =~= (repeat_k(xs, n) + repeat_k(
            xs,
            (m - 1) as nat,
        )) + xs);
        assert((n + m - 1) as nat == n + (m - 1) as nat);
    }
}

proof fn lemma_kinds_repeat(xs: Seq<Value>, n: nat, ks: Seq<int>)
    requires
        kinds_of(xs) == ks,
    ensures
        kinds_of(enc_repeat(xs, n)) == repeat_k(ks, n),
    decreases n,
{
    if n == 0 {
        assert(kinds_of(enc_repeat(xs, 0)) =~= Seq::<int>::empty());
    } else {
        lemma_kinds_repeat(xs, (n - 1) as nat, ks);
        lemma_kinds_add(enc_repeat(xs, (n - 1) as nat), xs);
    }
}

/// 値が全部ない行の列は、Mapの行の列である。
proof fn lemma_none_rows(n: nat, t: STy, enums: Seq<i64>)
    ensures
        map_rows_member(Seq::new(n, |_i: int| None::<SVal>), t, enums),
    decreases n,
{
    if n > 0 {
        let r = Seq::new(n, |_i: int| None::<SVal>);
        assert(r.drop_last() =~= Seq::new((n - 1) as nat, |_i: int| None::<SVal>));
        lemma_none_rows((n - 1) as nat, t, enums);
    }
}

/// 型に属する値と既定値の符号化の、位置ごとの種類は型で決まる。
pub proof fn lemma_kinds(v: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v, t, enums) || v == default_val(t, enums),
    ensures
        kinds_of(enc(v, t, enums)) == kinds(t, enums),
    decreases t, 2nat,
{
    let s = enc(v, t, enums);
    match t {
        STy::Bool | STy::Int(_, _) | STy::Enum(_) => {
            assert(kinds_of(s) =~= kinds(t, enums));
        },
        STy::Tuple(ts) => {
            lemma_kinds_seq(v->Tuple_0, ts, enums);
        },
        STy::Record(_, ts) => {
            lemma_kinds_seq(v->Tuple_0, ts, enums);
        },
        STy::Option(x) => {
            match v {
                SVal::Some(w) => {
                    lemma_kinds(*w, *x, enums);
                    lemma_kinds_add(seq![Value::Bool(true)], enc(*w, *x, enums));
                },
                _ => {
                    lemma_kinds(default_val(*x, enums), *x, enums);
                    lemma_kinds_add(seq![Value::Bool(false)], enc(default_val(*x, enums), *x, enums));
                },
            }
            assert(kinds_of(seq![Value::Bool(true)]) =~= seq![0int]);
            assert(kinds_of(seq![Value::Bool(false)]) =~= seq![0int]);
        },
        STy::Set(e) => {
            assert(kinds_of(s) =~= kinds(t, enums));
        },
        STy::Map(k, x) => {
            let rows = v->Map_0;
            if v == default_val(t, enums) {
                lemma_none_rows(keys_or_zero(*k, enums), *x, enums);
            }
            lemma_kinds_rows(rows, *x, enums);
        },
        STy::List(e, max) => {
            let items = v->List_0;
            let d = default_val(*e, enums);
            lemma_kinds(d, *e, enums);
            lemma_kinds_items(items, *e, enums);
            let n = (max - items.len()) as nat;
            lemma_kinds_repeat(enc(d, *e, enums), n, kinds(*e, enums));
            let h = seq![Value::Int(items.len() as i64)];
            lemma_kinds_add(h, enc_items(items, *e, enums));
            lemma_kinds_add(h + enc_items(items, *e, enums), enc_repeat(enc(d, *e, enums), n));
            lemma_repeat_k_add(kinds(*e, enums), items.len(), n);
            assert(kinds_of(h) =~= seq![1int]);
            assert(items.len() + n == max);
            let ke = kinds(*e, enums);
            assert(seq![1int] + repeat_k(ke, items.len()) + repeat_k(ke, n) =~= seq![1int] + (repeat_k(ke, items.len())
                + repeat_k(ke, n)));
        },
    }
}

proof fn lemma_kinds_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        members(vs, ts, enums) || vs == default_vals(ts, enums),
    ensures
        kinds_of(enc_seq(vs, ts, enums)) == kinds_seq(ts, enums),
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        assert(kinds_of(enc_seq(vs, ts, enums)) =~= Seq::<int>::empty());
    } else {
        lemma_default_vals_len(ts, enums);
        assert(vs.len() == ts.len());
        let a = vs.drop_last();
        if vs == default_vals(ts, enums) {
            assert(a == default_vals(ts.drop_last(), enums));
            assert(vs.last() == default_val(ts.last(), enums));
        }
        lemma_kinds_seq(a, ts.drop_last(), enums);
        lemma_kinds(vs.last(), ts.last(), enums);
        lemma_kinds_add(enc_seq(a, ts.drop_last(), enums), enc(vs.last(), ts.last(), enums));
    }
}

proof fn lemma_kinds_rows(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>)
    requires
        map_rows_member(rows, t, enums),
    ensures
        kinds_of(enc_rows(rows, t, enums)) == repeat_k(seq![0int] + kinds(t, enums), rows.len()),
    decreases t, rows.len() + 3,
{
    if rows.len() == 0 {
        assert(kinds_of(enc_rows(rows, t, enums)) =~= Seq::<int>::empty());
    } else {
        lemma_kinds_rows(rows.drop_last(), t, enums);
        let e = match rows.last() {
            Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
            None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
        };
        match rows.last() {
            Some(x) => {
                lemma_kinds(x, t, enums);
                lemma_kinds_add(seq![Value::Bool(true)], enc(x, t, enums));
            },
            None => {
                lemma_kinds(default_val(t, enums), t, enums);
                lemma_kinds_add(seq![Value::Bool(false)], enc(default_val(t, enums), t, enums));
            },
        }
        assert(kinds_of(seq![Value::Bool(true)]) =~= seq![0int]);
        assert(kinds_of(seq![Value::Bool(false)]) =~= seq![0int]);
        lemma_kinds_add(enc_rows(rows.drop_last(), t, enums), e);
    }
}

proof fn lemma_kinds_items(items: Seq<SVal>, t: STy, enums: Seq<i64>)
    requires
        list_items_member(items, t, enums),
    ensures
        kinds_of(enc_items(items, t, enums)) == repeat_k(kinds(t, enums), items.len()),
    decreases t, items.len() + 3,
{
    if items.len() == 0 {
        assert(kinds_of(enc_items(items, t, enums)) =~= Seq::<int>::empty());
    } else {
        lemma_kinds_items(items.drop_last(), t, enums);
        lemma_kinds(items.last(), t, enums);
        lemma_kinds_add(enc_items(items.drop_last(), t, enums), enc(items.last(), t, enums));
    }
}

// ---- 等しさの式 ----

/// `c` は、スロット `x` と `y` の表す型 `t` の値が等しいかを表す。
/// スロットが純粋なら `c` も純粋である。
pub open spec fn eq_ok(t: XTy, x: Seq<Expr>, y: Seq<Expr>, c: Expr, enums: Seq<i64>) -> bool {
    &&& forall|n: nat| all_pure(x, n) && all_pure(y, n) ==> #[trigger] pure_below(c, n)
    &&& forall|env: Env, l: Seq<Value>, vx: SVal, vy: SVal|
        #[trigger] denotes(x, env, l, vx, t, enums) && #[trigger] denotes(y, env, l, vy, t, enums) ==> eval_l(c, env, l)
            == Ok::<Value, ErrKind>(Value::Bool(vx == vy))
}

/// 組の各部分の等しさの式をすべて満たすことは、組の等しさである。
pub open spec fn eq_seq_ok(ts: Seq<XTy>, x: Seq<Expr>, y: Seq<Expr>, c: Expr, enums: Seq<i64>) -> bool {
    &&& forall|n: nat| all_pure(x, n) && all_pure(y, n) ==> #[trigger] pure_below(c, n)
    &&& forall|env: Env, l: Seq<Value>, vs1: Seq<SVal>, vs2: Seq<SVal>|
        clean(x, env, l) && clean(y, env, l) && #[trigger] models_seq(slot_vals(x, env, l), vs1, ts, enums)
            && #[trigger] models_seq(slot_vals(y, env, l), vs2, ts, enums) ==> eval_l(c, env, l) == Ok::<Value, ErrKind>(
            Value::Bool(vs1 == vs2),
        )
}

/// Bool、整数、列挙型の等しさ。
pub proof fn lemma_eq_scalar(t: XTy, x: Seq<Expr>, y: Seq<Expr>, enums: Seq<i64>)
    requires
        t is Bool || t is Int || t is Enum,
        x.len() > 0,
        y.len() > 0,
    ensures
        eq_ok(t, x, y, Expr::Bin(BinOp::Eq, Box::new(x[0]), Box::new(y[0])), enums),
{
    let c = Expr::Bin(BinOp::Eq, Box::new(x[0]), Box::new(y[0]));
    assert forall|n: nat| all_pure(x, n) && all_pure(y, n) implies #[trigger] pure_below(c, n) by {
        assert(pure_below(x[0], n) && pure_below(y[0], n));
    }
    assert forall|env: Env, l: Seq<Value>, vx: SVal, vy: SVal|
        #[trigger] denotes(x, env, l, vx, t, enums) && #[trigger] denotes(y, env, l, vy, t, enums) implies eval_l(
        c,
        env,
        l,
    ) == Ok::<Value, ErrKind>(Value::Bool(vx == vy)) by {
        assert(slot_vals(x, env, l)[0] == eval_l(x[0], env, l)->Ok_0);
        assert(slot_vals(y, env, l)[0] == eval_l(y[0], env, l)->Ok_0);
        assert(eval_l(x[0], env, l) is Ok);
        assert(eval_l(y[0], env, l) is Ok);
    }
}

/// Optionの等しさ。有無が等しく、あるなら中身が等しい。
pub proof fn lemma_eq_option(inner: XTy, x: Seq<Expr>, y: Seq<Expr>, rest: Expr, enums: Seq<i64>)
    requires
        x.len() > 0,
        y.len() > 0,
        eq_ok(inner, x.subrange(1, x.len() as int), y.subrange(1, y.len() as int), rest, enums),
    ensures
        eq_ok(
            XTy::Option(Box::new(inner)),
            x,
            y,
            and_s(Expr::Bin(BinOp::Eq, Box::new(x[0]), Box::new(y[0])), implies_s(x[0], rest)),
            enums,
        ),
{
    let t = XTy::Option(Box::new(inner));
    let xr = x.subrange(1, x.len() as int);
    let yr = y.subrange(1, y.len() as int);
    let e0 = Expr::Bin(BinOp::Eq, Box::new(x[0]), Box::new(y[0]));
    let imp = implies_s(x[0], rest);
    let c = and_s(e0, imp);
    assert forall|n: nat| all_pure(x, n) && all_pure(y, n) implies #[trigger] pure_below(c, n) by {
        assert(pure_below(x[0], n) && pure_below(y[0], n));
        assert(all_pure(xr, n)) by {
            assert forall|j: int| 0 <= j < xr.len() implies pure_below(#[trigger] xr[j], n) by {
                assert(xr[j] == x[j + 1]);
            }
        }
        assert(all_pure(yr, n)) by {
            assert forall|j: int| 0 <= j < yr.len() implies pure_below(#[trigger] yr[j], n) by {
                assert(yr[j] == y[j + 1]);
            }
        }
        assert(pure_below(rest, n));
        assert(pure_below(e0, n));
        assert(pure_below(imp, n));
    }
    assert forall|env: Env, l: Seq<Value>, vx: SVal, vy: SVal|
        #[trigger] denotes(x, env, l, vx, t, enums) && #[trigger] denotes(y, env, l, vy, t, enums) implies eval_l(
        c,
        env,
        l,
    ) == Ok::<Value, ErrKind>(Value::Bool(vx == vy)) by {
        let sx = slot_vals(x, env, l);
        let sy = slot_vals(y, env, l);
        assert(sx[0] == eval_l(x[0], env, l)->Ok_0);
        assert(sy[0] == eval_l(y[0], env, l)->Ok_0);
        assert(eval_l(x[0], env, l) is Ok);
        assert(eval_l(y[0], env, l) is Ok);
        let px = vx is Some;
        let py = vy is Some;
        assert(eval_l(x[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(px)));
        assert(eval_l(y[0], env, l) == Ok::<Value, ErrKind>(Value::Bool(py)));
        assert(eval_l(e0, env, l) == Ok::<Value, ErrKind>(Value::Bool(px == py)));
        if px && py {
            lemma_clean_sub(x, env, l, 1, x.len() as int);
            lemma_clean_sub(y, env, l, 1, y.len() as int);
            assert(sx.subrange(1, x.len() as int) =~= sx.drop_first());
            assert(sy.subrange(1, y.len() as int) =~= sy.drop_first());
            let w1 = *vx->Some_0;
            let w2 = *vy->Some_0;
            assert(denotes(xr, env, l, w1, inner, enums));
            assert(denotes(yr, env, l, w2, inner, enums));
            assert(eval_l(rest, env, l) == Ok::<Value, ErrKind>(Value::Bool(w1 == w2)));
            assert(eval_l(imp, env, l) == Ok::<Value, ErrKind>(Value::Bool(w1 == w2)));
            lemma_and(e0, imp, env, l, true, w1 == w2);
            assert((vx == vy) == (w1 == w2));
        } else if !px && !py {
            assert(vx == vy);
            if rest == bool_lit(true) {
                assert(eval_l(imp, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            } else {
                assert(eval_l(imp, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
            lemma_and(e0, imp, env, l, true, true);
        } else {
            assert(vx != vy);
            assert(e0 != bool_lit(true));
            if imp == bool_lit(true) {
                assert(c == e0);
            } else {
                assert(c == Expr::And(Box::new(e0), Box::new(imp)));
            }
        }
    }
}

/// 組の等しさ。各部分が等しい。
pub proof fn lemma_eq_parts(
    ts: Seq<XTy>,
    x: Seq<Expr>,
    y: Seq<Expr>,
    xs: Seq<Seq<Expr>>,
    ys: Seq<Seq<Expr>>,
    items: Seq<Expr>,
    enums: Seq<i64>,
)
    requires
        xs.len() == ts.len(),
        ys.len() == ts.len(),
        items.len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] split_ok(xs[i], x, ts, i, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] split_ok(ys[i], y, ts, i, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] eq_ok(ts[i], xs[i], ys[i], items[i], enums),
    ensures
        eq_seq_ok(ts, x, y, tree_s(items, bool_lit(true), Join::And), enums),
{
    let c = tree_s(items, bool_lit(true), Join::And);
    assert forall|n: nat| all_pure(x, n) && all_pure(y, n) implies #[trigger] pure_below(c, n) by {
        assert forall|i: int| 0 <= i < items.len() implies pure_below(#[trigger] items[i], n) by {
            assert(split_ok(xs[i], x, ts, i, enums));
            assert(split_ok(ys[i], y, ts, i, enums));
            assert(eq_ok(ts[i], xs[i], ys[i], items[i], enums));
            assert(all_pure(xs[i], n)) by {
                assert forall|j: int| 0 <= j < xs[i].len() implies pure_below(#[trigger] xs[i][j], n) by {
                    assert(xs[i][j] == x[xoff(ts, i, enums) + j]);
                }
            }
            assert(all_pure(ys[i], n)) by {
                assert forall|j: int| 0 <= j < ys[i].len() implies pure_below(#[trigger] ys[i][j], n) by {
                    assert(ys[i][j] == y[xoff(ts, i, enums) + j]);
                }
            }
        }
        lemma_tree_pure(items, bool_lit(true), Join::And, n);
    }
    assert forall|env: Env, l: Seq<Value>, vs1: Seq<SVal>, vs2: Seq<SVal>|
        clean(x, env, l) && clean(y, env, l) && #[trigger] models_seq(slot_vals(x, env, l), vs1, ts, enums)
            && #[trigger] models_seq(slot_vals(y, env, l), vs2, ts, enums) implies eval_l(c, env, l) == Ok::<
        Value,
        ErrKind,
    >(Value::Bool(vs1 == vs2)) by {
        if ts.len() == 0 {
            assert(vs1 =~= vs2);
        } else {
            lemma_denotes_part(x, env, l, vs1, ts, 0, enums);
            lemma_denotes_part(y, env, l, vs2, ts, 0, enums);
        }
        assert forall|i: int| 0 <= i < items.len() implies #[trigger] eval_l(items[i], env, l) == Ok::<Value, ErrKind>(
            Value::Bool(vs1[i] == vs2[i]),
        ) by {
            lemma_denotes_part(x, env, l, vs1, ts, i, enums);
            lemma_denotes_part(y, env, l, vs2, ts, i, enums);
            assert(split_ok(xs[i], x, ts, i, enums));
            assert(split_ok(ys[i], y, ts, i, enums));
            assert(eq_ok(ts[i], xs[i], ys[i], items[i], enums));
            assert(denotes(xs[i], env, l, vs1[i], ts[i], enums));
            assert(denotes(ys[i], env, l, vs2[i], ts[i], enums));
        }
        assert(all_bool(items, env, l)) by {
            assert forall|i: int| 0 <= i < items.len() implies bool_val(#[trigger] eval_l(items[i], env, l)) by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(vs1[i] == vs2[i])));
            }
        }
        lemma_all_of(items, env, l);
        if all_true(items, env, l) {
            assert forall|i: int| 0 <= i < vs1.len() implies vs1[i] == vs2[i] by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(vs1[i] == vs2[i])));
            }
            assert(vs1 =~= vs2);
        }
        if vs1 == vs2 {
            assert forall|i: int| 0 <= i < items.len() implies #[trigger] eval_l(items[i], env, l) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true)) by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(vs1[i] == vs2[i])));
            }
        }
    }
}

/// 組と記録の等しさは、各部分の等しさである。
pub proof fn lemma_eq_tuple(t: XTy, ts: Seq<XTy>, x: Seq<Expr>, y: Seq<Expr>, c: Expr, enums: Seq<i64>)
    requires
        (t is Tuple && t->Tuple_0 == ts) || (t is Record && t->Record_1 == ts),
        eq_seq_ok(ts, x, y, c, enums),
    ensures
        eq_ok(t, x, y, c, enums),
{
    assert forall|env: Env, l: Seq<Value>, vx: SVal, vy: SVal|
        #[trigger] denotes(x, env, l, vx, t, enums) && #[trigger] denotes(y, env, l, vy, t, enums) implies eval_l(
        c,
        env,
        l,
    ) == Ok::<Value, ErrKind>(Value::Bool(vx == vy)) by {
        let vs1 = vx->Tuple_0;
        let vs2 = vy->Tuple_0;
        assert(models_seq(slot_vals(x, env, l), vs1, ts, enums));
        assert(models_seq(slot_vals(y, env, l), vs2, ts, enums));
    }
}

/// Set、Map、Listの格納の型。
pub open spec fn coll_sty(t: XTy) -> STy {
    match t {
        XTy::Set(e) => STy::Set(e),
        XTy::Map(k, v) => STy::Map(k, v),
        XTy::List(e, max) => STy::List(e, max),
        _ => STy::Bool,
    }
}

/// Set、Map、Listの等しさ。スロットが位置ごとに等しい。
#[verifier::spinoff_prover]
pub proof fn lemma_eq_coll(t: XTy, x: Seq<Expr>, y: Seq<Expr>, items: Seq<Expr>, enums: Seq<i64>)
    requires
        t is Set || t is Map || t is List,
        small(coll_sty(t)),
        items.len() == if x.len() < y.len() {
            x.len()
        } else {
            y.len()
        },
        forall|i: int| 0 <= i < items.len() ==> #[trigger] items[i] == Expr::Bin(BinOp::Eq, Box::new(x[i]), Box::new(y[i])),
    ensures
        eq_ok(t, x, y, tree_s(items, bool_lit(true), Join::And), enums),
{
    let c = tree_s(items, bool_lit(true), Join::And);
    let st = coll_sty(t);
    assert forall|n: nat| all_pure(x, n) && all_pure(y, n) implies #[trigger] pure_below(c, n) by {
        assert forall|i: int| 0 <= i < items.len() implies pure_below(#[trigger] items[i], n) by {
            assert(pure_below(x[i], n) && pure_below(y[i], n));
        }
        lemma_tree_pure(items, bool_lit(true), Join::And, n);
    }
    assert forall|env: Env, l: Seq<Value>, vx: SVal, vy: SVal|
        #[trigger] denotes(x, env, l, vx, t, enums) && #[trigger] denotes(y, env, l, vy, t, enums) implies eval_l(
        c,
        env,
        l,
    ) == Ok::<Value, ErrKind>(Value::Bool(vx == vy)) by {
        let sx = slot_vals(x, env, l);
        let sy = slot_vals(y, env, l);
        assert(member(vx, st, enums) && sx == enc(vx, st, enums));
        assert(member(vy, st, enums) && sy == enc(vy, st, enums));
        lemma_enc_len(vx, st, enums);
        lemma_enc_len(vy, st, enums);
        lemma_kinds(vx, st, enums);
        lemma_kinds(vy, st, enums);
        assert(x.len() == y.len());
        assert forall|i: int| 0 <= i < items.len() implies #[trigger] eval_l(items[i], env, l) == Ok::<Value, ErrKind>(
            Value::Bool(sx[i] == sy[i]),
        ) by {
            assert(sx[i] == eval_l(x[i], env, l)->Ok_0);
            assert(sy[i] == eval_l(y[i], env, l)->Ok_0);
            assert(eval_l(x[i], env, l) is Ok);
            assert(eval_l(y[i], env, l) is Ok);
            assert(kinds_of(sx)[i] == kinds_of(sy)[i]);
            assert(same_kind(sx[i], sy[i]));
        }
        assert(all_bool(items, env, l)) by {
            assert forall|i: int| 0 <= i < items.len() implies bool_val(#[trigger] eval_l(items[i], env, l)) by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(sx[i] == sy[i])));
            }
        }
        lemma_all_of(items, env, l);
        if all_true(items, env, l) {
            assert forall|i: int| 0 <= i < sx.len() implies sx[i] == sy[i] by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(sx[i] == sy[i])));
            }
            assert(sx =~= sy);
            lemma_enc_inj(vx, vy, st, enums);
        }
        if vx == vy {
            assert forall|i: int| 0 <= i < items.len() implies #[trigger] eval_l(items[i], env, l) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true)) by {
                assert(eval_l(items[i], env, l) == Ok::<Value, ErrKind>(Value::Bool(sx[i] == sy[i])));
            }
        }
    }
}

} // verus!
