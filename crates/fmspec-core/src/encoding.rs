//! IRの型と値の意味、およびスロットの列への符号化の仕様（仕様書 §4.1、§12.6）。
//!
//! 複合型の値は、固定幅のスロットの列に符号化する。各スロットは中核の値（Bool、Int、Enum）である。
//!
//! | 型 | スロット |
//! |---|---|
//! | Bool、Int、Enum | 1つ |
//! | Tuple、Record | 要素のスロットを順に並べる |
//! | Option | 有無を表すBoolのあとに、中身のスロット |
//! | Set | 要素の型の値ごとに、含むかどうかを表すBool |
//! | Map | キーの型の値ごとに、キーがあるかどうかを表すBoolと、値のスロット |
//! | List | 長さを表すIntのあとに、`max` 個の要素のスロット |
//!
//! Setの要素とMapのキーになれる型（**キーの型**）の値は、[`domain`] の順（正規順）に並べる。
//! SetとMapの値は、この順に並べた列で表す。
//!
//! 型は2種類ある。
//!
//! - **格納の型** [`SType`]：状態変数、引数、Setの要素、Mapのキーと値、Listの要素の型。整数は範囲を持つ。
//!   格納の型の値は正規形で、符号化は関数 [`enc`] である。
//!   正規形では、空のOptionの中身、Mapにないキーの値、Listの長さより後ろの要素が既定値になる。
//! - **式の型** [`XType`]：式の値の型。式の中間結果の整数は範囲を持たない。
//!   空のOptionの中身のスロットは既定値とは限らないので、スロットの列が値を表すことを関係 [`models`] で定める。
//!
//! Recordの値は、フィールドを宣言の順に並べたTupleの値で表す。フィールドの名前は、名前の番号で型に持つ。

#[cfg(verus_keep_ghost)]
use crate::model::Value;
use vstd::prelude::*;

verus! {

/// キーの型が取れる値の数の上限。
pub const MAX_KEYS: u64 = 4096;

/// 格納の型。
pub enum SType {
    Bool,
    /// 閉区間 `min..=max` の整数。
    Int(i64, i64),
    /// 列挙型。列挙型の添字で指す。
    Enum(usize),
    Tuple(Vec<SType>),
    /// フィールドの名前の番号と、フィールドの型。
    Record(Vec<usize>, Vec<SType>),
    Option(Box<SType>),
    Set(Box<SType>),
    /// キーの型と値の型。
    Map(Box<SType>, Box<SType>),
    /// 要素の型と、長さの上限。
    List(Box<SType>, usize),
}

/// 式の型。
pub enum XType {
    Bool,
    Int,
    Enum(usize),
    Tuple(Vec<XType>),
    Record(Vec<usize>, Vec<XType>),
    Option(Box<XType>),
    Set(Box<SType>),
    Map(Box<SType>, Box<SType>),
    List(Box<SType>, usize),
}

/// IRの値。
pub enum SVal {
    Bool(bool),
    Int(i64),
    /// 列挙型の添字と、ラベルの添字。
    Enum(usize, i64),
    /// TupleとRecordの値。
    Tuple(Seq<SVal>),
    None,
    Some(Box<SVal>),
    /// 要素の型の正規順に並べた、含むかどうか。
    Set(Seq<bool>),
    /// キーの型の正規順に並べた、キーに対応する値。
    Map(Seq<Option<SVal>>),
    List(Seq<SVal>),
}

// ---- 型の大きさ ----

/// キーの型の値の数。キーの型でないか、`MAX_KEYS` を超えるなら `None`。
/// `enums` は各列挙型のラベルの数。
pub open spec fn keys(t: SType, enums: Seq<i64>) -> Option<nat>
    decreases t,
{
    let n: Option<nat> = match t {
        SType::Bool => Some(2),
        SType::Int(lo, hi) => if lo <= hi && hi - lo + 1 <= MAX_KEYS {
            Some((hi - lo + 1) as nat)
        } else {
            None
        },
        SType::Enum(id) => if id < enums.len() && enums[id as int] >= 0 {
            Some(enums[id as int] as nat)
        } else {
            None
        },
        SType::Tuple(ts) => keys_product(ts@, enums),
        SType::Record(_, ts) => keys_product(ts@, enums),
        SType::Option(x) => match keys(*x, enums) {
            Some(k) => Some(k + 1),
            None => None,
        },
        _ => None,
    };
    match n {
        Some(k) => if k <= MAX_KEYS {
            Some(k)
        } else {
            None
        },
        None => None,
    }
}

/// 要素の値の数の積。左から掛け、途中で `MAX_KEYS` を超えたら `None`。
pub open spec fn keys_product(ts: Seq<SType>, enums: Seq<i64>) -> Option<nat>
    decreases ts,
{
    if ts.len() == 0 {
        Some(1)
    } else {
        match (keys_product(ts.drop_last(), enums), keys(ts.last(), enums)) {
            (Some(p), Some(k)) => if p * k <= MAX_KEYS {
                Some(p * k)
            } else {
                None
            },
            _ => None,
        }
    }
}

/// スロット数。
pub open spec fn width(t: SType, enums: Seq<i64>) -> nat
    decreases t,
{
    match t {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) => 1,
        SType::Tuple(ts) => width_sum(ts@, enums),
        SType::Record(_, ts) => width_sum(ts@, enums),
        SType::Option(x) => 1 + width(*x, enums),
        SType::Set(e) => keys_or_zero(*e, enums),
        SType::Map(k, v) => keys_or_zero(*k, enums) * (1 + width(*v, enums)),
        SType::List(e, max) => 1 + (max as nat) * width(*e, enums),
    }
}

pub open spec fn width_sum(ts: Seq<SType>, enums: Seq<i64>) -> nat
    decreases ts,
{
    if ts.len() == 0 {
        0
    } else {
        width_sum(ts.drop_last(), enums) + width(ts.last(), enums)
    }
}

pub open spec fn keys_or_zero(t: SType, enums: Seq<i64>) -> nat {
    match keys(t, enums) {
        Some(k) => k,
        None => 0,
    }
}

/// 式の型のスロット数。
pub open spec fn xwidth(t: XType, enums: Seq<i64>) -> nat
    decreases t,
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => 1,
        XType::Tuple(ts) => xwidth_sum(ts@, enums),
        XType::Record(_, ts) => xwidth_sum(ts@, enums),
        XType::Option(x) => 1 + xwidth(*x, enums),
        XType::Set(e) => keys_or_zero(*e, enums),
        XType::Map(k, v) => keys_or_zero(*k, enums) * (1 + width(*v, enums)),
        XType::List(e, max) => 1 + (max as nat) * width(*e, enums),
    }
}

pub open spec fn xwidth_sum(ts: Seq<XType>, enums: Seq<i64>) -> nat
    decreases ts,
{
    if ts.len() == 0 {
        0
    } else {
        xwidth_sum(ts.drop_last(), enums) + xwidth(ts.last(), enums)
    }
}

// ---- 整形式の型 ----

/// 整形式の格納の型。整数の範囲は空でなく、列挙型は定義済みでラベルを持つ。
/// TupleとRecordは要素を1つ以上持ち、Recordのフィールドの名前は重複しない。
/// Setの要素とMapのキーはキーの型である。
pub open spec fn wf_stype(t: SType, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        SType::Bool => true,
        SType::Int(lo, hi) => lo <= hi,
        SType::Enum(id) => id < enums.len() && enums[id as int] >= 1,
        SType::Tuple(ts) => ts@.len() >= 1 && wf_stypes(ts@, enums),
        SType::Record(names, ts) => ts@.len() >= 1 && names@.len() == ts@.len() && names@.no_duplicates()
            && wf_stypes(ts@, enums),
        SType::Option(x) => wf_stype(*x, enums),
        SType::Set(e) => wf_stype(*e, enums) && keys(*e, enums) is Some,
        SType::Map(k, v) => wf_stype(*k, enums) && keys(*k, enums) is Some && wf_stype(*v, enums),
        SType::List(e, _) => wf_stype(*e, enums),
    }
}

pub open spec fn wf_stypes(ts: Seq<SType>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        wf_stypes(ts.drop_last(), enums) && wf_stype(ts.last(), enums)
    }
}

/// 整形式の式の型。
pub open spec fn wf_xtype(t: XType, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XType::Bool | XType::Int => true,
        XType::Enum(id) => id < enums.len() && enums[id as int] >= 1,
        XType::Tuple(ts) => ts@.len() >= 1 && wf_xtypes(ts@, enums),
        XType::Record(names, ts) => ts@.len() >= 1 && names@.len() == ts@.len() && names@.no_duplicates()
            && wf_xtypes(ts@, enums),
        XType::Option(x) => wf_xtype(*x, enums),
        XType::Set(e) => wf_stype(SType::Set(e), enums),
        XType::Map(k, v) => wf_stype(SType::Map(k, v), enums),
        XType::List(e, max) => wf_stype(SType::List(e, max), enums),
    }
}

pub open spec fn wf_xtypes(ts: Seq<XType>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        wf_xtypes(ts.drop_last(), enums) && wf_xtype(ts.last(), enums)
    }
}

// ---- 値の型 ----

/// 値 `v` が格納の型 `t` に属する（範囲と正規形を含む）。
pub open spec fn member(v: SVal, t: SType, enums: Seq<i64>) -> bool
    decreases t, 0nat,
{
    match t {
        SType::Bool => v is Bool,
        SType::Int(lo, hi) => match v {
            SVal::Int(x) => lo <= x && x <= hi,
            _ => false,
        },
        SType::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int],
            _ => false,
        },
        SType::Tuple(ts) => match v {
            SVal::Tuple(vs) => members(vs, ts@, enums),
            _ => false,
        },
        SType::Record(_, ts) => match v {
            SVal::Tuple(vs) => members(vs, ts@, enums),
            _ => false,
        },
        SType::Option(x) => match v {
            SVal::None => true,
            SVal::Some(w) => member(*w, *x, enums),
            _ => false,
        },
        SType::Set(e) => match v {
            SVal::Set(bits) => keys(*e, enums) == Some(bits.len()),
            _ => false,
        },
        SType::Map(k, x) => match v {
            SVal::Map(rows) => keys(*k, enums) == Some(rows.len()) && map_rows_member(rows, *x, enums),
            _ => false,
        },
        SType::List(e, max) => match v {
            SVal::List(items) => items.len() <= max && list_items_member(items, *e, enums),
            _ => false,
        },
    }
}

/// 値の列 `vs` の各値が、型の列 `ts` の対応する型に属する。
pub open spec fn members(vs: Seq<SVal>, ts: Seq<SType>, enums: Seq<i64>) -> bool
    decreases ts, 0nat,
{
    if ts.len() == 0 {
        vs.len() == 0
    } else {
        vs.len() == ts.len() && members(vs.drop_last(), ts.drop_last(), enums) && member(vs.last(), ts.last(), enums)
    }
}

pub open spec fn map_rows_member(rows: Seq<Option<SVal>>, t: SType, enums: Seq<i64>) -> bool
    decreases t, rows.len(),
{
    if rows.len() == 0 {
        true
    } else {
        map_rows_member(rows.drop_last(), t, enums) && match rows.last() {
            Some(x) => member(x, t, enums),
            None => true,
        }
    }
}

pub open spec fn list_items_member(items: Seq<SVal>, t: SType, enums: Seq<i64>) -> bool
    decreases t, items.len(),
{
    if items.len() == 0 {
        true
    } else {
        list_items_member(items.drop_last(), t, enums) && member(items.last(), t, enums)
    }
}

/// 値 `v` が式の型 `t` を持つ。整数の範囲は問わない。Set、Map、Listの値は格納の型に属する。
pub open spec fn has_xtype(v: SVal, t: XType, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XType::Bool => v is Bool,
        XType::Int => v is Int,
        XType::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int],
            _ => false,
        },
        XType::Tuple(ts) => match v {
            SVal::Tuple(vs) => has_xtypes(vs, ts@, enums),
            _ => false,
        },
        XType::Record(_, ts) => match v {
            SVal::Tuple(vs) => has_xtypes(vs, ts@, enums),
            _ => false,
        },
        XType::Option(x) => match v {
            SVal::None => true,
            SVal::Some(w) => has_xtype(*w, *x, enums),
            _ => false,
        },
        XType::Set(e) => member(v, SType::Set(e), enums),
        XType::Map(k, x) => member(v, SType::Map(k, x), enums),
        XType::List(e, max) => member(v, SType::List(e, max), enums),
    }
}

pub open spec fn has_xtypes(vs: Seq<SVal>, ts: Seq<XType>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        vs.len() == 0
    } else {
        vs.len() == ts.len() && has_xtypes(vs.drop_last(), ts.drop_last(), enums) && has_xtype(
            vs.last(),
            ts.last(),
            enums,
        )
    }
}

// ---- 既定値と符号化 ----

/// 格納の型の既定値。Boolは偽、Intは範囲の最小値、Enumは最初のラベル、Optionは空、
/// SetとMapは空、Listは長さ0、TupleとRecordは要素の既定値。
pub open spec fn default_val(t: SType, enums: Seq<i64>) -> SVal
    decreases t,
{
    match t {
        SType::Bool => SVal::Bool(false),
        SType::Int(lo, _) => SVal::Int(lo),
        SType::Enum(id) => SVal::Enum(id, 0),
        SType::Tuple(ts) => SVal::Tuple(default_vals(ts@, enums)),
        SType::Record(_, ts) => SVal::Tuple(default_vals(ts@, enums)),
        SType::Option(_) => SVal::None,
        SType::Set(e) => SVal::Set(Seq::new(keys_or_zero(*e, enums), |_i: int| false)),
        SType::Map(k, _) => SVal::Map(Seq::new(keys_or_zero(*k, enums), |_i: int| None)),
        SType::List(_, _) => SVal::List(Seq::empty()),
    }
}

pub open spec fn default_vals(ts: Seq<SType>, enums: Seq<i64>) -> Seq<SVal>
    decreases ts,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        default_vals(ts.drop_last(), enums).push(default_val(ts.last(), enums))
    }
}

/// 格納の型の値の符号化（正規形）。
pub open spec fn enc(v: SVal, t: SType, enums: Seq<i64>) -> Seq<Value>
    decreases t, 0nat,
{
    match t {
        SType::Bool => match v {
            SVal::Bool(b) => seq![Value::Bool(b)],
            _ => seq![Value::Bool(false)],
        },
        SType::Int(lo, _) => match v {
            SVal::Int(x) => seq![Value::Int(x)],
            _ => seq![Value::Int(lo)],
        },
        SType::Enum(id) => match v {
            SVal::Enum(_, k) => seq![Value::Enum(id, k)],
            _ => seq![Value::Enum(id, 0)],
        },
        SType::Tuple(ts) => match v {
            SVal::Tuple(vs) => enc_seq(vs, ts@, enums),
            _ => Seq::empty(),
        },
        SType::Record(_, ts) => match v {
            SVal::Tuple(vs) => enc_seq(vs, ts@, enums),
            _ => Seq::empty(),
        },
        SType::Option(x) => match v {
            SVal::Some(w) => seq![Value::Bool(true)] + enc(*w, *x, enums),
            _ => seq![Value::Bool(false)] + enc(default_val(*x, enums), *x, enums),
        },
        SType::Set(_) => match v {
            SVal::Set(bits) => Seq::new(bits.len(), |i: int| Value::Bool(bits[i])),
            _ => Seq::empty(),
        },
        SType::Map(_, x) => match v {
            SVal::Map(rows) => enc_rows(rows, *x, enums),
            _ => Seq::empty(),
        },
        SType::List(e, max) => match v {
            SVal::List(items) => seq![Value::Int(items.len() as i64)] + enc_items(items, *e, enums) + enc_repeat(
                enc(default_val(*e, enums), *e, enums),
                (max - items.len()) as nat,
            ),
            _ => Seq::empty(),
        },
    }
}

/// 値の列を、対応する型で符号化して順につなげる。
pub open spec fn enc_seq(vs: Seq<SVal>, ts: Seq<SType>, enums: Seq<i64>) -> Seq<Value>
    decreases ts, 0nat,
{
    if ts.len() == 0 || vs.len() == 0 {
        Seq::empty()
    } else {
        enc_seq(vs.drop_last(), ts.drop_last(), enums) + enc(vs.last(), ts.last(), enums)
    }
}

/// Mapの行を順につなげる。行は、有無のBoolと値のスロットである。ない行の値は既定値。
pub open spec fn enc_rows(rows: Seq<Option<SVal>>, t: SType, enums: Seq<i64>) -> Seq<Value>
    decreases t, rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        enc_rows(rows.drop_last(), t, enums) + match rows.last() {
            Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
            None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
        }
    }
}

/// Listの要素を順につなげる。
pub open spec fn enc_items(items: Seq<SVal>, t: SType, enums: Seq<i64>) -> Seq<Value>
    decreases t, items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        enc_items(items.drop_last(), t, enums) + enc(items.last(), t, enums)
    }
}

/// `xs` を `n` 回つなげる。
pub open spec fn enc_repeat(xs: Seq<Value>, n: nat) -> Seq<Value>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        enc_repeat(xs, (n - 1) as nat) + xs
    }
}

/// `x` は格納の型 `t` の式の型である。整数の範囲を落とし、Set、Map、Listの中の型はそのまま持つ。
pub open spec fn xtype_of(x: XType, t: SType) -> bool
    decreases t,
{
    match (x, t) {
        (XType::Bool, SType::Bool) | (XType::Int, SType::Int(_, _)) => true,
        (XType::Enum(a), SType::Enum(b)) => a == b,
        (XType::Tuple(xs), SType::Tuple(ts)) => xtypes_of(xs@, ts@),
        (XType::Record(m, xs), SType::Record(n, ts)) => m@ == n@ && xtypes_of(xs@, ts@),
        (XType::Option(a), SType::Option(b)) => xtype_of(*a, *b),
        (XType::Set(a), SType::Set(b)) => a == b,
        (XType::Map(ka, va), SType::Map(kb, vb)) => ka == kb && va == vb,
        (XType::List(a, n), SType::List(b, m)) => a == b && n == m,
        _ => false,
    }
}

pub open spec fn xtypes_of(xs: Seq<XType>, ts: Seq<SType>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        xs.len() == 0
    } else {
        xs.len() == ts.len() && xtypes_of(xs.drop_last(), ts.drop_last()) && xtype_of(xs.last(), ts.last())
    }
}

// ---- 式の値の表現 ----

/// スロットの値の列 `slots` は、式の型 `t` の値 `v` を表す。
/// 空のOptionの中身のスロットは、幅が合えばどの値でもよい。Set、Map、Listは正規形の符号化である。
pub open spec fn models(slots: Seq<Value>, v: SVal, t: XType, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XType::Bool => match v {
            SVal::Bool(b) => slots == seq![Value::Bool(b)],
            _ => false,
        },
        XType::Int => match v {
            SVal::Int(x) => slots == seq![Value::Int(x)],
            _ => false,
        },
        XType::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int] && slots == seq![
                Value::Enum(id, k),
            ],
            _ => false,
        },
        XType::Tuple(ts) => match v {
            SVal::Tuple(vs) => models_seq(slots, vs, ts@, enums),
            _ => false,
        },
        XType::Record(_, ts) => match v {
            SVal::Tuple(vs) => models_seq(slots, vs, ts@, enums),
            _ => false,
        },
        XType::Option(x) => slots.len() == 1 + xwidth(*x, enums) && match v {
            SVal::None => slots[0] == Value::Bool(false),
            SVal::Some(w) => slots[0] == Value::Bool(true) && models(slots.drop_first(), *w, *x, enums),
            _ => false,
        },
        XType::Set(e) => member(v, SType::Set(e), enums) && slots == enc(v, SType::Set(e), enums),
        XType::Map(k, x) => member(v, SType::Map(k, x), enums) && slots == enc(v, SType::Map(k, x), enums),
        XType::List(e, max) => member(v, SType::List(e, max), enums) && slots == enc(
            v,
            SType::List(e, max),
            enums,
        ),
    }
}

/// スロットの列を後ろから要素の幅で区切り、各部分が対応する値を表す。
pub open spec fn models_seq(slots: Seq<Value>, vs: Seq<SVal>, ts: Seq<XType>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        slots.len() == 0 && vs.len() == 0
    } else {
        let w = xwidth(ts.last(), enums);
        let cut = slots.len() - w;
        vs.len() == ts.len() && slots.len() >= w && models_seq(slots.take(cut), vs.drop_last(), ts.drop_last(), enums)
            && models(slots.skip(cut), vs.last(), ts.last(), enums)
    }
}

// ---- 補題 ----

pub proof fn lemma_repeat_len(xs: Seq<Value>, n: nat)
    ensures
        enc_repeat(xs, n).len() == n * xs.len(),
    decreases n,
{
    if n == 0 {
        assert(0 * xs.len() == 0) by (nonlinear_arith);
    } else {
        let m = (n - 1) as nat;
        lemma_repeat_len(xs, m);
        assert(enc_repeat(xs, n) == enc_repeat(xs, m) + xs);
        assert(m * xs.len() + xs.len() == n * xs.len()) by (nonlinear_arith)
            requires
                m + 1 == n,
        ;
    }
}

/// 既定値の符号化の長さは、型の幅である。
pub proof fn lemma_default_len(t: SType, enums: Seq<i64>)
    ensures
        enc(default_val(t, enums), t, enums).len() == width(t, enums),
    decreases t, 1nat,
{
    match t {
        SType::Tuple(ts) => lemma_default_vals_len(ts@, enums),
        SType::Record(_, ts) => lemma_default_vals_len(ts@, enums),
        SType::Option(x) => lemma_default_len(*x, enums),
        SType::Map(k, x) => {
            let n = keys_or_zero(*k, enums);
            lemma_default_len(*x, enums);
            lemma_absent_rows_len(n, *x, enums);
            let rows = default_val(t, enums)->Map_0;
            assert(rows =~= Seq::new(n, |_i: int| None::<SVal>));
        },
        SType::List(e, max) => {
            lemma_default_len(*e, enums);
            lemma_repeat_len(enc(default_val(*e, enums), *e, enums), max as nat);
            assert(enc_items(Seq::<SVal>::empty(), *e, enums).len() == 0);
            assert(enc(default_val(t, enums), t, enums).len() == width(t, enums));
        },
        SType::Set(e) => {
            assert(enc(default_val(t, enums), t, enums).len() == width(t, enums));
        },
        _ => {},
    }
}

proof fn lemma_default_vals_len(ts: Seq<SType>, enums: Seq<i64>)
    ensures
        default_vals(ts, enums).len() == ts.len(),
        enc_seq(default_vals(ts, enums), ts, enums).len() == width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_default_vals_len(ts.drop_last(), enums);
        lemma_default_len(ts.last(), enums);
        let d = default_vals(ts, enums);
        assert(d.drop_last() == default_vals(ts.drop_last(), enums));
    }
}

proof fn lemma_absent_rows_len(n: nat, t: SType, enums: Seq<i64>)
    requires
        enc(default_val(t, enums), t, enums).len() == width(t, enums),
    ensures
        enc_rows(Seq::new(n, |_i: int| None::<SVal>), t, enums).len() == n * (1 + width(t, enums)),
    decreases n,
{
    if n == 0 {
        assert(0 * (1 + width(t, enums)) == 0) by (nonlinear_arith);
    } else {
        let rows = Seq::new(n, |_i: int| None::<SVal>);
        lemma_absent_rows_len((n - 1) as nat, t, enums);
        assert(rows.drop_last() == Seq::new((n - 1) as nat, |_i: int| None::<SVal>));
        assert(rows.last() == None::<SVal>);
        let d = enc(default_val(t, enums), t, enums);
        assert(enc_rows(rows, t, enums) == enc_rows(rows.drop_last(), t, enums) + (seq![Value::Bool(false)] + d));
        let w = 1 + width(t, enums);
        let m = (n - 1) as nat;
        assert(enc_rows(rows.drop_last(), t, enums).len() == m * w);
        assert(m * w + w == n * w) by (nonlinear_arith)
            requires
                m + 1 == n,
        ;
    }
}

/// 正規形の符号化の長さは、型の幅である。
pub proof fn lemma_enc_len(v: SVal, t: SType, enums: Seq<i64>)
    requires
        member(v, t, enums),
    ensures
        enc(v, t, enums).len() == width(t, enums),
    decreases t, 1nat,
{
    match t {
        SType::Tuple(ts) => {
            let vs = v->Tuple_0;
            lemma_enc_seq_len(vs, ts@, enums);
        },
        SType::Record(_, ts) => {
            let vs = v->Tuple_0;
            lemma_enc_seq_len(vs, ts@, enums);
        },
        SType::Option(x) => match v {
            SVal::Some(w) => lemma_enc_len(*w, *x, enums),
            _ => lemma_default_len(*x, enums),
        },
        SType::Map(k, x) => {
            let rows = v->Map_0;
            lemma_enc_rows_len(rows, *x, enums);
        },
        SType::List(e, max) => {
            let items = v->List_0;
            lemma_enc_items_len(items, *e, enums);
            lemma_default_len(*e, enums);
            let w = width(*e, enums);
            lemma_repeat_len(enc(default_val(*e, enums), *e, enums), (max - items.len()) as nat);
            assert(items.len() * w + (max - items.len()) * w == max * w) by (nonlinear_arith)
                requires
                    items.len() <= max,
            ;
        },
        _ => {},
    }
}

proof fn lemma_enc_seq_len(vs: Seq<SVal>, ts: Seq<SType>, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
    ensures
        enc_seq(vs, ts, enums).len() == width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_enc_seq_len(vs.drop_last(), ts.drop_last(), enums);
        lemma_enc_len(vs.last(), ts.last(), enums);
    }
}

proof fn lemma_enc_rows_len(rows: Seq<Option<SVal>>, t: SType, enums: Seq<i64>)
    requires
        map_rows_member(rows, t, enums),
    ensures
        enc_rows(rows, t, enums).len() == rows.len() * (1 + width(t, enums)),
    decreases t, rows.len() + 1,
{
    if rows.len() > 0 {
        lemma_enc_rows_len(rows.drop_last(), t, enums);
        match rows.last() {
            Some(x) => lemma_enc_len(x, t, enums),
            None => lemma_default_len(t, enums),
        }
        let n = rows.len();
        let w = 1 + width(t, enums);
        assert((n - 1) * w + w == n * w) by (nonlinear_arith);
    }
}

proof fn lemma_enc_items_len(items: Seq<SVal>, t: SType, enums: Seq<i64>)
    requires
        list_items_member(items, t, enums),
    ensures
        enc_items(items, t, enums).len() == items.len() * width(t, enums),
    decreases t, items.len() + 1,
{
    if items.len() > 0 {
        lemma_enc_items_len(items.drop_last(), t, enums);
        lemma_enc_len(items.last(), t, enums);
        let n = items.len();
        let w = width(t, enums);
        assert((n - 1) * w + w == n * w) by (nonlinear_arith);
    }
}

/// 整形式の型のキーの型の値は、1つ以上ある。
pub proof fn lemma_keys_pos(t: SType, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        keys(t, enums) is Some,
    ensures
        keys(t, enums)->0 >= 1,
    decreases t, 1nat,
{
    match t {
        SType::Tuple(ts) => lemma_keys_product_pos(ts@, enums),
        SType::Record(_, ts) => lemma_keys_product_pos(ts@, enums),
        _ => {},
    }
}

proof fn lemma_keys_product_pos(ts: Seq<SType>, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
        keys_product(ts, enums) is Some,
    ensures
        keys_product(ts, enums)->0 >= 1,
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_keys_product_pos(ts.drop_last(), enums);
        lemma_keys_pos(ts.last(), enums);
        let p = keys_product(ts.drop_last(), enums)->0;
        let k = keys(ts.last(), enums)->0;
        assert(p * k >= 1) by (nonlinear_arith)
            requires
                p >= 1,
                k >= 1,
        ;
    }
}

/// 整形式の格納の型の幅は1以上である。幅0の値は、評価のエラーをスロットの式に残せない。
pub proof fn lemma_width_pos(t: SType, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
    ensures
        width(t, enums) >= 1,
    decreases t, 1nat,
{
    match t {
        SType::Tuple(ts) => lemma_width_sum_pos(ts@, enums),
        SType::Record(_, ts) => lemma_width_sum_pos(ts@, enums),
        SType::Set(e) => lemma_keys_pos(*e, enums),
        SType::Map(k, x) => {
            lemma_keys_pos(*k, enums);
            let n = keys_or_zero(*k, enums);
            let w = 1 + width(*x, enums);
            assert(n * w >= 1) by (nonlinear_arith)
                requires
                    n >= 1,
                    w >= 1,
            ;
        },
        _ => {},
    }
}

proof fn lemma_width_sum_pos(ts: Seq<SType>, enums: Seq<i64>)
    requires
        ts.len() >= 1,
        wf_stypes(ts, enums),
    ensures
        width_sum(ts, enums) >= 1,
    decreases ts, 0nat,
{
    lemma_width_pos(ts.last(), enums);
}

/// 整形式の式の型の幅は1以上である。
pub proof fn lemma_xwidth_pos(t: XType, enums: Seq<i64>)
    requires
        wf_xtype(t, enums),
    ensures
        xwidth(t, enums) >= 1,
    decreases t, 1nat,
{
    match t {
        XType::Tuple(ts) => {
            assert(wf_xtypes(ts@, enums));
            assert(wf_xtype(ts@.last(), enums));
            lemma_xwidth_pos(ts@.last(), enums);
            assert(xwidth_sum(ts@, enums) == xwidth_sum(ts@.drop_last(), enums) + xwidth(ts@.last(), enums));
            assert(xwidth(t, enums) == xwidth_sum(ts@, enums));
        },
        XType::Record(_, ts) => {
            assert(wf_xtypes(ts@, enums));
            assert(wf_xtype(ts@.last(), enums));
            lemma_xwidth_pos(ts@.last(), enums);
            assert(xwidth_sum(ts@, enums) == xwidth_sum(ts@.drop_last(), enums) + xwidth(ts@.last(), enums));
        },
        XType::Set(e) => lemma_width_pos(SType::Set(e), enums),
        XType::Map(k, x) => lemma_width_pos(SType::Map(k, x), enums),
        XType::List(e, max) => lemma_width_pos(SType::List(e, max), enums),
        _ => {},
    }
}

/// 格納の型とその式の型の幅は等しい。
pub proof fn lemma_xwidth_of(x: XType, t: SType, enums: Seq<i64>)
    requires
        xtype_of(x, t),
    ensures
        xwidth(x, enums) == width(t, enums),
    decreases t, 1nat,
{
    match (x, t) {
        (XType::Tuple(xs), SType::Tuple(ts)) => lemma_xwidths_of(xs@, ts@, enums),
        (XType::Record(_, xs), SType::Record(_, ts)) => lemma_xwidths_of(xs@, ts@, enums),
        (XType::Option(a), SType::Option(b)) => lemma_xwidth_of(*a, *b, enums),
        _ => {},
    }
}

proof fn lemma_xwidths_of(xs: Seq<XType>, ts: Seq<SType>, enums: Seq<i64>)
    requires
        xtypes_of(xs, ts),
    ensures
        xwidth_sum(xs, enums) == width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_xwidths_of(xs.drop_last(), ts.drop_last(), enums);
        lemma_xwidth_of(xs.last(), ts.last(), enums);
    }
}

/// 格納の型に属する値の正規形の符号化は、その式の型で値を表す。
pub proof fn lemma_models_enc(v: SVal, t: SType, x: XType, enums: Seq<i64>)
    requires
        member(v, t, enums),
        xtype_of(x, t),
    ensures
        models(enc(v, t, enums), v, x, enums),
    decreases t, 1nat,
{
    match (x, t) {
        (XType::Tuple(xs), SType::Tuple(ts)) => lemma_models_enc_seq(v->Tuple_0, ts@, xs@, enums),
        (XType::Record(_, xs), SType::Record(_, ts)) => lemma_models_enc_seq(v->Tuple_0, ts@, xs@, enums),
        (XType::Option(a), SType::Option(b)) => {
            lemma_xwidth_of(*a, *b, enums);
            match v {
                SVal::Some(w) => {
                    lemma_enc_len(*w, *b, enums);
                    lemma_models_enc(*w, *b, *a, enums);
                    let s = enc(v, t, enums);
                    assert(s.drop_first() == enc(*w, *b, enums));
                },
                _ => lemma_default_len(*b, enums),
            }
        },
        _ => {},
    }
}

proof fn lemma_models_enc_seq(vs: Seq<SVal>, ts: Seq<SType>, xs: Seq<XType>, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
        xtypes_of(xs, ts),
    ensures
        models_seq(enc_seq(vs, ts, enums), vs, xs, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let prefix = enc_seq(vs.drop_last(), ts.drop_last(), enums);
        let last = enc(vs.last(), ts.last(), enums);
        lemma_models_enc_seq(vs.drop_last(), ts.drop_last(), xs.drop_last(), enums);
        lemma_models_enc(vs.last(), ts.last(), xs.last(), enums);
        lemma_enc_len(vs.last(), ts.last(), enums);
        lemma_xwidth_of(xs.last(), ts.last(), enums);
        let s = enc_seq(vs, ts, enums);
        assert(s.take(prefix.len() as int) == prefix);
        assert(s.skip(prefix.len() as int) == last);
    }
}

} // verus!
