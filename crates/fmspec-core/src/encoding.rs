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
//! - **格納の型** [`STy`]：状態変数、引数、Setの要素、Mapのキーと値、Listの要素の型。整数は範囲を持つ。
//!   格納の型の値は正規形で、符号化は関数 [`enc`] である。
//!   正規形では、空のOptionの中身、Mapにないキーの値、Listの長さより後ろの要素が既定値になる。
//! - **式の型** [`XTy`]：式の値の型。式の中間結果の整数は範囲を持たない。
//!   空のOptionの中身のスロットは既定値とは限らないので、スロットの列が値を表すことを関係 [`models`] で定める。
//!
//! Recordの値は、フィールドを宣言の順に並べたTupleの値で表す。フィールドの名前は、名前の番号で型に持つ。

#[cfg(verus_keep_ghost)]
use crate::model::Value;
use vstd::prelude::*;

verus! {

/// キーの型が取れる値の数の上限。
pub const MAX_KEYS: u64 = 4096;

/// 格納の型（仕様）。
pub enum STy {
    Bool,
    /// 閉区間 `min..=max` の整数。
    Int(i64, i64),
    /// 列挙型。列挙型の添字で指す。
    Enum(usize),
    Tuple(Seq<STy>),
    /// フィールドの名前の番号と、フィールドの型。
    Record(Seq<usize>, Seq<STy>),
    Option(Box<STy>),
    Set(Box<STy>),
    /// キーの型と値の型。
    Map(Box<STy>, Box<STy>),
    /// 要素の型と、長さの上限。
    List(Box<STy>, usize),
}

/// 式の型（仕様）。
pub enum XTy {
    Bool,
    Int,
    Enum(usize),
    Tuple(Seq<XTy>),
    Record(Seq<usize>, Seq<XTy>),
    Option(Box<XTy>),
    Set(Box<STy>),
    Map(Box<STy>, Box<STy>),
    List(Box<STy>, usize),
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

/// 格納の型（実行時の表現）。仕様の型は [`sty`] で得る。
pub enum SType {
    Bool,
    Int(i64, i64),
    Enum(usize),
    Tuple(Vec<SType>),
    Record(Vec<usize>, Vec<SType>),
    Option(Box<SType>),
    Set(Box<SType>),
    Map(Box<SType>, Box<SType>),
    List(Box<SType>, usize),
}

/// 式の型（実行時の表現）。仕様の型は [`xty`] で得る。
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

pub open spec fn sty(t: SType) -> STy
    decreases t, 0nat,
{
    match t {
        SType::Bool => STy::Bool,
        SType::Int(lo, hi) => STy::Int(lo, hi),
        SType::Enum(id) => STy::Enum(id),
        SType::Tuple(ts) => STy::Tuple(stys(ts@)),
        SType::Record(names, ts) => STy::Record(names@, stys(ts@)),
        SType::Option(x) => STy::Option(Box::new(sty(*x))),
        SType::Set(e) => STy::Set(Box::new(sty(*e))),
        SType::Map(k, v) => STy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
        SType::List(e, max) => STy::List(Box::new(sty(*e)), max),
    }
}

pub open spec fn stys(ts: Seq<SType>) -> Seq<STy>
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        stys(ts.drop_last()).push(sty(ts.last()))
    }
}

pub open spec fn xty(t: XType) -> XTy
    decreases t, 0nat,
{
    match t {
        XType::Bool => XTy::Bool,
        XType::Int => XTy::Int,
        XType::Enum(id) => XTy::Enum(id),
        XType::Tuple(ts) => XTy::Tuple(xtys(ts@)),
        XType::Record(names, ts) => XTy::Record(names@, xtys(ts@)),
        XType::Option(x) => XTy::Option(Box::new(xty(*x))),
        XType::Set(e) => XTy::Set(Box::new(sty(*e))),
        XType::Map(k, v) => XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))),
        XType::List(e, max) => XTy::List(Box::new(sty(*e)), max),
    }
}

pub open spec fn xtys(ts: Seq<XType>) -> Seq<XTy>
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        xtys(ts.drop_last()).push(xty(ts.last()))
    }
}

// ---- 型の大きさ ----

/// キーの型の値の数。キーの型でないか、`MAX_KEYS` を超えるなら `None`。
/// `enums` は各列挙型のラベルの数。
pub open spec fn keys(t: STy, enums: Seq<i64>) -> Option<nat>
    decreases t,
{
    let n: Option<nat> = match t {
        STy::Bool => Some(2),
        STy::Int(lo, hi) => if lo <= hi && hi - lo + 1 <= MAX_KEYS {
            Some((hi - lo + 1) as nat)
        } else {
            None
        },
        STy::Enum(id) => if id < enums.len() && enums[id as int] >= 0 {
            Some(enums[id as int] as nat)
        } else {
            None
        },
        STy::Tuple(ts) => keys_product(ts, enums),
        STy::Record(_, ts) => keys_product(ts, enums),
        STy::Option(x) => match keys(*x, enums) {
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
pub open spec fn keys_product(ts: Seq<STy>, enums: Seq<i64>) -> Option<nat>
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
pub open spec fn width(t: STy, enums: Seq<i64>) -> nat
    decreases t,
{
    match t {
        STy::Bool | STy::Int(_, _) | STy::Enum(_) => 1,
        STy::Tuple(ts) => width_sum(ts, enums),
        STy::Record(_, ts) => width_sum(ts, enums),
        STy::Option(x) => 1 + width(*x, enums),
        STy::Set(e) => keys_or_zero(*e, enums),
        STy::Map(k, v) => keys_or_zero(*k, enums) * (1 + width(*v, enums)),
        STy::List(e, max) => 1 + (max as nat) * width(*e, enums),
    }
}

pub open spec fn width_sum(ts: Seq<STy>, enums: Seq<i64>) -> nat
    decreases ts,
{
    if ts.len() == 0 {
        0
    } else {
        width_sum(ts.drop_last(), enums) + width(ts.last(), enums)
    }
}

pub open spec fn keys_or_zero(t: STy, enums: Seq<i64>) -> nat {
    match keys(t, enums) {
        Some(k) => k,
        None => 0,
    }
}

/// 式の型のスロット数。
pub open spec fn xwidth(t: XTy, enums: Seq<i64>) -> nat
    decreases t,
{
    match t {
        XTy::Bool | XTy::Int | XTy::Enum(_) => 1,
        XTy::Tuple(ts) => xwidth_sum(ts, enums),
        XTy::Record(_, ts) => xwidth_sum(ts, enums),
        XTy::Option(x) => 1 + xwidth(*x, enums),
        XTy::Set(e) => keys_or_zero(*e, enums),
        XTy::Map(k, v) => keys_or_zero(*k, enums) * (1 + width(*v, enums)),
        XTy::List(e, max) => 1 + (max as nat) * width(*e, enums),
    }
}

pub open spec fn xwidth_sum(ts: Seq<XTy>, enums: Seq<i64>) -> nat
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
pub open spec fn wf_stype(t: STy, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        STy::Bool => true,
        STy::Int(lo, hi) => lo <= hi,
        STy::Enum(id) => id < enums.len() && enums[id as int] >= 1,
        STy::Tuple(ts) => ts.len() >= 1 && wf_stypes(ts, enums),
        STy::Record(names, ts) => ts.len() >= 1 && names.len() == ts.len() && names.no_duplicates()
            && wf_stypes(ts, enums),
        STy::Option(x) => wf_stype(*x, enums),
        STy::Set(e) => wf_stype(*e, enums) && keys(*e, enums) is Some,
        STy::Map(k, v) => wf_stype(*k, enums) && keys(*k, enums) is Some && wf_stype(*v, enums),
        STy::List(e, _) => wf_stype(*e, enums),
    }
}

pub open spec fn wf_stypes(ts: Seq<STy>, enums: Seq<i64>) -> bool
    decreases ts,
{
    if ts.len() == 0 {
        true
    } else {
        wf_stypes(ts.drop_last(), enums) && wf_stype(ts.last(), enums)
    }
}

/// 整形式の式の型。
pub open spec fn wf_xtype(t: XTy, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XTy::Bool | XTy::Int => true,
        XTy::Enum(id) => id < enums.len() && enums[id as int] >= 1,
        XTy::Tuple(ts) => ts.len() >= 1 && wf_xtypes(ts, enums),
        XTy::Record(names, ts) => ts.len() >= 1 && names.len() == ts.len() && names.no_duplicates()
            && wf_xtypes(ts, enums),
        XTy::Option(x) => wf_xtype(*x, enums),
        XTy::Set(e) => wf_stype(STy::Set(e), enums),
        XTy::Map(k, v) => wf_stype(STy::Map(k, v), enums),
        XTy::List(e, max) => wf_stype(STy::List(e, max), enums),
    }
}

pub open spec fn wf_xtypes(ts: Seq<XTy>, enums: Seq<i64>) -> bool
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
pub open spec fn member(v: SVal, t: STy, enums: Seq<i64>) -> bool
    decreases t, 0nat,
{
    match t {
        STy::Bool => v is Bool,
        STy::Int(lo, hi) => match v {
            SVal::Int(x) => lo <= x && x <= hi,
            _ => false,
        },
        STy::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int],
            _ => false,
        },
        STy::Tuple(ts) => match v {
            SVal::Tuple(vs) => members(vs, ts, enums),
            _ => false,
        },
        STy::Record(_, ts) => match v {
            SVal::Tuple(vs) => members(vs, ts, enums),
            _ => false,
        },
        STy::Option(x) => match v {
            SVal::None => true,
            SVal::Some(w) => member(*w, *x, enums),
            _ => false,
        },
        STy::Set(e) => match v {
            SVal::Set(bits) => keys(*e, enums) == Some(bits.len()),
            _ => false,
        },
        STy::Map(k, x) => match v {
            SVal::Map(rows) => keys(*k, enums) == Some(rows.len()) && map_rows_member(rows, *x, enums),
            _ => false,
        },
        STy::List(e, max) => match v {
            SVal::List(items) => items.len() <= max && list_items_member(items, *e, enums),
            _ => false,
        },
    }
}

/// 値の列 `vs` の各値が、型の列 `ts` の対応する型に属する。
pub open spec fn members(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>) -> bool
    decreases ts, 0nat,
{
    if ts.len() == 0 {
        vs.len() == 0
    } else {
        vs.len() == ts.len() && members(vs.drop_last(), ts.drop_last(), enums) && member(vs.last(), ts.last(), enums)
    }
}

pub open spec fn map_rows_member(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>) -> bool
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

pub open spec fn list_items_member(items: Seq<SVal>, t: STy, enums: Seq<i64>) -> bool
    decreases t, items.len(),
{
    if items.len() == 0 {
        true
    } else {
        list_items_member(items.drop_last(), t, enums) && member(items.last(), t, enums)
    }
}

/// 値 `v` が式の型 `t` を持つ。整数の範囲は問わない。Set、Map、Listの値は格納の型に属する。
pub open spec fn has_xtype(v: SVal, t: XTy, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XTy::Bool => v is Bool,
        XTy::Int => v is Int,
        XTy::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int],
            _ => false,
        },
        XTy::Tuple(ts) => match v {
            SVal::Tuple(vs) => has_xtypes(vs, ts, enums),
            _ => false,
        },
        XTy::Record(_, ts) => match v {
            SVal::Tuple(vs) => has_xtypes(vs, ts, enums),
            _ => false,
        },
        XTy::Option(x) => match v {
            SVal::None => true,
            SVal::Some(w) => has_xtype(*w, *x, enums),
            _ => false,
        },
        XTy::Set(e) => member(v, STy::Set(e), enums),
        XTy::Map(k, x) => member(v, STy::Map(k, x), enums),
        XTy::List(e, max) => member(v, STy::List(e, max), enums),
    }
}

pub open spec fn has_xtypes(vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>) -> bool
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
pub open spec fn default_val(t: STy, enums: Seq<i64>) -> SVal
    decreases t,
{
    match t {
        STy::Bool => SVal::Bool(false),
        STy::Int(lo, _) => SVal::Int(lo),
        STy::Enum(id) => SVal::Enum(id, 0),
        STy::Tuple(ts) => SVal::Tuple(default_vals(ts, enums)),
        STy::Record(_, ts) => SVal::Tuple(default_vals(ts, enums)),
        STy::Option(_) => SVal::None,
        STy::Set(e) => SVal::Set(Seq::new(keys_or_zero(*e, enums), |_i: int| false)),
        STy::Map(k, _) => SVal::Map(Seq::new(keys_or_zero(*k, enums), |_i: int| None)),
        STy::List(_, _) => SVal::List(Seq::empty()),
    }
}

pub open spec fn default_vals(ts: Seq<STy>, enums: Seq<i64>) -> Seq<SVal>
    decreases ts,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        default_vals(ts.drop_last(), enums).push(default_val(ts.last(), enums))
    }
}

/// 格納の型の値の符号化（正規形）。
pub open spec fn enc(v: SVal, t: STy, enums: Seq<i64>) -> Seq<Value>
    decreases t, 0nat,
{
    match t {
        STy::Bool => match v {
            SVal::Bool(b) => seq![Value::Bool(b)],
            _ => seq![Value::Bool(false)],
        },
        STy::Int(lo, _) => match v {
            SVal::Int(x) => seq![Value::Int(x)],
            _ => seq![Value::Int(lo)],
        },
        STy::Enum(id) => match v {
            SVal::Enum(_, k) => seq![Value::Enum(id, k)],
            _ => seq![Value::Enum(id, 0)],
        },
        STy::Tuple(ts) => match v {
            SVal::Tuple(vs) => enc_seq(vs, ts, enums),
            _ => Seq::empty(),
        },
        STy::Record(_, ts) => match v {
            SVal::Tuple(vs) => enc_seq(vs, ts, enums),
            _ => Seq::empty(),
        },
        STy::Option(x) => match v {
            SVal::Some(w) => seq![Value::Bool(true)] + enc(*w, *x, enums),
            _ => seq![Value::Bool(false)] + enc(default_val(*x, enums), *x, enums),
        },
        STy::Set(_) => match v {
            SVal::Set(bits) => Seq::new(bits.len(), |i: int| Value::Bool(bits[i])),
            _ => Seq::empty(),
        },
        STy::Map(_, x) => match v {
            SVal::Map(rows) => enc_rows(rows, *x, enums),
            _ => Seq::empty(),
        },
        STy::List(e, max) => match v {
            SVal::List(items) => seq![Value::Int(items.len() as i64)] + enc_items(items, *e, enums) + enc_repeat(
                enc(default_val(*e, enums), *e, enums),
                (max - items.len()) as nat,
            ),
            _ => Seq::empty(),
        },
    }
}

/// 値の列を、対応する型で符号化して順につなげる。
pub open spec fn enc_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>) -> Seq<Value>
    decreases ts, 0nat,
{
    if ts.len() == 0 || vs.len() == 0 {
        Seq::empty()
    } else {
        enc_seq(vs.drop_last(), ts.drop_last(), enums) + enc(vs.last(), ts.last(), enums)
    }
}

/// Mapの行を順につなげる。行は、有無のBoolと値のスロットである。ない行の値は既定値。
pub open spec fn enc_rows(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>) -> Seq<Value>
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
pub open spec fn enc_items(items: Seq<SVal>, t: STy, enums: Seq<i64>) -> Seq<Value>
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

/// 格納の型 `t` の式の型。整数の範囲を落とし、Set、Map、Listの中の型はそのまま持つ。
pub open spec fn to_xty(t: STy) -> XTy
    decreases t, 0nat,
{
    match t {
        STy::Bool => XTy::Bool,
        STy::Int(_, _) => XTy::Int,
        STy::Enum(id) => XTy::Enum(id),
        STy::Tuple(ts) => XTy::Tuple(to_xtys(ts)),
        STy::Record(names, ts) => XTy::Record(names, to_xtys(ts)),
        STy::Option(x) => XTy::Option(Box::new(to_xty(*x))),
        STy::Set(e) => XTy::Set(e),
        STy::Map(k, v) => XTy::Map(k, v),
        STy::List(e, max) => XTy::List(e, max),
    }
}

pub open spec fn to_xtys(ts: Seq<STy>) -> Seq<XTy>
    decreases ts, 1nat,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        to_xtys(ts.drop_last()).push(to_xty(ts.last()))
    }
}

// ---- 式の値の表現 ----

/// スロットの値の列 `slots` は、式の型 `t` の値 `v` を表す。
/// 空のOptionの中身のスロットは、幅が合えばどの値でもよい。Set、Map、Listは正規形の符号化である。
pub open spec fn models(slots: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>) -> bool
    decreases t,
{
    match t {
        XTy::Bool => match v {
            SVal::Bool(b) => slots == seq![Value::Bool(b)],
            _ => false,
        },
        XTy::Int => match v {
            SVal::Int(x) => slots == seq![Value::Int(x)],
            _ => false,
        },
        XTy::Enum(id) => match v {
            SVal::Enum(j, k) => j == id && id < enums.len() && 0 <= k < enums[id as int] && slots == seq![
                Value::Enum(id, k),
            ],
            _ => false,
        },
        XTy::Tuple(ts) => match v {
            SVal::Tuple(vs) => models_seq(slots, vs, ts, enums),
            _ => false,
        },
        XTy::Record(_, ts) => match v {
            SVal::Tuple(vs) => models_seq(slots, vs, ts, enums),
            _ => false,
        },
        XTy::Option(x) => slots.len() == 1 + xwidth(*x, enums) && match v {
            SVal::None => slots[0] == Value::Bool(false),
            SVal::Some(w) => slots[0] == Value::Bool(true) && models(slots.drop_first(), *w, *x, enums),
            _ => false,
        },
        XTy::Set(e) => member(v, STy::Set(e), enums) && slots == enc(v, STy::Set(e), enums),
        XTy::Map(k, x) => member(v, STy::Map(k, x), enums) && slots == enc(v, STy::Map(k, x), enums),
        XTy::List(e, max) => member(v, STy::List(e, max), enums) && slots == enc(
            v,
            STy::List(e, max),
            enums,
        ),
    }
}

/// スロットの列を後ろから要素の幅で区切り、各部分が対応する値を表す。
pub open spec fn models_seq(slots: Seq<Value>, vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>) -> bool
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
pub proof fn lemma_default_len(t: STy, enums: Seq<i64>)
    ensures
        enc(default_val(t, enums), t, enums).len() == width(t, enums),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_default_vals_len(ts, enums),
        STy::Record(_, ts) => lemma_default_vals_len(ts, enums),
        STy::Option(x) => lemma_default_len(*x, enums),
        STy::Map(k, x) => {
            let n = keys_or_zero(*k, enums);
            lemma_default_len(*x, enums);
            lemma_absent_rows_len(n, *x, enums);
            let rows = default_val(t, enums)->Map_0;
            assert(rows =~= Seq::new(n, |_i: int| None::<SVal>));
        },
        STy::List(e, max) => {
            lemma_default_len(*e, enums);
            lemma_repeat_len(enc(default_val(*e, enums), *e, enums), max as nat);
            assert(enc_items(Seq::<SVal>::empty(), *e, enums).len() == 0);
            assert(enc(default_val(t, enums), t, enums).len() == width(t, enums));
        },
        STy::Set(e) => {
            assert(enc(default_val(t, enums), t, enums).len() == width(t, enums));
        },
        _ => {},
    }
}

proof fn lemma_default_vals_len(ts: Seq<STy>, enums: Seq<i64>)
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

proof fn lemma_absent_rows_len(n: nat, t: STy, enums: Seq<i64>)
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
pub proof fn lemma_enc_len(v: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v, t, enums),
    ensures
        enc(v, t, enums).len() == width(t, enums),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => {
            let vs = v->Tuple_0;
            lemma_enc_seq_len(vs, ts, enums);
        },
        STy::Record(_, ts) => {
            let vs = v->Tuple_0;
            lemma_enc_seq_len(vs, ts, enums);
        },
        STy::Option(x) => match v {
            SVal::Some(w) => lemma_enc_len(*w, *x, enums),
            _ => lemma_default_len(*x, enums),
        },
        STy::Map(k, x) => {
            let rows = v->Map_0;
            lemma_enc_rows_len(rows, *x, enums);
        },
        STy::List(e, max) => {
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

proof fn lemma_enc_seq_len(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
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

proof fn lemma_enc_rows_len(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>)
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

proof fn lemma_enc_items_len(items: Seq<SVal>, t: STy, enums: Seq<i64>)
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
pub proof fn lemma_keys_pos(t: STy, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        keys(t, enums) is Some,
    ensures
        keys(t, enums)->0 >= 1,
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_keys_product_pos(ts, enums),
        STy::Record(_, ts) => lemma_keys_product_pos(ts, enums),
        _ => {},
    }
}

proof fn lemma_keys_product_pos(ts: Seq<STy>, enums: Seq<i64>)
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
pub proof fn lemma_width_pos(t: STy, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
    ensures
        width(t, enums) >= 1,
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_width_sum_pos(ts, enums),
        STy::Record(_, ts) => lemma_width_sum_pos(ts, enums),
        STy::Set(e) => lemma_keys_pos(*e, enums),
        STy::Map(k, x) => {
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

proof fn lemma_width_sum_pos(ts: Seq<STy>, enums: Seq<i64>)
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
pub proof fn lemma_xwidth_pos(t: XTy, enums: Seq<i64>)
    requires
        wf_xtype(t, enums),
    ensures
        xwidth(t, enums) >= 1,
    decreases t, 1nat,
{
    match t {
        XTy::Tuple(ts) => {
            assert(wf_xtypes(ts, enums));
            assert(wf_xtype(ts.last(), enums));
            lemma_xwidth_pos(ts.last(), enums);
            assert(xwidth_sum(ts, enums) == xwidth_sum(ts.drop_last(), enums) + xwidth(ts.last(), enums));
            assert(xwidth(t, enums) == xwidth_sum(ts, enums));
        },
        XTy::Record(_, ts) => {
            assert(wf_xtypes(ts, enums));
            assert(wf_xtype(ts.last(), enums));
            lemma_xwidth_pos(ts.last(), enums);
            assert(xwidth_sum(ts, enums) == xwidth_sum(ts.drop_last(), enums) + xwidth(ts.last(), enums));
        },
        XTy::Set(e) => lemma_width_pos(STy::Set(e), enums),
        XTy::Map(k, x) => lemma_width_pos(STy::Map(k, x), enums),
        XTy::List(e, max) => lemma_width_pos(STy::List(e, max), enums),
        _ => {},
    }
}

/// 格納の型とその式の型の幅は等しい。
pub proof fn lemma_xwidth_of(t: STy, enums: Seq<i64>)
    ensures
        xwidth(to_xty(t), enums) == width(t, enums),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_xwidths_of(ts, enums),
        STy::Record(_, ts) => lemma_xwidths_of(ts, enums),
        STy::Option(b) => lemma_xwidth_of(*b, enums),
        _ => {},
    }
}

proof fn lemma_xwidths_of(ts: Seq<STy>, enums: Seq<i64>)
    ensures
        to_xtys(ts).len() == ts.len(),
        xwidth_sum(to_xtys(ts), enums) == width_sum(ts, enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        lemma_xwidths_of(ts.drop_last(), enums);
        lemma_xwidth_of(ts.last(), enums);
        let xs = to_xtys(ts);
        assert(xs.drop_last() == to_xtys(ts.drop_last()));
    }
}

/// 格納の型に属する値の正規形の符号化は、その式の型で値を表す。
pub proof fn lemma_models_enc(v: SVal, t: STy, enums: Seq<i64>)
    requires
        member(v, t, enums),
    ensures
        models(enc(v, t, enums), v, to_xty(t), enums),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_models_enc_seq(v->Tuple_0, ts, enums),
        STy::Record(_, ts) => lemma_models_enc_seq(v->Tuple_0, ts, enums),
        STy::Option(b) => {
            lemma_xwidth_of(*b, enums);
            match v {
                SVal::Some(w) => {
                    lemma_enc_len(*w, *b, enums);
                    lemma_models_enc(*w, *b, enums);
                    let s = enc(v, t, enums);
                    assert(s.drop_first() == enc(*w, *b, enums));
                },
                _ => lemma_default_len(*b, enums),
            }
        },
        _ => {},
    }
}

proof fn lemma_models_enc_seq(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        members(vs, ts, enums),
    ensures
        models_seq(enc_seq(vs, ts, enums), vs, to_xtys(ts), enums),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let prefix = enc_seq(vs.drop_last(), ts.drop_last(), enums);
        let last = enc(vs.last(), ts.last(), enums);
        lemma_models_enc_seq(vs.drop_last(), ts.drop_last(), enums);
        lemma_models_enc(vs.last(), ts.last(), enums);
        lemma_enc_len(vs.last(), ts.last(), enums);
        lemma_xwidth_of(ts.last(), enums);
        lemma_xwidths_of(ts, enums);
        let xs = to_xtys(ts);
        assert(xs.drop_last() == to_xtys(ts.drop_last()));
        let s = enc_seq(vs, ts, enums);
        assert(s.take(prefix.len() as int) == prefix);
        assert(s.skip(prefix.len() as int) == last);
    }
}


// ---- 実行時の型の操作 ----

pub proof fn lemma_stys(ts: Seq<SType>)
    ensures
        stys(ts).len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] stys(ts)[i] == sty(ts[i]),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_stys(ts.drop_last());
    }
}

pub proof fn lemma_xtys(ts: Seq<XType>)
    ensures
        xtys(ts).len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] xtys(ts)[i] == xty(ts[i]),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_xtys(ts.drop_last());
    }
}

pub proof fn lemma_to_xtys(ts: Seq<STy>)
    ensures
        to_xtys(ts).len() == ts.len(),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] to_xtys(ts)[i] == to_xty(ts[i]),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_to_xtys(ts.drop_last());
    }
}

/// 2つの列の各要素の仕様の型が等しければ、列の仕様の型も等しい。
pub proof fn lemma_stys_ext(a: Seq<SType>, b: Seq<SType>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> sty(#[trigger] a[i]) == sty(b[i]),
    ensures
        stys(a) == stys(b),
{
    lemma_stys(a);
    lemma_stys(b);
    assert(stys(a) =~= stys(b));
}

pub proof fn lemma_xtys_ext(a: Seq<XType>, b: Seq<XType>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> xty(#[trigger] a[i]) == xty(b[i]),
    ensures
        xtys(a) == xtys(b),
{
    lemma_xtys(a);
    lemma_xtys(b);
    assert(xtys(a) =~= xtys(b));
}

/// 列の各要素が整形式なら、列は整形式である。
pub proof fn lemma_wf_stypes(ts: Seq<STy>, enums: Seq<i64>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> wf_stype(#[trigger] ts[i], enums),
    ensures
        wf_stypes(ts, enums),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_wf_stypes(ts.drop_last(), enums);
    }
}

pub fn copy_stype(t: &SType) -> (r: SType)
    ensures
        sty(r) == sty(*t),
    decreases t,
{
    match t {
        SType::Bool => SType::Bool,
        SType::Int(lo, hi) => SType::Int(*lo, *hi),
        SType::Enum(id) => SType::Enum(*id),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            SType::Tuple(copy_stypes(t, ts))
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            SType::Record(names.clone(), copy_stypes(t, ts))
        },
        SType::Option(x) => SType::Option(Box::new(copy_stype(x))),
        SType::Set(e) => SType::Set(Box::new(copy_stype(e))),
        SType::Map(k, v) => SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        SType::List(e, max) => SType::List(Box::new(copy_stype(e)), *max),
    }
}

fn copy_stypes(_parent: &SType, ts: &Vec<SType>) -> (r: Vec<SType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        stys(r@) == stys(ts@),
    decreases _parent, 0nat,
{
    let mut out: Vec<SType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> sty(#[trigger] out@[j]) == sty(ts@[j]),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(copy_stype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_stys_ext(out@, ts@);
    }
    out
}

/// 格納の型の式の型。
pub fn to_xtype(t: &SType) -> (r: XType)
    ensures
        xty(r) == to_xty(sty(*t)),
    decreases t,
{
    match t {
        SType::Bool => XType::Bool,
        SType::Int(_, _) => XType::Int,
        SType::Enum(id) => XType::Enum(*id),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Tuple(to_xtypes(t, ts))
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Record(names.clone(), to_xtypes(t, ts))
        },
        SType::Option(x) => XType::Option(Box::new(to_xtype(x))),
        SType::Set(e) => XType::Set(Box::new(copy_stype(e))),
        SType::Map(k, v) => XType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        SType::List(e, max) => XType::List(Box::new(copy_stype(e)), *max),
    }
}

fn to_xtypes(_parent: &SType, ts: &Vec<SType>) -> (r: Vec<XType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        xtys(r@) == to_xtys(stys(ts@)),
    decreases _parent, 0nat,
{
    let mut out: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> xty(#[trigger] out@[j]) == to_xty(sty(ts@[j])),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(to_xtype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_xtys(out@);
        lemma_stys(ts@);
        lemma_to_xtys(stys(ts@));
        assert(xtys(out@) =~= to_xtys(stys(ts@)));
    }
    out
}

pub fn copy_xtype(t: &XType) -> (r: XType)
    ensures
        xty(r) == xty(*t),
    decreases t,
{
    match t {
        XType::Bool => XType::Bool,
        XType::Int => XType::Int,
        XType::Enum(id) => XType::Enum(*id),
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Tuple(copy_xtypes(t, ts))
        },
        XType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Record(names.clone(), copy_xtypes(t, ts))
        },
        XType::Option(x) => XType::Option(Box::new(copy_xtype(x))),
        XType::Set(e) => XType::Set(Box::new(copy_stype(e))),
        XType::Map(k, v) => XType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        XType::List(e, max) => XType::List(Box::new(copy_stype(e)), *max),
    }
}

fn copy_xtypes(_parent: &XType, ts: &Vec<XType>) -> (r: Vec<XType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        xtys(r@) == xtys(ts@),
    decreases _parent, 0nat,
{
    let mut out: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> xty(#[trigger] out@[j]) == xty(ts@[j]),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(copy_xtype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_xtys_ext(out@, ts@);
    }
    out
}

pub fn usizes_eq(a: &Vec<usize>, b: &Vec<usize>) -> (r: bool)
    ensures
        r ==> a@ == b@,
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// 2つの格納の型が等しいかを判定する。真なら仕様の型が等しい。
pub fn stype_eq(a: &SType, b: &SType) -> (r: bool)
    ensures
        r ==> sty(*a) == sty(*b),
    decreases a,
{
    match (a, b) {
        (SType::Bool, SType::Bool) => true,
        (SType::Int(l1, h1), SType::Int(l2, h2)) => *l1 == *l2 && *h1 == *h2,
        (SType::Enum(x), SType::Enum(y)) => *x == *y,
        (SType::Tuple(xs), SType::Tuple(ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            stypes_eq(a, xs, ys)
        },
        (SType::Record(m, xs), SType::Record(n, ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            usizes_eq(m, n) && stypes_eq(a, xs, ys)
        },
        (SType::Option(x), SType::Option(y)) => stype_eq(x, y),
        (SType::Set(x), SType::Set(y)) => stype_eq(x, y),
        (SType::Map(k1, v1), SType::Map(k2, v2)) => stype_eq(k1, k2) && stype_eq(v1, v2),
        (SType::List(x, m), SType::List(y, n)) => *m == *n && stype_eq(x, y),
        _ => false,
    }
}

fn stypes_eq(_parent: &SType, xs: &Vec<SType>, ys: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r ==> stys(xs@) == stys(ys@),
    decreases _parent, 0nat,
{
    if xs.len() != ys.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ys.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> sty(#[trigger] xs@[j]) == sty(ys@[j]),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !stype_eq(&xs[i], &ys[i]) {
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys_ext(xs@, ys@);
    }
    true
}

/// 2つの式の型が等しいかを判定する。真なら仕様の型が等しい。
pub fn xtype_eq(a: &XType, b: &XType) -> (r: bool)
    ensures
        r ==> xty(*a) == xty(*b),
    decreases a,
{
    match (a, b) {
        (XType::Bool, XType::Bool) => true,
        (XType::Int, XType::Int) => true,
        (XType::Enum(x), XType::Enum(y)) => *x == *y,
        (XType::Tuple(xs), XType::Tuple(ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            xtypes_eq(a, xs, ys)
        },
        (XType::Record(m, xs), XType::Record(n, ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            usizes_eq(m, n) && xtypes_eq(a, xs, ys)
        },
        (XType::Option(x), XType::Option(y)) => xtype_eq(x, y),
        (XType::Set(x), XType::Set(y)) => stype_eq(x, y),
        (XType::Map(k1, v1), XType::Map(k2, v2)) => stype_eq(k1, k2) && stype_eq(v1, v2),
        (XType::List(x, m), XType::List(y, n)) => *m == *n && stype_eq(x, y),
        _ => false,
    }
}

fn xtypes_eq(_parent: &XType, xs: &Vec<XType>, ys: &Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r ==> xtys(xs@) == xtys(ys@),
    decreases _parent, 0nat,
{
    if xs.len() != ys.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ys.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> xty(#[trigger] xs@[j]) == xty(ys@[j]),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !xtype_eq(&xs[i], &ys[i]) {
            return false;
        }
        i += 1;
    }
    proof {
        lemma_xtys_ext(xs@, ys@);
    }
    true
}


/// キーの型の値の数。
pub fn keys_exec(t: &SType, enums: &Vec<i64>) -> (r: Option<u64>)
    ensures
        match r {
            Some(k) => keys(sty(*t), enums@) == Some(k as nat),
            None => keys(sty(*t), enums@) is None,
        },
    decreases t,
{
    let n: Option<u64> = match t {
        SType::Bool => Some(2),
        SType::Int(lo, hi) => {
            let d = (*hi as i128) - (*lo as i128) + 1;
            if *lo <= *hi && d <= MAX_KEYS as i128 {
                Some(d as u64)
            } else {
                None
            }
        },
        SType::Enum(id) => if *id < enums.len() && enums[*id] >= 0 {
            Some(enums[*id] as u64)
        } else {
            None
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            keys_product_exec(t, ts, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            keys_product_exec(t, ts, enums)
        },
        SType::Option(x) => match keys_exec(x, enums) {
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

fn keys_product_exec(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Option<u64>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        match r {
            Some(k) => keys_product(stys(ts@), enums@) == Some(k as nat) && k <= MAX_KEYS,
            None => keys_product(stys(ts@), enums@) is None,
        },
    decreases _parent, 0nat,
{
    let ghost ss = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(ss.take(0) =~= Seq::<STy>::empty());
    }
    let mut acc: Option<u64> = Some(1);
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            ss == stys(ts@),
            ss.len() == ts.len(),
            forall|j: int| 0 <= j < ts.len() ==> #[trigger] ss[j] == sty(ts@[j]),
            i <= ts.len(),
            match acc {
                Some(p) => keys_product(ss.take(i as int), enums@) == Some(p as nat) && p <= MAX_KEYS,
                None => keys_product(ss.take(i as int), enums@) is None,
            },
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            assert(ss.take(i + 1).drop_last() =~= ss.take(i as int));
            assert(ss.take(i + 1).last() == ss[i as int]);
        }
        acc = match acc {
            Some(p) => match keys_exec(&ts[i], enums) {
                Some(k) => {
                    proof {
                        assert(k <= MAX_KEYS);
                        assert(p * k <= MAX_KEYS * MAX_KEYS) by (nonlinear_arith)
                            requires
                                p <= MAX_KEYS,
                                k <= MAX_KEYS,
                        ;
                    }
                    if p * k <= MAX_KEYS {
                        Some(p * k)
                    } else {
                        None
                    }
                },
                None => None,
            },
            None => None,
        };
        i += 1;
    }
    proof {
        assert(ss.take(ts.len() as int) =~= ss);
    }
    acc
}

/// 名前の番号に重複がないかを判定する。真なら重複がない。
pub fn distinct_names(names: &Vec<usize>) -> (r: bool)
    ensures
        r ==> names@.no_duplicates(),
{
    let mut i = 0;
    while i < names.len()
        invariant
            i <= names.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> names@[a] != names@[b],
        decreases names.len() - i,
    {
        let mut j = 0;
        while j < i
            invariant
                i < names.len(),
                j <= i,
                forall|a: int, b: int| 0 <= a < b < i ==> names@[a] != names@[b],
                forall|a: int| 0 <= a < j ==> names@[a] != names@[i as int],
            decreases i - j,
        {
            if names[j] == names[i] {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

/// 格納の型が整形式かを判定する。真なら整形式である。
pub fn wf_stype_exec(t: &SType, enums: &Vec<i64>) -> (r: bool)
    ensures
        r ==> wf_stype(sty(*t), enums@),
    decreases t,
{
    match t {
        SType::Bool => true,
        SType::Int(lo, hi) => *lo <= *hi,
        SType::Enum(id) => *id < enums.len() && enums[*id] >= 1,
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            ts.len() >= 1 && wf_stypes_exec(t, ts, enums)
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            ts.len() >= 1 && names.len() == ts.len() && distinct_names(names) && wf_stypes_exec(t, ts, enums)
        },
        SType::Option(x) => wf_stype_exec(x, enums),
        SType::Set(e) => wf_stype_exec(e, enums) && keys_exec(e, enums).is_some(),
        SType::Map(k, v) => wf_stype_exec(k, enums) && keys_exec(k, enums).is_some() && wf_stype_exec(v, enums),
        SType::List(e, _) => wf_stype_exec(e, enums),
    }
}

fn wf_stypes_exec(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r ==> wf_stypes(stys(ts@), enums@) && stys(ts@).len() == ts.len(),
    decreases _parent, 0nat,
{
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            forall|j: int| 0 <= j < i ==> wf_stype(sty(#[trigger] ts@[j]), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !wf_stype_exec(&ts[i], enums) {
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys(ts@);
        let ss = stys(ts@);
        assert forall|j: int| 0 <= j < ss.len() implies wf_stype(#[trigger] ss[j], enums@) by {
            assert(ss[j] == sty(ts@[j]));
        }
        lemma_wf_stypes(ss, enums@);
    }
    true
}

} // verus!
