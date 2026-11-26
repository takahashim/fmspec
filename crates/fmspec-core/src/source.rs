//! IRの式の型付き構文木と、その意味論（仕様書 §4.2、§12.6）。
//!
//! [`TExpr`] は、IRのJSONの式と1対1に対応する構文木で、名前を番号に解決したものである。
//! 状態変数、引数、定数は宣言の番号で、局所変数は外側から数えた番号で指す。
//! 意味論が要素の型を必要とする演算（要素の番号を計算するもの）は、その型を注釈として持つ。
//! 注釈が実際の型と一致することは型検査が確かめる。
//!
//! [`eval_src`] は、値 [`SVal`] の上で直接評価する意味論で、参照実装（reference/fmspec_reference.rb）の
//! `ev` に対応する。部分式は左から順に評価し、`all`、`any`、`implies`、`ite` と量化は打ち切る。
//! エラーは中核の [`ErrKind`] で表す。算術と比較は中核の [`binop_spec`] と同じ意味である。
//! 高水準の演算の失敗は `ErrKind::Failed` で、番号は `FAIL_*` である。
//!
//! 意味論は、型検査を通った式について参照実装と一致する。型の合わない式の値は意味を持たない
//! （たとえば `Eq` は、参照実装と違い、種類の違うスカラーの比較を型エラーにしない）。
//!
//! 下ろしの正しさは、下ろした中核の式の評価が、この意味論の値の符号化になることとして述べる。

use crate::encoding::{SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{keys_or_zero, member};
#[cfg(verus_keep_ghost)]
use crate::eval::{binop_spec, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::keys::{domain, rank};
use crate::model::{BinOp, Value};
use vstd::prelude::*;

verus! {

/// `unwrap` の対象が空のOptionだった。
pub const FAIL_NONE: i64 = 1;
/// `get` のキーがMapになかった。
pub const FAIL_MISSING_KEY: i64 = 2;
/// `at` の添字が範囲外だった。
pub const FAIL_INDEX: i64 = 3;
/// `push` で、Listの長さが上限に達していた。
pub const FAIL_FULL: i64 = 4;
/// `first`、`last`、`pop`、`shift` で、Listが空だった。
pub const FAIL_EMPTY: i64 = 5;
/// Setの要素、Mapのキーと値、Listの要素が、その型に属さなかった。
pub const FAIL_NOT_IN_DOMAIN: i64 = 6;

/// Setどうしの演算。
pub enum SetOp {
    Union,
    Intersection,
    Difference,
    /// 左が右の部分集合である（Boolを返す）。
    Subset,
}

/// Mapのリテラルの1項目。
pub struct Item {
    pub key: TExpr,
    pub value: TExpr,
}

/// 量化でたどる値。
pub enum Over {
    /// 型の値を正規順にたどる。
    Type(SType),
    /// Setの要素を正規順にたどる。要素の型を持つ。
    Set(SType, Box<TExpr>),
    /// Mapのキーを正規順にたどる。キーの型を持つ。
    Map(SType, Box<TExpr>),
    /// Listの要素を先頭から順にたどる。
    List(Box<TExpr>),
}

/// IRの式の型付き構文木。
pub enum TExpr {
    /// Bool、Int、Enumのリテラル。
    Lit(Value),
    /// 遷移前の状態変数（宣言の番号）。
    Var(usize),
    /// 遷移後の状態変数。遷移契約でだけ使える。
    Next(usize),
    /// 操作の引数。公開引数に続けて内部選択を並べた番号。
    Arg(usize),
    /// 操作の出力。
    Out,
    /// 局所変数。外側から数えた番号。
    Local(usize),
    /// 名前付きの定数（宣言の番号）。
    Const(usize),
    /// `add`、`sub`、`mul`、`div`、`mod`、`lt`、`le`、`gt`、`ge`。
    Bin(BinOp, Box<TExpr>, Box<TExpr>),
    /// `eq`（真）と `ne`（偽）。
    Eq(bool, Box<TExpr>, Box<TExpr>),
    Not(Box<TExpr>),
    /// `all`（真）と `any`（偽）。
    Fold(bool, Vec<TExpr>),
    Implies(Box<TExpr>, Box<TExpr>),
    Ite(Box<TExpr>, Box<TExpr>, Box<TExpr>),
    /// 値を局所変数に束縛して本体を評価する。
    Let(Box<TExpr>, Box<TExpr>),
    /// `forall`（真）と `exists`（偽）。本体は、たどる値を局所変数に束縛して評価する。
    Quant(bool, Over, Box<TExpr>),
    Tuple(Vec<TExpr>),
    /// フィールドの名前の番号と、フィールドの式。
    Record(Vec<usize>, Vec<TExpr>),
    Nth(Box<TExpr>, usize),
    /// フィールドの名前の番号と、Recordの型でのそのフィールドの位置。
    Field(Box<TExpr>, usize, usize),
    /// 中身の型を持つ空のOption。
    None(SType),
    Some(Box<TExpr>),
    IsSome(Box<TExpr>),
    IsNone(Box<TExpr>),
    Unwrap(Box<TExpr>),
    /// 要素の型と要素の式。
    SetLit(SType, Vec<TExpr>),
    /// キーの型、値の型、項目。
    MapLit(SType, SType, Vec<Item>),
    /// 要素の型、長さの上限、要素の式。
    ListLit(SType, usize, Vec<TExpr>),
    /// Setが要素を含む。要素の型を持つ。
    SetContains(SType, Box<TExpr>, Box<TExpr>),
    /// Listが要素を含む。
    ListContains(Box<TExpr>, Box<TExpr>),
    Insert(SType, Box<TExpr>, Box<TExpr>),
    Remove(SType, Box<TExpr>, Box<TExpr>),
    SetBin(SetOp, Box<TExpr>, Box<TExpr>),
    /// Set、Map、Listの大きさ。
    Size(Box<TExpr>),
    IsEmpty(Box<TExpr>),
    /// キーの型を持つ。
    HasKey(SType, Box<TExpr>, Box<TExpr>),
    Get(SType, Box<TExpr>, Box<TExpr>),
    /// キーの型、値の型、Map、キー、値。
    Put(SType, SType, Box<TExpr>, Box<TExpr>, Box<TExpr>),
    Delete(SType, Box<TExpr>, Box<TExpr>),
    Keys(Box<TExpr>),
    At(Box<TExpr>, Box<TExpr>),
    First(Box<TExpr>),
    Last(Box<TExpr>),
    /// 要素の型、長さの上限、List、要素。
    Push(SType, usize, Box<TExpr>, Box<TExpr>),
    Pop(Box<TExpr>),
    Shift(Box<TExpr>),
}

/// 式を評価する環境。状態、引数、出力、定数は値で持つ。`enums` は各列挙型のラベルの数。
pub struct SEnv {
    pub pre: Seq<SVal>,
    pub args: Seq<SVal>,
    pub post: Seq<SVal>,
    pub out: Option<SVal>,
    pub consts: Seq<SVal>,
    pub enums: Seq<i64>,
}

// ---- 値の変換 ----

/// 中核の値を、IRの値にする。
pub open spec fn of_value(v: Value) -> SVal {
    match v {
        Value::Bool(b) => SVal::Bool(b),
        Value::Int(x) => SVal::Int(x),
        Value::Enum(id, k) => SVal::Enum(id, k),
    }
}

/// スカラーの値を、中核の値にする。スカラーでなければ `None`。
pub open spec fn to_value(v: SVal) -> Option<Value> {
    match v {
        SVal::Bool(b) => Some(Value::Bool(b)),
        SVal::Int(x) => Some(Value::Int(x)),
        SVal::Enum(id, k) => Some(Value::Enum(id, k)),
        _ => None,
    }
}

pub open spec fn fail<T>(code: i64) -> Result<T, ErrKind> {
    Err(ErrKind::Failed(code))
}

pub open spec fn src_bool(r: Result<SVal, ErrKind>) -> Result<bool, ErrKind> {
    match r {
        Ok(SVal::Bool(b)) => Ok(b),
        Ok(_) => Err(ErrKind::TypeMismatch),
        Err(k) => Err(k),
    }
}

pub open spec fn at(xs: Seq<SVal>, i: usize) -> Result<SVal, ErrKind> {
    if i < xs.len() {
        Ok(xs[i as int])
    } else {
        Err(ErrKind::Unbound)
    }
}

/// 真のBoolの数。
pub open spec fn count_true(bits: Seq<bool>) -> nat
    decreases bits.len(),
{
    if bits.len() == 0 {
        0
    } else {
        count_true(bits.drop_last()) + if bits.last() {
            1nat
        } else {
            0nat
        }
    }
}

/// 値のある行の数。
pub open spec fn count_some(rows: Seq<Option<SVal>>) -> nat
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        count_some(rows.drop_last()) + if rows.last() is Some {
            1nat
        } else {
            0nat
        }
    }
}

/// 正規順の列 `dom` から、`bits` が真の位置の値を順に選ぶ。
pub open spec fn select_bits(dom: Seq<SVal>, bits: Seq<bool>) -> Seq<SVal>
    decreases bits.len(),
{
    if bits.len() == 0 {
        Seq::empty()
    } else {
        let pre = select_bits(dom, bits.drop_last());
        if bits.last() {
            pre.push(dom[bits.len() - 1])
        } else {
            pre
        }
    }
}

// ---- 意味論 ----

/// 式の意味論。`ls` は局所変数の値で、`Let` と量化が末尾に積む。
pub open spec fn eval_src(e: TExpr, env: SEnv, ls: Seq<SVal>) -> Result<SVal, ErrKind>
    decreases e, 0nat,
{
    let enums = env.enums;
    match e {
        TExpr::Lit(v) => Ok(of_value(v)),
        TExpr::Var(i) => at(env.pre, i),
        TExpr::Next(i) => at(env.post, i),
        TExpr::Arg(i) => at(env.args, i),
        TExpr::Out => match env.out {
            Some(v) => Ok(v),
            None => Err(ErrKind::Unbound),
        },
        TExpr::Local(i) => at(ls, i),
        TExpr::Const(i) => at(env.consts, i),
        TExpr::Bin(op, a, b) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(x) => match eval_src(*b, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match (to_value(x), to_value(y)) {
                    (Some(p), Some(q)) => match binop_spec(op, p, q) {
                        Ok(r) => Ok(of_value(r)),
                        Err(k) => Err(k),
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Eq(positive, a, b) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(x) => match eval_src(*b, env, ls) {
                Err(k) => Err(k),
                Ok(y) => Ok(SVal::Bool((x == y) == positive)),
            },
        },
        TExpr::Not(a) => match src_bool(eval_src(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(b) => Ok(SVal::Bool(!b)),
        },
        TExpr::Fold(all, es) => match eval_fold(all, es@, env, ls) {
            Err(k) => Err(k),
            Ok(b) => Ok(SVal::Bool(b)),
        },
        TExpr::Implies(a, b) => match src_bool(eval_src(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(false) => Ok(SVal::Bool(true)),
            Ok(true) => match src_bool(eval_src(*b, env, ls)) {
                Err(k) => Err(k),
                Ok(q) => Ok(SVal::Bool(q)),
            },
        },
        TExpr::Ite(c, a, b) => match src_bool(eval_src(*c, env, ls)) {
            Err(k) => Err(k),
            Ok(true) => eval_src(*a, env, ls),
            Ok(false) => eval_src(*b, env, ls),
        },
        TExpr::Let(a, b) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(v) => eval_src(*b, env, ls.push(v)),
        },
        TExpr::Quant(all, over, body) => {
            let values: Result<Seq<SVal>, ErrKind> = match over {
                Over::Type(t) => Ok(domain(t, enums)),
                Over::Set(t, s) => match eval_src(*s, env, ls) {
                    Ok(SVal::Set(bits)) => Ok(select_bits(domain(t, enums), bits)),
                    Ok(_) => Err(ErrKind::TypeMismatch),
                    Err(k) => Err(k),
                },
                Over::Map(t, m) => match eval_src(*m, env, ls) {
                    Ok(SVal::Map(rows)) => Ok(
                        select_bits(domain(t, enums), Seq::new(rows.len(), |i: int| rows[i] is Some)),
                    ),
                    Ok(_) => Err(ErrKind::TypeMismatch),
                    Err(k) => Err(k),
                },
                Over::List(l) => match eval_src(*l, env, ls) {
                    Ok(SVal::List(items)) => Ok(items),
                    Ok(_) => Err(ErrKind::TypeMismatch),
                    Err(k) => Err(k),
                },
            };
            match values {
                Err(k) => Err(k),
                Ok(xs) => match eval_quant(all, xs, *body, env, ls) {
                    Err(k) => Err(k),
                    Ok(b) => Ok(SVal::Bool(b)),
                },
            }
        },
        TExpr::Tuple(es) => match eval_seq(es@, env, ls) {
            Err(k) => Err(k),
            Ok(vs) => Ok(SVal::Tuple(vs)),
        },
        TExpr::Record(_, es) => match eval_seq(es@, env, ls) {
            Err(k) => Err(k),
            Ok(vs) => Ok(SVal::Tuple(vs)),
        },
        TExpr::Nth(a, i) => match eval_src(*a, env, ls) {
            Ok(SVal::Tuple(vs)) => at(vs, i),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::Field(a, _, i) => match eval_src(*a, env, ls) {
            Ok(SVal::Tuple(vs)) => at(vs, i),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::None(_) => Ok(SVal::None),
        TExpr::Some(a) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(v) => Ok(SVal::Some(Box::new(v))),
        },
        TExpr::IsSome(a) => match eval_src(*a, env, ls) {
            Ok(SVal::None) => Ok(SVal::Bool(false)),
            Ok(SVal::Some(_)) => Ok(SVal::Bool(true)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::IsNone(a) => match eval_src(*a, env, ls) {
            Ok(SVal::None) => Ok(SVal::Bool(true)),
            Ok(SVal::Some(_)) => Ok(SVal::Bool(false)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::Unwrap(a) => match eval_src(*a, env, ls) {
            Ok(SVal::None) => fail(FAIL_NONE),
            Ok(SVal::Some(v)) => Ok(*v),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::SetLit(t, es) => match eval_set_items(t, es@, env, ls) {
            Err(k) => Err(k),
            Ok(bits) => Ok(SVal::Set(bits)),
        },
        TExpr::MapLit(k, v, items) => match eval_map_items(k, v, items@, env, ls) {
            Err(err) => Err(err),
            Ok(rows) => Ok(SVal::Map(rows)),
        },
        TExpr::ListLit(t, _, es) => match eval_elements(t, es@, env, ls) {
            Err(k) => Err(k),
            Ok(items) => Ok(SVal::List(items)),
        },
        TExpr::SetContains(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(s) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match s {
                    SVal::Set(bits) => Ok(SVal::Bool(member(y, t, enums) && bits[rank(y, t, enums)])),
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::ListContains(a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(l) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match l {
                    SVal::List(items) => Ok(SVal::Bool(items.contains(y))),
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Insert(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(s) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match s {
                    SVal::Set(bits) => if member(y, t, enums) {
                        Ok(SVal::Set(bits.update(rank(y, t, enums), true)))
                    } else {
                        fail(FAIL_NOT_IN_DOMAIN)
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Remove(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(s) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match s {
                    SVal::Set(bits) => if member(y, t, enums) {
                        Ok(SVal::Set(bits.update(rank(y, t, enums), false)))
                    } else {
                        Ok(SVal::Set(bits))
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::SetBin(op, a, b) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(x) => match eval_src(*b, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match (x, y) {
                    (SVal::Set(p), SVal::Set(q)) => if p.len() != q.len() {
                        Err(ErrKind::TypeMismatch)
                    } else {
                        match op {
                            SetOp::Union => Ok(SVal::Set(Seq::new(p.len(), |i: int| p[i] || q[i]))),
                            SetOp::Intersection => Ok(SVal::Set(Seq::new(p.len(), |i: int| p[i] && q[i]))),
                            SetOp::Difference => Ok(SVal::Set(Seq::new(p.len(), |i: int| p[i] && !q[i]))),
                            SetOp::Subset => Ok(
                                SVal::Bool(forall|i: int| 0 <= i < p.len() ==> (p[i] ==> q[i])),
                            ),
                        }
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Size(a) => match eval_src(*a, env, ls) {
            Ok(SVal::Set(bits)) => Ok(SVal::Int(count_true(bits) as i64)),
            Ok(SVal::Map(rows)) => Ok(SVal::Int(count_some(rows) as i64)),
            Ok(SVal::List(items)) => Ok(SVal::Int(items.len() as i64)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::IsEmpty(a) => match eval_src(*a, env, ls) {
            Ok(SVal::Set(bits)) => Ok(SVal::Bool(count_true(bits) == 0)),
            Ok(SVal::Map(rows)) => Ok(SVal::Bool(count_some(rows) == 0)),
            Ok(SVal::List(items)) => Ok(SVal::Bool(items.len() == 0)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::HasKey(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(m) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match m {
                    SVal::Map(rows) => Ok(SVal::Bool(member(y, t, enums) && rows[rank(y, t, enums)] is Some)),
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Get(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(m) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match m {
                    SVal::Map(rows) => if member(y, t, enums) {
                        match rows[rank(y, t, enums)] {
                            Some(v) => Ok(v),
                            None => fail(FAIL_MISSING_KEY),
                        }
                    } else {
                        fail(FAIL_MISSING_KEY)
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Put(kt, vt, a, x, y) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(m) => match put_row(m, kt, vt, eval_src(*x, env, ls), eval_src(*y, env, ls), enums) {
                Err(k) => Err(k),
                Ok(rows) => Ok(SVal::Map(rows)),
            },
        },
        TExpr::Delete(t, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(m) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match m {
                    SVal::Map(rows) => if member(y, t, enums) {
                        Ok(SVal::Map(rows.update(rank(y, t, enums), None)))
                    } else {
                        Ok(SVal::Map(rows))
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Keys(a) => match eval_src(*a, env, ls) {
            Ok(SVal::Map(rows)) => Ok(SVal::Set(Seq::new(rows.len(), |i: int| rows[i] is Some))),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::At(a, i) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(l) => match eval_src(*i, env, ls) {
                Err(k) => Err(k),
                Ok(j) => match (l, j) {
                    (SVal::List(items), SVal::Int(n)) => if 0 <= n < items.len() {
                        Ok(items[n as int])
                    } else {
                        fail(FAIL_INDEX)
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::First(a) => match eval_src(*a, env, ls) {
            Ok(SVal::List(items)) => if items.len() == 0 {
                fail(FAIL_EMPTY)
            } else {
                Ok(items[0])
            },
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::Last(a) => match eval_src(*a, env, ls) {
            Ok(SVal::List(items)) => if items.len() == 0 {
                fail(FAIL_EMPTY)
            } else {
                Ok(items.last())
            },
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::Push(t, max, a, x) => match eval_src(*a, env, ls) {
            Err(k) => Err(k),
            Ok(l) => match eval_src(*x, env, ls) {
                Err(k) => Err(k),
                Ok(y) => match l {
                    SVal::List(items) => if !member(y, t, enums) {
                        fail(FAIL_NOT_IN_DOMAIN)
                    } else if items.len() >= max {
                        fail(FAIL_FULL)
                    } else {
                        Ok(SVal::List(items.push(y)))
                    },
                    _ => Err(ErrKind::TypeMismatch),
                },
            },
        },
        TExpr::Pop(a) => match eval_src(*a, env, ls) {
            Ok(SVal::List(items)) => if items.len() == 0 {
                fail(FAIL_EMPTY)
            } else {
                Ok(SVal::List(items.drop_last()))
            },
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        TExpr::Shift(a) => match eval_src(*a, env, ls) {
            Ok(SVal::List(items)) => if items.len() == 0 {
                fail(FAIL_EMPTY)
            } else {
                Ok(SVal::List(items.drop_first()))
            },
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
    }
}

/// `all`（`all` が真）と `any`。左から評価し、`all` と異なる値が出た時点でその値を返す。
pub open spec fn eval_fold(all: bool, es: Seq<TExpr>, env: SEnv, ls: Seq<SVal>) -> Result<bool, ErrKind>
    decreases es, 1nat,
{
    if es.len() == 0 {
        Ok(all)
    } else {
        match eval_fold(all, es.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(b) => if b != all {
                Ok(b)
            } else {
                src_bool(eval_src(es.last(), env, ls))
            },
        }
    }
}

/// 式の列を左から評価する。
pub open spec fn eval_seq(es: Seq<TExpr>, env: SEnv, ls: Seq<SVal>) -> Result<Seq<SVal>, ErrKind>
    decreases es, 1nat,
{
    if es.len() == 0 {
        Ok(Seq::empty())
    } else {
        match eval_seq(es.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(vs) => match eval_src(es.last(), env, ls) {
                Err(k) => Err(k),
                Ok(v) => Ok(vs.push(v)),
            },
        }
    }
}

/// 要素の式の列を左から評価し、各要素が型 `t` に属することを確かめる。
pub open spec fn eval_elements(t: SType, es: Seq<TExpr>, env: SEnv, ls: Seq<SVal>) -> Result<Seq<SVal>, ErrKind>
    decreases es, 1nat,
{
    if es.len() == 0 {
        Ok(Seq::empty())
    } else {
        match eval_elements(t, es.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(vs) => match eval_src(es.last(), env, ls) {
                Err(k) => Err(k),
                Ok(v) => if member(v, t, env.enums) {
                    Ok(vs.push(v))
                } else {
                    fail(FAIL_NOT_IN_DOMAIN)
                },
            },
        }
    }
}

/// Setのリテラルの要素を左から評価し、空のSetに順に加える。
pub open spec fn eval_set_items(t: SType, es: Seq<TExpr>, env: SEnv, ls: Seq<SVal>) -> Result<Seq<bool>, ErrKind>
    decreases es, 1nat,
{
    if es.len() == 0 {
        Ok(Seq::new(keys_or_zero(t, env.enums), |_i: int| false))
    } else {
        match eval_set_items(t, es.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(bits) => match eval_src(es.last(), env, ls) {
                Err(k) => Err(k),
                Ok(v) => if member(v, t, env.enums) {
                    Ok(bits.update(rank(v, t, env.enums), true))
                } else {
                    fail(FAIL_NOT_IN_DOMAIN)
                },
            },
        }
    }
}

/// Mapのリテラルの項目を左から評価し、空のMapに順に置く。
pub open spec fn eval_map_items(kt: SType, vt: SType, items: Seq<Item>, env: SEnv, ls: Seq<SVal>) -> Result<
    Seq<Option<SVal>>,
    ErrKind,
>
    decreases items, 1nat,
{
    if items.len() == 0 {
        Ok(Seq::new(keys_or_zero(kt, env.enums), |_i: int| None))
    } else {
        match eval_map_items(kt, vt, items.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(rows) => put_row(
                SVal::Map(rows),
                kt,
                vt,
                eval_src(items.last().key, env, ls),
                eval_src(items.last().value, env, ls),
                env.enums,
            ),
        }
    }
}

/// Mapの値 `m` に、キーの評価結果 `key` と値の評価結果 `value` を置く。
/// キーのエラーとキーの型の検査が、値のエラーより先に来る（キーを評価して型を確かめてから、値を評価する）。
pub open spec fn put_row(
    m: SVal,
    kt: SType,
    vt: SType,
    key: Result<SVal, ErrKind>,
    value: Result<SVal, ErrKind>,
    enums: Seq<i64>,
) -> Result<Seq<Option<SVal>>, ErrKind> {
    match key {
        Err(k) => Err(k),
        Ok(x) => if !member(x, kt, enums) {
            fail(FAIL_NOT_IN_DOMAIN)
        } else {
            match value {
                Err(k) => Err(k),
                Ok(v) => if !member(v, vt, enums) {
                    fail(FAIL_NOT_IN_DOMAIN)
                } else {
                    match m {
                        SVal::Map(rows) => Ok(rows.update(rank(x, kt, enums), Some(v))),
                        _ => Err(ErrKind::TypeMismatch),
                    }
                },
            }
        },
    }
}

/// 量化。値の列 `xs` を順にたどり、値を局所変数に束縛して本体を評価する。
/// 本体の値が `all` と異なった時点でその値を返す。たどり終えたら `all` を返す。
pub open spec fn eval_quant(all: bool, xs: Seq<SVal>, body: TExpr, env: SEnv, ls: Seq<SVal>) -> Result<
    bool,
    ErrKind,
>
    decreases body, xs.len() + 1,
{
    if xs.len() == 0 {
        Ok(all)
    } else {
        match eval_quant(all, xs.drop_last(), body, env, ls) {
            Err(k) => Err(k),
            Ok(b) => if b != all {
                Ok(b)
            } else {
                src_bool(eval_src(body, env, ls.push(xs.last())))
            },
        }
    }
}

} // verus!
