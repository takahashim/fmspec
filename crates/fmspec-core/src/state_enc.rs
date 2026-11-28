//! 状態と引数の符号化列。各スロットが型に属すこと（`vals_ok`）、値の符号化（`encode`）と、符号化列の複製と比較。

use crate::eval::ErrKind;
#[cfg(verus_keep_ghost)]
use crate::eval::decode;
use crate::model::{Type, Value};
#[cfg(verus_keep_ghost)]
use crate::model::RawModel;
use vstd::prelude::*;

verus! {

pub open spec fn in_type(enums: Seq<i64>, ty: Type, x: i64) -> bool {
    match ty {
        Type::Bool => 0 <= x <= 1,
        Type::Int(lo, hi) => lo <= x <= hi,
        Type::Enum(id) => id < enums.len() && 0 <= x < enums[id as int],
    }
}

pub open spec fn vals_ok(enums: Seq<i64>, tys: Seq<Type>, xs: Seq<i64>) -> bool {
    &&& xs.len() == tys.len()
    &&& forall|i: int| 0 <= i < tys.len() ==> in_type(enums, #[trigger] tys[i], xs[i])
}

/// 状態の符号化列が状態型に従う。
pub open spec fn state_ok(m: RawModel, s: Seq<i64>) -> bool {
    vals_ok(m.enums@, m.state_types@, s)
}

/// 引数の列（公開引数と内部選択）が操作のドメインに従う。
pub open spec fn args_ok(m: RawModel, a: int, args: Seq<i64>) -> bool {
    vals_ok(m.enums@, m.actions@[a].domains@, args)
}

/// 型に属する値の範囲。`lo > hi` なら空。
pub open spec fn type_range(enums: Seq<i64>, ty: Type) -> (int, int) {
    match ty {
        Type::Bool => (0, 1),
        Type::Int(lo, hi) => (lo as int, hi as int),
        Type::Enum(id) => if id < enums.len() {
            (0, enums[id as int] - 1)
        } else {
            (0, -1)
        },
    }
}

pub fn type_range_exec(enums: &Vec<i64>, ty: &Type) -> (r: (i128, i128))
    ensures
        r.0 == type_range(enums@, *ty).0,
        r.1 == type_range(enums@, *ty).1,
        i64::MIN <= r.0,
        r.1 <= i64::MAX,
        forall|x: i64| in_type(enums@, *ty, x) <==> r.0 <= x <= r.1,
{
    match ty {
        Type::Bool => (0, 1),
        Type::Int(lo, hi) => (*lo as i128, *hi as i128),
        Type::Enum(id) => if *id < enums.len() {
            (0, enums[*id] as i128 - 1)
        } else {
            (0, -1)
        },
    }
}

pub fn in_type_exec(enums: &Vec<i64>, ty: &Type, x: i64) -> (r: bool)
    ensures
        r == in_type(enums@, *ty, x),
{
    match ty {
        Type::Bool => 0 <= x && x <= 1,
        Type::Int(lo, hi) => *lo <= x && x <= *hi,
        Type::Enum(id) => *id < enums.len() && 0 <= x && x < enums[*id],
    }
}

pub fn vals_ok_exec(enums: &Vec<i64>, tys: &Vec<Type>, xs: &Vec<i64>) -> (r: bool)
    ensures
        r == vals_ok(enums@, tys@, xs@),
{
    if xs.len() != tys.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < tys.len()
        invariant
            xs@.len() == tys@.len(),
            i <= tys@.len(),
            forall|j: int| 0 <= j < i ==> in_type(enums@, #[trigger] tys@[j], xs@[j]),
        decreases tys@.len() - i,
    {
        if !in_type_exec(enums, &tys[i], xs[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}

/// 値を型の符号に変換する。範囲外の整数は `OutOfRange`、型が合わなければ `TypeMismatch`。
pub open spec fn encode_spec(enums: Seq<i64>, ty: Type, v: Value) -> Result<i64, ErrKind> {
    match (ty, v) {
        (Type::Bool, Value::Bool(b)) => Ok(
            if b {
                1i64
            } else {
                0i64
            },
        ),
        (Type::Int(lo, hi), Value::Int(x)) => if lo <= x <= hi {
            Ok(x)
        } else {
            Err(ErrKind::OutOfRange(x))
        },
        (Type::Enum(id), Value::Enum(id2, k)) => if id == id2 && in_type(enums, ty, k) {
            Ok(k)
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => Err(ErrKind::TypeMismatch),
    }
}

pub fn encode(enums: &Vec<i64>, ty: &Type, v: &Value) -> (r: Result<i64, ErrKind>)
    ensures
        r == encode_spec(enums@, *ty, *v),
{
    match (ty, v) {
        (Type::Bool, Value::Bool(b)) => Ok(
            if *b {
                1
            } else {
                0
            },
        ),
        (Type::Int(lo, hi), Value::Int(x)) => if *lo <= *x && *x <= *hi {
            Ok(*x)
        } else {
            Err(ErrKind::OutOfRange(*x))
        },
        (Type::Enum(id), Value::Enum(id2, k)) => if *id == *id2 && in_type_exec(enums, ty, *k) {
            Ok(*k)
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => Err(ErrKind::TypeMismatch),
    }
}

/// 符号化に成功した値は型に属する。
pub proof fn lemma_encode_in_type(enums: Seq<i64>, ty: Type, v: Value)
    ensures
        encode_spec(enums, ty, v) matches Ok(x) ==> in_type(enums, ty, x),
{
}

/// 型に属する符号は、値と一対一に対応する。
/// 状態の等価性は符号化列の一致で定義するので、型に従う状態が等しいことと、
/// 各状態変数の値が等しいことは一致する（仕様書 §14.1 State Equality）。
pub proof fn lemma_decode_injective(enums: Seq<i64>, ty: Type, x: i64, y: i64)
    requires
        in_type(enums, ty, x),
        in_type(enums, ty, y),
        decode(ty, x) == decode(ty, y),
    ensures
        x == y,
{
}

/// 型に属する符号を値に戻して符号化し直すと、元の符号になる。
pub proof fn lemma_encode_decode(enums: Seq<i64>, ty: Type, x: i64)
    requires
        in_type(enums, ty, x),
    ensures
        encode_spec(enums, ty, decode(ty, x)) == Ok::<i64, ErrKind>(x),
{
}

pub fn copy_vec(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        r@ == v@,
{
    let mut r: Vec<i64> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j],
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
    }
    assert(r@ =~= v@);
    r
}

pub fn vec_eq(a: &Vec<i64>, b: &Vec<i64>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

} // verus!
