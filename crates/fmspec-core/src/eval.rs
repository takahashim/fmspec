//! 式の形式意味論と実行Evaluator。
//!
//! `eval_spec` が意味論の定義で、`eval` はそれと一致することを証明した実装である
//! （仕様書 §14.1 Evaluation Correctness）。

use crate::model::*;
use vstd::prelude::*;

verus! {

/// 評価と状態更新の失敗。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrKind {
    /// 符号付き64ビット整数の範囲を超えた。
    Overflow,
    TypeMismatch,
    /// 束縛されていない変数、引数、出力を参照した。
    Unbound,
    /// 型の範囲外の値で状態または出力を更新しようとした。
    OutOfRange(i64),
}

/// 式を評価する環境。状態と引数は符号化列で持つ。
pub struct Env {
    pub st_tys: Seq<Type>,
    pub arg_tys: Seq<Type>,
    pub pre: Seq<i64>,
    pub args: Seq<i64>,
    pub post: Seq<i64>,
    pub out: Option<Value>,
}

pub open spec fn decode(ty: Type, x: i64) -> Value {
    match ty {
        Type::Bool => Value::Bool(x != 0),
        Type::Int(_, _) => Value::Int(x),
        Type::Enum(id) => Value::Enum(id, x),
    }
}

pub open spec fn lookup(tys: Seq<Type>, xs: Seq<i64>, i: usize) -> Result<Value, ErrKind> {
    if i < tys.len() && i < xs.len() {
        Ok(decode(tys[i as int], xs[i as int]))
    } else {
        Err(ErrKind::Unbound)
    }
}

pub open spec fn same_kind(x: Value, y: Value) -> bool {
    match (x, y) {
        (Value::Bool(_), Value::Bool(_)) => true,
        (Value::Int(_), Value::Int(_)) => true,
        (Value::Enum(a, _), Value::Enum(b, _)) => a == b,
        _ => false,
    }
}

pub open spec fn int_result(r: int) -> Result<Value, ErrKind> {
    if i64::MIN <= r <= i64::MAX {
        Ok(Value::Int(r as i64))
    } else {
        Err(ErrKind::Overflow)
    }
}

pub open spec fn binop_spec(op: BinOp, x: Value, y: Value) -> Result<Value, ErrKind> {
    match op {
        BinOp::Eq => if same_kind(x, y) {
            Ok(Value::Bool(x == y))
        } else {
            Err(ErrKind::TypeMismatch)
        },
        BinOp::Ne => if same_kind(x, y) {
            Ok(Value::Bool(x != y))
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => match (x, y) {
            (Value::Int(a), Value::Int(b)) => match op {
                BinOp::Add => int_result(a + b),
                BinOp::Sub => int_result(a - b),
                BinOp::Mul => int_result(a * b),
                BinOp::Lt => Ok(Value::Bool(a < b)),
                BinOp::Le => Ok(Value::Bool(a <= b)),
                BinOp::Gt => Ok(Value::Bool(a > b)),
                _ => Ok(Value::Bool(a >= b)),
            },
            _ => Err(ErrKind::TypeMismatch),
        },
    }
}

/// Bool として使う値。Bool 以外は型エラー。
pub open spec fn as_bool(r: Result<Value, ErrKind>) -> Result<bool, ErrKind> {
    match r {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(_) => Err(ErrKind::TypeMismatch),
        Err(k) => Err(k),
    }
}

/// 式の意味論。評価した部分式のエラーだけが伝播する（仕様書 §4.2）。
pub open spec fn eval_spec(e: Expr, env: Env) -> Result<Value, ErrKind>
    decreases e,
{
    match e {
        Expr::Const(v) => Ok(v),
        Expr::Var(i) => lookup(env.st_tys, env.pre, i),
        Expr::Arg(i) => lookup(env.arg_tys, env.args, i),
        Expr::Next(i) => lookup(env.st_tys, env.post, i),
        Expr::Out => match env.out {
            Some(v) => Ok(v),
            None => Err(ErrKind::Unbound),
        },
        Expr::Bin(op, a, b) => match eval_spec(*a, env) {
            Err(k) => Err(k),
            Ok(x) => match eval_spec(*b, env) {
                Err(k) => Err(k),
                Ok(y) => binop_spec(op, x, y),
            },
        },
        Expr::Not(a) => match as_bool(eval_spec(*a, env)) {
            Err(k) => Err(k),
            Ok(b) => Ok(Value::Bool(!b)),
        },
        Expr::And(a, b) => match as_bool(eval_spec(*a, env)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(false)),
            Ok(true) => match as_bool(eval_spec(*b, env)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Or(a, b) => match as_bool(eval_spec(*a, env)) {
            Err(k) => Err(k),
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => match as_bool(eval_spec(*b, env)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Implies(a, b) => match as_bool(eval_spec(*a, env)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(true)),
            Ok(true) => match as_bool(eval_spec(*b, env)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Ite(c, a, b) => match as_bool(eval_spec(*c, env)) {
            Err(k) => Err(k),
            Ok(true) => eval_spec(*a, env),
            Ok(false) => eval_spec(*b, env),
        },
    }
}

/// 述語（不変条件、guard、契約、終端条件）としての評価。
pub open spec fn prop_spec(e: Expr, env: Env) -> Result<bool, ErrKind> {
    as_bool(eval_spec(e, env))
}

// ---- 実行Evaluator ----

/// 実行時の環境。`view` が意味論の `Env` を与える。
pub struct Ctx<'a> {
    pub st_tys: &'a Vec<Type>,
    pub arg_tys: &'a Vec<Type>,
    pub pre: &'a Vec<i64>,
    pub args: &'a Vec<i64>,
    pub post: &'a Vec<i64>,
    pub out: Option<Value>,
}

impl<'a> Ctx<'a> {
    pub open spec fn view(&self) -> Env {
        Env {
            st_tys: self.st_tys@,
            arg_tys: self.arg_tys@,
            pre: self.pre@,
            args: self.args@,
            post: self.post@,
            out: self.out,
        }
    }
}

pub fn decode_value(ty: &Type, x: i64) -> (v: Value)
    ensures
        v == decode(*ty, x),
{
    match ty {
        Type::Bool => Value::Bool(x != 0),
        Type::Int(_, _) => Value::Int(x),
        Type::Enum(id) => Value::Enum(*id, x),
    }
}

fn lookup_value(tys: &Vec<Type>, xs: &Vec<i64>, i: usize) -> (r: Result<Value, ErrKind>)
    ensures
        r == lookup(tys@, xs@, i),
{
    if i < tys.len() && i < xs.len() {
        Ok(decode_value(&tys[i], xs[i]))
    } else {
        Err(ErrKind::Unbound)
    }
}

pub fn value_eq(x: &Value, y: &Value) -> (r: bool)
    ensures
        r == (*x == *y),
{
    match (x, y) {
        (Value::Bool(a), Value::Bool(b)) => *a == *b,
        (Value::Int(a), Value::Int(b)) => *a == *b,
        (Value::Enum(i, a), Value::Enum(j, b)) => *i == *j && *a == *b,
        _ => false,
    }
}

fn same_kind_exec(x: &Value, y: &Value) -> (r: bool)
    ensures
        r == same_kind(*x, *y),
{
    match (x, y) {
        (Value::Bool(_), Value::Bool(_)) => true,
        (Value::Int(_), Value::Int(_)) => true,
        (Value::Enum(a, _), Value::Enum(b, _)) => *a == *b,
        _ => false,
    }
}

fn checked(r: Option<i64>) -> (v: Result<Value, ErrKind>)
    ensures
        v == match r {
            Some(z) => Ok::<Value, ErrKind>(Value::Int(z)),
            None => Err::<Value, ErrKind>(ErrKind::Overflow),
        },
{
    match r {
        Some(z) => Ok(Value::Int(z)),
        None => Err(ErrKind::Overflow),
    }
}

fn binop(op: &BinOp, x: &Value, y: &Value) -> (r: Result<Value, ErrKind>)
    ensures
        r == binop_spec(*op, *x, *y),
{
    match op {
        BinOp::Eq => if same_kind_exec(x, y) {
            Ok(Value::Bool(value_eq(x, y)))
        } else {
            Err(ErrKind::TypeMismatch)
        },
        BinOp::Ne => if same_kind_exec(x, y) {
            Ok(Value::Bool(!value_eq(x, y)))
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => match (x, y) {
            (Value::Int(a), Value::Int(b)) => match op {
                BinOp::Add => checked(a.checked_add(*b)),
                BinOp::Sub => checked(a.checked_sub(*b)),
                BinOp::Mul => checked(a.checked_mul(*b)),
                BinOp::Lt => Ok(Value::Bool(*a < *b)),
                BinOp::Le => Ok(Value::Bool(*a <= *b)),
                BinOp::Gt => Ok(Value::Bool(*a > *b)),
                _ => Ok(Value::Bool(*a >= *b)),
            },
            _ => Err(ErrKind::TypeMismatch),
        },
    }
}

fn to_bool(r: Result<Value, ErrKind>) -> (b: Result<bool, ErrKind>)
    ensures
        b == as_bool(r),
{
    match r {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(_) => Err(ErrKind::TypeMismatch),
        Err(k) => Err(k),
    }
}

/// 式を評価する。結果は意味論 `eval_spec` と一致する。
pub fn eval(e: &Expr, c: &Ctx) -> (r: Result<Value, ErrKind>)
    ensures
        r == eval_spec(*e, c@),
    decreases e,
{
    match e {
        Expr::Const(v) => Ok(*v),
        Expr::Var(i) => lookup_value(c.st_tys, c.pre, *i),
        Expr::Arg(i) => lookup_value(c.arg_tys, c.args, *i),
        Expr::Next(i) => lookup_value(c.st_tys, c.post, *i),
        Expr::Out => match c.out {
            Some(v) => Ok(v),
            None => Err(ErrKind::Unbound),
        },
        Expr::Bin(op, a, b) => match eval(a, c) {
            Err(k) => Err(k),
            Ok(x) => match eval(b, c) {
                Err(k) => Err(k),
                Ok(y) => binop(op, &x, &y),
            },
        },
        Expr::Not(a) => match to_bool(eval(a, c)) {
            Err(k) => Err(k),
            Ok(b) => Ok(Value::Bool(!b)),
        },
        Expr::And(a, b) => match to_bool(eval(a, c)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(false)),
            Ok(true) => match to_bool(eval(b, c)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Or(a, b) => match to_bool(eval(a, c)) {
            Err(k) => Err(k),
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => match to_bool(eval(b, c)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Implies(a, b) => match to_bool(eval(a, c)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(true)),
            Ok(true) => match to_bool(eval(b, c)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Ite(cond, a, b) => match to_bool(eval(cond, c)) {
            Err(k) => Err(k),
            Ok(true) => eval(a, c),
            Ok(false) => eval(b, c),
        },
    }
}

/// 述語として評価する。結果は `prop_spec` と一致する。
pub fn eval_prop(e: &Expr, c: &Ctx) -> (r: Result<bool, ErrKind>)
    ensures
        r == prop_spec(*e, c@),
{
    to_bool(eval(e, c))
}

pub fn errkind_eq(a: &ErrKind, b: &ErrKind) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (ErrKind::Overflow, ErrKind::Overflow) => true,
        (ErrKind::TypeMismatch, ErrKind::TypeMismatch) => true,
        (ErrKind::Unbound, ErrKind::Unbound) => true,
        (ErrKind::OutOfRange(x), ErrKind::OutOfRange(y)) => *x == *y,
        _ => false,
    }
}

} // verus!
