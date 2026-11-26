//! 式の形式意味論と実行Evaluator。
//!
//! `eval_spec` が意味論の定義で、`eval` はそれと一致することを証明した実装である
//! （仕様書 §14.1 Evaluation Correctness）。
//! 局所変数（`let` と量化の束縛）を持つ式は `eval_l` で評価する。`eval_spec` は局所変数のない文脈での評価である。

use crate::model::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
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
    /// 0で割った。
    DivByZero,
    /// `Expr::Fail` による失敗。番号の意味はIRが定める。
    Failed(i64),
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

/// 床除算。商を負の無限大の方向に丸める。`b` は0でない。
/// `int` の `/` はユークリッド除算なので、除数が負のときは両辺の符号を反転して正の除数で割る。
pub open spec fn floor_div(a: int, b: int) -> int {
    if b > 0 {
        a / b
    } else {
        (-a) / (-b)
    }
}

/// 床除算の余り。`a == b * floor_div(a, b) + floor_mod(a, b)` で、符号は除数と同じになる。
pub open spec fn floor_mod(a: int, b: int) -> int {
    a - b * floor_div(a, b)
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
                BinOp::Div => if b == 0 {
                    Err(ErrKind::DivByZero)
                } else {
                    int_result(floor_div(a as int, b as int))
                },
                BinOp::Mod => if b == 0 {
                    Err(ErrKind::DivByZero)
                } else {
                    int_result(floor_mod(a as int, b as int))
                },
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

/// 値の符号。Bool は0と1、整数はその値、列挙型はラベルの添字。
pub open spec fn code_of(v: Value) -> i64 {
    match v {
        Value::Bool(b) => if b {
            1
        } else {
            0
        },
        Value::Int(x) => x,
        Value::Enum(_, k) => k,
    }
}

/// 式の意味論。評価した部分式のエラーだけが伝播する（仕様書 §4.2）。`ls` は局所変数の値。
pub open spec fn eval_l(e: Expr, env: Env, ls: Seq<Value>) -> Result<Value, ErrKind>
    decreases e, 0int,
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
        Expr::Bin(op, a, b) => match eval_l(*a, env, ls) {
            Err(k) => Err(k),
            Ok(x) => match eval_l(*b, env, ls) {
                Err(k) => Err(k),
                Ok(y) => binop_spec(op, x, y),
            },
        },
        Expr::Not(a) => match as_bool(eval_l(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(b) => Ok(Value::Bool(!b)),
        },
        Expr::And(a, b) => match as_bool(eval_l(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(false)),
            Ok(true) => match as_bool(eval_l(*b, env, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Or(a, b) => match as_bool(eval_l(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => match as_bool(eval_l(*b, env, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Implies(a, b) => match as_bool(eval_l(*a, env, ls)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(true)),
            Ok(true) => match as_bool(eval_l(*b, env, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Ite(c, a, b) => match as_bool(eval_l(*c, env, ls)) {
            Err(k) => Err(k),
            Ok(true) => eval_l(*a, env, ls),
            Ok(false) => eval_l(*b, env, ls),
        },
        Expr::Local(i) => if i < ls.len() {
            Ok(ls[i as int])
        } else {
            Err(ErrKind::Unbound)
        },
        Expr::Let(a, b) => match eval_l(*a, env, ls) {
            Err(k) => Err(k),
            Ok(v) => eval_l(*b, env, ls.push(v)),
        },
        Expr::Forall(ty, lo, hi, body) => quant_l(true, ty, *body, env, ls, lo as int, hi as int),
        Expr::Exists(ty, lo, hi, body) => quant_l(false, ty, *body, env, ls, lo as int, hi as int),
        Expr::Code(a) => match eval_l(*a, env, ls) {
            Err(k) => Err(k),
            Ok(v) => Ok(Value::Int(code_of(v))),
        },
        Expr::Fail(_, k) => Err(ErrKind::Failed(k)),
    }
}

/// 量化の意味論。符号 `x..=hi` を昇順にたどる。`all` が真なら forall、偽なら exists で、
/// 本体の値が `all` と異なった時点でその値を返す。たどり終えたら `all` を返す。
pub open spec fn quant_l(all: bool, ty: Type, body: Expr, env: Env, ls: Seq<Value>, x: int, hi: int) -> Result<
    Value,
    ErrKind,
>
    decreases body, hi - x + 1,
{
    if x > hi {
        Ok(Value::Bool(all))
    } else {
        match as_bool(eval_l(body, env, ls.push(decode(ty, x as i64)))) {
            Err(k) => Err(k),
            Ok(b) => if b == all {
                quant_l(all, ty, body, env, ls, x + 1, hi)
            } else {
                Ok(Value::Bool(b))
            },
        }
    }
}

/// 局所変数のない文脈での式の意味論。
pub open spec fn eval_spec(e: Expr, env: Env) -> Result<Value, ErrKind> {
    eval_l(e, env, Seq::empty())
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

/// `x` を正の `d` で割った床除算の商と余り。
fn pos_divmod(x: i128, d: i128) -> (r: (i128, i128))
    requires
        -0x8000_0000_0000_0000 <= x <= 0x8000_0000_0000_0000,
        1 <= d <= 0x8000_0000_0000_0000,
    ensures
        r.0 == x as int / d as int,
        r.1 == x - d * r.0,
        0 <= r.1 < d,
        -0x8000_0000_0000_0001 <= r.0 <= 0x8000_0000_0000_0000,
{
    if x >= 0 {
        let ux = x as u128;
        let ud = d as u128;
        let q = ux / ud;
        let rr = ux % ud;
        proof {
            lemma_fundamental_div_mod(x as int, d as int);
            lemma_mod_pos_bound(x as int, d as int);
            assert(q as int <= x) by (nonlinear_arith)
                requires
                    x == d * q + rr,
                    rr >= 0,
                    d >= 1,
                    q >= 0,
            ;
        }
        (q as i128, rr as i128)
    } else {
        let ux = (-x) as u128;
        let ud = d as u128;
        let t = (ux - 1) / ud;
        let r0 = (ux - 1) % ud;
        proof {
            lemma_fundamental_div_mod((ux - 1) as int, d as int);
            lemma_mod_pos_bound((ux - 1) as int, d as int);
            assert(t as int <= ux - 1) by (nonlinear_arith)
                requires
                    ux - 1 == d * t + r0,
                    r0 >= 0,
                    d >= 1,
                    t >= 0,
            ;
            assert(x == d * (-t - 1) + (d - r0 - 1)) by (nonlinear_arith)
                requires
                    ux - 1 == d * t + r0,
                    x == -ux,
            ;
            lemma_fundamental_div_mod_converse(x as int, d as int, -t - 1, d - r0 - 1);
        }
        (-(t as i128) - 1, d - (r0 as i128) - 1)
    }
}

/// 床除算の商と余り。
fn floor_divmod(a: i64, b: i64) -> (r: (i128, i128))
    requires
        b != 0,
    ensures
        r.0 == floor_div(a as int, b as int),
        r.1 == floor_mod(a as int, b as int),
{
    if b > 0 {
        pos_divmod(a as i128, b as i128)
    } else {
        let (q, rr) = pos_divmod(-(a as i128), -(b as i128));
        proof {
            assert(floor_mod(a as int, b as int) == -rr) by (nonlinear_arith)
                requires
                    rr == -(a as int) - (-(b as int)) * q,
                    q == floor_div(a as int, b as int),
            ;
        }
        (q, -rr)
    }
}

fn int_result_exec(q: i128) -> (r: Result<Value, ErrKind>)
    ensures
        r == int_result(q as int),
{
    if i64::MIN as i128 <= q && q <= i64::MAX as i128 {
        Ok(Value::Int(q as i64))
    } else {
        Err(ErrKind::Overflow)
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
                BinOp::Div => if *b == 0 {
                    Err(ErrKind::DivByZero)
                } else {
                    int_result_exec(floor_divmod(*a, *b).0)
                },
                BinOp::Mod => if *b == 0 {
                    Err(ErrKind::DivByZero)
                } else {
                    int_result_exec(floor_divmod(*a, *b).1)
                },
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

fn code_exec(v: &Value) -> (r: i64)
    ensures
        r == code_of(*v),
{
    match v {
        Value::Bool(b) => if *b {
            1
        } else {
            0
        },
        Value::Int(x) => *x,
        Value::Enum(_, k) => *k,
    }
}

fn copy_values(v: &Vec<Value>) -> (r: Vec<Value>)
    ensures
        r@ == v@,
{
    let mut r: Vec<Value> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        assert(r@ =~= v@.subrange(0, i as int));
    }
    assert(v@.subrange(0, v@.len() as int) =~= v@);
    r
}

/// 式を評価する。結果は意味論 `eval_spec` と一致する。
pub fn eval(e: &Expr, c: &Ctx) -> (r: Result<Value, ErrKind>)
    ensures
        r == eval_spec(*e, c@),
{
    let ls: Vec<Value> = Vec::new();
    assert(ls@ =~= Seq::<Value>::empty());
    eval_in(e, c, &ls)
}

/// 局所変数 `ls` の下で式を評価する。結果は意味論 `eval_l` と一致する。
fn eval_in(e: &Expr, c: &Ctx, ls: &Vec<Value>) -> (r: Result<Value, ErrKind>)
    ensures
        r == eval_l(*e, c@, ls@),
    decreases e, 0int,
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
        Expr::Bin(op, a, b) => match eval_in(a, c, ls) {
            Err(k) => Err(k),
            Ok(x) => match eval_in(b, c, ls) {
                Err(k) => Err(k),
                Ok(y) => binop(op, &x, &y),
            },
        },
        Expr::Not(a) => match to_bool(eval_in(a, c, ls)) {
            Err(k) => Err(k),
            Ok(b) => Ok(Value::Bool(!b)),
        },
        Expr::And(a, b) => match to_bool(eval_in(a, c, ls)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(false)),
            Ok(true) => match to_bool(eval_in(b, c, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Or(a, b) => match to_bool(eval_in(a, c, ls)) {
            Err(k) => Err(k),
            Ok(true) => Ok(Value::Bool(true)),
            Ok(false) => match to_bool(eval_in(b, c, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Implies(a, b) => match to_bool(eval_in(a, c, ls)) {
            Err(k) => Err(k),
            Ok(false) => Ok(Value::Bool(true)),
            Ok(true) => match to_bool(eval_in(b, c, ls)) {
                Err(k) => Err(k),
                Ok(y) => Ok(Value::Bool(y)),
            },
        },
        Expr::Ite(cond, a, b) => match to_bool(eval_in(cond, c, ls)) {
            Err(k) => Err(k),
            Ok(true) => eval_in(a, c, ls),
            Ok(false) => eval_in(b, c, ls),
        },
        Expr::Local(i) => if *i < ls.len() {
            Ok(ls[*i])
        } else {
            Err(ErrKind::Unbound)
        },
        Expr::Let(a, b) => match eval_in(a, c, ls) {
            Err(k) => Err(k),
            Ok(v) => {
                let mut inner = copy_values(ls);
                inner.push(v);
                eval_in(b, c, &inner)
            },
        },
        Expr::Forall(ty, lo, hi, body) => quant(true, ty, *lo, *hi, body, c, ls),
        Expr::Exists(ty, lo, hi, body) => quant(false, ty, *lo, *hi, body, c, ls),
        Expr::Code(a) => match eval_in(a, c, ls) {
            Err(k) => Err(k),
            Ok(v) => Ok(Value::Int(code_exec(&v))),
        },
        Expr::Fail(_, k) => Err(ErrKind::Failed(*k)),
    }
}

/// 量化を評価する。結果は意味論 `quant_l` と一致する。
#[verifier::loop_isolation(false)]
fn quant(all: bool, ty: &Type, lo: i64, hi: i64, body: &Expr, c: &Ctx, ls: &Vec<Value>) -> (r: Result<
    Value,
    ErrKind,
>)
    ensures
        r == quant_l(all, *ty, *body, c@, ls@, lo as int, hi as int),
    decreases body, 1int,
{
    let mut inner = copy_values(ls);
    inner.push(Value::Bool(false));
    let n = ls.len();
    let mut x: i128 = lo as i128;
    while x <= hi as i128
        invariant
            lo <= x,
            n == ls@.len(),
            inner@.len() == n + 1,
            inner@.subrange(0, n as int) == ls@,
            quant_l(all, *ty, *body, c@, ls@, x as int, hi as int) == quant_l(
                all,
                *ty,
                *body,
                c@,
                ls@,
                lo as int,
                hi as int,
            ),
        decreases hi - x + 1,
    {
        inner.set(n, decode_value(ty, x as i64));
        assert(inner@ =~= ls@.push(decode(*ty, x as i64)));
        match to_bool(eval_in(body, c, &inner)) {
            Err(k) => {
                return Err(k);
            },
            Ok(b) => {
                if b != all {
                    return Ok(Value::Bool(b));
                }
            },
        }
        assert(inner@.subrange(0, n as int) =~= ls@);
        x = x + 1;
    }
    Ok(Value::Bool(all))
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
        (ErrKind::DivByZero, ErrKind::DivByZero) => true,
        (ErrKind::Failed(x), ErrKind::Failed(y)) => *x == *y,
        _ => false,
    }
}

} // verus!
