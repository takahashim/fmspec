//! IRの式の型付け規則（仕様）と型検査器。
//!
//! [`type_of`] は、型付き構文木の式の型を決める規則である。型が付かなければ `None`。
//! 規則は今の Rust 側の型検査（fmspec-ir の下ろし）と同じで、整数の範囲は式の型に持たない。
//! Setの要素、Mapのキーと値、Listの要素になる式の型は、格納の型の式の型 [`to_xty`] と等しくなければならない。
//! 要素の型の注釈は、実際の型と一致しなければならない。
//!
//! [`check`] は型検査器で、型を返したら、それが [`type_of`] の値であることを証明してある。
//! 型が付く式を拒否しないことは証明していない（拒否はモデルの読み込みの誤りになるので、テストで検査する）。

use crate::encoding::STy;
use crate::encoding::{copy_stype, copy_xtype, distinct_names, keys_exec, stype_eq, to_xtype};
#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, lemma_stys, lemma_xtys, sty, stys, to_xty, wf_stype, xty, xtys, XTy};
use crate::encoding::{wf_stype_exec, xtype_eq, SType, XType};
use crate::model::{BinOp, Value};
use crate::source::{Item, Over, SetOp, TExpr};
use vstd::prelude::*;

verus! {

/// 型付けの文脈（仕様）。
pub struct SCtx {
    /// 各列挙型のラベルの数。
    pub enums: Seq<i64>,
    /// 状態変数の型。`None` なら状態を参照できない（初期値と定数）。
    pub states: Option<Seq<STy>>,
    /// 公開引数に続けて内部選択の型。
    pub args: Seq<STy>,
    /// 遷移後の状態と出力を参照できる（遷移契約）。
    pub next: bool,
    /// 出力の型。
    pub out: Option<STy>,
    /// 定数の型。
    pub consts: Seq<STy>,
}

pub open spec fn is_arith(op: BinOp) -> bool {
    op is Add || op is Sub || op is Mul || op is Div || op is Mod
}

pub open spec fn is_compare(op: BinOp) -> bool {
    op is Lt || op is Le || op is Gt || op is Ge
}

/// 中核の値のリテラルの型。
pub open spec fn lit_type(v: Value, enums: Seq<i64>) -> Option<XTy> {
    match v {
        Value::Bool(_) => Some(XTy::Bool),
        Value::Int(_) => Some(XTy::Int),
        Value::Enum(id, k) => if id < enums.len() && 0 <= k < enums[id as int] {
            Some(XTy::Enum(id))
        } else {
            None
        },
    }
}

/// 格納の型 `t` の要素として置ける型。整形式でなければ `None`。
pub open spec fn element(t: STy, enums: Seq<i64>) -> Option<XTy> {
    if wf_stype(t, enums) {
        Some(to_xty(t))
    } else {
        None
    }
}

/// 式の型。`lt` は局所変数の型。
pub open spec fn type_of(e: TExpr, c: SCtx, lt: Seq<XTy>) -> Option<XTy>
    decreases e, 0nat,
{
    let enums = c.enums;
    match e {
        TExpr::Lit(v) => lit_type(v, enums),
        TExpr::Var(i) => match c.states {
            Some(s) => if i < s.len() {
                Some(to_xty(s[i as int]))
            } else {
                None
            },
            None => None,
        },
        TExpr::Next(i) => match c.states {
            Some(s) => if c.next && i < s.len() {
                Some(to_xty(s[i as int]))
            } else {
                None
            },
            None => None,
        },
        TExpr::Arg(i) => if i < c.args.len() {
            Some(to_xty(c.args[i as int]))
        } else {
            None
        },
        TExpr::Out => match c.out {
            Some(t) => if c.next {
                Some(to_xty(t))
            } else {
                None
            },
            None => None,
        },
        TExpr::Local(i) => if i < lt.len() {
            Some(lt[i as int])
        } else {
            None
        },
        TExpr::Const(i) => if i < c.consts.len() {
            Some(to_xty(c.consts[i as int]))
        } else {
            None
        },
        TExpr::Bin(op, a, b) => if type_of(*a, c, lt) == Some(XTy::Int) && type_of(*b, c, lt) == Some(XTy::Int) {
            if is_arith(op) {
                Some(XTy::Int)
            } else if is_compare(op) {
                Some(XTy::Bool)
            } else {
                None
            }
        } else {
            None
        },
        TExpr::Eq(_, a, b) => match type_of(*a, c, lt) {
            Some(x) => if type_of(*b, c, lt) == Some(x) {
                Some(XTy::Bool)
            } else {
                None
            },
            None => None,
        },
        TExpr::Not(a) => if type_of(*a, c, lt) == Some(XTy::Bool) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Fold(_, es) => if all_bool(es@, c, lt) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Implies(a, b) => if type_of(*a, c, lt) == Some(XTy::Bool) && type_of(*b, c, lt) == Some(XTy::Bool) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Ite(p, a, b) => if type_of(*p, c, lt) == Some(XTy::Bool) {
            match type_of(*a, c, lt) {
                Some(x) => if type_of(*b, c, lt) == Some(x) {
                    Some(x)
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        },
        TExpr::Let(a, b) => match type_of(*a, c, lt) {
            Some(x) => type_of(*b, c, lt.push(x)),
            None => None,
        },
        TExpr::Quant(_, over, body) => {
            let bound: Option<XTy> = match over {
                Over::Type(t) => if wf_stype(sty(t), enums) && keys(sty(t), enums) is Some {
                    Some(to_xty(sty(t)))
                } else {
                    None
                },
                Over::Set(t, s) => if type_of(*s, c, lt) == Some(XTy::Set(Box::new(sty(t)))) {
                    Some(to_xty(sty(t)))
                } else {
                    None
                },
                Over::Map(t, m) => match type_of(*m, c, lt) {
                    Some(XTy::Map(k, _)) => if *k == sty(t) {
                        Some(to_xty(sty(t)))
                    } else {
                        None
                    },
                    _ => None,
                },
                Over::List(l) => match type_of(*l, c, lt) {
                    Some(XTy::List(t, _)) => Some(to_xty(*t)),
                    _ => None,
                },
            };
            match bound {
                Some(x) => if type_of(*body, c, lt.push(x)) == Some(XTy::Bool) {
                    Some(XTy::Bool)
                } else {
                    None
                },
                None => None,
            }
        },
        TExpr::Tuple(es) => match types_of(es@, c, lt) {
            Some(ts) => if ts.len() >= 1 {
                Some(XTy::Tuple(ts))
            } else {
                None
            },
            None => None,
        },
        TExpr::Record(names, es) => match types_of(es@, c, lt) {
            Some(ts) => if ts.len() >= 1 && names@.len() == ts.len() && names@.no_duplicates() {
                Some(XTy::Record(names@, ts))
            } else {
                None
            },
            None => None,
        },
        TExpr::Nth(a, i) => match type_of(*a, c, lt) {
            Some(XTy::Tuple(ts)) => if i < ts.len() {
                Some(ts[i as int])
            } else {
                None
            },
            _ => None,
        },
        TExpr::Field(a, name, i) => match type_of(*a, c, lt) {
            Some(XTy::Record(names, ts)) => if i < ts.len() && names[i as int] == name {
                Some(ts[i as int])
            } else {
                None
            },
            _ => None,
        },
        TExpr::None(t) => match element(sty(t), enums) {
            Some(x) => Some(XTy::Option(Box::new(x))),
            None => None,
        },
        TExpr::Some(a) => match type_of(*a, c, lt) {
            Some(x) => Some(XTy::Option(Box::new(x))),
            None => None,
        },
        TExpr::IsSome(a) => match type_of(*a, c, lt) {
            Some(XTy::Option(_)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::IsNone(a) => match type_of(*a, c, lt) {
            Some(XTy::Option(_)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::Unwrap(a) => match type_of(*a, c, lt) {
            Some(XTy::Option(x)) => Some(*x),
            _ => None,
        },
        TExpr::SetLit(t, es) => {
            let s = STy::Set(Box::new(sty(t)));
            if wf_stype(s, enums) && all_typed(es@, to_xty(sty(t)), c, lt) {
                Some(to_xty(s))
            } else {
                None
            }
        },
        TExpr::MapLit(k, v, items) => {
            let m = STy::Map(Box::new(sty(k)), Box::new(sty(v)));
            if wf_stype(m, enums) && items_typed(items@, to_xty(sty(k)), to_xty(sty(v)), c, lt) {
                Some(to_xty(m))
            } else {
                None
            }
        },
        TExpr::ListLit(t, max, es) => {
            let l = STy::List(Box::new(sty(t)), max);
            if wf_stype(l, enums) && es@.len() <= max && all_typed(es@, to_xty(sty(t)), c, lt) {
                Some(to_xty(l))
            } else {
                None
            }
        },
        TExpr::SetContains(t, a, x) => if type_of(*a, c, lt) == Some(XTy::Set(Box::new(sty(t)))) && type_of(
            *x,
            c,
            lt,
        ) == Some(to_xty(sty(t))) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::ListContains(a, x) => match type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => if type_of(*x, c, lt) == Some(to_xty(*t)) {
                Some(XTy::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Insert(t, a, x) => {
            let s = XTy::Set(Box::new(sty(t)));
            if type_of(*a, c, lt) == Some(s) && type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(s)
            } else {
                None
            }
        },
        TExpr::Remove(t, a, x) => {
            let s = XTy::Set(Box::new(sty(t)));
            if type_of(*a, c, lt) == Some(s) && type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(s)
            } else {
                None
            }
        },
        TExpr::SetBin(op, a, b) => match type_of(*a, c, lt) {
            Some(XTy::Set(e)) => if type_of(*b, c, lt) == Some(XTy::Set(e)) {
                match op {
                    SetOp::Subset => Some(XTy::Bool),
                    _ => Some(XTy::Set(e)),
                }
            } else {
                None
            },
            _ => None,
        },
        TExpr::Size(a) => match type_of(*a, c, lt) {
            Some(XTy::Set(_)) | Some(XTy::Map(_, _)) | Some(XTy::List(_, _)) => Some(XTy::Int),
            _ => None,
        },
        TExpr::IsEmpty(a) => match type_of(*a, c, lt) {
            Some(XTy::Set(_)) | Some(XTy::Map(_, _)) | Some(XTy::List(_, _)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::HasKey(t, a, x) => match type_of(*a, c, lt) {
            Some(XTy::Map(k, _)) => if *k == sty(t) && type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(XTy::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Get(t, a, x) => match type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(t) && type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(to_xty(*v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Put(kt, vt, a, x, y) => match type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(kt) && *v == sty(vt) && type_of(*x, c, lt) == Some(to_xty(*k))
                && type_of(*y, c, lt) == Some(to_xty(*v)) {
                Some(XTy::Map(k, v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Delete(t, a, x) => match type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(t) && type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(XTy::Map(k, v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Keys(a) => match type_of(*a, c, lt) {
            Some(XTy::Map(k, _)) => Some(XTy::Set(k)),
            _ => None,
        },
        TExpr::At(a, i) => match type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => if type_of(*i, c, lt) == Some(XTy::Int) {
                Some(to_xty(*t))
            } else {
                None
            },
            _ => None,
        },
        TExpr::First(a) => match type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => Some(to_xty(*t)),
            _ => None,
        },
        TExpr::Last(a) => match type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => Some(to_xty(*t)),
            _ => None,
        },
        TExpr::Push(t, max, a, x) => {
            let l = XTy::List(Box::new(sty(t)), max);
            if type_of(*a, c, lt) == Some(l) && type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(l)
            } else {
                None
            }
        },
        TExpr::Pop(a) => match type_of(*a, c, lt) {
            Some(XTy::List(t, n)) => Some(XTy::List(t, n)),
            _ => None,
        },
        TExpr::Shift(a) => match type_of(*a, c, lt) {
            Some(XTy::List(t, n)) => Some(XTy::List(t, n)),
            _ => None,
        },
    }
}

/// 式の列のすべてがBoolである。
pub open spec fn all_bool(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>) -> bool
    decreases es, 1nat,
{
    if es.len() == 0 {
        true
    } else {
        all_bool(es.drop_last(), c, lt) && type_of(es.last(), c, lt) == Some(XTy::Bool)
    }
}

/// 式の列のすべてが型 `x` を持つ。
pub open spec fn all_typed(es: Seq<TExpr>, x: XTy, c: SCtx, lt: Seq<XTy>) -> bool
    decreases es, 1nat,
{
    if es.len() == 0 {
        true
    } else {
        all_typed(es.drop_last(), x, c, lt) && type_of(es.last(), c, lt) == Some(x)
    }
}

/// Mapのリテラルの項目のキーが型 `k`、値が型 `v` を持つ。
pub open spec fn items_typed(items: Seq<Item>, k: XTy, v: XTy, c: SCtx, lt: Seq<XTy>) -> bool
    decreases items, 1nat,
{
    if items.len() == 0 {
        true
    } else {
        items_typed(items.drop_last(), k, v, c, lt) && type_of(items.last().key, c, lt) == Some(k) && type_of(
            items.last().value,
            c,
            lt,
        ) == Some(v)
    }
}

/// 式の列の型。どれかに型が付かなければ `None`。
pub open spec fn types_of(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>) -> Option<Seq<XTy>>
    decreases es, 1nat,
{
    if es.len() == 0 {
        Some(Seq::empty())
    } else {
        match (types_of(es.drop_last(), c, lt), type_of(es.last(), c, lt)) {
            (Some(ts), Some(x)) => Some(ts.push(x)),
            _ => None,
        }
    }
}


/// 型検査の文脈（実行時の表現）。
pub struct Scope {
    pub enums: Vec<i64>,
    pub states: Option<Vec<SType>>,
    pub args: Vec<SType>,
    pub next: bool,
    pub out: Option<SType>,
    pub consts: Vec<SType>,
}

pub open spec fn scope_view(s: &Scope) -> SCtx {
    SCtx {
        enums: s.enums@,
        states: match s.states {
            Some(v) => Some(stys(v@)),
            None => None,
        },
        args: stys(s.args@),
        next: s.next,
        out: match s.out {
            Some(t) => Some(sty(t)),
            None => None,
        },
        consts: stys(s.consts@),
    }
}

fn lit_type_exec(v: &Value, enums: &Vec<i64>) -> (r: Option<XType>)
    ensures
        r matches Some(x) ==> lit_type(*v, enums@) == Some(xty(x)),
{
    match v {
        Value::Bool(_) => Some(XType::Bool),
        Value::Int(_) => Some(XType::Int),
        Value::Enum(id, k) => if *id < enums.len() && 0 <= *k && *k < enums[*id] {
            Some(XType::Enum(*id))
        } else {
            None
        },
    }
}

fn element_exec(t: &SType, enums: &Vec<i64>) -> (r: Option<XType>)
    ensures
        r matches Some(x) ==> element(sty(*t), enums@) == Some(xty(x)),
{
    if wf_stype_exec(t, enums) {
        Some(to_xtype(t))
    } else {
        None
    }
}

/// 状態変数、引数、定数の型の列の `i` 番目の式の型。
fn slot_type(ts: &Vec<SType>, i: usize) -> (r: Option<XType>)
    ensures
        r matches Some(x) ==> i < ts@.len() && stys(ts@).len() == ts@.len() && xty(x) == to_xty(stys(ts@)[i as int]),
{
    if i < ts.len() {
        proof {
            lemma_stys(ts@);
        }
        Some(to_xtype(&ts[i]))
    } else {
        None
    }
}

/// 型検査器。型を返したら、それは [`type_of`] の値である。`lt` は局所変数の型で、検査の後に元に戻る。
pub fn check(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 2nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_)
        | TExpr::Bin(_, _, _) | TExpr::Eq(_, _, _) | TExpr::Not(_) | TExpr::Fold(_, _) | TExpr::Implies(_, _)
        | TExpr::Ite(_, _, _) | TExpr::Let(_, _) => check_core(e, s, lt),
        TExpr::Quant(_, _, _) | TExpr::Tuple(_) | TExpr::Record(_, _) | TExpr::Nth(_, _) | TExpr::Field(_, _, _)
        | TExpr::None(_) | TExpr::Some(_) | TExpr::IsSome(_) | TExpr::IsNone(_) | TExpr::Unwrap(_) => check_struct(
            e,
            s,
            lt,
        ),
        TExpr::SetLit(_, _) | TExpr::MapLit(_, _, _) | TExpr::ListLit(_, _, _) | TExpr::SetContains(_, _, _)
        | TExpr::ListContains(_, _) | TExpr::Insert(_, _, _) | TExpr::Remove(_, _, _) | TExpr::SetBin(_, _, _)
        | TExpr::Size(_) | TExpr::IsEmpty(_) => check_coll(e, s, lt),
        _ => check_access(e, s, lt),
    }
}

/// リテラル、参照、スカラーの演算、短絡する演算、`let` の型検査。
fn check_core(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 1nat,
{
    let ghost c = scope_view(s);
    let ghost l = xtys(lt@);
    match e {
        TExpr::Lit(v) => lit_type_exec(v, &s.enums),
        TExpr::Var(i) => match &s.states {
            Some(ts) => slot_type(ts, *i),
            None => None,
        },
        TExpr::Next(i) => match &s.states {
            Some(ts) => if s.next {
                slot_type(ts, *i)
            } else {
                None
            },
            None => None,
        },
        TExpr::Arg(i) => slot_type(&s.args, *i),
        TExpr::Out => match &s.out {
            Some(t) => if s.next {
                Some(to_xtype(t))
            } else {
                None
            },
            None => None,
        },
        TExpr::Local(i) => if *i < lt.len() {
            proof {
                lemma_xtys(lt@);
            }
            Some(copy_xtype(&lt[*i]))
        } else {
            None
        },
        TExpr::Const(i) => slot_type(&s.consts, *i),
        TExpr::Bin(op, a, b) => {
            let ta = check(a, s, lt);
            let tb = check(b, s, lt);
            match (ta, tb) {
                (Some(XType::Int), Some(XType::Int)) => match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => Some(XType::Int),
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Some(XType::Bool),
                    _ => None,
                },
                _ => None,
            }
        },
        TExpr::Eq(_, a, b) => match (check(a, s, lt), check(b, s, lt)) {
            (Some(x), Some(y)) => if xtype_eq(&x, &y) {
                Some(XType::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Not(a) => match check(a, s, lt) {
            Some(XType::Bool) => Some(XType::Bool),
            _ => None,
        },
        TExpr::Fold(_, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            if check_all(e, es, &XType::Bool, s, lt) {
                proof {
                    lemma_all_typed_bool(es@, c, l);
                }
                Some(XType::Bool)
            } else {
                None
            }
        },
        TExpr::Implies(a, b) => match (check(a, s, lt), check(b, s, lt)) {
            (Some(XType::Bool), Some(XType::Bool)) => Some(XType::Bool),
            _ => None,
        },
        TExpr::Ite(p, a, b) => match check(p, s, lt) {
            Some(XType::Bool) => match (check(a, s, lt), check(b, s, lt)) {
                (Some(x), Some(y)) => if xtype_eq(&x, &y) {
                    Some(x)
                } else {
                    None
                },
                _ => None,
            },
            _ => None,
        },
        TExpr::Let(a, b) => match check(a, s, lt) {
            Some(x) => {
                let ghost before = lt@;
                lt.push(x);
                proof {
                    assert(lt@.drop_last() == before);
                }
                let r = check(b, s, lt);
                lt.pop();
                proof {
                    assert(lt@ =~= before);
                }
                r
            },
            None => None,
        },
        _ => None,
    }
}

/// 量化、Tuple、Record、Optionの型検査。
fn check_struct(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 1nat,
{
    let ghost c = scope_view(s);
    let ghost l = xtys(lt@);
    match e {
        TExpr::Quant(_, _, _) => check_quant(e, s, lt),
        TExpr::Tuple(es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            match check_seq(e, es, s, lt) {
                Some(ts) => if ts.len() >= 1 {
                    proof {
                        lemma_xtys(ts@);
                    }
                    Some(XType::Tuple(ts))
                } else {
                    None
                },
                None => None,
            }
        },
        TExpr::Record(names, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            match check_seq(e, es, s, lt) {
                Some(ts) => if ts.len() >= 1 && names.len() == ts.len() && distinct_names(names) {
                    proof {
                        lemma_xtys(ts@);
                    }
                    Some(XType::Record(names.clone(), ts))
                } else {
                    None
                },
                None => None,
            }
        },
        TExpr::Nth(a, i) => match check(a, s, lt) {
            Some(XType::Tuple(ts)) => if *i < ts.len() {
                proof {
                    lemma_xtys(ts@);
                }
                Some(copy_xtype(&ts[*i]))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Field(a, name, i) => match check(a, s, lt) {
            Some(XType::Record(names, ts)) => if *i < ts.len() && *i < names.len() && names[*i] == *name {
                proof {
                    lemma_xtys(ts@);
                }
                Some(copy_xtype(&ts[*i]))
            } else {
                None
            },
            _ => None,
        },
        TExpr::None(t) => match element_exec(t, &s.enums) {
            Some(x) => Some(XType::Option(Box::new(x))),
            None => None,
        },
        TExpr::Some(a) => match check(a, s, lt) {
            Some(x) => Some(XType::Option(Box::new(x))),
            None => None,
        },
        TExpr::IsSome(a) => match check(a, s, lt) {
            Some(XType::Option(_)) => Some(XType::Bool),
            _ => None,
        },
        TExpr::IsNone(a) => match check(a, s, lt) {
            Some(XType::Option(_)) => Some(XType::Bool),
            _ => None,
        },
        TExpr::Unwrap(a) => match check(a, s, lt) {
            Some(XType::Option(x)) => Some(*x),
            _ => None,
        },
        _ => None,
    }
}

/// 量化の型検査。
fn check_quant(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 0nat,
{
    match e {
        TExpr::Quant(_, over, body) => {
            let bound: Option<XType> = match over {
                Over::Type(t) => if wf_stype_exec(t, &s.enums) && keys_exec(t, &s.enums).is_some() {
                    Some(to_xtype(t))
                } else {
                    None
                },
                Over::Set(t, a) => match check(a, s, lt) {
                    Some(XType::Set(u)) => if stype_eq(&u, t) {
                        Some(to_xtype(t))
                    } else {
                        None
                    },
                    _ => None,
                },
                Over::Map(t, a) => match check(a, s, lt) {
                    Some(XType::Map(k, _)) => if stype_eq(&k, t) {
                        Some(to_xtype(t))
                    } else {
                        None
                    },
                    _ => None,
                },
                Over::List(a) => match check(a, s, lt) {
                    Some(XType::List(u, _)) => Some(to_xtype(&u)),
                    _ => None,
                },
            };
            match bound {
                Some(x) => {
                    let ghost before = lt@;
                    lt.push(x);
                    proof {
                        assert(lt@.drop_last() == before);
                    }
                    let r = check(body, s, lt);
                    lt.pop();
                    proof {
                        assert(lt@ =~= before);
                    }
                    match r {
                        Some(XType::Bool) => Some(XType::Bool),
                        _ => None,
                    }
                },
                None => None,
            }
        },
        _ => None,
    }
}

/// Set、Map、Listのリテラルと、Setの演算と大きさの型検査。
fn check_coll(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 1nat,
{
    let ghost c = scope_view(s);
    let ghost l = xtys(lt@);
    match e {
        TExpr::SetLit(t, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            let set = SType::Set(Box::new(copy_stype(t)));
            if wf_stype_exec(&set, &s.enums) && check_all(e, es, &to_xtype(t), s, lt) {
                Some(to_xtype(&set))
            } else {
                None
            }
        },
        TExpr::MapLit(k, v, items) => {
            proof {
                assert(decreases_to!(*e => *items));
            }
            let map = SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v)));
            if wf_stype_exec(&map, &s.enums) && check_items(e, items, &to_xtype(k), &to_xtype(v), s, lt) {
                Some(to_xtype(&map))
            } else {
                None
            }
        },
        TExpr::ListLit(t, max, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            let list = SType::List(Box::new(copy_stype(t)), *max);
            if wf_stype_exec(&list, &s.enums) && es.len() <= *max && check_all(e, es, &to_xtype(t), s, lt) {
                Some(to_xtype(&list))
            } else {
                None
            }
        },
        TExpr::SetContains(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Set(u)), Some(y)) => if stype_eq(&u, t) && xtype_eq(&y, &to_xtype(t)) {
                Some(XType::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::ListContains(a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::List(u, _)), Some(y)) => if xtype_eq(&y, &to_xtype(&u)) {
                Some(XType::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Insert(t, a, x) | TExpr::Remove(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Set(u)), Some(y)) => if stype_eq(&u, t) && xtype_eq(&y, &to_xtype(t)) {
                Some(XType::Set(u))
            } else {
                None
            },
            _ => None,
        },
        TExpr::SetBin(op, a, b) => match (check(a, s, lt), check(b, s, lt)) {
            (Some(XType::Set(u)), Some(XType::Set(w))) => if stype_eq(&u, &w) {
                match op {
                    SetOp::Subset => Some(XType::Bool),
                    _ => Some(XType::Set(u)),
                }
            } else {
                None
            },
            _ => None,
        },
        TExpr::Size(a) => match check(a, s, lt) {
            Some(XType::Set(_)) | Some(XType::Map(_, _)) | Some(XType::List(_, _)) => Some(XType::Int),
            _ => None,
        },
        TExpr::IsEmpty(a) => match check(a, s, lt) {
            Some(XType::Set(_)) | Some(XType::Map(_, _)) | Some(XType::List(_, _)) => Some(XType::Bool),
            _ => None,
        },
        _ => None,
    }
}

/// Mapの参照と更新、Listの参照と更新の型検査。
fn check_access(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(x) ==> type_of(*e, scope_view(s), xtys(old(lt)@)) == Some(xty(x)),
    decreases e, 1nat,
{
    let ghost c = scope_view(s);
    let ghost l = xtys(lt@);
    match e {
        TExpr::HasKey(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Map(k, _)), Some(y)) => if stype_eq(&k, t) && xtype_eq(&y, &to_xtype(&k)) {
                Some(XType::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Get(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Map(k, v)), Some(y)) => if stype_eq(&k, t) && xtype_eq(&y, &to_xtype(&k)) {
                Some(to_xtype(&v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Put(kt, vt, a, x, y) => {
            let tm = check(a, s, lt);
            let tx = check(x, s, lt);
            let ty = check(y, s, lt);
            match (tm, tx, ty) {
                (Some(XType::Map(k, v)), Some(p), Some(q)) => if stype_eq(&k, kt) && stype_eq(&v, vt) && xtype_eq(
                    &p,
                    &to_xtype(&k),
                ) && xtype_eq(&q, &to_xtype(&v)) {
                    Some(XType::Map(k, v))
                } else {
                    None
                },
                _ => None,
            }
        },
        TExpr::Delete(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Map(k, v)), Some(y)) => if stype_eq(&k, t) && xtype_eq(&y, &to_xtype(&k)) {
                Some(XType::Map(k, v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Keys(a) => match check(a, s, lt) {
            Some(XType::Map(k, _)) => Some(XType::Set(k)),
            _ => None,
        },
        TExpr::At(a, i) => match (check(a, s, lt), check(i, s, lt)) {
            (Some(XType::List(u, _)), Some(XType::Int)) => Some(to_xtype(&u)),
            _ => None,
        },
        TExpr::First(a) | TExpr::Last(a) => match check(a, s, lt) {
            Some(XType::List(u, _)) => Some(to_xtype(&u)),
            _ => None,
        },
        TExpr::Push(t, max, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::List(u, n)), Some(y)) => if n == *max && stype_eq(&u, t) && xtype_eq(&y, &to_xtype(t)) {
                Some(XType::List(u, n))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Pop(a) | TExpr::Shift(a) => match check(a, s, lt) {
            Some(XType::List(u, n)) => Some(XType::List(u, n)),
            _ => None,
        },        _ => None,
    }
}

proof fn lemma_all_typed_bool(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>)
    requires
        all_typed(es, XTy::Bool, c, lt),
    ensures
        all_bool(es, c, lt),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_all_typed_bool(es.drop_last(), c, lt);
    }
}

/// 式の列のすべてが型 `x` を持つかを検査する。
fn check_all(_parent: &TExpr, es: &Vec<TExpr>, x: &XType, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *es),
    ensures
        final(lt)@ == old(lt)@,
        r ==> all_typed(es@, xty(*x), scope_view(s), xtys(old(lt)@)),
    decreases _parent, 0nat,
{
    let ghost l = xtys(lt@);
    let ghost l0 = lt@;
    let mut i = 0;
    while i < es.len()
        invariant
            decreases_to!(*_parent => *es),
            lt@ == l0,
            l0 == old(lt)@,
            l == xtys(l0),
            i <= es.len(),
            all_typed(es@.take(i as int), xty(*x), scope_view(s), l),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
            assert(es@.take(i + 1).last() == es@[i as int]);
        }
        match check(&es[i], s, lt) {
            Some(y) => if !xtype_eq(&y, x) {
                return false;
            },
            None => return false,
        }
        i += 1;
    }
    proof {
        assert(es@.take(es.len() as int) =~= es@);
    }
    true
}

/// 式の列の型。
fn check_seq(_parent: &TExpr, es: &Vec<TExpr>, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<Vec<XType>>)
    requires
        decreases_to!(*_parent => *es),
    ensures
        final(lt)@ == old(lt)@,
        r matches Some(ts) ==> types_of(es@, scope_view(s), xtys(old(lt)@)) == Some(xtys(ts@)),
    decreases _parent, 0nat,
{
    let ghost l = xtys(lt@);
    let ghost l0 = lt@;
    let mut out: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < es.len()
        invariant
            decreases_to!(*_parent => *es),
            lt@ == l0,
            l0 == old(lt)@,
            l == xtys(l0),
            i <= es.len(),
            types_of(es@.take(i as int), scope_view(s), l) == Some(xtys(out@)),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
            assert(es@.take(i + 1).drop_last() =~= es@.take(i as int));
            assert(es@.take(i + 1).last() == es@[i as int]);
        }
        match check(&es[i], s, lt) {
            Some(y) => {
                let ghost before = out@;
                out.push(y);
                proof {
                    assert(out@.drop_last() == before);
                }
            },
            None => return None,
        }
        i += 1;
    }
    proof {
        assert(es@.take(es.len() as int) =~= es@);
    }
    Some(out)
}

/// Mapのリテラルの項目の型を検査する。
fn check_items(_parent: &TExpr, items: &Vec<Item>, k: &XType, v: &XType, s: &Scope, lt: &mut Vec<XType>) -> (r:
    bool)
    requires
        decreases_to!(*_parent => *items),
    ensures
        final(lt)@ == old(lt)@,
        r ==> items_typed(items@, xty(*k), xty(*v), scope_view(s), xtys(old(lt)@)),
    decreases _parent, 0nat,
{
    let ghost l = xtys(lt@);
    let ghost l0 = lt@;
    let mut i = 0;
    while i < items.len()
        invariant
            decreases_to!(*_parent => *items),
            lt@ == l0,
            l0 == old(lt)@,
            l == xtys(l0),
            i <= items.len(),
            items_typed(items@.take(i as int), xty(*k), xty(*v), scope_view(s), l),
        decreases items.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*items, i as int);
            assert(items@.take(i + 1).drop_last() =~= items@.take(i as int));
            assert(items@.take(i + 1).last() == items@[i as int]);
        }
        let item = &items[i];
        proof {
            assert(decreases_to!(*_parent => item.key));
            assert(decreases_to!(*_parent => item.value));
        }
        let tk = check(&item.key, s, lt);
        let tv = check(&item.value, s, lt);
        match (tk, tv) {
            (Some(a), Some(b)) => if !(xtype_eq(&a, k) && xtype_eq(&b, v)) {
                return false;
            },
            _ => return false,
        }
        i += 1;
    }
    proof {
        assert(items@.take(items.len() as int) =~= items@);
    }
    true
}

} // verus!
