//! IRの式の型付け規則（仕様）と型検査器。
//!
//! [`ir_type_of`] は、型付き構文木の式の型を決める規則である。型が付かなければ `None`。
//! 整数の範囲は式の型に持たない。この規則は `fmspec-ir` の型検査とは別に定めてあり、両者の一致は証明していない。
//! `fmspec-ir` が受理したモデルを中核の型検査も受理することは、ランダムなテスト（`crates/fmspec-ir/tests/random_ir.rs`）で確かめる。
//! Setの要素、Mapのキーと値、Listの要素になる式の型は、格納の型の式の型 [`to_xty`] と等しくなければならない。
//! 要素の型の注釈は、実際の型と一致しなければならない。
//!
//! [`check`] は型検査器で、その結果が [`ir_type_of`] の値と一致することを証明してある（型が付く式を拒否しない）。
//! 下ろしの前に、[`crate::model_total::check_model`] がモデル全体の式でこれと大きさの条件を確かめる。
//! 型が付く式の下ろしが型の誤りで失敗しないこと（全域性）は [`crate::total`] の仕様で述べる。

#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, lemma_stys, lemma_xtys, sty, stys, to_xty, wf_stype, xty, xtys, XTy};
use crate::encoding::{STy, SType, XType};
use crate::model::{BinOp, Value};
use crate::source::{Item, Over, SetOp, TExpr};
use crate::stype_exec::{copy_stype, copy_xtype, distinct_names, keys_exec, stype_eq, to_xtype};
use crate::stype_exec::{wf_stype_exec, xtype_eq};
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
pub open spec fn ir_type_of(e: TExpr, c: SCtx, lt: Seq<XTy>) -> Option<XTy>
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
        TExpr::Bin(op, a, b) => if ir_type_of(*a, c, lt) == Some(XTy::Int) && ir_type_of(*b, c, lt) == Some(XTy::Int) {
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
        TExpr::Eq(_, a, b) => match ir_type_of(*a, c, lt) {
            Some(x) => if ir_type_of(*b, c, lt) == Some(x) {
                Some(XTy::Bool)
            } else {
                None
            },
            None => None,
        },
        TExpr::Not(a) => if ir_type_of(*a, c, lt) == Some(XTy::Bool) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Fold(_, es) => if all_bool(es@, c, lt) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Implies(a, b) => if ir_type_of(*a, c, lt) == Some(XTy::Bool) && ir_type_of(*b, c, lt) == Some(XTy::Bool) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::Ite(p, a, b) => if ir_type_of(*p, c, lt) == Some(XTy::Bool) {
            match ir_type_of(*a, c, lt) {
                Some(x) => if ir_type_of(*b, c, lt) == Some(x) {
                    Some(x)
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        },
        TExpr::Let(a, b) => match ir_type_of(*a, c, lt) {
            Some(x) => ir_type_of(*b, c, lt.push(x)),
            None => None,
        },
        TExpr::Quant(_, over, body) => {
            let bound: Option<XTy> = match over {
                Over::Type(t) => if wf_stype(sty(t), enums) && keys(sty(t), enums) is Some {
                    Some(to_xty(sty(t)))
                } else {
                    None
                },
                Over::Set(t, s) => if ir_type_of(*s, c, lt) == Some(XTy::Set(Box::new(sty(t)))) {
                    Some(to_xty(sty(t)))
                } else {
                    None
                },
                Over::Map(t, m) => match ir_type_of(*m, c, lt) {
                    Some(XTy::Map(k, _)) => if *k == sty(t) {
                        Some(to_xty(sty(t)))
                    } else {
                        None
                    },
                    _ => None,
                },
                Over::List(l) => match ir_type_of(*l, c, lt) {
                    Some(XTy::List(t, _)) => Some(to_xty(*t)),
                    _ => None,
                },
            };
            match bound {
                Some(x) => if ir_type_of(*body, c, lt.push(x)) == Some(XTy::Bool) {
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
        TExpr::Nth(a, i) => match ir_type_of(*a, c, lt) {
            Some(XTy::Tuple(ts)) => if i < ts.len() {
                Some(ts[i as int])
            } else {
                None
            },
            _ => None,
        },
        TExpr::Field(a, name, i) => match ir_type_of(*a, c, lt) {
            Some(XTy::Record(names, ts)) => if i < ts.len() && i < names.len() && names[i as int] == name {
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
        TExpr::Some(a) => match ir_type_of(*a, c, lt) {
            Some(x) => Some(XTy::Option(Box::new(x))),
            None => None,
        },
        TExpr::IsSome(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::Option(_)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::IsNone(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::Option(_)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::Unwrap(a) => match ir_type_of(*a, c, lt) {
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
        TExpr::SetContains(t, a, x) => if ir_type_of(*a, c, lt) == Some(XTy::Set(Box::new(sty(t)))) && ir_type_of(
            *x,
            c,
            lt,
        ) == Some(to_xty(sty(t))) {
            Some(XTy::Bool)
        } else {
            None
        },
        TExpr::ListContains(a, x) => match ir_type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => if ir_type_of(*x, c, lt) == Some(to_xty(*t)) {
                Some(XTy::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Insert(t, a, x) => {
            let s = XTy::Set(Box::new(sty(t)));
            if ir_type_of(*a, c, lt) == Some(s) && ir_type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(s)
            } else {
                None
            }
        },
        TExpr::Remove(t, a, x) => {
            let s = XTy::Set(Box::new(sty(t)));
            if ir_type_of(*a, c, lt) == Some(s) && ir_type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(s)
            } else {
                None
            }
        },
        TExpr::SetBin(op, a, b) => match ir_type_of(*a, c, lt) {
            Some(XTy::Set(e)) => if ir_type_of(*b, c, lt) == Some(XTy::Set(e)) {
                match op {
                    SetOp::Subset => Some(XTy::Bool),
                    _ => Some(XTy::Set(e)),
                }
            } else {
                None
            },
            _ => None,
        },
        TExpr::Size(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::Set(_)) | Some(XTy::Map(_, _)) | Some(XTy::List(_, _)) => Some(XTy::Int),
            _ => None,
        },
        TExpr::IsEmpty(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::Set(_)) | Some(XTy::Map(_, _)) | Some(XTy::List(_, _)) => Some(XTy::Bool),
            _ => None,
        },
        TExpr::HasKey(t, a, x) => match ir_type_of(*a, c, lt) {
            Some(XTy::Map(k, _)) => if *k == sty(t) && ir_type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(XTy::Bool)
            } else {
                None
            },
            _ => None,
        },
        TExpr::Get(t, a, x) => match ir_type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(t) && ir_type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(to_xty(*v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Put(kt, vt, a, x, y) => match ir_type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(kt) && *v == sty(vt) && ir_type_of(*x, c, lt) == Some(to_xty(*k))
                && ir_type_of(*y, c, lt) == Some(to_xty(*v)) {
                Some(XTy::Map(k, v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Delete(t, a, x) => match ir_type_of(*a, c, lt) {
            Some(XTy::Map(k, v)) => if *k == sty(t) && ir_type_of(*x, c, lt) == Some(to_xty(*k)) {
                Some(XTy::Map(k, v))
            } else {
                None
            },
            _ => None,
        },
        TExpr::Keys(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::Map(k, _)) => Some(XTy::Set(k)),
            _ => None,
        },
        TExpr::At(a, i) => match ir_type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => if ir_type_of(*i, c, lt) == Some(XTy::Int) {
                Some(to_xty(*t))
            } else {
                None
            },
            _ => None,
        },
        TExpr::First(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => Some(to_xty(*t)),
            _ => None,
        },
        TExpr::Last(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::List(t, _)) => Some(to_xty(*t)),
            _ => None,
        },
        TExpr::Push(t, max, a, x) => {
            let l = XTy::List(Box::new(sty(t)), max);
            if ir_type_of(*a, c, lt) == Some(l) && ir_type_of(*x, c, lt) == Some(to_xty(sty(t))) {
                Some(l)
            } else {
                None
            }
        },
        TExpr::Pop(a) => match ir_type_of(*a, c, lt) {
            Some(XTy::List(t, n)) => Some(XTy::List(t, n)),
            _ => None,
        },
        TExpr::Shift(a) => match ir_type_of(*a, c, lt) {
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
        all_bool(es.drop_last(), c, lt) && ir_type_of(es.last(), c, lt) == Some(XTy::Bool)
    }
}

/// 式の列のすべてが型 `x` を持つ。
pub open spec fn all_typed(es: Seq<TExpr>, x: XTy, c: SCtx, lt: Seq<XTy>) -> bool
    decreases es, 1nat,
{
    if es.len() == 0 {
        true
    } else {
        all_typed(es.drop_last(), x, c, lt) && ir_type_of(es.last(), c, lt) == Some(x)
    }
}

/// Mapのリテラルの項目のキーが型 `k`、値が型 `v` を持つ。
pub open spec fn items_typed(items: Seq<Item>, k: XTy, v: XTy, c: SCtx, lt: Seq<XTy>) -> bool
    decreases items, 1nat,
{
    if items.len() == 0 {
        true
    } else {
        items_typed(items.drop_last(), k, v, c, lt) && ir_type_of(items.last().key, c, lt) == Some(k) && ir_type_of(
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
        match (types_of(es.drop_last(), c, lt), ir_type_of(es.last(), c, lt)) {
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
        r is None ==> lit_type(*v, enums@) is None,
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
        r is None ==> element(sty(*t), enums@) is None,
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
        r is None ==> i >= ts@.len() && stys(ts@).len() == ts@.len(),
{
    proof {
        lemma_stys(ts@);
    }
    if i < ts.len() {
        Some(to_xtype(&ts[i]))
    } else {
        None
    }
}

/// 型検査の結果が型付け規則の値と一致する。
pub open spec fn agrees(r: Option<XType>, t: Option<XTy>) -> bool {
    match r {
        Some(x) => t == Some(xty(x)),
        None => t is None,
    }
}

/// 型検査器。結果は [`ir_type_of`] の値と一致する。`lt` は局所変数の型で、検査の後に元に戻る。
pub fn check(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 2nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_)
        | TExpr::Const(_) => check_leaf(e, s, lt),
        TExpr::Bin(_, _, _) => check_bin(e, s, lt),
        TExpr::Eq(_, _, _) | TExpr::Not(_) | TExpr::Implies(_, _) => check_logic(e, s, lt),
        TExpr::Fold(_, _) => check_fold(e, s, lt),
        TExpr::Ite(_, _, _) => check_ite(e, s, lt),
        TExpr::Let(_, _) => check_let(e, s, lt),
        TExpr::Quant(_, _, _) => check_quant(e, s, lt),
        TExpr::Tuple(_) | TExpr::Record(_, _) => check_tuple(e, s, lt),
        TExpr::Nth(_, _) | TExpr::Field(_, _, _) => check_proj(e, s, lt),
        TExpr::None(_) | TExpr::Some(_) | TExpr::IsSome(_) | TExpr::IsNone(_) | TExpr::Unwrap(_) => check_opt(e, s, lt),
        TExpr::SetLit(_, _) | TExpr::MapLit(_, _, _) | TExpr::ListLit(_, _, _) => check_coll_lit(e, s, lt),
        TExpr::SetContains(_, _, _) | TExpr::Insert(_, _, _) | TExpr::Remove(_, _, _) | TExpr::SetBin(_, _, _) => check_set(
            e,
            s,
            lt,
        ),
        TExpr::ListContains(_, _) | TExpr::Size(_) | TExpr::IsEmpty(_) => check_size(e, s, lt),
        TExpr::HasKey(_, _, _) | TExpr::Get(_, _, _) | TExpr::Put(_, _, _, _, _) | TExpr::Delete(_, _, _)
        | TExpr::Keys(_) => check_map(e, s, lt),
        TExpr::At(_, _) | TExpr::First(_) | TExpr::Last(_) | TExpr::Push(_, _, _, _) | TExpr::Pop(_) | TExpr::Shift(
            _,
        ) => check_list(e, s, lt),
    }
}

/// リテラルと参照。
fn check_leaf(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    proof {
        lemma_xtys(lt@);
    }
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
            Some(copy_xtype(&lt[*i]))
        } else {
            None
        },
        TExpr::Const(i) => slot_type(&s.consts, *i),
        _ => None,
    }
}

/// 整数の演算と比較。
fn check_bin(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Bin,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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
        _ => None,
    }
}

/// 等価比較、否定、含意。
fn check_logic(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Eq || e is Not || e is Implies,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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
        TExpr::Implies(a, b) => match (check(a, s, lt), check(b, s, lt)) {
            (Some(XType::Bool), Some(XType::Bool)) => Some(XType::Bool),
            _ => None,
        },
        _ => None,
    }
}

/// `all` と `any`。
fn check_fold(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Fold,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
        TExpr::Fold(_, es) => {
            let ghost c = scope_view(s);
            let ghost l = xtys(lt@);
            proof {
                assert(decreases_to!(*e => *es));
            }
            let ok = check_all(e, es, &XType::Bool, s, lt);
            proof {
                lemma_all_typed_bool(es@, c, l);
            }
            if ok {
                Some(XType::Bool)
            } else {
                None
            }
        },
        _ => None,
    }
}

/// 条件式。
fn check_ite(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Ite,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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
        _ => None,
    }
}

/// `let`。
fn check_let(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Let,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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

/// 量化。
fn check_quant(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Quant,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
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

/// TupleとRecord。
fn check_tuple(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Tuple || e is Record,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
        TExpr::Tuple(es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            match check_seq(e, es, s, lt) {
                Some(ts) => {
                    proof {
                        lemma_xtys(ts@);
                    }
                    if ts.len() >= 1 {
                        Some(XType::Tuple(ts))
                    } else {
                        None
                    }
                },
                None => None,
            }
        },
        TExpr::Record(names, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            match check_seq(e, es, s, lt) {
                Some(ts) => {
                    proof {
                        lemma_xtys(ts@);
                    }
                    if ts.len() >= 1 && names.len() == ts.len() && distinct_names(names) {
                        Some(XType::Record(names.clone(), ts))
                    } else {
                        None
                    }
                },
                None => None,
            }
        },
        _ => None,
    }
}

/// Tupleの要素とRecordのフィールド。
fn check_proj(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is Nth || e is Field,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
        TExpr::Nth(a, i) => match check(a, s, lt) {
            Some(XType::Tuple(ts)) => {
                proof {
                    lemma_xtys(ts@);
                }
                if *i < ts.len() {
                    Some(copy_xtype(&ts[*i]))
                } else {
                    None
                }
            },
            _ => None,
        },
        TExpr::Field(a, name, i) => match check(a, s, lt) {
            Some(XType::Record(names, ts)) => {
                proof {
                    lemma_xtys(ts@);
                }
                if *i < ts.len() && *i < names.len() && names[*i] == *name {
                    Some(copy_xtype(&ts[*i]))
                } else {
                    None
                }
            },
            _ => None,
        },
        _ => None,
    }
}

/// Option。
fn check_opt(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is None || e is Some || e is IsSome || e is IsNone || e is Unwrap,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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

/// Set、Map、Listのリテラル。
fn check_coll_lit(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is SetLit || e is MapLit || e is ListLit,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
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
        _ => None,
    }
}

/// Setの要素の検査と演算。
fn check_set(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is SetContains || e is Insert || e is Remove || e is SetBin,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
        TExpr::SetContains(t, a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::Set(u)), Some(y)) => if stype_eq(&u, t) && xtype_eq(&y, &to_xtype(t)) {
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
        _ => None,
    }
}

/// Listの要素の検査と、大きさ。
fn check_size(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is ListContains || e is Size || e is IsEmpty,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
        TExpr::ListContains(a, x) => match (check(a, s, lt), check(x, s, lt)) {
            (Some(XType::List(u, _)), Some(y)) => if xtype_eq(&y, &to_xtype(&u)) {
                Some(XType::Bool)
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

/// Mapの参照と更新。
fn check_map(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is HasKey || e is Get || e is Put || e is Delete || e is Keys,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
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
        _ => None,
    }
}

/// Listの参照と更新。
fn check_list(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    requires
        e is At || e is First || e is Last || e is Push || e is Pop || e is Shift,
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, ir_type_of(*e, scope_view(s), xtys(old(lt)@))),
    decreases e, 1nat,
{
    match e {
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
        },
        _ => None,
    }
}

pub proof fn lemma_all_typed_bool(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>)
    ensures
        all_bool(es, c, lt) == all_typed(es, XTy::Bool, c, lt),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_all_typed_bool(es.drop_last(), c, lt);
    }
}

/// 列の型付けは、要素ごとの型付けと同じである。
pub proof fn lemma_all_typed_iff(es: Seq<TExpr>, x: XTy, c: SCtx, lt: Seq<XTy>)
    ensures
        all_typed(es, x, c, lt) == forall|j: int| 0 <= j < es.len() ==> ir_type_of(#[trigger] es[j], c, lt) == Some(x),
    decreases es.len(),
{
    if es.len() > 0 {
        let p = es.drop_last();
        lemma_all_typed_iff(p, x, c, lt);
        assert(es.last() == es[es.len() - 1]);
        if forall|j: int| 0 <= j < es.len() ==> ir_type_of(#[trigger] es[j], c, lt) == Some(x) {
            assert forall|j: int| 0 <= j < p.len() implies ir_type_of(#[trigger] p[j], c, lt) == Some(x) by {
                assert(p[j] == es[j]);
            }
        }
        if all_typed(es, x, c, lt) {
            assert forall|j: int| 0 <= j < es.len() implies ir_type_of(#[trigger] es[j], c, lt) == Some(x) by {
                if j < p.len() {
                    assert(p[j] == es[j]);
                }
            }
        }
    }
}

pub proof fn lemma_types_of_iff(es: Seq<TExpr>, c: SCtx, lt: Seq<XTy>)
    ensures
        types_of(es, c, lt) is Some == forall|j: int| 0 <= j < es.len() ==> ir_type_of(#[trigger] es[j], c, lt) is Some,
        types_of(es, c, lt) matches Some(ts) ==> ts.len() == es.len(),
    decreases es.len(),
{
    if es.len() > 0 {
        let p = es.drop_last();
        lemma_types_of_iff(p, c, lt);
        assert(es.last() == es[es.len() - 1]);
        if forall|j: int| 0 <= j < es.len() ==> ir_type_of(#[trigger] es[j], c, lt) is Some {
            assert forall|j: int| 0 <= j < p.len() implies ir_type_of(#[trigger] p[j], c, lt) is Some by {
                assert(p[j] == es[j]);
            }
        }
        if types_of(es, c, lt) is Some {
            assert forall|j: int| 0 <= j < es.len() implies ir_type_of(#[trigger] es[j], c, lt) is Some by {
                if j < p.len() {
                    assert(p[j] == es[j]);
                }
            }
        }
    }
}

pub proof fn lemma_items_typed_iff(items: Seq<Item>, k: XTy, v: XTy, c: SCtx, lt: Seq<XTy>)
    ensures
        items_typed(items, k, v, c, lt) == forall|j: int|
            0 <= j < items.len() ==> ir_type_of((#[trigger] items[j]).key, c, lt) == Some(k) && ir_type_of(items[j].value, c, lt)
                == Some(v),
    decreases items.len(),
{
    if items.len() > 0 {
        let p = items.drop_last();
        lemma_items_typed_iff(p, k, v, c, lt);
        assert(items.last() == items[items.len() - 1]);
        if forall|j: int|
            0 <= j < items.len() ==> ir_type_of((#[trigger] items[j]).key, c, lt) == Some(k) && ir_type_of(items[j].value, c, lt)
                == Some(v) {
            assert forall|j: int| 0 <= j < p.len() implies ir_type_of((#[trigger] p[j]).key, c, lt) == Some(k) && ir_type_of(
                p[j].value,
                c,
                lt,
            ) == Some(v) by {
                assert(p[j] == items[j]);
            }
        }
        if items_typed(items, k, v, c, lt) {
            assert forall|j: int| 0 <= j < items.len() implies ir_type_of((#[trigger] items[j]).key, c, lt) == Some(k)
                && ir_type_of(items[j].value, c, lt) == Some(v) by {
                if j < p.len() {
                    assert(p[j] == items[j]);
                }
            }
        }
    }
}

/// 式の列のすべてが型 `x` を持つかを検査する。
fn check_all(_parent: &TExpr, es: &Vec<TExpr>, x: &XType, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *es),
    ensures
        final(lt)@ == old(lt)@,
        r == all_typed(es@, xty(*x), scope_view(s), xtys(old(lt)@)),
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
                proof {
                    lemma_all_typed_iff(es@, xty(*x), scope_view(s), l);
                }
                return false;
            },
            None => {
                proof {
                    lemma_all_typed_iff(es@, xty(*x), scope_view(s), l);
                }
                return false;
            },
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
        r is None ==> types_of(es@, scope_view(s), xtys(old(lt)@)) is None,
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
            None => {
                proof {
                    lemma_types_of_iff(es@, scope_view(s), l);
                }
                return None;
            },
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
        r == items_typed(items@, xty(*k), xty(*v), scope_view(s), xtys(old(lt)@)),
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
                proof {
                    lemma_items_typed_iff(items@, xty(*k), xty(*v), scope_view(s), l);
                }
                return false;
            },
            _ => {
                proof {
                    lemma_items_typed_iff(items@, xty(*k), xty(*v), scope_view(s), l);
                }
                return false;
            },
        }
        i += 1;
    }
    proof {
        assert(items@.take(items.len() as int) =~= items@);
    }
    true
}

} // verus!
