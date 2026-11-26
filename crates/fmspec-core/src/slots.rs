//! 下ろしで使う、スロットの式の組み立て。
//!
//! 下ろしは、IRの式の値を、スロットごとの中核の式の列にする（[`crate::encoding`] の符号化）。
//! ここにあるのは、その部品である。部品は、長さや型の合わない入力には `None` を返す。
//! 下ろしは `None` を内部エラーにするので、`None` を返すことは健全性を損なわない。

use crate::bindings::wrap_bindings;
use crate::encoding::{keys_exec, to_xtype, SType, XType};
use crate::expr_copy::copy_expr;
use crate::model::{BinOp, Expr, Type, Value};
use crate::ranking::{mixed_rank_expr, offset_rank, option_rank};
use vstd::prelude::*;

verus! {

// ---- 中核の式の組み立て ----

pub open spec fn bool_lit(b: bool) -> Expr {
    Expr::Const(Value::Bool(b))
}

pub open spec fn int_lit(x: i64) -> Expr {
    Expr::Const(Value::Int(x))
}

pub fn cb(x: bool) -> (r: Expr)
    ensures
        r == bool_lit(x),
{
    Expr::Const(Value::Bool(x))
}

pub fn ci(x: i64) -> (r: Expr)
    ensures
        r == int_lit(x),
{
    Expr::Const(Value::Int(x))
}

pub fn is_bool_lit(e: &Expr, b: bool) -> (r: bool)
    ensures
        r == (*e == bool_lit(b)),
{
    match e {
        Expr::Const(Value::Bool(x)) => *x == b,
        _ => false,
    }
}

pub open spec fn and_s(x: Expr, y: Expr) -> Expr {
    if x == bool_lit(true) {
        y
    } else if y == bool_lit(true) {
        x
    } else {
        Expr::And(Box::new(x), Box::new(y))
    }
}

pub open spec fn or_s(x: Expr, y: Expr) -> Expr {
    if x == bool_lit(false) {
        y
    } else if y == bool_lit(false) {
        x
    } else {
        Expr::Or(Box::new(x), Box::new(y))
    }
}

pub open spec fn implies_s(x: Expr, y: Expr) -> Expr {
    if y == bool_lit(true) {
        y
    } else {
        Expr::Implies(Box::new(x), Box::new(y))
    }
}

/// 一方が真のリテラルなら、もう一方にする。
pub fn and(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == and_s(x, y),
{
    if is_bool_lit(&x, true) {
        y
    } else if is_bool_lit(&y, true) {
        x
    } else {
        Expr::And(Box::new(x), Box::new(y))
    }
}

/// 一方が偽のリテラルなら、もう一方にする。
pub fn or(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == or_s(x, y),
{
    if is_bool_lit(&x, false) {
        y
    } else if is_bool_lit(&y, false) {
        x
    } else {
        Expr::Or(Box::new(x), Box::new(y))
    }
}

/// 後件が真のリテラルなら、真にする。
pub fn implies(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == implies_s(x, y),
{
    if is_bool_lit(&y, true) {
        y
    } else {
        Expr::Implies(Box::new(x), Box::new(y))
    }
}

pub fn not(x: Expr) -> (r: Expr)
    ensures
        r == Expr::Not(Box::new(x)),
{
    Expr::Not(Box::new(x))
}

pub fn ite(c: Expr, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == Expr::Ite(Box::new(c), Box::new(x), Box::new(y)),
{
    Expr::Ite(Box::new(c), Box::new(x), Box::new(y))
}

pub fn bin(op: BinOp, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == Expr::Bin(op, Box::new(x), Box::new(y)),
{
    Expr::Bin(op, Box::new(x), Box::new(y))
}

pub fn eq(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == Expr::Bin(BinOp::Eq, Box::new(x), Box::new(y)),
{
    Expr::Bin(BinOp::Eq, Box::new(x), Box::new(y))
}

/// 式の列の複製。
pub fn copy_exprs(xs: &Vec<Expr>) -> (r: Vec<Expr>)
    ensures
        r@ == xs@,
{
    sub_exprs(xs, 0, xs.len())
}

/// 式の列の `lo..hi` の部分の複製。
pub fn sub_exprs(xs: &Vec<Expr>, lo: usize, hi: usize) -> (r: Vec<Expr>)
    ensures
        lo <= hi <= xs@.len() ==> r@ == xs@.subrange(lo as int, hi as int),
{
    let mut out: Vec<Expr> = Vec::new();
    if !(lo <= hi && hi <= xs.len()) {
        return out;
    }
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= xs@.len(),
            out@ == xs@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(copy_expr(&xs[i]));
        proof {
            assert(out@ =~= xs@.subrange(lo as int, i + 1));
        }
        i += 1;
    }
    out
}

// ---- 平衡した二分木 ----

/// 二分木の節の作り方。
#[derive(Clone, Copy)]
pub enum Join {
    /// [`and`]（真のリテラルを省く）。
    And,
    /// [`or`]（偽のリテラルを省く）。
    Or,
    /// `Expr::And`。
    RawAnd,
    /// `Expr::Or`。
    RawOr,
    /// 整数の和。
    Add,
}

pub open spec fn join_s(k: Join, x: Expr, y: Expr) -> Expr {
    match k {
        Join::And => and_s(x, y),
        Join::Or => or_s(x, y),
        Join::RawAnd => Expr::And(Box::new(x), Box::new(y)),
        Join::RawOr => Expr::Or(Box::new(x), Box::new(y)),
        Join::Add => Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)),
    }
}

fn join(k: Join, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == join_s(k, x, y),
{
    match k {
        Join::And => and(x, y),
        Join::Or => or(x, y),
        Join::RawAnd => Expr::And(Box::new(x), Box::new(y)),
        Join::RawOr => Expr::Or(Box::new(x), Box::new(y)),
        Join::Add => Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)),
    }
}

/// 列を平衡した二分木にたたむ。前半は長さの半分（切り捨て）。空なら `unit`。
pub open spec fn tree_s(items: Seq<Expr>, unit: Expr, k: Join) -> Expr
    decreases items.len(),
{
    if items.len() == 0 {
        unit
    } else if items.len() == 1 {
        items[0]
    } else {
        let m = items.len() / 2;
        join_s(k, tree_s(items.take(m as int), unit, k), tree_s(items.skip(m as int), unit, k))
    }
}

fn tree_range(items: &Vec<Expr>, lo: usize, hi: usize, unit: &Expr, k: Join) -> (r: Expr)
    requires
        lo <= hi <= items@.len(),
    ensures
        r == tree_s(items@.subrange(lo as int, hi as int), *unit, k),
    decreases hi - lo,
{
    let ghost s = items@.subrange(lo as int, hi as int);
    if hi - lo == 0 {
        copy_expr(unit)
    } else if hi - lo == 1 {
        copy_expr(&items[lo])
    } else {
        let mid = lo + (hi - lo) / 2;
        proof {
            assert(s.take(((hi - lo) / 2) as int) =~= items@.subrange(lo as int, mid as int));
            assert(s.skip(((hi - lo) / 2) as int) =~= items@.subrange(mid as int, hi as int));
        }
        let l = tree_range(items, lo, mid, unit, k);
        let r = tree_range(items, mid, hi, unit, k);
        join(k, l, r)
    }
}

pub fn tree(items: &Vec<Expr>, unit: Expr, k: Join) -> (r: Expr)
    ensures
        r == tree_s(items@, unit, k),
{
    proof {
        assert(items@.subrange(0, items@.len() as int) =~= items@);
    }
    tree_range(items, 0, items.len(), &unit, k)
}

/// すべてが真。
pub fn all_of(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, bool_lit(true), Join::And),
{
    tree(items, cb(true), Join::And)
}

/// どれかが真。
pub fn any_of(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, bool_lit(false), Join::Or),
{
    tree(items, cb(false), Join::Or)
}

/// 整数の和。
pub fn sum(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, int_lit(0), Join::Add),
{
    tree(items, ci(0), Join::Add)
}

// ---- 式の性質 ----

/// 評価が失敗しうる。整数の演算は、値によってはオーバーフローするので失敗しうるとみなす。
pub open spec fn may_fail_s(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Bin(op, x, y) => op is Add || op is Sub || op is Mul || op is Div || op is Mod || may_fail_s(*x)
            || may_fail_s(*y),
        Expr::Fail(_, _) => true,
        Expr::Not(x) => may_fail_s(*x),
        Expr::Code(x) => may_fail_s(*x),
        Expr::And(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Or(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Implies(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Let(x, y) => may_fail_s(*x) || may_fail_s(*y),
        Expr::Ite(c, x, y) => may_fail_s(*c) || may_fail_s(*x) || may_fail_s(*y),
        Expr::Forall(_, _, _, body) => may_fail_s(*body),
        Expr::Exists(_, _, _, body) => may_fail_s(*body),
        _ => false,
    }
}

pub fn may_fail(e: &Expr) -> (r: bool)
    ensures
        r == may_fail_s(*e),
    decreases e,
{
    match e {
        Expr::Bin(op, x, y) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => true,
            _ => may_fail(x) || may_fail(y),
        },
        Expr::Fail(_, _) => true,
        Expr::Not(x) => may_fail(x),
        Expr::Code(x) => may_fail(x),
        Expr::And(x, y) => may_fail(x) || may_fail(y),
        Expr::Or(x, y) => may_fail(x) || may_fail(y),
        Expr::Implies(x, y) => may_fail(x) || may_fail(y),
        Expr::Let(x, y) => may_fail(x) || may_fail(y),
        Expr::Ite(c, x, y) => may_fail(c) || may_fail(x) || may_fail(y),
        Expr::Forall(_, _, _, body) => may_fail(body),
        Expr::Exists(_, _, _, body) => may_fail(body),
        _ => false,
    }
}

/// 束縛子（`let`、量化）を含む。
pub open spec fn binds_s(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::Let(_, _) => true,
        Expr::Forall(_, _, _, _) => true,
        Expr::Exists(_, _, _, _) => true,
        Expr::Bin(_, x, y) => binds_s(*x) || binds_s(*y),
        Expr::And(x, y) => binds_s(*x) || binds_s(*y),
        Expr::Or(x, y) => binds_s(*x) || binds_s(*y),
        Expr::Implies(x, y) => binds_s(*x) || binds_s(*y),
        Expr::Not(x) => binds_s(*x),
        Expr::Code(x) => binds_s(*x),
        Expr::Ite(c, x, y) => binds_s(*c) || binds_s(*x) || binds_s(*y),
        _ => false,
    }
}

pub fn binds(e: &Expr) -> (r: bool)
    ensures
        r == binds_s(*e),
    decreases e,
{
    match e {
        Expr::Let(_, _) => true,
        Expr::Forall(_, _, _, _) => true,
        Expr::Exists(_, _, _, _) => true,
        Expr::Bin(_, x, y) => binds(x) || binds(y),
        Expr::And(x, y) => binds(x) || binds(y),
        Expr::Or(x, y) => binds(x) || binds(y),
        Expr::Implies(x, y) => binds(x) || binds(y),
        Expr::Not(x) => binds(x),
        Expr::Code(x) => binds(x),
        Expr::Ite(c, x, y) => binds(c) || binds(x) || binds(y),
        _ => false,
    }
}

pub open spec fn atomic_s(e: Expr) -> bool {
    e is Const || e is Var || e is Arg || e is Next || e is Out || e is Local
}

pub fn atomic(e: &Expr) -> (r: bool)
    ensures
        r == atomic_s(*e),
{
    match e {
        Expr::Const(_) | Expr::Var(_) | Expr::Arg(_) | Expr::Next(_) | Expr::Out | Expr::Local(_) => true,
        _ => false,
    }
}

// ---- 束縛の列 ----

/// 評価の順に並べた束縛の列。`base` は最初の束縛の局所変数の添字。
pub struct Block {
    pub base: usize,
    pub binds: Vec<Expr>,
}

impl Block {
    pub open spec fn wf(&self) -> bool {
        self.base + self.binds@.len() < usize::MAX
    }

    pub open spec fn depth_s(&self) -> nat {
        (self.base + self.binds@.len()) as nat
    }
}

/// `new` は `old` の束縛の列の後ろに束縛を加えたものである。
pub open spec fn extends(old: Block, new: Block) -> bool {
    new.base == old.base && new.wf() && old.binds@.len() <= new.binds@.len() && forall|i: int|
        0 <= i < old.binds@.len() ==> #[trigger] new.binds@[i] == old.binds@[i]
}

pub proof fn lemma_extends_refl(a: Block)
    requires
        a.wf(),
    ensures
        extends(a, a),
{
}

pub fn new_block(base: usize) -> (r: Option<Block>)
    ensures
        r matches Some(b) ==> b.wf() && b.base == base && b.binds@.len() == 0,
{
    if base < usize::MAX {
        Some(Block { base, binds: Vec::new() })
    } else {
        None
    }
}

pub(crate) fn depth(blk: &Block) -> (r: usize)
    requires
        blk.wf(),
    ensures
        r == blk.depth_s(),
{
    blk.base + blk.binds.len()
}

/// 式を束縛し、それを指す局所変数を返す。
pub(crate) fn bind(blk: &mut Block, e: Expr) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r matches Some(x) ==> x == Expr::Local(old(blk).depth_s() as usize) && final(blk).binds@ == old(
            blk,
        ).binds@.push(e),
        r is None ==> *final(blk) == *old(blk),
{
    let i = depth(blk);
    if i + 1 == usize::MAX {
        proof {
            lemma_extends_refl(*blk);
        }
        return None;
    }
    blk.binds.push(e);
    Some(Expr::Local(i))
}

/// 失敗しうる式と束縛子を含む式は束縛し、それ以外はそのまま返す。
pub(crate) fn keep(blk: &mut Block, e: Expr) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
{
    if may_fail(&e) || binds(&e) {
        bind(blk, e)
    } else {
        proof {
            lemma_extends_refl(*blk);
        }
        Some(e)
    }
}

/// 何度も参照する式を束縛する。
pub(crate) fn atom(blk: &mut Block, e: Expr) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
{
    if atomic(&e) {
        proof {
            lemma_extends_refl(*blk);
        }
        Some(e)
    } else {
        bind(blk, e)
    }
}

/// `cond` が偽なら、番号 `code` で失敗する。
pub(crate) fn check(blk: &mut Block, cond: Expr, code: i64) -> (r: Option<()>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
{
    if is_bool_lit(&cond, true) {
        proof {
            lemma_extends_refl(*blk);
        }
        Some(())
    } else {
        let _ = bind(blk, ite(cond, cb(true), Expr::Fail(Type::Bool, code)))?;
        Some(())
    }
}

/// 束縛を順に評価してから `e` を評価する式。
pub fn wrap(binds: &Vec<Expr>, e: Expr) -> (r: Expr) {
    wrap_bindings(copy_exprs(binds), e)
}

// ---- 型の大きさ ----

pub fn is_scalar(t: &XType) -> (r: bool) {
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => true,
        _ => false,
    }
}

pub fn keys_or_zero_exec(t: &SType, enums: &Vec<i64>) -> (r: usize) {
    match keys_exec(t, enums) {
        Some(k) => k as usize,
        None => 0,
    }
}

/// 格納の型のスロット数。`usize` に収まらなければ `None`。
pub fn stype_width(t: &SType, enums: &Vec<i64>) -> (r: Option<usize>)
    decreases t, 1nat,
{
    match t {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) => Some(1),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            stype_width_sum(t, ts, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            stype_width_sum(t, ts, enums)
        },
        SType::Option(x) => {
            let w = stype_width(x, enums)?;
            w.checked_add(1)
        },
        SType::Set(e) => Some(keys_or_zero_exec(e, enums)),
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let w = stype_width(v, enums)?;
            n.checked_mul(w.checked_add(1)?)
        },
        SType::List(e, n) => {
            let w = stype_width(e, enums)?;
            n.checked_mul(w)?.checked_add(1)
        },
    }
}

fn stype_width_sum(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        decreases_to!(*_parent => *ts),
    decreases _parent, 0nat,
{
    let mut acc: usize = 0;
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let w = stype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        i += 1;
    }
    Some(acc)
}

/// 式の型のスロット数。
pub fn xtype_width(t: &XType, enums: &Vec<i64>) -> (r: Option<usize>)
    decreases t, 1nat,
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => Some(1),
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            xtype_width_sum(t, ts, enums)
        },
        XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            xtype_width_sum(t, ts, enums)
        },
        XType::Option(x) => {
            let w = xtype_width(x, enums)?;
            w.checked_add(1)
        },
        XType::Set(e) => Some(keys_or_zero_exec(e, enums)),
        XType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let w = stype_width(v, enums)?;
            n.checked_mul(w.checked_add(1)?)
        },
        XType::List(e, n) => {
            let w = stype_width(e, enums)?;
            n.checked_mul(w)?.checked_add(1)
        },
    }
}

fn xtype_width_sum(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        decreases_to!(*_parent => *ts),
    decreases _parent, 0nat,
{
    let mut acc: usize = 0;
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let w = xtype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        i += 1;
    }
    Some(acc)
}

/// スロットの中核の型を `out` に追加する。
pub fn slot_types(t: &SType, enums: &Vec<i64>, out: &mut Vec<Type>)
    decreases t, 1nat,
{
    match t {
        SType::Bool => out.push(Type::Bool),
        SType::Int(lo, hi) => out.push(Type::Int(*lo, *hi)),
        SType::Enum(id) => out.push(Type::Enum(*id)),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_all(t, ts, enums, out)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_all(t, ts, enums, out)
        },
        SType::Option(x) => {
            out.push(Type::Bool);
            slot_types(x, enums, out);
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut i = 0;
            while i < n
                decreases n - i,
            {
                out.push(Type::Bool);
                i += 1;
            }
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let mut i = 0;
            proof {
                assert(decreases_to!(*t => **v));
            }
            while i < n
                invariant
                    decreases_to!(*t => **v),
                decreases n - i,
            {
                out.push(Type::Bool);
                slot_types(v, enums, out);
                i += 1;
            }
        },
        SType::List(e, n) => {
            let top: i64 = if *n <= 0x7fff_ffffusize {
                *n as i64
            } else {
                0x7fff_ffff
            };
            out.push(Type::Int(0, top));
            let mut i = 0;
            proof {
                assert(decreases_to!(*t => **e));
            }
            while i < *n
                invariant
                    decreases_to!(*t => **e),
                decreases *n - i,
            {
                slot_types(e, enums, out);
                i += 1;
            }
        },
    }
}

fn slot_types_all(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, out: &mut Vec<Type>)
    requires
        decreases_to!(*_parent => *ts),
    decreases _parent, 0nat,
{
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        slot_types(&ts[i], enums, out);
        i += 1;
    }
}

/// 中核の型の既定値。Boolは偽、Intは範囲の最小値、Enumは最初のラベル。
pub fn default_value(t: Type) -> (r: Value) {
    match t {
        Type::Bool => Value::Bool(false),
        Type::Int(lo, _) => Value::Int(lo),
        Type::Enum(id) => Value::Enum(id, 0),
    }
}

/// 型 `t` の既定値のスロット。
pub fn defaults(t: &SType, enums: &Vec<i64>) -> (r: Vec<Expr>) {
    let mut tys: Vec<Type> = Vec::new();
    slot_types(t, enums, &mut tys);
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < tys.len()
        decreases tys.len() - i,
    {
        out.push(Expr::Const(default_value(tys[i])));
        i += 1;
    }
    out
}

/// 量化で束縛する型の、スロットごとの範囲。
pub fn quant_ranges(t: &SType, enums: &Vec<i64>) -> (r: Vec<(Type, i64, i64)>) {
    let mut tys: Vec<Type> = Vec::new();
    slot_types(t, enums, &mut tys);
    let mut out: Vec<(Type, i64, i64)> = Vec::new();
    let mut i = 0;
    while i < tys.len()
        decreases tys.len() - i,
    {
        let ty = tys[i];
        let (lo, hi) = match ty {
            Type::Bool => (0i64, 1i64),
            Type::Int(lo, hi) => (lo, hi),
            Type::Enum(id) => if id < enums.len() && enums[id] > i64::MIN {
                (0, enums[id] - 1)
            } else {
                (0, -1)
            },
        };
        out.push((ty, lo, hi));
        i += 1;
    }
    out
}

// ---- スロットの操作 ----

/// 添字 `idx`（`0..rows.len()` に収まる）の行の `j` 番目のスロットを、二分木の `ite` で選ぶ。
fn pick(rows: &Vec<Vec<Expr>>, lo: usize, hi: usize, j: usize, idx: &Expr) -> (r: Option<Expr>)
    requires
        lo < hi <= rows@.len(),
    decreases hi - lo,
{
    if hi - lo == 1 {
        if j < rows[lo].len() {
            Some(copy_expr(&rows[lo][j]))
        } else {
            None
        }
    } else {
        let mid = lo + (hi - lo) / 2;
        if mid > 0x7fff_ffffusize {
            return None;
        }
        let x = pick(rows, lo, mid, j, idx)?;
        let y = pick(rows, mid, hi, j, idx)?;
        Some(ite(bin(BinOp::Lt, copy_expr(idx), ci(mid as i64)), x, y))
    }
}

/// 添字 `idx` の行を選ぶ。行がなければ `fallback`。
pub fn select(rows: &Vec<Vec<Expr>>, idx: &Expr, fallback: &Vec<Expr>) -> (r: Option<Vec<Expr>>) {
    if rows.len() == 0 {
        return Some(copy_exprs(fallback));
    }
    let n = rows[0].len();
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < n
        invariant
            rows@.len() > 0,
        decreases n - j,
    {
        out.push(pick(rows, 0, rows.len(), j, idx)?);
        j += 1;
    }
    Some(out)
}

/// 要素の型ごとに、スロットの列を区切る。
pub fn split(tys: &Vec<XType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Vec<Vec<Expr>>>) {
    let mut out: Vec<Vec<Expr>> = Vec::new();
    let mut at: usize = 0;
    let mut i = 0;
    while i < tys.len()
        decreases tys.len() - i,
    {
        let w = xtype_width(&tys[i], enums)?;
        let end = at.checked_add(w)?;
        if end > slots.len() {
            return None;
        }
        out.push(sub_exprs(slots, at, end));
        at = end;
        i += 1;
    }
    Some(out)
}

/// 構造の等しさ。Option が空なら中身は比べない。
pub fn eq_slots(t: &XType, x: &Vec<Expr>, y: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    decreases t, 1nat,
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => {
            if x.len() == 0 || y.len() == 0 {
                return None;
            }
            Some(eq(copy_expr(&x[0]), copy_expr(&y[0])))
        },
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            eq_parts(t, ts, x, y, enums)
        },
        XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            eq_parts(t, ts, x, y, enums)
        },
        XType::Option(inner) => {
            if x.len() == 0 || y.len() == 0 {
                return None;
            }
            let rest = eq_slots(inner, &sub_exprs(x, 1, x.len()), &sub_exprs(y, 1, y.len()), enums)?;
            Some(and(eq(copy_expr(&x[0]), copy_expr(&y[0])), implies(copy_expr(&x[0]), rest)))
        },
        // Set、Map、List は正規形なので、スロットの一致が値の一致である。
        XType::Set(_) | XType::Map(_, _) | XType::List(_, _) => {
            let n = if x.len() < y.len() {
                x.len()
            } else {
                y.len()
            };
            let mut items: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= x.len(),
                    n <= y.len(),
                decreases n - i,
            {
                items.push(eq(copy_expr(&x[i]), copy_expr(&y[i])));
                i += 1;
            }
            Some(all_of(&items))
        },
    }
}

fn eq_parts(_parent: &XType, ts: &Vec<XType>, x: &Vec<Expr>, y: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<
    Expr,
>)
    requires
        decreases_to!(*_parent => *ts),
    decreases _parent, 0nat,
{
    let xs = split(ts, x, enums)?;
    let ys = split(ts, y, enums)?;
    if xs.len() != ts.len() || ys.len() != ts.len() {
        return None;
    }
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            xs.len() == ts.len(),
            ys.len() == ts.len(),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        items.push(eq_slots(&ts[i], &xs[i], &ys[i], enums)?);
        i += 1;
    }
    Some(all_of(&items))
}

/// 値を型 `st` の場所に置く。値が型に属する条件と、正規形にしたスロットを返す。
/// `t` は `st` に合うものとする。
pub fn store(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<(Expr, Vec<Expr>)>)
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Int, SType::Int(lo, hi)) => {
            if slots.len() == 0 {
                return None;
            }
            let c = and(
                bin(BinOp::Le, ci(*lo), copy_expr(&slots[0])),
                bin(BinOp::Le, copy_expr(&slots[0]), ci(*hi)),
            );
            Some((c, copy_exprs(slots)))
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            store_parts(t, xs, ts, slots, enums)
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            store_parts(t, xs, ts, slots, enums)
        },
        (XType::Option(x), SType::Option(inner)) => {
            if slots.len() == 0 {
                return None;
            }
            let (c, payload) = store(x, &sub_exprs(slots, 1, slots.len()), inner, enums)?;
            let defs = defaults(inner, enums);
            let mut out: Vec<Expr> = Vec::new();
            out.push(copy_expr(&slots[0]));
            let n = if payload.len() < defs.len() {
                payload.len()
            } else {
                defs.len()
            };
            let mut i = 0;
            while i < n
                invariant
                    n <= payload.len(),
                    n <= defs.len(),
                    slots.len() > 0,
                decreases n - i,
            {
                out.push(ite(copy_expr(&slots[0]), copy_expr(&payload[i]), copy_expr(&defs[i])));
                i += 1;
            }
            Some((implies(copy_expr(&slots[0]), c), out))
        },
        _ => Some((cb(true), copy_exprs(slots))),
    }
}

fn store_parts(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r:
    Option<(Expr, Vec<Expr>)>)
    requires
        decreases_to!(*_parent => *xs),
    decreases _parent, 0nat,
{
    let parts = split(xs, slots, enums)?;
    let mut n = xs.len();
    if ts.len() < n {
        n = ts.len();
    }
    if parts.len() < n {
        n = parts.len();
    }
    let mut conds: Vec<Expr> = Vec::new();
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n <= xs.len(),
            n <= ts.len(),
            n <= parts.len(),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        let (c, s) = store(&xs[i], &parts[i], &ts[i], enums)?;
        conds.push(c);
        let mut j = 0;
        while j < s.len()
            decreases s.len() - j,
        {
            out.push(copy_expr(&s[j]));
            j += 1;
        }
        i += 1;
    }
    Some((all_of(&conds), out))
}

/// 要素の型 `st` での番号。値が型に属するときに限って評価する。
pub fn rank_expr(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>)
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Int, SType::Int(lo, _)) => {
            if slots.len() == 0 {
                return None;
            }
            Some(offset_rank(copy_expr(&slots[0]), *lo))
        },
        (XType::Bool, _) | (XType::Enum(_), _) => {
            if slots.len() == 0 {
                return None;
            }
            Some(Expr::Code(Box::new(copy_expr(&slots[0]))))
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            mixed(t, xs, ts, slots, enums)
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            mixed(t, xs, ts, slots, enums)
        },
        (XType::Option(x), SType::Option(inner)) => {
            if slots.len() == 0 {
                return None;
            }
            let payload = rank_expr(x, &sub_exprs(slots, 1, slots.len()), inner, enums)?;
            Some(option_rank(copy_expr(&slots[0]), payload))
        },
        _ => Some(ci(0)),
    }
}

fn mixed(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<
    Expr,
>)
    requires
        decreases_to!(*_parent => *xs),
    decreases _parent, 0nat,
{
    let n = if xs.len() < ts.len() {
        xs.len()
    } else {
        ts.len()
    };
    let mut ranks: Vec<(Expr, i64)> = Vec::new();
    let mut at: usize = 0;
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n <= xs.len(),
            n <= ts.len(),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        let w = xtype_width(&xs[i], enums)?;
        let end = at.checked_add(w)?;
        if end > slots.len() {
            return None;
        }
        let k = rank_expr(&xs[i], &sub_exprs(slots, at, end), &ts[i], enums)?;
        at = end;
        let radix = match keys_exec(&ts[i], enums) {
            Some(k) => k as i64,
            None => 1,
        };
        ranks.push((k, radix));
        i += 1;
    }
    Some(mixed_rank_expr(&ranks))
}

/// 値が要素の型に属すれば、その番号。属さなければ -1。
pub fn rank_or_neg(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>) {
    let (in_dom, _) = store(t, slots, st, enums)?;
    let r = rank_expr(t, slots, st, enums)?;
    if is_bool_lit(&in_dom, true) {
        Some(r)
    } else {
        Some(ite(in_dom, r, ci(-1)))
    }
}

/// `xs` と `ys` の対応するスロットが等しい。
fn eq_all(xs: &Vec<Expr>, ys: &Vec<Expr>) -> (r: Expr) {
    let n = if xs.len() < ys.len() {
        xs.len()
    } else {
        ys.len()
    };
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            n <= xs.len(),
            n <= ys.len(),
        decreases n - i,
    {
        items.push(eq(copy_expr(&xs[i]), copy_expr(&ys[i])));
        i += 1;
    }
    all_of(&items)
}

/// 型 `st` の値として正規形である（Option が空なら中身が既定値、など）。
/// 引数と量化の束縛は、スロットごとに値を列挙するので、正規形でない組を除く。
pub fn canonical(st: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    decreases st, 1nat,
{
    match st {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) | SType::Set(_) => Some(cb(true)),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*st => *ts));
            }
            canonical_parts(st, ts, slots, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*st => *ts));
            }
            canonical_parts(st, ts, slots, enums)
        },
        SType::Option(t) => {
            if slots.len() == 0 {
                return None;
            }
            let payload = sub_exprs(slots, 1, slots.len());
            let inner = canonical(t, &payload, enums)?;
            let empty = eq_all(&payload, &defaults(t, enums));
            if is_bool_lit(&inner, true) && is_bool_lit(&empty, true) {
                Some(cb(true))
            } else {
                Some(ite(copy_expr(&slots[0]), inner, empty))
            }
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let w = stype_width(v, enums)?;
            let stride = w.checked_add(1)?;
            let defs = defaults(v, enums);
            let mut items: Vec<Expr> = Vec::new();
            let mut i = 0;
            proof {
                assert(decreases_to!(*st => **v));
            }
            while i < n
                invariant
                    stride == w + 1,
                    decreases_to!(*st => **v),
                decreases n - i,
            {
                let at = i.checked_mul(stride)?;
                let end = at.checked_add(stride)?;
                if end > slots.len() {
                    return None;
                }
                let vals = sub_exprs(slots, at + 1, end);
                let empty = eq_all(&vals, &defs);
                items.push(ite(copy_expr(&slots[at]), canonical(v, &vals, enums)?, empty));
                i += 1;
            }
            Some(all_of(&items))
        },
        SType::List(t, max) => {
            let w = stype_width(t, enums)?;
            let defs = defaults(t, enums);
            if slots.len() == 0 || *max > 0x7fff_ffffusize {
                return None;
            }
            let mut items: Vec<Expr> = Vec::new();
            let mut p = 0;
            proof {
                assert(decreases_to!(*st => **t));
            }
            while p < *max
                invariant
                    slots.len() > 0,
                    *max <= 0x7fff_ffffusize,
                    decreases_to!(*st => **t),
                decreases *max - p,
            {
                let start = p.checked_mul(w)?.checked_add(1)?;
                let end = start.checked_add(w)?;
                if end > slots.len() {
                    return None;
                }
                let item = sub_exprs(slots, start, end);
                let empty = eq_all(&item, &defs);
                items.push(
                    ite(bin(BinOp::Lt, ci(p as i64), copy_expr(&slots[0])), canonical(t, &item, enums)?, empty),
                );
                p += 1;
            }
            Some(all_of(&items))
        },
    }
}

fn canonical_parts(_parent: &SType, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Expr>)
    requires
        decreases_to!(*_parent => *ts),
    decreases _parent, 0nat,
{
    let mut xs: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        decreases ts.len() - i,
    {
        xs.push(to_xtype(&ts[i]));
        i += 1;
    }
    let parts = split(&xs, slots, enums)?;
    let n = if ts.len() < parts.len() {
        ts.len()
    } else {
        parts.len()
    };
    let mut items: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *ts),
            n <= ts.len(),
            n <= parts.len(),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        items.push(canonical(&ts[i], &parts[i], enums)?);
        i += 1;
    }
    Some(all_of(&items))
}

/// Mapのスロットの、キーごとの有無と値。
pub fn map_parts(k: &SType, v: &SType, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<(Vec<Expr>, Vec<Vec<Expr>>)>) {
    let n = keys_or_zero_exec(k, enums);
    let w = stype_width(v, enums)?;
    let stride = w.checked_add(1)?;
    let mut present: Vec<Expr> = Vec::new();
    let mut values: Vec<Vec<Expr>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            stride == w + 1,
        decreases n - i,
    {
        let at = i.checked_mul(stride)?;
        let end = at.checked_add(stride)?;
        if end > slots.len() {
            return None;
        }
        present.push(copy_expr(&slots[at]));
        values.push(sub_exprs(slots, at + 1, end));
        i += 1;
    }
    Some((present, values))
}

pub fn map_join(present: &Vec<Expr>, values: &Vec<Vec<Expr>>) -> (r: Vec<Expr>) {
    let n = if present.len() < values.len() {
        present.len()
    } else {
        values.len()
    };
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            n <= present.len(),
            n <= values.len(),
        decreases n - i,
    {
        out.push(copy_expr(&present[i]));
        let mut j = 0;
        while j < values[i].len()
            invariant
                i < values.len(),
            decreases values@[i as int]@.len() - j,
        {
            out.push(copy_expr(&values[i][j]));
            j += 1;
        }
        i += 1;
    }
    out
}

/// List のスロットの、長さと要素。
pub fn list_parts(t: &SType, max: usize, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<(Expr, Vec<Vec<Expr>>)>) {
    let w = stype_width(t, enums)?;
    if slots.len() == 0 {
        return None;
    }
    let mut items: Vec<Vec<Expr>> = Vec::new();
    let mut p = 0;
    while p < max
        decreases max - p,
    {
        let start = p.checked_mul(w)?.checked_add(1)?;
        let end = start.checked_add(w)?;
        if end > slots.len() {
            return None;
        }
        items.push(sub_exprs(slots, start, end));
        p += 1;
    }
    Some((copy_expr(&slots[0]), items))
}

pub fn list_join(len: Expr, items: &Vec<Vec<Expr>>) -> (r: Vec<Expr>) {
    let mut out: Vec<Expr> = Vec::new();
    out.push(len);
    let mut i = 0;
    while i < items.len()
        decreases items.len() - i,
    {
        let mut j = 0;
        while j < items[i].len()
            invariant
                i < items.len(),
            decreases items@[i as int]@.len() - j,
        {
            out.push(copy_expr(&items[i][j]));
            j += 1;
        }
        i += 1;
    }
    out
}

} // verus!
