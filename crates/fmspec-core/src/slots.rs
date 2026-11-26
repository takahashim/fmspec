//! 下ろしで使う、スロットの式の組み立て。
//!
//! 下ろしは、IRの式の値を、スロットごとの中核の式の列にする（[`crate::encoding`] の符号化）。
//! ここにあるのは、その部品である。部品は、長さや型の合わない入力には `None` を返す。
//! 下ろしは `None` を内部エラーにするので、`None` を返すことは健全性を損なわない。

#[cfg(verus_keep_ghost)]
use crate::bindings::eval_bound_body;
use crate::bindings::wrap_bindings;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq, keys, keys_or_zero};
use crate::encoding::{keys_exec, to_xtype, SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{keys_product, lemma_default_len, lemma_default_vals_len, lemma_stys, lemma_xtys, member};
#[cfg(verus_keep_ghost)]
use crate::encoding::{members, models_seq, sty, stys, width, width_sum, xty, xtys, xwidth, xwidth_sum, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{XTy, MAX_KEYS};
#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, radix, rank, rank_seq};
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
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

pub open spec fn ite_s(c: Expr, x: Expr, y: Expr) -> Expr {
    Expr::Ite(Box::new(c), Box::new(x), Box::new(y))
}

pub fn ite(c: Expr, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == ite_s(c, x, y),
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
        r matches Some(x) ==> added(*old(blk), *final(blk), e, x),
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
        r matches Some(x) ==> added(*old(blk), *final(blk), e, x) && (atomic_s(e) ==> x == e),
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
        r is Some ==> (cond == bool_lit(true) && final(blk).binds@ == old(blk).binds@) || final(blk).binds@ == old(
            blk,
        ).binds@.push(ite_s(cond, bool_lit(true), Expr::Fail(Type::Bool, code))),
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
pub fn wrap(binds: &Vec<Expr>, e: Expr) -> (r: Expr)
    ensures
        forall|env: Env, ls: Seq<Value>|
            #[trigger] eval_l(r, env, ls) == eval_bound_body(binds@, binds@.len(), e, env, ls),
{
    wrap_bindings(copy_exprs(binds), e)
}

// ---- 型の大きさ ----

pub fn is_scalar(t: &XType) -> (r: bool) {
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => true,
        _ => false,
    }
}

pub fn keys_or_zero_exec(t: &SType, enums: &Vec<i64>) -> (r: usize)
    ensures
        r == keys_or_zero(sty(*t), enums@),
        r <= MAX_KEYS,
{
    match keys_exec(t, enums) {
        Some(k) => k as usize,
        None => 0,
    }
}

/// 格納の型のスロット数。`usize` に収まらなければ `None`。
pub fn stype_width(t: &SType, enums: &Vec<i64>) -> (r: Option<usize>)
    ensures
        r matches Some(w) ==> w == width(sty(*t), enums@),
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
    ensures
        r matches Some(w) ==> w == width_sum(stys(ts@), enums@),
    decreases _parent, 0nat,
{
    let mut acc: usize = 0;
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            acc == width_sum(stys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let w = stype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    Some(acc)
}

/// 式の型のスロット数。
pub fn xtype_width(t: &XType, enums: &Vec<i64>) -> (r: Option<usize>)
    ensures
        r matches Some(w) ==> w == xwidth(xty(*t), enums@),
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
    ensures
        r matches Some(w) ==> w == xwidth_sum(xtys(ts@), enums@),
    decreases _parent, 0nat,
{
    let mut acc: usize = 0;
    let mut i = 0;
    proof {
        lemma_xtys(ts@);
        assert(xtys(ts@).take(0) =~= Seq::<XTy>::empty());
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            xtys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xtys(ts@)[j] == xty(ts@[j]),
            acc == xwidth_sum(xtys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let w = xtype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        proof {
            let xs = xtys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        i += 1;
    }
    proof {
        assert(xtys(ts@).take(ts@.len() as int) =~= xtys(ts@));
    }
    Some(acc)
}

/// 中核の型の既定値。Boolは偽、Intは範囲の最小値、Enumは最初のラベル。
pub fn default_value(t: Type) -> (r: Value) {
    match t {
        Type::Bool => Value::Bool(false),
        Type::Int(lo, _) => Value::Int(lo),
        Type::Enum(id) => Value::Enum(id, 0),
    }
}

/// 値の列を、定数の式の列にする。
pub open spec fn lits(vs: Seq<Value>) -> Seq<Expr> {
    vs.map_values(|v: Value| Expr::Const(v))
}

/// `out` の後ろに `xs` の複製を加える。
pub fn extend(out: &mut Vec<Expr>, xs: &Vec<Expr>)
    ensures
        final(out)@ == old(out)@ + xs@,
{
    let ghost start = out@;
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            out@ == start + xs@.take(i as int),
        decreases xs.len() - i,
    {
        out.push(copy_expr(&xs[i]));
        proof {
            assert(xs@.take(i + 1) =~= xs@.take(i as int).push(xs@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs@.len() as int) =~= xs@);
    }
}

/// 型 `t` の既定値のスロット。
pub fn defaults(t: &SType, enums: &Vec<i64>) -> (r: Vec<Expr>)
    ensures
        r@ == lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)),
    decreases t, 1nat,
{
    let mut out: Vec<Expr> = Vec::new();
    match t {
        SType::Bool => {
            out.push(cb(false));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Int(lo, _) => {
            out.push(ci(*lo));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Enum(id) => {
            out.push(Expr::Const(Value::Enum(*id, 0)));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = defaults_all(t, ts, enums);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = defaults_all(t, ts, enums);
        },
        SType::Option(x) => {
            out.push(cb(false));
            let d = defaults(x, enums);
            extend(&mut out, &d);
            proof {
                let dv = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                assert(out@ =~= lits(seq![Value::Bool(false)] + dv));
            }
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut i = 0;
            while i < n
                invariant
                    i <= n,
                    out@ == lits(Seq::new(i as nat, |_j: int| Value::Bool(false))),
                decreases n - i,
            {
                out.push(cb(false));
                proof {
                    assert(out@ =~= lits(Seq::new((i + 1) as nat, |_j: int| Value::Bool(false))));
                }
                i += 1;
            }
            proof {
                let bits = Seq::new(n as nat, |_i: int| false);
                assert(enc(default_val(sty(*t), enums@), sty(*t), enums@) =~= Seq::new(
                    n as nat,
                    |_j: int| Value::Bool(false),
                ));
            }
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let d = defaults(v, enums);
            let ghost dv = enc(default_val(sty(**v), enums@), sty(**v), enums@);
            let mut i = 0;
            proof {
                assert(enc_rows(Seq::new(0, |_j: int| None::<SVal>), sty(**v), enums@) =~= Seq::<Value>::empty());
                assert(out@ =~= lits(Seq::<Value>::empty()));
            }
            while i < n
                invariant
                    i <= n,
                    d@ == lits(dv),
                    dv == enc(default_val(sty(**v), enums@), sty(**v), enums@),
                    out@ == lits(enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@)),
                decreases n - i,
            {
                out.push(cb(false));
                extend(&mut out, &d);
                proof {
                    let rows = Seq::new((i + 1) as nat, |_j: int| None::<SVal>);
                    assert(rows.drop_last() =~= Seq::new(i as nat, |_j: int| None::<SVal>));
                    let prev = enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@);
                    assert(enc_rows(rows, sty(**v), enums@) == prev + (seq![Value::Bool(false)] + dv));
                    assert(out@ =~= lits(prev + (seq![Value::Bool(false)] + dv)));
                }
                i += 1;
            }
        },
        SType::List(e, max) => {
            out.push(ci(0));
            let d = defaults(e, enums);
            let ghost dv = enc(default_val(sty(**e), enums@), sty(**e), enums@);
            let mut i = 0;
            proof {
                assert(out@ =~= lits(seq![Value::Int(0)] + enc_repeat(dv, 0)));
            }
            while i < *max
                invariant
                    i <= *max,
                    d@ == lits(dv),
                    dv == enc(default_val(sty(**e), enums@), sty(**e), enums@),
                    out@ == lits(seq![Value::Int(0)] + enc_repeat(dv, i as nat)),
                decreases *max - i,
            {
                extend(&mut out, &d);
                proof {
                    assert(enc_repeat(dv, (i + 1) as nat) == enc_repeat(dv, i as nat) + dv);
                    assert(out@ =~= lits(seq![Value::Int(0)] + enc_repeat(dv, (i + 1) as nat)));
                }
                i += 1;
            }
            proof {
                let items = Seq::<SVal>::empty();
                assert(enc_items(items, sty(**e), enums@) =~= Seq::<Value>::empty());
                assert(enc(default_val(sty(*t), enums@), sty(*t), enums@) =~= seq![Value::Int(0)] + enc_repeat(
                    dv,
                    *max as nat,
                ));
            }
        },
    }
    out
}

fn defaults_all(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Vec<Expr>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r@ == lits(enc_seq(default_vals(stys(ts@), enums@), stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let mut out: Vec<Expr> = Vec::new();
    let ghost xs = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(xs.take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= lits(enc_seq(default_vals(xs.take(0), enums@), xs.take(0), enums@)));
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts@.len(),
            xs == stys(ts@),
            xs.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xs[j] == sty(ts@[j]),
            out@ == lits(enc_seq(default_vals(xs.take(i as int), enums@), xs.take(i as int), enums@)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let d = defaults(&ts[i], enums);
        let ghost prev = out@;
        extend(&mut out, &d);
        proof {
            let p = xs.take(i + 1);
            assert(p.drop_last() =~= xs.take(i as int));
            assert(p.last() == xs[i as int]);
            let dvs = default_vals(p, enums@);
            assert(dvs.drop_last() == default_vals(xs.take(i as int), enums@));
            assert(dvs.last() == default_val(xs[i as int], enums@));
            lemma_default_vals_len(p, enums@);
            assert(enc_seq(dvs, p, enums@) == enc_seq(dvs.drop_last(), p.drop_last(), enums@) + enc(
                dvs.last(),
                p.last(),
                enums@,
            ));
            let a = enc_seq(default_vals(xs.take(i as int), enums@), xs.take(i as int), enums@);
            let b = enc(default_val(xs[i as int], enums@), xs[i as int], enums@);
            assert(out@ =~= lits(a + b));
        }
        i += 1;
    }
    proof {
        assert(xs.take(ts@.len() as int) =~= xs);
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
pub fn split(tys: &Vec<XType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Vec<Vec<Expr>>>)
    ensures
        r matches Some(parts) ==> parts@.len() == tys@.len() && forall|i: int|
            0 <= i < tys@.len() ==> #[trigger] split_ok(parts@[i]@, slots@, xtys(tys@), i, enums@),
{
    let mut out: Vec<Vec<Expr>> = Vec::new();
    let mut at: usize = 0;
    let mut i = 0;
    proof {
        lemma_xtys(tys@);
        assert(xtys(tys@).take(0) =~= Seq::<XTy>::empty());
    }
    while i < tys.len()
        invariant
            i <= tys@.len(),
            xtys(tys@).len() == tys@.len(),
            forall|j: int| 0 <= j < tys@.len() ==> #[trigger] xtys(tys@)[j] == xty(tys@[j]),
            at == xoff(xtys(tys@), i as int, enums@),
            at <= slots@.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] split_ok(out@[k]@, slots@, xtys(tys@), k, enums@),
        decreases tys.len() - i,
    {
        let w = xtype_width(&tys[i], enums)?;
        let end = at.checked_add(w)?;
        if end > slots.len() {
            return None;
        }
        proof {
            lemma_xoff_step(xtys(tys@), i as int, enums@);
        }
        out.push(sub_exprs(slots, at, end));
        proof {
            assert(split_ok(out@[i as int]@, slots@, xtys(tys@), i as int, enums@));
        }
        at = end;
        i += 1;
    }
    Some(out)
}

/// `part` は、型の列 `ts` のスロットの列 `slots` の `i` 番目の部分である。
pub open spec fn split_ok(part: Seq<Expr>, slots: Seq<Expr>, ts: Seq<XTy>, i: int, enums: Seq<i64>) -> bool {
    &&& 0 <= xoff(ts, i, enums)
    &&& xoff(ts, i, enums) + xwidth(ts[i], enums) <= slots.len()
    &&& part == slots.subrange(xoff(ts, i, enums), xoff(ts, i, enums) + xwidth(ts[i], enums))
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
    ensures
        r matches Some((c, out)) ==> store_spec(xty(*t), slots@, sty(*st), enums@, c, out@),
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Int, SType::Int(lo, hi)) => {
            if slots.len() == 0 {
                return None;
            }
            let x = bin(BinOp::Le, ci(*lo), copy_expr(&slots[0]));
            let y = bin(BinOp::Le, copy_expr(&slots[0]), ci(*hi));
            let c = and(copy_expr(&x), copy_expr(&y));
            let out = copy_exprs(slots);
            proof {
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(c, n) && all_pure(out@, n) by {
                    assert(pure_below(slots@[0], n));
                    assert(pure_below(Expr::Const(Value::Int(*lo)), n));
                    assert(pure_below(Expr::Const(Value::Int(*hi)), n));
                    assert(pure_below(x, n));
                    assert(pure_below(y, n));
                    lemma_join_pure(Join::And, x, y, n);
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    let k = v->Int_0;
                    assert(sv[0] == Value::Int(k));
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(Value::Int(k)));
                    assert(eval_l(Expr::Const(Value::Int(*lo)), env, ls) == Ok::<Value, ErrKind>(Value::Int(*lo)));
                    assert(eval_l(Expr::Const(Value::Int(*hi)), env, ls) == Ok::<Value, ErrKind>(Value::Int(*hi)));
                    assert(eval_l(x, env, ls) == Ok::<Value, ErrKind>(Value::Bool(*lo <= k)));
                    assert(eval_l(y, env, ls) == Ok::<Value, ErrKind>(Value::Bool(k <= *hi)));
                    lemma_and(x, y, env, ls, *lo <= k, k <= *hi);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let (c, out) = store_parts(t, xs, ts, slots, enums)?;
            proof {
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let (c, out) = store_parts(t, xs, ts, slots, enums)?;
            proof {
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some((c, out))
        },
        (XType::Option(x), SType::Option(inner)) => {
            proof {
                assert(decreases_to!(*t => **x));
            }
            store_option(t, x, slots, st, inner, enums)
        },
        _ => {
            let c = cb(true);
            let out = copy_exprs(slots);
            proof {
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) implies store_ok(
                    c,
                    out@,
                    env,
                    ls,
                    v,
                    sty(*st),
                    enums@,
                ) by {
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Some((c, out))
        },
    }
}

fn store_option(_parent: &XType, x: &XType, slots: &Vec<Expr>, _st: &SType, inner: &SType, enums: &Vec<i64>) -> (r:
    Option<(Expr, Vec<Expr>)>)
    requires
        decreases_to!(*_parent => *x),
        *_parent == XType::Option(Box::new(*x)),
        *_st == SType::Option(Box::new(*inner)),
    ensures
        r matches Some((c, out)) ==> store_spec(xty(*_parent), slots@, sty(*_st), enums@, c, out@),
    decreases _parent, 0nat,
{
    if slots.len() == 0 {
        return None;
    }
    let rest = sub_exprs(slots, 1, slots.len());
    let (c, payload) = store(x, &rest, inner, enums)?;
    let defs = defaults(inner, enums);
    if payload.len() != defs.len() {
        return None;
    }
    let tag = copy_expr(&slots[0]);
    let mut out: Vec<Expr> = Vec::new();
    out.push(copy_expr(&tag));
    let n = defs.len();
    let mut i = 0;
    while i < n
        invariant
            n == payload@.len(),
            n == defs@.len(),
            i <= n,
            out@.len() == 1 + i,
            out@[0] == tag,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[1 + j] == ite_s(tag, payload@[j], defs@[j]),
        decreases n - i,
    {
        out.push(ite(copy_expr(&tag), copy_expr(&payload[i]), copy_expr(&defs[i])));
        i += 1;
    }
    let cond = implies(copy_expr(&tag), copy_expr(&c));
    proof {
        let dv = enc(default_val(sty(*inner), enums@), sty(*inner), enums@);
        lemma_default_len(sty(*inner), enums@);
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(cond, m) && all_pure(out@, m) by {
            assert(pure_below(slots@[0], m));
            lemma_sub_pure(slots@, 1, slots@.len() as int, m);
            assert(all_pure(rest@, m));
            assert(all_pure(payload@, m));
            lemma_lits(dv, arbitrary(), arbitrary());
            assert(all_pure(defs@, m));
            lemma_option_out_pure(tag, payload@, defs@, out@, m);
        }
        assert forall|env: Env, ls: Seq<Value>, v: SVal|
            fits_s(xty(*_parent), sty(*_st)) && #[trigger] denotes(slots@, env, ls, v, xty(*_parent), enums@) implies store_ok(
            cond,
            out@,
            env,
            ls,
            v,
            sty(*_st),
            enums@,
        ) by {
            let sv = slot_vals(slots@, env, ls);
            lemma_clean_pure(slots@, env, ls);
            let m = ls.len();
            lemma_sub_pure(slots@, 1, slots@.len() as int, m);
            assert(all_pure(rest@, m));
            lemma_lits(dv, env, ls);
            assert(eval_l(tag, env, ls) == Ok::<Value, ErrKind>(sv[0]));
            assert(pure_below(tag, m));
            match v {
                SVal::Some(w) => {
                    lemma_clean_sub(slots@, env, ls, 1, slots@.len() as int);
                    assert(sv.subrange(1, sv.len() as int) =~= sv.drop_first());
                    assert(denotes(rest@, env, ls, *w, xty(*x), enums@));
                    assert(store_ok(c, payload@, env, ls, *w, sty(*inner), enums@));
                    if member(*w, sty(*inner), enums@) {
                        lemma_option_out(tag, payload@, defs@, out@, env, ls, true);
                        assert(slot_vals(out@, env, ls) =~= enc(v, sty(*_st), enums@));
                    }
                },
                _ => {
                    assert(all_pure(payload@, m));
                    lemma_option_out(tag, payload@, defs@, out@, env, ls, false);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*_st), enums@));
                },
            }
        }
    }
    Some((cond, out))
}

#[verifier::spinoff_prover]
fn store_parts(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r:
    Option<(Expr, Vec<Expr>)>)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r matches Some((c, out)) ==> store_parts_spec(xtys(xs@), slots@, stys(ts@), enums@, c, out@),
    decreases _parent, 0nat,
{
    let parts = split(xs, slots, enums)?;
    if xs.len() != ts.len() {
        return None;
    }
    let n = xs.len();
    let mut conds: Vec<Expr> = Vec::new();
    let mut out: Vec<Expr> = Vec::new();
    let ghost mut outs: Seq<Seq<Expr>> = Seq::empty();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n == xs@.len(),
            n == ts@.len(),
            n == parts@.len(),
            i <= n,
            conds@.len() == i,
            outs.len() == i,
            out@ == concat(outs),
            forall|k: int|
                0 <= k < i ==> #[trigger] store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]),
            forall|k: int| 0 <= k < xs@.len() ==> #[trigger] split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        let (c, s) = store(&xs[i], &parts[i], &ts[i], enums)?;
        conds.push(c);
        extend(&mut out, &s);
        proof {
            lemma_concat_push(outs, s@);
            outs = outs.push(s@);
            assert forall|k: int|
                0 <= k < i + 1 implies #[trigger] store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]) by {
                if k < i {
                }
            }
        }
        i += 1;
    }
    let c = all_of(&conds);
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(c, m) && all_pure(out@, m) by {
            assert forall|k: int| 0 <= k < n implies #[trigger] all_pure(outs[k], m) && pure_below(conds@[k], m) by {
                assert(split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@));
                lemma_sub_pure(slots@, xoff(xtys(xs@), k, enums@), xoff(xtys(xs@), k, enums@) + xwidth(xtys(xs@)[k], enums@), m);
                assert(all_pure(parts@[k]@, m));
                assert(store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]));
            }
            assert forall|k: int| 0 <= k < conds@.len() implies pure_below(#[trigger] conds@[k], m) by {
                assert(all_pure(outs[k], m) && pure_below(conds@[k], m));
            }
            lemma_tree_pure(conds@, bool_lit(true), Join::And, m);
            assert forall|k: int| 0 <= k < outs.len() implies #[trigger] all_pure(outs[k], m) by {
                assert(all_pure(outs[k], m) && pure_below(conds@[k], m));
            }
            lemma_concat_pure(outs, m);
        }
        assert forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
            fits_all_s(xtys(xs@), stys(ts@)) && clean(slots@, env, ls) && #[trigger] models_seq(
                slot_vals(slots@, env, ls),
                vs,
                xtys(xs@),
                enums@,
            ) implies {
            &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(members(vs, stys(ts@), enums@)))
            &&& members(vs, stys(ts@), enums@) ==> clean(out@, env, ls) && slot_vals(out@, env, ls) == enc_seq(
                vs,
                stys(ts@),
                enums@,
            )
        } by {
            let xt = xtys(xs@);
            let st = stys(ts@);
            lemma_fits_all(xt, st);
            assert forall|k: int| 0 <= k < n implies #[trigger] store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@) by {
                lemma_denotes_part(slots@, env, ls, vs, xt, k, enums@);
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                assert(fits_s(xt[k], st[k]));
                assert(store_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, conds@[k], outs[k]));
            }
            assert forall|k: int| 0 <= k < conds@.len() implies bool_val(#[trigger] eval_l(conds@[k], env, ls)) by {
                assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
            }
            lemma_all_of(conds@, env, ls);
            lemma_members(vs, st, enums@);
            lemma_models_seq_parts(slot_vals(slots@, env, ls), vs, xt, enums@);
            if all_true(conds@, env, ls) {
                assert forall|k: int| 0 <= k < st.len() implies #[trigger] member(vs[k], st[k], enums@) by {
                    assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
                    assert(eval_l(conds@[k], env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
                }
            }
            if members(vs, st, enums@) {
                assert forall|k: int| 0 <= k < conds@.len() implies #[trigger] eval_l(conds@[k], env, ls) == Ok::<
                    Value,
                    ErrKind,
                >(Value::Bool(true)) by {
                    assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
                    assert(member(vs[k], st[k], enums@));
                }
                assert forall|k: int| 0 <= k < outs.len() implies #[trigger] clean(outs[k], env, ls) && slot_vals(
                    outs[k],
                    env,
                    ls,
                ) == enc(vs[k], st[k], enums@) by {
                    assert(store_ok(conds@[k], outs[k], env, ls, vs[k], st[k], enums@));
                    assert(member(vs[k], st[k], enums@));
                }
                lemma_concat_enc(outs, vs, st, env, ls, enums@);
            }
        }
    }
    Some((c, out))
}

/// 要素の型 `st` での番号。値が型に属するときに限って評価する。
pub fn rank_expr(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(e) ==> rank_spec(xty(*t), slots@, sty(*st), enums@, e),
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Int, SType::Int(lo, _)) => {
            if slots.len() == 0 {
                return None;
            }
            let e = offset_rank(copy_expr(&slots[0]), *lo);
            proof {
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                    assert(pure_below(int_lit(*lo), n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(sv[0]));
                }
            }
            Some(e)
        },
        (XType::Bool, _) | (XType::Enum(_), _) => {
            if slots.len() == 0 {
                return None;
            }
            let e = Expr::Code(Box::new(copy_expr(&slots[0])));
            proof {
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(slots@[0], env, ls) == Ok::<Value, ErrKind>(sv[0]));
                }
            }
            Some(e)
        },
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let e = mixed(t, xs, ts, slots, enums)?;
            proof {
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some(e)
        },
        (XType::Record(_, xs), SType::Record(_, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            let e = mixed(t, xs, ts, slots, enums)?;
            proof {
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    assert(models_seq(slot_vals(slots@, env, ls), v->Tuple_0, xtys(xs@), enums@));
                }
            }
            Some(e)
        },
        (XType::Option(x), SType::Option(inner)) => {
            if slots.len() == 0 {
                return None;
            }
            let rest = sub_exprs(slots, 1, slots.len());
            let payload = rank_expr(x, &rest, inner, enums)?;
            let tag = copy_expr(&slots[0]);
            let e = option_rank(copy_expr(&tag), copy_expr(&payload));
            proof {
                assert forall|n: nat| #[trigger] all_pure(slots@, n) implies pure_below(e, n) by {
                    assert(pure_below(slots@[0], n));
                    lemma_sub_pure(slots@, 1, slots@.len() as int, n);
                    assert(all_pure(rest@, n));
                    assert(pure_below(payload, n));
                    assert(pure_below(int_lit(1), n));
                    assert(pure_below(int_lit(0), n));
                    assert(pure_below(Expr::Bin(BinOp::Add, Box::new(int_lit(1)), Box::new(payload)), n));
                }
                assert forall|env: Env, ls: Seq<Value>, v: SVal|
                    fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && member(
                        v,
                        sty(*st),
                        enums@,
                    ) && keys(sty(*st), enums@) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(
                    Value::Int(rank(v, sty(*st), enums@) as i64),
                ) by {
                    let sv = slot_vals(slots@, env, ls);
                    assert(eval_l(tag, env, ls) == Ok::<Value, ErrKind>(sv[0]));
                    match v {
                        SVal::Some(w) => {
                            lemma_clean_sub(slots@, env, ls, 1, slots@.len() as int);
                            assert(sv.subrange(1, sv.len() as int) =~= sv.drop_first());
                            assert(denotes(rest@, env, ls, *w, xty(**x), enums@));
                            assert(keys(sty(**inner), enums@) is Some);
                            lemma_rank_in_domain(*w, sty(**inner), enums@);
                            assert(eval_l(payload, env, ls) == Ok::<Value, ErrKind>(
                                Value::Int(rank(*w, sty(**inner), enums@) as i64),
                            ));
                        },
                        _ => {},
                    }
                }
            }
            Some(e)
        },
        _ => Some(ci(0)),
    }
}

fn mixed(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<
    Expr,
>)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r matches Some(e) ==> mixed_spec(xtys(xs@), slots@, stys(ts@), enums@, e),
    decreases _parent, 0nat,
{
    let parts = split(xs, slots, enums)?;
    if xs.len() != ts.len() {
        return None;
    }
    let n = xs.len();
    let mut ranks: Vec<(Expr, i64)> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            decreases_to!(*_parent => *xs),
            n == xs@.len(),
            n == ts@.len(),
            n == parts@.len(),
            i <= n,
            ranks@.len() == i,
            forall|k: int|
                0 <= k < i ==> #[trigger] rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0) && keys(
                    sty(ts@[k]),
                    enums@,
                ) is Some && ranks@[k].1 as int == radix(sty(ts@[k]), enums@),
            forall|k: int| 0 <= k < xs@.len() ==> #[trigger] split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@),
        decreases n - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        let k = rank_expr(&xs[i], &parts[i], &ts[i], enums)?;
        let base = match keys_exec(&ts[i], enums) {
            Some(k) => k as i64,
            None => return None,
        };
        ranks.push((k, base));
        proof {
            assert forall|j: int|
                0 <= j < i + 1 implies #[trigger] rank_spec(xty(xs@[j]), parts@[j]@, sty(ts@[j]), enums@, ranks@[j].0)
                && keys(sty(ts@[j]), enums@) is Some && ranks@[j].1 as int == radix(sty(ts@[j]), enums@) by {
                if j < i {
                }
            }
        }
        i += 1;
    }
    let e = mixed_rank_expr(&ranks);
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(e, m) by {
            assert forall|k: int| 0 <= k < ranks@.len() implies pure_below(#[trigger] ranks@[k].0, m) by {
                assert(split_ok(parts@[k]@, slots@, xtys(xs@), k, enums@));
                lemma_sub_pure(slots@, xoff(xtys(xs@), k, enums@), xoff(xtys(xs@), k, enums@) + xwidth(xtys(xs@)[k], enums@), m);
                assert(all_pure(parts@[k]@, m));
                assert(rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0));
            }
            assert(ranks_pure(ranks@, m));
        }
        assert forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
            fits_all_s(xtys(xs@), stys(ts@)) && clean(slots@, env, ls) && #[trigger] models_seq(
                slot_vals(slots@, env, ls),
                vs,
                xtys(xs@),
                enums@,
            ) && members(vs, stys(ts@), enums@) && keys_product(stys(ts@), enums@) is Some implies eval_l(e, env, ls)
            == Ok::<Value, ErrKind>(Value::Int(rank_seq(vs, stys(ts@), enums@) as i64)) by {
            let xt = xtys(xs@);
            let st = stys(ts@);
            lemma_fits_all(xt, st);
            lemma_members(vs, st, enums@);
            lemma_models_seq_parts(slot_vals(slots@, env, ls), vs, xt, enums@);
            assert forall|k: int|
                0 <= k < st.len() implies #[trigger] eval_l(ranks@[k].0, env, ls) == Ok::<Value, ErrKind>(
                Value::Int(rank(vs[k], st[k], enums@) as i64),
            ) && ranks@[k].1 as int == radix(st[k], enums@) by {
                lemma_denotes_part(slots@, env, ls, vs, xt, k, enums@);
                assert(split_ok(parts@[k]@, slots@, xt, k, enums@));
                assert(fits_s(xt[k], st[k]));
                assert(member(vs[k], st[k], enums@));
                assert(rank_spec(xty(xs@[k]), parts@[k]@, sty(ts@[k]), enums@, ranks@[k].0));
            }
            lemma_mixed_eval(ranks@, vs, st, env, ls, n as nat, enums@);
            assert(vs.take(n as int) =~= vs);
            assert(st.take(n as int) =~= st);
        }
    }
    Some(e)
}

/// 値が要素の型に属すれば、その番号。属さなければ -1。
pub fn rank_or_neg(t: &XType, slots: &Vec<Expr>, st: &SType, enums: &Vec<i64>) -> (r: Option<Expr>)
    ensures
        r matches Some(e) ==> rank_neg_spec(xty(*t), slots@, sty(*st), enums@, e),
{
    let (in_dom, _) = store(t, slots, st, enums)?;
    let r = rank_expr(t, slots, st, enums)?;
    if is_bool_lit(&in_dom, true) {
        proof {
            assert forall|env: Env, ls: Seq<Value>, v: SVal|
                fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && keys(
                    sty(*st),
                    enums@,
                ) is Some implies eval_l(r, env, ls) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums@) {
                rank(v, sty(*st), enums@) as i64
            } else {
                -1i64
            })) by {
                assert(eval_l(in_dom, env, ls) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
        }
        Some(r)
    } else {
        let e = ite(copy_expr(&in_dom), copy_expr(&r), ci(-1));
        proof {
            assert forall|m: nat| #[trigger] all_pure(slots@, m) implies pure_below(e, m) by {
                assert(pure_below(in_dom, m));
                assert(pure_below(r, m));
                assert(pure_below(int_lit(-1i64), m));
            }
            assert forall|env: Env, ls: Seq<Value>, v: SVal|
                fits_s(xty(*t), sty(*st)) && #[trigger] denotes(slots@, env, ls, v, xty(*t), enums@) && keys(
                    sty(*st),
                    enums@,
                ) is Some implies eval_l(e, env, ls) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums@) {
                rank(v, sty(*st), enums@) as i64
            } else {
                -1i64
            })) by {
                assert(eval_l(in_dom, env, ls) == Ok::<Value, ErrKind>(Value::Bool(member(v, sty(*st), enums@))));
                assert(eval_l(int_lit(-1i64), env, ls) == Ok::<Value, ErrKind>(Value::Int(-1i64)));
            }
        }
        Some(e)
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
