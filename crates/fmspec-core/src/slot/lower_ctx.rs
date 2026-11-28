//! 下ろしの文脈（`LowerCtx`）と、束縛の列（`Block`）。下ろしの各モジュールと、その証明が共有する型。

use crate::kernel::model::{Expr, Value};
use crate::kernel::typing::ETy;
#[cfg(verus_keep_ghost)]
use crate::slot::expr_build::all_pure;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{sty, wf_xtype, width, width_sum, xty, xwidth, STy, XTy};
use crate::value::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::value::limits::{lemma_width_sum_prefix, lim_x};
use vstd::prelude::*;

verus! {

/// 状態変数や引数の、スロットの列での位置。
pub struct Layout {
    pub ty: SType,
    pub offset: usize,
}

/// 名前付きの定数。値はスロットごとの中核の値。
pub struct Constant {
    pub ty: SType,
    pub slots: Vec<Value>,
}

/// 下ろしの文脈。
pub struct LowerCtx {
    /// 各列挙型のラベルの数。
    pub enums: Vec<i64>,
    /// 状態変数。`None` なら状態を参照できない（初期値と定数）。
    pub states: Option<Vec<Layout>>,
    /// 公開引数に続けて内部選択。
    pub args: Vec<Layout>,
    /// 遷移後の状態と出力を参照できる（遷移契約）。
    pub next: bool,
    pub out: Option<SType>,
    pub consts: Vec<Constant>,
}

/// 局所変数（`let` と量化の束縛）。
pub struct Bound {
    pub ty: XType,
    pub slots: Vec<Expr>,
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

/// 評価の順に並べた束縛の列。`base` は最初の束縛の局所変数の添字。
pub struct Block {
    pub base: usize,
    pub binds: Vec<Expr>,
    /// 外側の局所変数（添字が `base` 未満）の中核の型。
    pub outer: Ghost<Seq<ETy>>,
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
    new.base == old.base && new.outer == old.outer && new.wf() && old.binds@.len() <= new.binds@.len() && forall|i: int|
        0 <= i < old.binds@.len() ==> #[trigger] new.binds@[i] == old.binds@[i]
}

/// 下ろしの失敗。
pub enum Fail {
    /// 型や大きさが合わないか、スロットの数などが食い違う。
    Type,
    /// 束縛の深さが `usize::MAX` に達した。
    Depth,
}

/// `b1` は、`b0` に `e` を束縛して `x` で指すか、`e` をそのまま `x` とするかである。
pub open spec fn added(b0: Block, b1: Block, e: Expr, x: Expr) -> bool {
    ||| x == e && b1.binds@ == b0.binds@
    ||| x == Expr::Local(b0.depth_s() as usize) && b1.binds@ == b0.binds@.push(e)
}

/// `l` は、型の列 `ts` の `i` 番目の位置である。位置は、それより前の型の幅の和である。
pub open spec fn layout_at(l: Layout, ts: Seq<STy>, i: int, enums: Seq<i64>) -> bool {
    sty(l.ty) == ts[i] && l.offset == width_sum(ts.take(i), enums)
}

pub open spec fn layouts_at(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>) -> bool {
    &&& ls.len() == ts.len()
    &&& width_sum(ts, enums) <= usize::MAX
    &&& forall|i: int| 0 <= i < ls.len() ==> #[trigger] layout_at(ls[i], ts, i, enums)
}

/// 型の列の位置の終わりは、幅の和以下である。
pub proof fn lemma_layout_end(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>, i: int)
    requires
        layouts_at(ls, ts, enums),
        0 <= i < ls.len(),
    ensures
        ls[i].offset + width(ts[i], enums) <= width_sum(ts, enums),
{
    assert(layout_at(ls[i], ts, i, enums));
    assert(ts.take(i + 1).drop_last() =~= ts.take(i));
    assert(ts.take(i + 1).last() == ts[i]);
    lemma_width_sum_prefix(ts, enums, i + 1);
}

/// 式の型が整形式で、大きさの条件を満たす。
pub open spec fn ok_x(t: XTy, enums: Seq<i64>) -> bool {
    wf_xtype(t, enums) && lim_x(t, enums)
}

/// スロットの列は型 `t` の幅だけあり、深さ `n` 未満の局所変数だけを参照する純粋な式である。
pub open spec fn shaped(slots: Seq<Expr>, t: XTy, n: nat, enums: Seq<i64>) -> bool {
    slots.len() == xwidth(t, enums) && all_pure(slots, n)
}

pub open spec fn layout_tys(ls: Seq<Layout>) -> Seq<STy> {
    Seq::new(ls.len(), |i: int| sty(ls[i].ty))
}

/// 局所変数の束縛が整形式である。
pub open spec fn sc_wf(sc: Seq<Bound>, n: nat, enums: Seq<i64>) -> bool {
    forall|i: int|
        0 <= i < sc.len() ==> ok_x(xty(#[trigger] sc[i].ty), enums) && shaped(sc[i].slots@, xty(sc[i].ty), n, enums)
}

} // verus!
