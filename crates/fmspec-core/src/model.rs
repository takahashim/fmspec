//! IR検証前のモデルと、値・型・式の定義。
//!
//! 名前（状態名、操作名など）は持たない。文字列名はIRのロード時に添字へ解決する（仕様書 §6）。

use vstd::prelude::*;

verus! {

/// 状態変数、引数、出力の型。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    /// 閉区間 `min..=max` の整数。
    Int(i64, i64),
    /// 列挙型。`RawModel::enums` の添字で指す。
    Enum(usize),
}

/// 式の評価結果。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i64),
    /// 列挙型の添字と、ラベルの添字。
    Enum(usize, i64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

pub enum Expr {
    Const(Value),
    /// 遷移前の状態変数。不変条件と終端条件では現在の状態変数。
    Var(usize),
    /// 操作の引数。公開引数に続けて内部選択を並べた列の添字。
    Arg(usize),
    /// 遷移後の状態変数。遷移契約でだけ使える。
    Next(usize),
    /// 操作の出力。出力を宣言した操作の遷移契約でだけ使える。
    Out,
    /// 両辺を左から順に評価する二項演算。
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    /// 左が偽なら右を評価しない。
    And(Box<Expr>, Box<Expr>),
    /// 左が真なら右を評価しない。
    Or(Box<Expr>, Box<Expr>),
    /// 前件が偽なら後件を評価しない。
    Implies(Box<Expr>, Box<Expr>),
    /// 条件に続いて、選ばれた枝だけを評価する。
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
}

pub struct Update {
    pub target: usize,
    pub expr: Expr,
}

pub struct Output {
    pub ty: Type,
    pub expr: Expr,
}

pub struct Action {
    /// `domains` の先頭 `n_params` 個が公開引数、残りが内部選択。
    pub n_params: usize,
    pub domains: Vec<Type>,
    pub guard: Expr,
    pub updates: Vec<Update>,
    pub output: Option<Output>,
}

/// 遷移契約。`action` の有効な遷移すべてに適用する。
pub struct Contract {
    pub action: usize,
    pub expr: Expr,
}

pub struct RawModel {
    /// 各列挙型のラベル数。
    pub enums: Vec<i64>,
    pub state_types: Vec<Type>,
    /// 初期状態の符号化列。
    pub init: Vec<i64>,
    pub actions: Vec<Action>,
    pub invariants: Vec<Expr>,
    pub contracts: Vec<Contract>,
    pub terminal: Option<Expr>,
}

} // verus!
