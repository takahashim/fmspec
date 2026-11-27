//! IRのJSONと、名前を解決したモデルの対応（仕様）。
//!
//! `fmspec-ir` は、IRのJSONを読んで名前を解決したモデル（[`SModel`]）と名前の表（[`IrNames`]）を組み立てる。
//! ここでは、JSONの木と組み立てた結果の対応 [`ir_rel`] を、IRの各構文が `SModel` のどの構造になるかを
//! 直接書いて定める（`docs/ir.md` の「モデル」「型と値」「式」）。これがIRの意味の定義である。
//! 対応を確かめる検査は [`crate::ir_check`] にある。
//!
//! 受理の条件（未知のキー、空でない配列など）は定めない。拒否すべきIRを拒否するのは `fmspec-ir` の仕事で、
//! ここでは受理したIRの意味を定める。式の型から決まる注釈（`contains` の Set と List の区別、要素の型など）は
//! JSONに書かれないので制約しない。注釈は中核の型付け（[`crate::infer::type_of`]）が検査する。

#[cfg(verus_keep_ghost)]
use crate::encoding::{sty, stys, width_sum};
use crate::encoding::SType;
use crate::model::{BinOp, Value};
use crate::smodel::{SAction, SModel};
use crate::source::{Over, SetOp, TExpr};
use vstd::prelude::*;

verus! {

// ---- JSONの木 ----

/// オブジェクトの1つのキーと値。
pub struct Member {
    pub key: Vec<char>,
    pub value: Json,
}

/// JSONの値。数は符号付き64ビット整数だけを持つ。それ以外の数は `Other` にする。
pub enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Str(Vec<char>),
    Arr(Vec<Json>),
    Obj(Vec<Member>),
    Other,
}

/// 名前の表。`fmspec-ir` が組み立て、検査の条件や証拠を名前で読むときと、結果を表示するときに使う。
pub struct IrNames {
    pub enums: Vec<Vec<char>>,
    /// 列挙型ごとのラベル。
    pub variants: Vec<Vec<Vec<char>>>,
    pub consts: Vec<Vec<char>>,
    pub states: Vec<Vec<char>>,
    pub actions: Vec<Vec<char>>,
    /// 操作ごとの公開引数と内部選択の名前。
    pub params: Vec<Vec<Vec<char>>>,
    pub choices: Vec<Vec<Vec<char>>>,
    pub invariants: Vec<Vec<char>>,
    pub contracts: Vec<Vec<char>>,
    /// Recordのフィールドの名前。`SType::Record` と `TExpr::Record`、`TExpr::Field` の番号はこの表の添字である。
    pub fields: Vec<Vec<char>>,
}

// ---- JSONの読み方 ----

/// キー `k` を持つ最初のメンバーの位置。
pub open spec fn find(ms: Seq<Member>, k: Seq<char>) -> Option<int>
    decreases ms.len(),
{
    if ms.len() == 0 {
        None
    } else if ms[0].key@ == k {
        Some(0)
    } else {
        match find(ms.drop_first(), k) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// オブジェクトのキー `k` の値。
pub open spec fn get(j: Json, k: Seq<char>) -> Option<Json> {
    match j {
        Json::Obj(ms) => match find(ms@, k) {
            Some(i) => Some(ms@[i].value),
            None => None,
        },
        _ => None,
    }
}

/// キー `k` がないか、値が `null`。
pub open spec fn absent(j: Json, k: Seq<char>) -> bool {
    get(j, k) is None || get(j, k) == Some(Json::Null)
}

/// キー `k` の値。[`absent`] でないときに使う。
pub open spec fn at(j: Json, k: Seq<char>) -> Json {
    get(j, k)->Some_0
}

/// キーを1つだけ持つオブジェクトの、そのキーと値。式と型はこの形である。
pub open spec fn one(j: Json) -> Option<(Seq<char>, Json)> {
    match j {
        Json::Obj(ms) => if ms@.len() == 1 {
            Some((ms@[0].key@, ms@[0].value))
        } else {
            None
        },
        _ => None,
    }
}

/// 配列の要素の列。
pub open spec fn arr(j: Json) -> Option<Seq<Json>> {
    match j {
        Json::Arr(xs) => Some(xs@),
        _ => None,
    }
}

/// 長さ `n` の配列の要素の列（演算子のオペランド）。
pub open spec fn ops(j: Json, n: nat) -> Option<Seq<Json>> {
    match j {
        Json::Arr(xs) => if xs@.len() == n {
            Some(xs@)
        } else {
            None
        },
        _ => None,
    }
}

/// 省略できる配列のキー。省略か `null` なら空の列。
pub open spec fn opt_arr(j: Json, k: Seq<char>) -> Option<Seq<Json>> {
    if absent(j, k) {
        Some(Seq::empty())
    } else {
        arr(at(j, k))
    }
}

pub open spec fn str_of(j: Json) -> Option<Seq<char>> {
    match j {
        Json::Str(s) => Some(s@),
        _ => None,
    }
}

/// 0以上の整数。
pub open spec fn nat_of(j: Json) -> Option<nat> {
    match j {
        Json::Int(n) => if n >= 0 {
            Some(n as nat)
        } else {
            None
        },
        _ => None,
    }
}

/// 空のオブジェクト（`{"bool": {}}` と `{"output": {}}` の値）。
pub open spec fn empty_obj(j: Json) -> bool {
    match j {
        Json::Obj(ms) => ms@.len() == 0,
        _ => false,
    }
}

// ---- 名前 ----

pub open spec fn strs(v: Seq<Vec<char>>) -> Seq<Seq<char>> {
    v.map_values(|s: Vec<char>| s@)
}

/// 名前 `x` の最初の位置。
pub open spec fn index_of(s: Seq<Seq<char>>, x: Seq<char>) -> Option<int>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s[0] == x {
        Some(0)
    } else {
        match index_of(s.drop_first(), x) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// 名前 `x` の最後の位置（内側から探す局所変数）。
pub open spec fn last_of(s: Seq<Seq<char>>, x: Seq<char>) -> Option<int>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s.last() == x {
        Some(s.len() - 1)
    } else {
        last_of(s.drop_last(), x)
    }
}

pub open spec fn distinct(s: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// 名前の表の名前に重複がない（列挙型、ラベル、定数、操作、Recordのフィールド）。
pub open spec fn names_ok(ns: IrNames) -> bool {
    &&& distinct(strs(ns.enums@))
    &&& ns.variants@.len() == ns.enums@.len()
    &&& forall|i: int| 0 <= i < ns.variants@.len() ==> distinct(#[trigger] strs(ns.variants@[i]@))
    &&& distinct(strs(ns.consts@))
    &&& distinct(strs(ns.actions@))
    &&& distinct(strs(ns.fields@))
}

// ---- 型 ----

/// 型のJSON `j` は型 `t` を表す。
pub open spec fn ty_rel(j: Json, ns: IrNames, t: SType) -> bool
    decreases j, 1nat,
    via ty_rel_dec
{
    match one(j) {
        None => false,
        Some((k, b)) => if k == "bool"@ {
            empty_obj(b) && t == SType::Bool
        } else if k == "int"@ {
            match t {
                SType::Int(lo, hi) => get(b, "min"@) == Some(Json::Int(lo)) && get(b, "max"@) == Some(Json::Int(hi)),
                _ => false,
            }
        } else if k == "enum"@ {
            match (str_of(b), t) {
                (Some(n), SType::Enum(id)) => index_of(strs(ns.enums@), n) == Some(id as int),
                _ => false,
            }
        } else if k == "tuple"@ {
            match (arr(b), t) {
                (Some(xs), SType::Tuple(ts)) => xs.len() == ts@.len() && forall|i: int|
                    0 <= i < xs.len() ==> ty_rel(#[trigger] xs[i], ns, ts@[i]),
                _ => false,
            }
        } else if k == "record"@ {
            match (arr(b), t) {
                (Some(xs), SType::Record(ids, ts)) => xs.len() == ts@.len() && xs.len() == ids@.len() && forall|i: int|
                    0 <= i < xs.len() ==> field_ty_rel(#[trigger] xs[i], ns, ids@[i], ts@[i]),
                _ => false,
            }
        } else if k == "option"@ {
            match t {
                SType::Option(x) => ty_rel(b, ns, *x),
                _ => false,
            }
        } else if k == "set"@ {
            match t {
                SType::Set(x) => ty_rel(b, ns, *x),
                _ => false,
            }
        } else if k == "map"@ {
            match t {
                SType::Map(x, y) => !absent(b, "key"@) && !absent(b, "value"@) && ty_rel(at(b, "key"@), ns, *x) && ty_rel(
                    at(b, "value"@),
                    ns,
                    *y,
                ),
                _ => false,
            }
        } else if k == "list"@ {
            match t {
                SType::List(x, max) => !absent(b, "of"@) && ty_rel(at(b, "of"@), ns, *x) && get(b, "max"@) is Some
                    && nat_of(at(b, "max"@)) == Some(max as nat),
                _ => false,
            }
        } else {
            false
        },
    }
}

/// Recordの型のフィールド `{"name", "type"}` は、名前の番号 `id` と型 `t` を表す。
pub open spec fn field_ty_rel(j: Json, ns: IrNames, id: usize, t: SType) -> bool
    decreases j, 0nat,
    via field_ty_rel_dec
{
    &&& get(j, "name"@) is Some
    &&& id < ns.fields@.len()
    &&& str_of(at(j, "name"@)) == Some(ns.fields@[id as int]@)
    &&& get(j, "type"@) is Some
    &&& ty_rel(at(j, "type"@), ns, t)
}

/// キー `k` の値が型 `t` を表す。
pub open spec fn ty_rel_at(j: Json, k: Seq<char>, ns: IrNames, t: SType) -> bool {
    get(j, k) is Some && ty_rel(at(j, k), ns, t)
}

#[via_fn]
proof fn ty_rel_dec(j: Json, ns: IrNames, t: SType) {
    lemma_one_dec(j);
    if let Some((_, b)) = one(j) {
        lemma_get_dec(b);
        lemma_arr_dec(b);
    }
}

#[via_fn]
proof fn field_ty_rel_dec(j: Json, ns: IrNames, id: usize, t: SType) {
    lemma_get_dec(j);
}

// ---- 式 ----

/// 式を読む文脈。操作の公開引数と内部選択の数（操作の外では0）。
pub struct ECtx {
    pub np: nat,
    pub nc: nat,
}

/// 二項演算子のキー。
pub open spec fn bin_op(k: Seq<char>) -> Option<BinOp> {
    if k == "add"@ {
        Some(BinOp::Add)
    } else if k == "sub"@ {
        Some(BinOp::Sub)
    } else if k == "mul"@ {
        Some(BinOp::Mul)
    } else if k == "div"@ {
        Some(BinOp::Div)
    } else if k == "mod"@ {
        Some(BinOp::Mod)
    } else if k == "lt"@ {
        Some(BinOp::Lt)
    } else if k == "le"@ {
        Some(BinOp::Le)
    } else if k == "gt"@ {
        Some(BinOp::Gt)
    } else if k == "ge"@ {
        Some(BinOp::Ge)
    } else {
        None
    }
}

/// 集合の演算子のキー。
pub open spec fn set_op(k: Seq<char>) -> Option<SetOp> {
    if k == "union"@ {
        Some(SetOp::Union)
    } else if k == "intersection"@ {
        Some(SetOp::Intersection)
    } else if k == "difference"@ {
        Some(SetOp::Difference)
    } else if k == "subset"@ {
        Some(SetOp::Subset)
    } else {
        None
    }
}

/// 配列 `b` の各要素の式が、式の列 `es` に対応する。
pub open spec fn exs_rel(b: Json, es: Seq<TExpr>, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 0nat,
    via exs_rel_dec
{
    match b {
        Json::Arr(xs) => xs@.len() == es.len() && forall|i: int|
            0 <= i < xs@.len() ==> ex_rel(#[trigger] xs@[i], es[i], ns, c, sc),
        _ => false,
    }
}

#[via_fn]
proof fn exs_rel_dec(b: Json, es: Seq<TExpr>, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_arr_dec(b);
}

/// 式のJSON `j` は、局所変数の名前の列 `sc`（外側から順に並べる）のもとで、式 `e` を表す。
pub open spec fn ex_rel(j: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases j, 1nat,
    via ex_rel_dec
{
    match one(j) {
        None => false,
        Some((k, b)) => if k == "int"@ {
            b matches Json::Int(n) && e == TExpr::Lit(Value::Int(n))
        } else if k == "bool"@ {
            b matches Json::Bool(x) && e == TExpr::Lit(Value::Bool(x))
        } else if k == "enum"@ {
            match (e, str_of(at(b, "type"@)), str_of(at(b, "variant"@))) {
                (TExpr::Lit(Value::Enum(id, v)), Some(tn), Some(vn)) => get(b, "type"@) is Some && get(b, "variant"@) is Some
                    && index_of(strs(ns.enums@), tn) == Some(id as int) && id < ns.variants@.len() && index_of(
                    strs(ns.variants@[id as int]@),
                    vn,
                ) == Some(v as int),
                _ => false,
            }
        } else if k == "var"@ {
            match (nat_of(b), e) {
                (Some(i), TExpr::Var(x)) => x as nat == i,
                _ => false,
            }
        } else if k == "next"@ {
            match (nat_of(b), e) {
                (Some(i), TExpr::Next(x)) => x as nat == i,
                _ => false,
            }
        } else if k == "param"@ {
            match (nat_of(b), e) {
                (Some(i), TExpr::Arg(x)) => i < c.np && x as nat == i,
                _ => false,
            }
        } else if k == "choice"@ {
            match (nat_of(b), e) {
                (Some(i), TExpr::Arg(x)) => i < c.nc && x as nat == c.np + i,
                _ => false,
            }
        } else if k == "output"@ {
            empty_obj(b) && e == TExpr::Out
        } else if k == "local"@ {
            match (str_of(b), e) {
                (Some(n), TExpr::Local(i)) => last_of(sc, n) == Some(i as int),
                _ => false,
            }
        } else if k == "const"@ {
            match (str_of(b), e) {
                (Some(n), TExpr::Const(i)) => index_of(strs(ns.consts@), n) == Some(i as int),
                _ => false,
            }
        } else if bin_op(k) is Some {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Bin(op, x, y)) => Some(op) == bin_op(k) && ex_rel(xs[0], *x, ns, c, sc) && ex_rel(
                    xs[1],
                    *y,
                    ns,
                    c,
                    sc,
                ),
                _ => false,
            }
        } else if k == "eq"@ || k == "ne"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Eq(pos, x, y)) => pos == (k == "eq"@) && ex_rel(xs[0], *x, ns, c, sc) && ex_rel(
                    xs[1],
                    *y,
                    ns,
                    c,
                    sc,
                ),
                _ => false,
            }
        } else if k == "not"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Not(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "all"@ || k == "any"@ {
            match (arr(b), e) {
                (Some(_), TExpr::Fold(all, es)) => all == (k == "all"@) && exs_rel(b, es@, ns, c, sc),
                _ => false,
            }
        } else if k == "implies"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Implies(x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "ite"@ {
            match (ops(b, 3), e) {
                (Some(xs), TExpr::Ite(p, x, y)) => ex_rel(xs[0], *p, ns, c, sc) && ex_rel(xs[1], *x, ns, c, sc)
                    && ex_rel(xs[2], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "let"@ {
            match (str_of(at(b, "name"@)), e) {
                (Some(n), TExpr::Let(x, y)) => get(b, "name"@) is Some && get(b, "value"@) is Some && get(b, "body"@) is Some
                    && ex_rel(at(b, "value"@), *x, ns, c, sc) && ex_rel(at(b, "body"@), *y, ns, c, sc.push(n)),
                _ => false,
            }
        } else if k == "forall"@ || k == "exists"@ {
            match (str_of(at(b, "name"@)), e) {
                (Some(n), TExpr::Quant(all, over, y)) => all == (k == "forall"@) && get(b, "name"@) is Some && get(
                    b,
                    "body"@,
                ) is Some && over_rel(b, over, ns, c, sc) && ex_rel(at(b, "body"@), *y, ns, c, sc.push(n)),
                _ => false,
            }
        } else if k == "tuple"@ {
            match (arr(b), e) {
                (Some(_), TExpr::Tuple(es)) => exs_rel(b, es@, ns, c, sc),
                _ => false,
            }
        } else if k == "record"@ {
            match (arr(b), e) {
                (Some(xs), TExpr::Record(ids, es)) => xs.len() == ids@.len() && xs.len() == es@.len() && forall|i: int|
                    0 <= i < xs.len() ==> field_rel(#[trigger] xs[i], ids@[i], es@[i], ns, c, sc),
                _ => false,
            }
        } else if k == "nth"@ {
            match (nat_of(at(b, "index"@)), e) {
                (Some(i), TExpr::Nth(x, y)) => get(b, "of"@) is Some && get(b, "index"@) is Some && y as nat == i && ex_rel(
                    at(b, "of"@),
                    *x,
                    ns,
                    c,
                    sc,
                ),
                _ => false,
            }
        } else if k == "field"@ {
            match (str_of(at(b, "name"@)), e) {
                (Some(n), TExpr::Field(x, id, _)) => get(b, "of"@) is Some && get(b, "name"@) is Some && id < ns.fields@.len()
                    && ns.fields@[id as int]@ == n && ex_rel(at(b, "of"@), *x, ns, c, sc),
                _ => false,
            }
        } else if k == "none"@ {
            match e {
                TExpr::None(t) => ty_rel(b, ns, t),
                _ => false,
            }
        } else if k == "some"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Some(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "is_some"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::IsSome(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "is_none"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::IsNone(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "unwrap"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Unwrap(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "set"@ {
            match (arr(at(b, "items"@)), e) {
                (Some(_), TExpr::SetLit(t, es)) => get(b, "items"@) is Some && ty_rel_at(b, "of"@, ns, t) && exs_rel(
                    at(b, "items"@),
                    es@,
                    ns,
                    c,
                    sc,
                ),
                _ => false,
            }
        } else if k == "map"@ {
            match (arr(at(b, "items"@)), e) {
                (Some(xs), TExpr::MapLit(kt, vt, items)) => get(b, "items"@) is Some && ty_rel_at(b, "key"@, ns, kt)
                    && ty_rel_at(b, "value"@, ns, vt) && xs.len() == items@.len() && forall|i: int|
                    0 <= i < xs.len() ==> item_rel(#[trigger] xs[i], items@[i], ns, c, sc),
                _ => false,
            }
        } else if k == "list"@ {
            match (arr(at(b, "items"@)), e) {
                (Some(xs), TExpr::ListLit(t, max, es)) => get(b, "items"@) is Some && ty_rel_at(b, "of"@, ns, t) && get(
                    b,
                    "max"@,
                ) is Some && nat_of(at(b, "max"@)) == Some(max as nat) && exs_rel(at(b, "items"@), es@, ns, c, sc),
                _ => false,
            }
        } else if k == "contains"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::SetContains(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                (Some(xs), TExpr::ListContains(x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "insert"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Insert(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "remove"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Remove(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if set_op(k) is Some {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::SetBin(op, x, y)) => Some(op) == set_op(k) && ex_rel(xs[0], *x, ns, c, sc) && ex_rel(
                    xs[1],
                    *y,
                    ns,
                    c,
                    sc,
                ),
                _ => false,
            }
        } else if k == "size"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Size(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "is_empty"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::IsEmpty(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "has_key"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::HasKey(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "get"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Get(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "delete"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Delete(_, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "put"@ {
            match (ops(b, 3), e) {
                (Some(xs), TExpr::Put(_, _, x, y, z)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc)
                    && ex_rel(xs[2], *z, ns, c, sc),
                _ => false,
            }
        } else if k == "keys"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Keys(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "at"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::At(x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "first"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::First(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "last"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Last(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "push"@ {
            match (ops(b, 2), e) {
                (Some(xs), TExpr::Push(_, _, x, y)) => ex_rel(xs[0], *x, ns, c, sc) && ex_rel(xs[1], *y, ns, c, sc),
                _ => false,
            }
        } else if k == "pop"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Pop(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else if k == "shift"@ {
            match (ops(b, 1), e) {
                (Some(xs), TExpr::Shift(x)) => ex_rel(xs[0], *x, ns, c, sc),
                _ => false,
            }
        } else {
            false
        },
    }
}

/// Recordの式のフィールド `{"name", "expr"}`。
pub open spec fn field_rel(j: Json, id: usize, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases j, 0nat,
    via field_rel_dec
{
    &&& get(j, "name"@) is Some
    &&& id < ns.fields@.len()
    &&& str_of(at(j, "name"@)) == Some(ns.fields@[id as int]@)
    &&& get(j, "expr"@) is Some
    &&& ex_rel(at(j, "expr"@), e, ns, c, sc)
}

/// Mapの式の項目 `[キー, 値]`。
pub open spec fn item_rel(j: Json, it: crate::source::Item, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases j, 0nat,
    via item_rel_dec
{
    match ops(j, 2) {
        Some(xs) => ex_rel(xs[0], it.key, ns, c, sc) && ex_rel(xs[1], it.value, ns, c, sc),
        None => false,
    }
}

/// 量化のたどる値。`in` の式か、`type` の型。
pub open spec fn over_rel(b: Json, over: Over, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 0nat,
    via over_rel_dec
{
    if get(b, "in"@) is Some && get(b, "type"@) is None {
        match over {
            Over::Set(_, x) => ex_rel(at(b, "in"@), *x, ns, c, sc),
            Over::Map(_, x) => ex_rel(at(b, "in"@), *x, ns, c, sc),
            Over::List(x) => ex_rel(at(b, "in"@), *x, ns, c, sc),
            _ => false,
        }
    } else if get(b, "type"@) is Some && get(b, "in"@) is None {
        match over {
            Over::Type(t) => ty_rel(at(b, "type"@), ns, t),
            _ => false,
        }
    } else {
        false
    }
}

#[via_fn]
proof fn field_rel_dec(j: Json, id: usize, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_get_dec(j);
}

#[via_fn]
proof fn item_rel_dec(j: Json, it: crate::source::Item, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_arr_dec(j);
}

#[via_fn]
proof fn over_rel_dec(b: Json, over: Over, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_get_dec(b);
}

#[via_fn]
proof fn ex_rel_dec(j: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_one_dec(j);
    if let Some((_, b)) = one(j) {
        lemma_get_dec(b);
        lemma_arr_dec(b);
        if let Some(x) = get(b, "items"@) {
            lemma_arr_dec(x);
        }
    }
}

// ---- 減少の補題 ----

pub proof fn lemma_find(ms: Seq<Member>, k: Seq<char>)
    ensures
        find(ms, k) matches Some(i) ==> 0 <= i < ms.len() && ms[i].key@ == k,
    decreases ms.len(),
{
    if ms.len() > 0 && ms[0].key@ != k {
        lemma_find(ms.drop_first(), k);
    }
}

pub proof fn lemma_one_dec(j: Json)
    ensures
        one(j) matches Some((_, b)) ==> decreases_to!(j => b),
{
    if let Json::Obj(ms) = j {
        if ms@.len() == 1 {
            vstd::std_specs::vec::axiom_vec_index_decreases(ms, 0);
        }
    }
}

pub proof fn lemma_get_dec(j: Json)
    ensures
        forall|k: Seq<char>| #[trigger] get(j, k) is Some ==> decreases_to!(j => get(j, k)->Some_0),
{
    assert forall|k: Seq<char>| #[trigger] get(j, k) is Some implies decreases_to!(j => get(j, k)->Some_0) by {
        if let Json::Obj(ms) = j {
            lemma_find(ms@, k);
            if let Some(i) = find(ms@, k) {
                vstd::std_specs::vec::axiom_vec_index_decreases(ms, i);
            }
        }
    }
}

pub proof fn lemma_arr_dec(j: Json)
    ensures
        arr(j) matches Some(xs) ==> forall|i: int| 0 <= i < xs.len() ==> decreases_to!(j => #[trigger] xs[i]),
{
    if let Json::Arr(xs) = j {
        assert forall|i: int| 0 <= i < xs@.len() implies decreases_to!(j => #[trigger] xs@[i]) by {
            vstd::std_specs::vec::axiom_vec_index_decreases(xs, i);
        }
    }
}

// ---- モデル ----

/// 列挙型の定義 `{"name", "variants"}`。
pub open spec fn enum_rel(j: Json, ns: IrNames, i: int, n: i64) -> bool {
    &&& str_of(at(j, "name"@)) == Some(ns.enums@[i]@)
    &&& get(j, "name"@) is Some
    &&& get(j, "variants"@) is Some
    &&& arr(at(j, "variants"@)) matches Some(vs) && vs.len() == ns.variants@[i]@.len() && n == vs.len() && forall|q: int|
        0 <= q < vs.len() ==> #[trigger] str_of(vs[q]) == Some(ns.variants@[i]@[q]@)
}

/// 状態も引数も参照しない文脈（定数、初期値、初期条件、不変条件、終端条件）。
pub open spec fn no_args() -> ECtx {
    ECtx { np: 0, nc: 0 }
}

/// 操作 `a` の文脈（guard、更新、出力、遷移契約）。
pub open spec fn act_ctx(ns: IrNames, a: int) -> ECtx {
    ECtx { np: ns.params@[a]@.len(), nc: ns.choices@[a]@.len() }
}

/// 定数の定義 `{"name", "type", "value"}`。
pub open spec fn const_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.consts@[i]@)
    &&& ty_rel_at(j, "type"@, ns, sm.consts@[i].ty)
    &&& get(j, "value"@) is Some
    &&& ex_rel(at(j, "value"@), sm.consts@[i].expr, ns, no_args(), Seq::empty())
}

/// 状態変数の定義 `{"id", "name", "type", "initial"}` または `{"id", "name", "type", "initial_in"}`。
pub open spec fn state_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    let inits = sm.inits@[i]@;
    &&& get(j, "id"@) matches Some(x) ==> nat_of(x) == Some(i as nat)
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.states@[i]@)
    &&& ty_rel_at(j, "type"@, ns, sm.states@[i])
    &&& if get(j, "initial"@) is Some {
        get(j, "initial_in"@) is None && inits.len() == 1 && ex_rel(at(j, "initial"@), inits[0], ns, no_args(), Seq::empty())
    } else {
        get(j, "initial_in"@) is Some && exs_rel(at(j, "initial_in"@), inits, ns, no_args(), Seq::empty())
    }
}

/// 引数の宣言 `{"name", "type", "in"}` の列。
pub open spec fn binds_rel(xs: Seq<Json>, names: Seq<Vec<char>>, tys: Seq<SType>, ns: IrNames) -> bool {
    &&& xs.len() == names.len()
    &&& xs.len() == tys.len()
    &&& forall|i: int|
        0 <= i < xs.len() ==> get(#[trigger] xs[i], "name"@) is Some && str_of(at(xs[i], "name"@)) == Some(names[i]@)
            && ty_rel_at(xs[i], "type"@, ns, tys[i])
}

/// 引数の宣言の列から、動的ドメイン（`in`）を持つ引数の、引数の番号とドメインの式の列。
pub open spec fn doms(xs: Seq<Json>, base: nat) -> Seq<(nat, Json)>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else {
        let rest = doms(xs.drop_first(), base + 1);
        if get(xs[0], "in"@) is Some {
            seq![(base, at(xs[0], "in"@))] + rest
        } else {
            rest
        }
    }
}

/// 動的ドメインの検査 `contains(ドメイン, 引数)`。
pub open spec fn member_rel(d: (nat, Json), e: TExpr, ns: IrNames, c: ECtx) -> bool {
    match e {
        TExpr::SetContains(_, x, y) => ex_rel(d.1, *x, ns, c, Seq::empty()) && y == Box::new(TExpr::Arg(d.0 as usize)),
        TExpr::ListContains(x, y) => ex_rel(d.1, *x, ns, c, Seq::empty()) && y == Box::new(TExpr::Arg(d.0 as usize)),
        _ => false,
    }
}

/// guard。動的ドメインがあれば、その検査を引数の順に並べ、最後に guard の式を置いた `all` にする。
/// guard を省略すれば真。
pub open spec fn guard_rel(j: Json, ds: Seq<(nat, Json)>, g: TExpr, ns: IrNames, c: ECtx) -> bool {
    let user = |u: TExpr|
        if absent(j, "guard"@) {
            u == TExpr::Lit(Value::Bool(true))
        } else {
            ex_rel(at(j, "guard"@), u, ns, c, Seq::empty())
        };
    if ds.len() == 0 {
        user(g)
    } else {
        match g {
            TExpr::Fold(all, es) => all && es@.len() == ds.len() + 1 && user(es@.last()) && forall|q: int|
                0 <= q < ds.len() ==> #[trigger] member_rel(ds[q], es@[q], ns, c),
            _ => false,
        }
    }
}

/// 更新 `{"target", "expr"}`。
pub open spec fn update_rel(j: Json, u: crate::smodel::SUpdate, ns: IrNames, c: ECtx) -> bool {
    &&& get(j, "target"@) is Some
    &&& nat_of(at(j, "target"@)) == Some(u.var as nat)
    &&& get(j, "expr"@) is Some
    &&& ex_rel(at(j, "expr"@), u.expr, ns, c, Seq::empty())
}

/// 操作 `{"name", "params", "choices", "guard", "updates", "output"}`。
pub open spec fn action_rel(j: Json, ns: IrNames, a: int, sa: SAction, enums: Seq<i64>) -> bool {
    let c = act_ctx(ns, a);
    let ps = ns.params@[a]@;
    let cs = ns.choices@[a]@;
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.actions@[a]@)
    &&& match (opt_arr(j, "params"@), opt_arr(j, "choices"@)) {
        (Some(px), Some(cx)) => {
            &&& binds_rel(px, ps, sa.args@.take(ps.len() as int), ns)
            &&& binds_rel(cx, cs, sa.args@.skip(ps.len() as int), ns)
            &&& sa.args@.len() == ps.len() + cs.len()
            &&& sa.n_params as int == width_sum(stys(sa.args@.take(ps.len() as int)), enums)
            &&& guard_rel(j, doms(px + cx, 0), sa.guard, ns, c)
        },
        _ => false,
    }
    &&& opt_arr(j, "updates"@) matches Some(us) && us.len() == sa.updates@.len() && forall|u: int|
        0 <= u < us.len() ==> #[trigger] update_rel(us[u], sa.updates@[u], ns, c)
    &&& if absent(j, "output"@) {
        sa.output is None
    } else {
        sa.output matches Some(o) && ty_rel_at(at(j, "output"@), "type"@, ns, o.ty) && get(at(j, "output"@), "expr"@) is Some
            && ex_rel(at(at(j, "output"@), "expr"@), o.expr, ns, c, Seq::empty())
    }
}

/// 遷移契約 `{"name", "action", "expr"}`。
pub open spec fn contract_rel(j: Json, ns: IrNames, k: int, sm: SModel) -> bool {
    let a = sm.contracts@[k].action as int;
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.contracts@[k]@)
    &&& get(j, "action"@) is Some
    &&& str_of(at(j, "action"@)) matches Some(an) && index_of(strs(ns.actions@), an) == Some(a)
    &&& get(j, "expr"@) is Some
    &&& ex_rel(at(j, "expr"@), sm.contracts@[k].expr, ns, act_ctx(ns, a), Seq::empty())
}

/// 不変条件 `{"name", "expr"}`。
pub open spec fn invariant_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.invariants@[i]@)
    &&& get(j, "expr"@) is Some
    &&& ex_rel(at(j, "expr"@), sm.invariants@[i], ns, no_args(), Seq::empty())
}

/// 省略できる式のキー。省略か `null` なら `None`。
pub open spec fn opt_ex_rel(j: Json, k: Seq<char>, e: Option<TExpr>, ns: IrNames) -> bool {
    if absent(j, k) {
        e is None
    } else {
        e matches Some(x) && ex_rel(at(j, k), x, ns, no_args(), Seq::empty())
    }
}

/// IRのJSON `j` は、名前の表 `ns` のもとで、名前を解決したモデル `sm` を表す。
pub open spec fn ir_rel(j: Json, ns: IrNames, sm: SModel) -> bool {
    &&& names_ok(ns)
    &&& opt_arr(j, "enums"@) matches Some(es) && es.len() == ns.enums@.len() && es.len() == sm.enums@.len() && forall|i: int|
        0 <= i < es.len() ==> #[trigger] enum_rel(es[i], ns, i, sm.enums@[i])
    &&& opt_arr(j, "constants"@) matches Some(cs) && cs.len() == ns.consts@.len() && cs.len() == sm.consts@.len() && forall|i: int|
        0 <= i < cs.len() ==> #[trigger] const_rel(cs[i], ns, i, sm)
    &&& get(j, "states"@) is Some
    &&& arr(at(j, "states"@)) matches Some(ss) && ss.len() == ns.states@.len() && ss.len() == sm.states@.len() && ss.len()
        == sm.inits@.len() && forall|i: int| 0 <= i < ss.len() ==> #[trigger] state_rel(ss[i], ns, i, sm)
    &&& opt_ex_rel(j, "initial_constraint"@, sm.constraint, ns)
    &&& opt_arr(j, "actions"@) matches Some(acts) && acts.len() == ns.actions@.len() && acts.len() == sm.actions@.len()
        && acts.len() == ns.params@.len() && acts.len() == ns.choices@.len() && forall|a: int|
        0 <= a < acts.len() ==> #[trigger] action_rel(acts[a], ns, a, sm.actions@[a], sm.enums@)
    &&& opt_arr(j, "invariants"@) matches Some(is) && is.len() == ns.invariants@.len() && is.len() == sm.invariants@.len()
        && forall|i: int| 0 <= i < is.len() ==> #[trigger] invariant_rel(is[i], ns, i, sm)
    &&& opt_arr(j, "contracts"@) matches Some(ks) && ks.len() == ns.contracts@.len() && ks.len() == sm.contracts@.len()
        && forall|k: int| 0 <= k < ks.len() ==> #[trigger] contract_rel(ks[k], ns, k, sm)
    &&& opt_ex_rel(j, "terminal"@, sm.terminal, ns)
}

} // verus!
