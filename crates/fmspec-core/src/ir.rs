//! IRのJSONと、名前を解決したモデルの対応（仕様）。
//!
//! これは JSON の読み取りの正しさで、IR検証（[`crate::checked::validate`]、中核のモデルの整形式性）とは別である。
//!
//! `fmspec-ir` は、IRのJSONを読んで名前を解決したモデル（[`SModel`]）と名前の表（[`IrNames`]）を組み立てる。
//! ここでは、JSONの木と組み立てた結果の対応 [`ir_rel`] を、IRの各構文が `SModel` のどの構造になるかを
//! 直接書いて定める（`docs/ir.md` の「モデル」「型と値」「式」）。これがIRの意味の定義である。
//! 対応を確かめる検査は [`crate::ir_check`] にある。
//!
//! 読み方：
//!
//! - 型は [`ty_rel`] の、型の種類ごとの1行の規則（`docs/ir.md` の「型と値」の表）。
//! - 式のうち、オペランドの配列を持つ演算子は、キーとオペランドの並びの表 [`op_form`]（「基本の式」「複合型の値を作る式」
//!   「複合型の値を調べる式」の表）。それ以外の構文（リテラル、参照、`let`、量化、Record、`nth`、`field`、`none`、
//!   Set・Map・List のリテラル）は [`form_rel`] の、構文ごとの規則。[`ex_rel`] はこの2つを選ぶだけである。
//! - モデルは [`ir_rel`] と、定義の種類ごとの `*_rel`（「モデル」の節）。
//! - 「JSONの読み方」「名前」の節の関数と、`*_dec`、`lemma_*` は、JSONの値の取り出しと停止性のための部品で、
//!   意味の規則は含まない。
//!
//! 受理の条件（未知のキー、空でない配列など）は定めない。拒否すべきIRを拒否するのは `fmspec-ir` の仕事で、
//! ここでは受理したIRの意味を定める。式の型から決まる注釈（`contains` の Set と List の区別、要素の型など）は
//! JSONに書かれないので制約しない。注釈は中核の型付け（[`crate::infer::ir_type_of`]）が検査する。

#[cfg(verus_keep_ghost)]
use crate::encoding::{stys, width_sum, SType};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Value};
#[cfg(verus_keep_ghost)]
use crate::smodel::{SAction, SModel};
#[cfg(verus_keep_ghost)]
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
//
// `docs/ir.md` の「型と値」の表。型のJSONは、型の種類を表すキーを1つだけ持つオブジェクトである。

/// 型のJSON `j` は型 `t` を表す。
pub open spec fn ty_rel(j: Json, ns: IrNames, t: SType) -> bool
    decreases j, 1nat,
    via ty_rel_dec
{
    match one(j) {
        None => false,
        Some((k, b)) => match t {
            // {"bool": {}}
            SType::Bool => k == "bool"@ && empty_obj(b),
            // {"int": {"min": 下限, "max": 上限}}
            SType::Int(lo, hi) => k == "int"@ && get(b, "min"@) == Some(Json::Int(lo)) && get(b, "max"@) == Some(
                Json::Int(hi),
            ),
            // {"enum": 列挙型の名前}
            SType::Enum(id) => k == "enum"@ && (str_of(b) matches Some(n) && index_of(strs(ns.enums@), n) == Some(id as int)),
            // {"tuple": [型, ...]}
            SType::Tuple(ts) => k == "tuple"@ && tys_rel(b, ts@, ns),
            // {"record": [{"name", "type"}, ...]}
            SType::Record(ids, ts) => k == "record"@ && (arr(b) matches Some(xs) && xs.len() == ts@.len() && xs.len()
                == ids@.len() && forall|i: int| 0 <= i < xs.len() ==> field_ty_rel(#[trigger] xs[i], ns, ids@[i], ts@[i])),
            // {"option": 型}
            SType::Option(x) => k == "option"@ && ty_rel(b, ns, *x),
            // {"set": 要素の型}
            SType::Set(x) => k == "set"@ && ty_rel(b, ns, *x),
            // {"map": {"key": 型, "value": 型}}
            SType::Map(x, y) => k == "map"@ && ty_at(b, "key"@, ns, *x) && ty_at(b, "value"@, ns, *y),
            // {"list": {"of": 型, "max": 上限}}
            SType::List(x, max) => k == "list"@ && ty_at(b, "of"@, ns, *x) && get(b, "max"@) is Some && nat_of(
                at(b, "max"@),
            ) == Some(max as nat),
        },
    }
}

/// オブジェクト `b` のキー `k` の値が、型 `t` を表す。
pub open spec fn ty_at(b: Json, k: Seq<char>, ns: IrNames, t: SType) -> bool
    decreases b, 0nat,
    via ty_at_dec
{
    get(b, k) is Some && ty_rel(at(b, k), ns, t)
}

/// 配列 `b` の各要素が、型の列 `ts` を表す。
pub open spec fn tys_rel(b: Json, ts: Seq<SType>, ns: IrNames) -> bool
    decreases b, 0nat,
    via tys_rel_dec
{
    arr(b) matches Some(xs) && xs.len() == ts.len() && forall|i: int| 0 <= i < xs.len() ==> ty_rel(#[trigger] xs[i], ns, ts[i])
}

/// Recordの型のフィールド `{"name", "type"}` は、名前の表の `id` 番目のフィールドと型 `t` を表す。
pub open spec fn field_ty_rel(j: Json, ns: IrNames, id: usize, t: SType) -> bool
    decreases j, 1nat,
{
    &&& id < ns.fields@.len()
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.fields@[id as int]@)
    &&& ty_at(j, "type"@, ns, t)
}

#[via_fn]
proof fn ty_rel_dec(j: Json, ns: IrNames, t: SType) {
    lemma_one_dec(j);
    if let Some((_, b)) = one(j) {
        lemma_arr_dec(b);
    }
}

#[via_fn]
proof fn ty_at_dec(b: Json, k: Seq<char>, ns: IrNames, t: SType) {
    lemma_get_dec(b);
}

#[via_fn]
proof fn tys_rel_dec(b: Json, ts: Seq<SType>, ns: IrNames) {
    lemma_arr_dec(b);
}

// ---- 式 ----
//
// `docs/ir.md` の「式」の節。式のJSONは、演算子を表すキーを1つだけ持つオブジェクトである。
// オペランドの配列を持つ演算子は、キーとオペランドの並びの表 `op_form` で定める。
// それ以外（リテラル、参照、`let`、量化、Record、`nth`、`field`、`none`、Set・Map・List のリテラル）は
// `form_rel` で1つずつ定める。

/// 式を読む文脈。操作の公開引数と内部選択の数（操作の外では0）。
pub struct ECtx {
    pub np: nat,
    pub nc: nat,
}

/// オペランドの配列を持つ演算子の、キーとオペランドの列。`{キー: [オペランド, ...]}` と書く。
/// 式の型から決まる注釈（要素の型など）は、JSONに書かれないので現れない。
pub open spec fn op_form(e: TExpr) -> Option<(Seq<char>, Seq<TExpr>)> {
    match e {
        // 基本の式
        TExpr::Bin(BinOp::Add, x, y) => Some(("add"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Sub, x, y) => Some(("sub"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Mul, x, y) => Some(("mul"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Div, x, y) => Some(("div"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Mod, x, y) => Some(("mod"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Lt, x, y) => Some(("lt"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Le, x, y) => Some(("le"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Gt, x, y) => Some(("gt"@, seq![*x, *y])),
        TExpr::Bin(BinOp::Ge, x, y) => Some(("ge"@, seq![*x, *y])),
        TExpr::Eq(true, x, y) => Some(("eq"@, seq![*x, *y])),
        TExpr::Eq(false, x, y) => Some(("ne"@, seq![*x, *y])),
        TExpr::Not(x) => Some(("not"@, seq![*x])),
        TExpr::Fold(true, es) => Some(("all"@, es@)),
        TExpr::Fold(false, es) => Some(("any"@, es@)),
        TExpr::Implies(x, y) => Some(("implies"@, seq![*x, *y])),
        TExpr::Ite(p, x, y) => Some(("ite"@, seq![*p, *x, *y])),
        // 複合型の値を作る式
        TExpr::Tuple(es) => Some(("tuple"@, es@)),
        TExpr::Some(x) => Some(("some"@, seq![*x])),
        // 複合型の値を調べる式
        TExpr::IsSome(x) => Some(("is_some"@, seq![*x])),
        TExpr::IsNone(x) => Some(("is_none"@, seq![*x])),
        TExpr::Unwrap(x) => Some(("unwrap"@, seq![*x])),
        TExpr::SetContains(_, x, y) => Some(("contains"@, seq![*x, *y])),
        TExpr::ListContains(x, y) => Some(("contains"@, seq![*x, *y])),
        TExpr::Insert(_, x, y) => Some(("insert"@, seq![*x, *y])),
        TExpr::Remove(_, x, y) => Some(("remove"@, seq![*x, *y])),
        TExpr::SetBin(SetOp::Union, x, y) => Some(("union"@, seq![*x, *y])),
        TExpr::SetBin(SetOp::Intersection, x, y) => Some(("intersection"@, seq![*x, *y])),
        TExpr::SetBin(SetOp::Difference, x, y) => Some(("difference"@, seq![*x, *y])),
        TExpr::SetBin(SetOp::Subset, x, y) => Some(("subset"@, seq![*x, *y])),
        TExpr::Size(x) => Some(("size"@, seq![*x])),
        TExpr::IsEmpty(x) => Some(("is_empty"@, seq![*x])),
        TExpr::HasKey(_, x, y) => Some(("has_key"@, seq![*x, *y])),
        TExpr::Get(_, x, y) => Some(("get"@, seq![*x, *y])),
        TExpr::Put(_, _, x, y, z) => Some(("put"@, seq![*x, *y, *z])),
        TExpr::Delete(_, x, y) => Some(("delete"@, seq![*x, *y])),
        TExpr::Keys(x) => Some(("keys"@, seq![*x])),
        TExpr::At(x, y) => Some(("at"@, seq![*x, *y])),
        TExpr::First(x) => Some(("first"@, seq![*x])),
        TExpr::Last(x) => Some(("last"@, seq![*x])),
        TExpr::Push(_, _, x, y) => Some(("push"@, seq![*x, *y])),
        TExpr::Pop(x) => Some(("pop"@, seq![*x])),
        TExpr::Shift(x) => Some(("shift"@, seq![*x])),
        _ => None,
    }
}

/// 式のJSON `j` は、局所変数の名前の列 `sc`（外側から順に並べる）のもとで、式 `e` を表す。
pub open spec fn ex_rel(j: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases j, 1nat,
    via ex_rel_dec
{
    match one(j) {
        None => false,
        Some((k, b)) => match op_form(e) {
            Some((key, es)) => k == key && exs_rel(b, es, ns, c, sc),
            None => form_rel(k, b, e, ns, c, sc),
        },
    }
}

/// オペランドの配列でない式。キー `k` と値 `b` が式 `e` を表す。
pub open spec fn form_rel(k: Seq<char>, b: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 2nat,
    via form_rel_dec
{
    match e {
        // {"int": 整数}、{"bool": 真偽値}
        TExpr::Lit(Value::Int(n)) => k == "int"@ && b == Json::Int(n),
        TExpr::Lit(Value::Bool(x)) => k == "bool"@ && b == Json::Bool(x),
        // {"enum": {"type": 列挙型の名前, "variant": ラベル}}
        TExpr::Lit(Value::Enum(id, v)) => k == "enum"@ && id < ns.variants@.len() && name_at(b, "type"@, strs(ns.enums@))
            == Some(id as int) && name_at(b, "variant"@, strs(ns.variants@[id as int]@)) == Some(v as int),
        // {"var": i}、{"next": i}
        TExpr::Var(x) => k == "var"@ && nat_of(b) == Some(x as nat),
        TExpr::Next(x) => k == "next"@ && nat_of(b) == Some(x as nat),
        // {"param": i} は i 番目の公開引数、{"choice": i} は i 番目の内部選択（公開引数に続けて並べる）
        TExpr::Arg(x) => (k == "param"@ && x < c.np && nat_of(b) == Some(x as nat)) || (k == "choice"@ && c.np <= x
            < c.np + c.nc && nat_of(b) == Some((x - c.np) as nat)),
        // {"output": {}}
        TExpr::Out => k == "output"@ && empty_obj(b),
        // {"local": 名前} は、内側から探して最初に見つかった束縛
        TExpr::Local(i) => k == "local"@ && (str_of(b) matches Some(n) && last_of(sc, n) == Some(i as int)),
        // {"const": 名前}
        TExpr::Const(i) => k == "const"@ && (str_of(b) matches Some(n) && index_of(strs(ns.consts@), n) == Some(i as int)),
        // {"let": {"name", "value", "body"}}。body では name を束縛する
        TExpr::Let(x, y) => k == "let"@ && (str_of(at(b, "name"@)) matches Some(n) && get(b, "name"@) is Some && ex_at(
            b,
            "value"@,
            *x,
            ns,
            c,
            sc,
        ) && ex_at(b, "body"@, *y, ns, c, sc.push(n))),
        // {"forall": {"name", "in" または "type", "body"}}、{"exists": ...}。body では name を束縛する
        TExpr::Quant(all, over, y) => k == (if all {
            "forall"@
        } else {
            "exists"@
        }) && (str_of(at(b, "name"@)) matches Some(n) && get(b, "name"@) is Some && over_rel(b, over, ns, c, sc) && ex_at(
            b,
            "body"@,
            *y,
            ns,
            c,
            sc.push(n),
        )),
        // {"record": [{"name", "expr"}, ...]}
        TExpr::Record(ids, es) => k == "record"@ && (arr(b) matches Some(xs) && xs.len() == ids@.len() && xs.len()
            == es@.len() && forall|i: int| 0 <= i < xs.len() ==> field_rel(#[trigger] xs[i], ids@[i], es@[i], ns, c, sc)),
        // {"nth": {"of", "index"}}
        TExpr::Nth(x, i) => k == "nth"@ && get(b, "index"@) is Some && nat_of(at(b, "index"@)) == Some(i as nat) && ex_at(
            b,
            "of"@,
            *x,
            ns,
            c,
            sc,
        ),
        // {"field": {"of", "name"}}
        TExpr::Field(x, id, _) => k == "field"@ && id < ns.fields@.len() && get(b, "name"@) is Some && str_of(
            at(b, "name"@),
        ) == Some(ns.fields@[id as int]@) && ex_at(b, "of"@, *x, ns, c, sc),
        // {"none": 型}
        TExpr::None(t) => k == "none"@ && ty_rel(b, ns, t),
        // {"set": {"of", "items"}}
        TExpr::SetLit(t, es) => k == "set"@ && ty_at(b, "of"@, ns, t) && get(b, "items"@) is Some && exs_rel(
            at(b, "items"@),
            es@,
            ns,
            c,
            sc,
        ),
        // {"map": {"key", "value", "items": [[キー, 値], ...]}}
        TExpr::MapLit(kt, vt, items) => k == "map"@ && ty_at(b, "key"@, ns, kt) && ty_at(b, "value"@, ns, vt) && get(
            b,
            "items"@,
        ) is Some && (arr(at(b, "items"@)) matches Some(xs) && xs.len() == items@.len() && forall|i: int|
            0 <= i < xs.len() ==> exs_rel(#[trigger] xs[i], seq![items@[i].key, items@[i].value], ns, c, sc)),
        // {"list": {"of", "max", "items"}}
        TExpr::ListLit(t, max, es) => k == "list"@ && ty_at(b, "of"@, ns, t) && get(b, "max"@) is Some && nat_of(
            at(b, "max"@),
        ) == Some(max as nat) && get(b, "items"@) is Some && exs_rel(at(b, "items"@), es@, ns, c, sc),
        _ => false,
    }
}

/// オブジェクト `b` のキー `k` の値（名前）の、名前の列 `names` での位置。
pub open spec fn name_at(b: Json, k: Seq<char>, names: Seq<Seq<char>>) -> Option<int> {
    match get(b, k) {
        Some(Json::Str(s)) => index_of(names, s@),
        _ => None,
    }
}

/// 配列 `b` の各要素が、式の列 `es` を表す。
pub open spec fn exs_rel(b: Json, es: Seq<TExpr>, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 0nat,
    via exs_rel_dec
{
    arr(b) matches Some(xs) && xs.len() == es.len() && forall|i: int| 0 <= i < xs.len() ==> ex_rel(#[trigger] xs[i], es[i], ns, c, sc)
}

/// オブジェクト `b` のキー `k` の値が、式 `e` を表す。
pub open spec fn ex_at(b: Json, k: Seq<char>, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 0nat,
    via ex_at_dec
{
    get(b, k) is Some && ex_rel(at(b, k), e, ns, c, sc)
}

/// Recordの式のフィールド `{"name", "expr"}`。
pub open spec fn field_rel(j: Json, id: usize, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases j, 1nat,
{
    &&& id < ns.fields@.len()
    &&& get(j, "name"@) is Some
    &&& str_of(at(j, "name"@)) == Some(ns.fields@[id as int]@)
    &&& ex_at(j, "expr"@, e, ns, c, sc)
}

/// 量化のたどる値。`in` の式（Set の要素、Map のキー、List の要素）か、`type` の型の値。
pub open spec fn over_rel(b: Json, over: Over, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) -> bool
    decreases b, 1nat,
{
    match over {
        Over::Set(_, x) => get(b, "type"@) is None && ex_at(b, "in"@, *x, ns, c, sc),
        Over::Map(_, x) => get(b, "type"@) is None && ex_at(b, "in"@, *x, ns, c, sc),
        Over::List(x) => get(b, "type"@) is None && ex_at(b, "in"@, *x, ns, c, sc),
        Over::Type(t) => get(b, "in"@) is None && ty_at(b, "type"@, ns, t),
    }
}

#[via_fn]
proof fn ex_rel_dec(j: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_one_dec(j);
}

#[via_fn]
proof fn form_rel_dec(k: Seq<char>, b: Json, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_get_dec(b);
    lemma_arr_dec(b);
    if let Some(x) = get(b, "items"@) {
        lemma_arr_dec(x);
    }
}

#[via_fn]
proof fn exs_rel_dec(b: Json, es: Seq<TExpr>, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_arr_dec(b);
}

#[via_fn]
proof fn ex_at_dec(b: Json, k: Seq<char>, e: TExpr, ns: IrNames, c: ECtx, sc: Seq<Seq<char>>) {
    lemma_get_dec(b);
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
//
// `docs/ir.md` の「モデル」の節。定義の式は局所変数のない文脈で読む。

/// キー `k` の値が文字列 `n` である。
pub open spec fn name_is(j: Json, k: Seq<char>, n: Seq<char>) -> bool {
    get(j, k) is Some && str_of(at(j, k)) == Some(n)
}

/// キー `k` の値が、局所変数のない文脈 `c` で式 `e` を表す。
pub open spec fn top_at(j: Json, k: Seq<char>, e: TExpr, ns: IrNames, c: ECtx) -> bool {
    ex_at(j, k, e, ns, c, Seq::empty())
}

/// 状態も引数も参照しない文脈（定数、初期値、初期条件、不変条件、終端条件）。
pub open spec fn no_args() -> ECtx {
    ECtx { np: 0, nc: 0 }
}

/// 操作 `a` の文脈（guard、更新、出力、遷移契約）。
pub open spec fn act_ctx(ns: IrNames, a: int) -> ECtx {
    ECtx { np: ns.params@[a]@.len(), nc: ns.choices@[a]@.len() }
}

/// 列挙型 `{"name", "variants"}`。`n` はラベルの数。
pub open spec fn enum_rel(j: Json, ns: IrNames, i: int, n: i64) -> bool {
    &&& name_is(j, "name"@, ns.enums@[i]@)
    &&& get(j, "variants"@) is Some
    &&& arr(at(j, "variants"@)) matches Some(vs) && vs.len() == ns.variants@[i]@.len() && n == vs.len() && forall|q: int|
        0 <= q < vs.len() ==> #[trigger] str_of(vs[q]) == Some(ns.variants@[i]@[q]@)
}

/// 定数 `{"name", "type", "value"}`。
pub open spec fn const_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    &&& name_is(j, "name"@, ns.consts@[i]@)
    &&& ty_at(j, "type"@, ns, sm.consts@[i].ty)
    &&& top_at(j, "value"@, sm.consts@[i].expr, ns, no_args())
}

/// 状態変数 `{"id", "name", "type", "initial"}` または `{"id", "name", "type", "initial_in"}`。
/// `initial` は候補が1つ、`initial_in` は配列の各要素が候補。`id` は書くなら添字と一致する。
pub open spec fn state_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    let inits = sm.inits@[i]@;
    &&& get(j, "id"@) matches Some(x) ==> nat_of(x) == Some(i as nat)
    &&& name_is(j, "name"@, ns.states@[i]@)
    &&& ty_at(j, "type"@, ns, sm.states@[i])
    &&& if get(j, "initial"@) is Some {
        get(j, "initial_in"@) is None && inits.len() == 1 && top_at(j, "initial"@, inits[0], ns, no_args())
    } else {
        get(j, "initial_in"@) is Some && exs_rel(at(j, "initial_in"@), inits, ns, no_args(), Seq::empty())
    }
}

/// 引数の宣言 `{"name", "type", "in"}` の列。
pub open spec fn binds_rel(xs: Seq<Json>, names: Seq<Vec<char>>, tys: Seq<SType>, ns: IrNames) -> bool {
    &&& xs.len() == names.len()
    &&& xs.len() == tys.len()
    &&& forall|i: int| 0 <= i < xs.len() ==> name_is(#[trigger] xs[i], "name"@, names[i]@) && ty_at(xs[i], "type"@, ns, tys[i])
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

/// 引数 `d.0` の動的ドメインの検査 `contains(ドメイン, 引数)`。ドメインは Set か List。
pub open spec fn member_rel(d: (nat, Json), e: TExpr, ns: IrNames, c: ECtx) -> bool {
    match e {
        TExpr::SetContains(_, x, y) => ex_rel(d.1, *x, ns, c, Seq::empty()) && y == Box::new(TExpr::Arg(d.0 as usize)),
        TExpr::ListContains(x, y) => ex_rel(d.1, *x, ns, c, Seq::empty()) && y == Box::new(TExpr::Arg(d.0 as usize)),
        _ => false,
    }
}

/// 利用者の書いた guard。省略すれば真。
pub open spec fn user_guard_rel(j: Json, u: TExpr, ns: IrNames, c: ECtx) -> bool {
    if absent(j, "guard"@) {
        u == TExpr::Lit(Value::Bool(true))
    } else {
        ex_rel(at(j, "guard"@), u, ns, c, Seq::empty())
    }
}

/// guard。動的ドメインがあれば、その検査を引数の順に並べ、最後に利用者の guard を置いた `all` にする。
pub open spec fn guard_rel(j: Json, ds: Seq<(nat, Json)>, g: TExpr, ns: IrNames, c: ECtx) -> bool {
    if ds.len() == 0 {
        user_guard_rel(j, g, ns, c)
    } else {
        match g {
            TExpr::Fold(all, es) => all && es@.len() == ds.len() + 1 && user_guard_rel(j, es@.last(), ns, c) && forall|q: int|
                0 <= q < ds.len() ==> #[trigger] member_rel(ds[q], es@[q], ns, c),
            _ => false,
        }
    }
}

/// 更新 `{"target", "expr"}`。`target` は状態変数の添字。
pub open spec fn update_rel(j: Json, u: crate::smodel::SUpdate, ns: IrNames, c: ECtx) -> bool {
    &&& get(j, "target"@) is Some
    &&& nat_of(at(j, "target"@)) == Some(u.var as nat)
    &&& top_at(j, "expr"@, u.expr, ns, c)
}

/// 操作 `{"name", "params", "choices", "guard", "updates", "output"}`。
/// 引数の型の列は公開引数に続けて内部選択で、`n_params` は公開引数のスロットの数。
pub open spec fn action_rel(j: Json, ns: IrNames, a: int, sa: SAction, enums: Seq<i64>) -> bool {
    let c = act_ctx(ns, a);
    let ps = ns.params@[a]@;
    let cs = ns.choices@[a]@;
    &&& name_is(j, "name"@, ns.actions@[a]@)
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
        sa.output matches Some(o) && ty_at(at(j, "output"@), "type"@, ns, o.ty) && top_at(at(j, "output"@), "expr"@, o.expr, ns, c)
    }
}

/// 遷移契約 `{"name", "action", "expr"}`。式は、名前の操作の文脈で読む。
pub open spec fn contract_rel(j: Json, ns: IrNames, k: int, sm: SModel) -> bool {
    let a = sm.contracts@[k].action as int;
    &&& name_is(j, "name"@, ns.contracts@[k]@)
    &&& get(j, "action"@) is Some
    &&& str_of(at(j, "action"@)) matches Some(an) && index_of(strs(ns.actions@), an) == Some(a)
    &&& top_at(j, "expr"@, sm.contracts@[k].expr, ns, act_ctx(ns, a))
}

/// 不変条件 `{"name", "expr"}`。
pub open spec fn invariant_rel(j: Json, ns: IrNames, i: int, sm: SModel) -> bool {
    &&& name_is(j, "name"@, ns.invariants@[i]@)
    &&& top_at(j, "expr"@, sm.invariants@[i], ns, no_args())
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
/// 各定義の列は、JSONの配列の順に、名前の表とモデルの列に対応する。
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
