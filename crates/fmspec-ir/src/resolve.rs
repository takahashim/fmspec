//! IRの式の名前解決。JSONの式を、中核の型付き構文木（[`TExpr`]）にする。
//!
//! 名前を番号に解決し、型を検査する。
//! 構文木は、意味論が必要とする要素の型を注釈として持つ。
//! 構文木は、中核の検証済みの下ろし（[`fmspec_core::lowering`]）が型を検査し直してから中核の式にする。
//! したがって、この名前解決の型検査は信頼の基盤に入らない。信頼の基盤に入るのは、名前を正しい番号に
//! 解決することだけである。
//!
//! Recordのフィールドの名前は、モデル全体で共有する [`Fields`] で番号にする。

use crate::json::{array, index, int, object, operands, required, schema, single, string};
use crate::model::{EnumNames, LoadError};
use crate::type_syntax::{parse_type, type_name};
use crate::types::{SType, XType, MAX_KEYS};
use fmspec_core::encoding::SType as CS;
use fmspec_core::model::{BinOp, Value as CV};
use fmspec_core::source::{Item, Over, SetOp, TExpr};
use serde_json::Value;
use std::cell::RefCell;
use std::collections::HashSet;

/// Recordのフィールドの名前の番号。
#[derive(Default)]
pub(crate) struct Fields(RefCell<Vec<String>>);

impl Fields {
    pub(crate) fn id(&self, name: &str) -> usize {
        let mut names = self.0.borrow_mut();
        match names.iter().position(|n| n == name) {
            Some(i) => i,
            None => {
                names.push(name.to_string());
                names.len() - 1
            }
        }
    }

    /// 格納の型を、中核の型にする。
    pub(crate) fn stype(&self, t: &SType) -> CS {
        match t {
            SType::Bool => CS::Bool,
            SType::Int(lo, hi) => CS::Int(*lo, *hi),
            SType::Enum(id) => CS::Enum(*id),
            SType::Tuple(ts) => CS::Tuple(ts.iter().map(|t| self.stype(t)).collect()),
            SType::Record(fs) => CS::Record(
                fs.iter().map(|(n, _)| self.id(n)).collect(),
                fs.iter().map(|(_, t)| self.stype(t)).collect(),
            ),
            SType::Option(t) => CS::Option(Box::new(self.stype(t))),
            SType::Set(t) => CS::Set(Box::new(self.stype(t))),
            SType::Map(k, v) => CS::Map(Box::new(self.stype(k)), Box::new(self.stype(v))),
            SType::List(t, n) => CS::List(Box::new(self.stype(t)), *n),
        }
    }
}

/// 名前解決の誤り。`Type` は型の誤りと未定義の参照で、どの定義で起きたかを呼び出し側が付ける。
#[derive(Debug)]
pub(crate) enum Error {
    Schema(LoadError),
    Type(String),
}

impl From<LoadError> for Error {
    fn from(e: LoadError) -> Self {
        Error::Schema(e)
    }
}

pub(crate) type Res<T> = Result<T, Error>;

pub(crate) fn type_error<T>(path: &str, message: impl Into<String>) -> Res<T> {
    Err(Error::Type(format!("{path}: {}", message.into())))
}

/// 状態変数や引数の、スロットの列での位置。
#[derive(Clone, Debug)]
pub struct Layout {
    pub ty: SType,
    pub offset: usize,
}

/// 名前付きの定数。値は中核の下ろしが式を評価して求める。
#[derive(Clone, Debug)]
pub(crate) struct Constant {
    pub name: String,
    pub ty: SType,
}

/// 式を名前解決する文脈。
pub(crate) struct Ctx<'a> {
    pub enums: &'a [EnumNames],
    /// 状態変数。`None` なら状態を参照できない（初期値と定数）。
    pub states: Option<&'a [Layout]>,
    /// 公開引数に続けて内部選択。
    pub args: &'a [Layout],
    pub n_params: usize,
    /// 遷移後の状態を参照できる（遷移契約）。
    pub next: bool,
    pub output: Option<&'a SType>,
    pub constants: &'a [Constant],
    /// Recordのフィールドの名前の番号。モデル全体で共有する。
    pub fields: &'a Fields,
}

/// 名前で参照する局所変数。番号は、外側から数えた位置である。
struct Local {
    name: String,
    ty: XType,
}

fn b(e: TExpr) -> Box<TExpr> {
    Box::new(e)
}

impl<'a> Ctx<'a> {
    fn expect(&self, path: &str, t: &XType, want: &XType) -> Res<()> {
        if t != want {
            return type_error(
                path,
                format!(
                    "{} が必要ですが、{} です",
                    type_name(self.enums, want),
                    type_name(self.enums, t)
                ),
            );
        }
        Ok(())
    }

    fn expect_fits(&self, path: &str, t: &XType, st: &SType) -> Res<()> {
        if !t.fits(st) {
            return type_error(
                path,
                format!(
                    "{} が必要ですが、{} です",
                    type_name(self.enums, &st.xtype()),
                    type_name(self.enums, t)
                ),
            );
        }
        Ok(())
    }

    fn set_elem(&self, t: &XType, path: &str) -> Res<SType> {
        match t {
            XType::Set(e) => Ok((**e).clone()),
            _ => type_error(path, format!("set が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    fn map_types(&self, t: &XType, path: &str) -> Res<(SType, SType)> {
        match t {
            XType::Map(k, v) => Ok(((**k).clone(), (**v).clone())),
            _ => type_error(path, format!("map が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    fn list_type(&self, t: &XType, path: &str) -> Res<(SType, usize)> {
        match t {
            XType::List(e, n) => Ok(((**e).clone(), *n)),
            _ => type_error(path, format!("list が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    /// 述語を名前解決する。
    pub(crate) fn prop(&self, v: &Value, path: &str) -> Res<TExpr> {
        self.closed_bool(v, path, &mut Vec::new())
    }

    /// 型 `st` の場所に置く値を名前解決する。
    pub(crate) fn stored(&self, v: &Value, path: &str, st: &SType) -> Res<TExpr> {
        self.fitting(v, path, &mut Vec::new(), st)
    }

    fn scalar(&self, v: &Value, path: &str, sc: &mut Vec<Local>, want: &XType) -> Res<TExpr> {
        let (t, e) = self.tree(v, path, sc)?;
        self.expect(path, &t, want)?;
        Ok(e)
    }

    /// 独立に評価する述語の位置（`all` と `any` の2番目以降、`implies` の後件、量化の本体）。
    /// スカラー型でなければ、Boolでない場合と別のメッセージにする。
    fn closed_bool(&self, v: &Value, path: &str, sc: &mut Vec<Local>) -> Res<TExpr> {
        let (t, e) = self.tree(v, path, sc)?;
        if !t.is_scalar() {
            return type_error(
                path,
                format!("スカラー型の式が必要ですが、{} です", type_name(self.enums, &t)),
            );
        }
        self.expect(path, &t, &XType::Bool)?;
        Ok(e)
    }

    fn fitting(&self, v: &Value, path: &str, sc: &mut Vec<Local>, st: &SType) -> Res<TExpr> {
        let (t, e) = self.tree(v, path, sc)?;
        self.expect_fits(path, &t, st)?;
        Ok(e)
    }

    fn tree(&self, v: &Value, path: &str, sc: &mut Vec<Local>) -> Res<(XType, TExpr)> {
        let Some(map) = v.as_object() else {
            return schema(path, "式はオブジェクトです");
        };
        let (key, body) = single(map, path, "式は演算子を表すキーを1つだけ持つオブジェクトです")?;
        let path = format!("{path}.{key}");
        let path = path.as_str();
        let enums = self.enums;
        let f = self.fields;
        let ops = |n: usize| operands(body, path, n);
        let at = |i: usize| format!("{path}[{i}]");
        match key.as_str() {
            "int" => Ok((XType::Int, TExpr::Lit(CV::Int(int(body, path)?)))),
            "bool" => match body.as_bool() {
                Some(x) => Ok((XType::Bool, TExpr::Lit(CV::Bool(x)))),
                None => schema(path, "真偽値が必要です"),
            },
            "enum" => {
                let m = object(body, path, &["type", "variant"])?;
                let ty = string(required(m, path, "type")?, &format!("{path}.type"))?;
                let variant = string(required(m, path, "variant")?, &format!("{path}.variant"))?;
                let Some(id) = enums.iter().position(|e| e.name == ty) else {
                    return schema(path, format!("未定義の列挙型 {ty:?}"));
                };
                let Some(k) = enums[id].variants.iter().position(|x| *x == variant) else {
                    return schema(path, format!("列挙型 {ty:?} に未定義のラベル {variant:?}"));
                };
                Ok((XType::Enum(id), TExpr::Lit(CV::Enum(id, k as i64))))
            }
            "var" | "next" => {
                let Some(states) = self.states else {
                    return type_error(path, "ここでは状態変数を参照できません");
                };
                if key == "next" && !self.next {
                    return type_error(path, "next は遷移契約でだけ使えます");
                }
                let i = index(body, path)?;
                let Some(l) = states.get(i) else {
                    return type_error(path, format!("未定義の状態変数 {i}"));
                };
                Ok((l.ty.xtype(), if key == "var" { TExpr::Var(i) } else { TExpr::Next(i) }))
            }
            "param" | "choice" => {
                let i = index(body, path)?;
                let (i, n) = if key == "param" {
                    (i, self.n_params)
                } else {
                    (self.n_params.saturating_add(i), self.args.len())
                };
                match self.args.get(i) {
                    Some(l) if i < n => Ok((l.ty.xtype(), TExpr::Arg(i))),
                    _ => type_error(
                        path,
                        format!("未定義の{} {}", if key == "param" { "引数" } else { "内部選択" }, i),
                    ),
                }
            }
            "output" => {
                object(body, path, &[])?;
                match self.output {
                    Some(st) if self.next => Ok((st.xtype(), TExpr::Out)),
                    _ => type_error(path, "output は出力を宣言した操作の遷移契約でだけ使えます"),
                }
            }
            "local" => {
                let name = string(body, path)?;
                match sc.iter().rposition(|x| x.name == name) {
                    Some(i) => Ok((sc[i].ty.clone(), TExpr::Local(i))),
                    None => schema(path, format!("未定義の局所変数 {name:?}")),
                }
            }
            "const" => {
                let name = string(body, path)?;
                match self.constants.iter().position(|c| c.name == name) {
                    Some(i) => Ok((self.constants[i].ty.xtype(), TExpr::Const(i))),
                    None => schema(path, format!("未定義の定数 {name:?}")),
                }
            }
            "add" | "sub" | "mul" | "div" | "mod" | "lt" | "le" | "gt" | "ge" => {
                let items = ops(2)?;
                let x = self.scalar(&items[0], &at(0), sc, &XType::Int)?;
                let y = self.scalar(&items[1], &at(1), sc, &XType::Int)?;
                let (op, t) = match key.as_str() {
                    "add" => (BinOp::Add, XType::Int),
                    "sub" => (BinOp::Sub, XType::Int),
                    "mul" => (BinOp::Mul, XType::Int),
                    "div" => (BinOp::Div, XType::Int),
                    "mod" => (BinOp::Mod, XType::Int),
                    "lt" => (BinOp::Lt, XType::Bool),
                    "le" => (BinOp::Le, XType::Bool),
                    "gt" => (BinOp::Gt, XType::Bool),
                    _ => (BinOp::Ge, XType::Bool),
                };
                Ok((t, TExpr::Bin(op, b(x), b(y))))
            }
            "eq" | "ne" => {
                let items = ops(2)?;
                let (tx, x) = self.tree(&items[0], &at(0), sc)?;
                let (ty, y) = self.tree(&items[1], &at(1), sc)?;
                self.expect(&at(1), &ty, &tx)?;
                Ok((XType::Bool, TExpr::Eq(key == "eq", b(x), b(y))))
            }
            "not" => {
                let items = ops(1)?;
                let x = self.scalar(&items[0], &at(0), sc, &XType::Bool)?;
                Ok((XType::Bool, TExpr::Not(b(x))))
            }
            "all" | "any" => {
                let items = array(body, path)?;
                let mut terms = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    terms.push(if i == 0 {
                        self.scalar(item, &at(0), sc, &XType::Bool)?
                    } else {
                        self.closed_bool(item, &at(i), sc)?
                    });
                }
                Ok((XType::Bool, TExpr::Fold(key == "all", terms)))
            }
            "implies" => {
                let items = ops(2)?;
                let p = self.scalar(&items[0], &at(0), sc, &XType::Bool)?;
                let q = self.closed_bool(&items[1], &at(1), sc)?;
                Ok((XType::Bool, TExpr::Implies(b(p), b(q))))
            }
            "ite" => {
                let items = ops(3)?;
                let c = self.scalar(&items[0], &at(0), sc, &XType::Bool)?;
                let (tx, x) = self.tree(&items[1], &at(1), sc)?;
                let (ty, y) = self.tree(&items[2], &at(2), sc)?;
                self.expect(&at(2), &ty, &tx)?;
                Ok((tx, TExpr::Ite(b(c), b(x), b(y))))
            }
            "let" => {
                let m = object(body, path, &["name", "value", "body"])?;
                let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
                let (t, x) = self.tree(required(m, path, "value")?, &format!("{path}.value"), sc)?;
                sc.push(Local { name, ty: t });
                let r = self.tree(required(m, path, "body")?, &format!("{path}.body"), sc);
                sc.pop();
                let (tb, y) = r?;
                Ok((tb, TExpr::Let(b(x), b(y))))
            }
            "forall" | "exists" => self.quantifier(key == "forall", body, path, sc),
            "tuple" => {
                let items = array(body, path)?;
                if items.is_empty() {
                    return schema(path, "tuple は1つ以上の要素を持ちます");
                }
                let mut ts = Vec::new();
                let mut es = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    let (t, e) = self.tree(item, &at(i), sc)?;
                    ts.push(t);
                    es.push(e);
                }
                Ok((XType::Tuple(ts), TExpr::Tuple(es)))
            }
            "record" => {
                let items = array(body, path)?;
                if items.is_empty() {
                    return schema(path, "record は1つ以上のフィールドを持ちます");
                }
                let mut seen = HashSet::new();
                let mut fs = Vec::new();
                let mut ids = Vec::new();
                let mut es = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    let path = at(i);
                    let fv = object(item, &path, &["name", "expr"])?;
                    let name = string(required(fv, &path, "name")?, &format!("{path}.name"))?;
                    if !seen.insert(name.clone()) {
                        return schema(&path, format!("フィールド {name:?} が重複しています"));
                    }
                    let (t, e) = self.tree(required(fv, &path, "expr")?, &format!("{path}.expr"), sc)?;
                    ids.push(f.id(&name));
                    fs.push((name, t));
                    es.push(e);
                }
                Ok((XType::Record(fs), TExpr::Record(ids, es)))
            }
            "nth" => {
                let m = object(body, path, &["of", "index"])?;
                let (t, x) = self.tree(required(m, path, "of")?, &format!("{path}.of"), sc)?;
                let i = index(required(m, path, "index")?, &format!("{path}.index"))?;
                let XType::Tuple(ts) = &t else {
                    return type_error(path, format!("tuple が必要ですが、{} です", type_name(enums, &t)));
                };
                match ts.get(i) {
                    Some(t) => Ok((t.clone(), TExpr::Nth(b(x), i))),
                    None => type_error(path, format!("tuple の要素は {} 個です", ts.len())),
                }
            }
            "field" => {
                let m = object(body, path, &["of", "name"])?;
                let (t, x) = self.tree(required(m, path, "of")?, &format!("{path}.of"), sc)?;
                let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
                let XType::Record(fs) = &t else {
                    return type_error(path, format!("record が必要ですが、{} です", type_name(enums, &t)));
                };
                match fs.iter().position(|(n, _)| *n == name) {
                    Some(i) => Ok((fs[i].1.clone(), TExpr::Field(b(x), f.id(&name), i))),
                    None => type_error(path, format!("record にフィールド {name:?} がありません")),
                }
            }
            "none" => {
                let st = parse_type(body, path, enums)?;
                Ok((XType::Option(Box::new(st.xtype())), TExpr::None(f.stype(&st))))
            }
            "some" => {
                let items = ops(1)?;
                let (t, x) = self.tree(&items[0], &at(0), sc)?;
                Ok((XType::Option(Box::new(t)), TExpr::Some(b(x))))
            }
            "is_some" | "is_none" => {
                let items = ops(1)?;
                let (t, x) = self.tree(&items[0], &at(0), sc)?;
                if !matches!(t, XType::Option(_)) {
                    return type_error(path, format!("option が必要ですが、{} です", type_name(enums, &t)));
                }
                Ok((
                    XType::Bool,
                    if key == "is_some" {
                        TExpr::IsSome(b(x))
                    } else {
                        TExpr::IsNone(b(x))
                    },
                ))
            }
            "unwrap" => {
                let items = ops(1)?;
                let (t, x) = self.tree(&items[0], &at(0), sc)?;
                let XType::Option(inner) = t else {
                    return type_error(path, format!("option が必要ですが、{} です", type_name(enums, &t)));
                };
                Ok((*inner, TExpr::Unwrap(b(x))))
            }
            "set" => {
                let m = object(body, path, &["of", "items"])?;
                let st = parse_type(&serde_json::json!({"set": required(m, path, "of")?}), path, enums)?;
                let SType::Set(elem) = &st else {
                    return type_error(path, "set の型が不正です");
                };
                let mut es = Vec::new();
                for (i, item) in array(required(m, path, "items")?, &format!("{path}.items"))?
                    .iter()
                    .enumerate()
                {
                    es.push(self.fitting(item, &format!("{path}.items[{i}]"), sc, elem)?);
                }
                Ok((st.xtype(), TExpr::SetLit(f.stype(elem), es)))
            }
            "map" => {
                let m = object(body, path, &["key", "value", "items"])?;
                let st = parse_type(
                    &serde_json::json!({"map": {"key": required(m, path, "key")?, "value": required(m, path, "value")?}}),
                    path,
                    enums,
                )?;
                let SType::Map(k, val) = &st else {
                    return type_error(path, "map の型が不正です");
                };
                let mut items = Vec::new();
                for (i, item) in array(required(m, path, "items")?, &format!("{path}.items"))?
                    .iter()
                    .enumerate()
                {
                    let ipath = format!("{path}.items[{i}]");
                    let pair = operands(item, &ipath, 2)?;
                    let key = self.fitting(&pair[0], &format!("{ipath}[0]"), sc, k)?;
                    let value = self.fitting(&pair[1], &format!("{ipath}[1]"), sc, val)?;
                    items.push(Item { key, value });
                }
                Ok((st.xtype(), TExpr::MapLit(f.stype(k), f.stype(val), items)))
            }
            "list" => {
                let m = object(body, path, &["of", "max", "items"])?;
                let st = parse_type(
                    &serde_json::json!({"list": {"of": required(m, path, "of")?, "max": required(m, path, "max")?}}),
                    path,
                    enums,
                )?;
                let SType::List(t, max) = &st else {
                    return type_error(path, "list の型が不正です");
                };
                let items = array(required(m, path, "items")?, &format!("{path}.items"))?;
                if items.len() > *max {
                    return type_error(path, format!("要素が {} 個あり、上限 {max} を超えます", items.len()));
                }
                let mut es = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    es.push(self.fitting(item, &format!("{path}.items[{i}]"), sc, t)?);
                }
                Ok((st.xtype(), TExpr::ListLit(f.stype(t), *max, es)))
            }
            "contains" => {
                let items = ops(2)?;
                let (tc, c) = self.tree(&items[0], &at(0), sc)?;
                match &tc {
                    XType::Set(elem) => {
                        let x = self.fitting(&items[1], &at(1), sc, elem)?;
                        Ok((XType::Bool, TExpr::SetContains(f.stype(elem), b(c), b(x))))
                    }
                    XType::List(elem, _) => {
                        let x = self.fitting(&items[1], &at(1), sc, elem)?;
                        Ok((XType::Bool, TExpr::ListContains(b(c), b(x))))
                    }
                    _ => type_error(
                        path,
                        format!("set か list が必要ですが、{} です", type_name(enums, &tc)),
                    ),
                }
            }
            "insert" | "remove" => {
                let items = ops(2)?;
                let (ts, s) = self.tree(&items[0], &at(0), sc)?;
                let elem = self.set_elem(&ts, &at(0))?;
                let x = self.fitting(&items[1], &at(1), sc, &elem)?;
                let e = if key == "insert" {
                    TExpr::Insert(f.stype(&elem), b(s), b(x))
                } else {
                    TExpr::Remove(f.stype(&elem), b(s), b(x))
                };
                Ok((ts, e))
            }
            "union" | "intersection" | "difference" | "subset" => {
                let items = ops(2)?;
                let (ta, x) = self.tree(&items[0], &at(0), sc)?;
                let (tb, y) = self.tree(&items[1], &at(1), sc)?;
                self.set_elem(&ta, &at(0))?;
                self.expect(&at(1), &tb, &ta)?;
                let (op, t) = match key.as_str() {
                    "union" => (SetOp::Union, ta),
                    "intersection" => (SetOp::Intersection, ta),
                    "difference" => (SetOp::Difference, ta),
                    _ => (SetOp::Subset, XType::Bool),
                };
                Ok((t, TExpr::SetBin(op, b(x), b(y))))
            }
            "size" | "is_empty" => {
                let items = ops(1)?;
                let (t, x) = self.tree(&items[0], &at(0), sc)?;
                if !matches!(t, XType::Set(_) | XType::Map(_, _) | XType::List(_, _)) {
                    return type_error(
                        path,
                        format!("set、map、list が必要ですが、{} です", type_name(enums, &t)),
                    );
                }
                Ok(if key == "size" {
                    (XType::Int, TExpr::Size(b(x)))
                } else {
                    (XType::Bool, TExpr::IsEmpty(b(x)))
                })
            }
            "has_key" | "get" | "delete" => {
                let items = ops(2)?;
                let (tm, m) = self.tree(&items[0], &at(0), sc)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                let x = self.fitting(&items[1], &at(1), sc, &k)?;
                Ok(match key.as_str() {
                    "has_key" => (XType::Bool, TExpr::HasKey(f.stype(&k), b(m), b(x))),
                    "get" => (v.xtype(), TExpr::Get(f.stype(&k), b(m), b(x))),
                    _ => (tm, TExpr::Delete(f.stype(&k), b(m), b(x))),
                })
            }
            "put" => {
                let items = ops(3)?;
                let (tm, m) = self.tree(&items[0], &at(0), sc)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                let x = self.fitting(&items[1], &format!("{path}[1]"), sc, &k)?;
                let y = self.fitting(&items[2], &format!("{path}[2]"), sc, &v)?;
                Ok((tm, TExpr::Put(f.stype(&k), f.stype(&v), b(m), b(x), b(y))))
            }
            "keys" => {
                let items = ops(1)?;
                let (tm, m) = self.tree(&items[0], &at(0), sc)?;
                let (k, _) = self.map_types(&tm, &at(0))?;
                Ok((XType::Set(Box::new(k)), TExpr::Keys(b(m))))
            }
            "at" => {
                let items = ops(2)?;
                let (tl, l) = self.tree(&items[0], &at(0), sc)?;
                let (t, _) = self.list_type(&tl, &at(0))?;
                let i = self.scalar(&items[1], &at(1), sc, &XType::Int)?;
                Ok((t.xtype(), TExpr::At(b(l), b(i))))
            }
            "first" | "last" | "pop" | "shift" => {
                let items = ops(1)?;
                let (tl, l) = self.tree(&items[0], &at(0), sc)?;
                let (t, _) = self.list_type(&tl, &at(0))?;
                Ok(match key.as_str() {
                    "first" => (t.xtype(), TExpr::First(b(l))),
                    "last" => (t.xtype(), TExpr::Last(b(l))),
                    "pop" => (tl, TExpr::Pop(b(l))),
                    _ => (tl, TExpr::Shift(b(l))),
                })
            }
            "push" => {
                let items = ops(2)?;
                let (tl, l) = self.tree(&items[0], &at(0), sc)?;
                let (t, max) = self.list_type(&tl, &at(0))?;
                let x = self.fitting(&items[1], &at(1), sc, &t)?;
                Ok((tl, TExpr::Push(f.stype(&t), max, b(l), b(x))))
            }
            _ => schema(path, format!("未知の演算子 {key:?}")),
        }
    }

    fn quantifier(&self, all: bool, body: &Value, path: &str, sc: &mut Vec<Local>) -> Res<(XType, TExpr)> {
        let enums = self.enums;
        let f = self.fields;
        let m = object(body, path, &["name", "in", "type", "body"])?;
        let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
        let body_v = required(m, path, "body")?;
        let body_path = format!("{path}.body");
        let (over, ty) = match (m.get("in"), m.get("type")) {
            (Some(c), None) => {
                let (t, x) = self.tree(c, &format!("{path}.in"), sc)?;
                match t {
                    XType::Set(e) => (Over::Set(f.stype(&e), b(x)), e.xtype()),
                    XType::Map(k, _) => (Over::Map(f.stype(&k), b(x)), k.xtype()),
                    XType::List(e, _) => (Over::List(b(x)), e.xtype()),
                    _ => {
                        return type_error(
                            &format!("{path}.in"),
                            format!("set、map、list が必要ですが、{} です", type_name(enums, &t)),
                        )
                    }
                }
            }
            (None, Some(t)) => {
                let st = parse_type(t, &format!("{path}.type"), enums)?;
                if st.keys(enums).is_none() {
                    return schema(
                        &format!("{path}.type"),
                        format!("量化する型は、値の数が {MAX_KEYS} 以下で、set、map、list を含まない型に限ります"),
                    );
                }
                (Over::Type(f.stype(&st)), st.xtype())
            }
            _ => return schema(path, "in と type のどちらか一方が必要です"),
        };
        sc.push(Local { name, ty });
        let r = self.closed_bool(body_v, &body_path, sc);
        sc.pop();
        Ok((XType::Bool, TExpr::Quant(all, over, b(r?))))
    }
}
