//! IRの式の名前解決と型検査を経て、中核の式に下ろす。
//!
//! 名前解決（[`crate::resolve`]）が、JSONの式を中核の型付き構文木にし、型の誤りを報告する。
//! 中核の式への下ろしは、中核の検証済みの関数（[`fmspec_core::lowering`]）が行う。
//! ここにあるのは、下ろしの文脈、型の構文の読み取り、型の名前、定数の評価である。

use crate::json::{array, int, object, required, schema, single, string};
use crate::model::{EnumNames, LoadError};
use crate::resolve::Resolver;
use crate::types::{core_value, SType, XType, MAX_KEYS, MAX_LIST, MAX_WIDTH};
use fmspec_core::model::{Expr as C, Type, Value as CV};
use serde_json::Value;
use std::collections::HashSet;

/// `Expr::Fail` の番号。
pub const FAIL_NONE: i64 = fmspec_core::source::FAIL_NONE;
pub const FAIL_MISSING_KEY: i64 = fmspec_core::source::FAIL_MISSING_KEY;
pub const FAIL_INDEX: i64 = fmspec_core::source::FAIL_INDEX;
pub const FAIL_FULL: i64 = fmspec_core::source::FAIL_FULL;
pub const FAIL_EMPTY: i64 = fmspec_core::source::FAIL_EMPTY;
pub const FAIL_NOT_IN_DOMAIN: i64 = fmspec_core::source::FAIL_NOT_IN_DOMAIN;

/// 下ろすときの誤り。`Type` は型の誤りと未定義の参照で、どの定義で起きたかを呼び出し側が付ける。
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

/// 名前付きの定数。値はスロットごとの符号。
#[derive(Clone, Debug)]
pub(crate) struct Constant {
    pub name: String,
    pub ty: SType,
    pub codes: Vec<i64>,
}

/// 式を下ろす文脈。
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
}

// ---- 型 ----

fn int_range(v: &Value, path: &str) -> Res<(i64, i64)> {
    let range = object(v, path, &["min", "max"])?;
    let min = int(required(range, path, "min")?, &format!("{path}.min"))?;
    let max = int(required(range, path, "max")?, &format!("{path}.max"))?;
    Ok((min, max))
}

fn enum_id(enums: &[EnumNames], v: &Value, path: &str) -> Res<usize> {
    let name = string(v, path)?;
    match enums.iter().position(|e| e.name == name) {
        Some(id) => Ok(id),
        None => Ok(schema(path, format!("未定義の列挙型 {name:?}"))?),
    }
}

/// 型を読む。Setの要素とMapのキーは、値の数が `MAX_KEYS` 以下の、Set、Map、Listを含まない型に限る。
pub(crate) fn parse_type(v: &Value, path: &str, enums: &[EnumNames]) -> Res<SType> {
    let ty = parse_type_inner(v, path, enums)?;
    if ty.width(enums) > MAX_WIDTH {
        return Ok(schema(path, format!("型のスロット数が上限 {MAX_WIDTH} を超えます"))?);
    }
    Ok(ty)
}

fn parse_type_inner(v: &Value, path: &str, enums: &[EnumNames]) -> Res<SType> {
    let map = object(
        v,
        path,
        &["bool", "int", "enum", "tuple", "record", "option", "set", "map", "list"],
    )?;
    let (key, body) = single(
        map,
        path,
        "型は bool、int、enum、tuple、record、option、set、map、list のいずれか1つのキーを持つオブジェクトです",
    )?;
    let path = format!("{path}.{key}");
    let keyable = |t: &SType, what: &str| -> Res<()> {
        if t.keys(enums).is_none() {
            return Ok(schema(
                &path,
                format!("{what}の型は、値の数が {MAX_KEYS} 以下で、set、map、list を含まない型に限ります"),
            )?);
        }
        Ok(())
    };
    match key.as_str() {
        "bool" => {
            object(body, &path, &[])?;
            Ok(SType::Bool)
        }
        "int" => {
            let (min, max) = int_range(body, &path)?;
            Ok(SType::Int(min, max))
        }
        "enum" => Ok(SType::Enum(enum_id(enums, body, &path)?)),
        "tuple" => {
            let items = array(body, &path)?;
            if items.is_empty() {
                return Ok(schema(&path, "tuple は1つ以上の要素を持ちます")?);
            }
            let ts = items
                .iter()
                .enumerate()
                .map(|(i, t)| parse_type_inner(t, &format!("{path}[{i}]"), enums))
                .collect::<Res<Vec<_>>>()?;
            Ok(SType::Tuple(ts))
        }
        "record" => {
            let items = array(body, &path)?;
            if items.is_empty() {
                return Ok(schema(&path, "record は1つ以上のフィールドを持ちます")?);
            }
            let mut seen = HashSet::new();
            let mut fields = Vec::new();
            for (i, item) in items.iter().enumerate() {
                let path = format!("{path}[{i}]");
                let f = object(item, &path, &["name", "type"])?;
                let name = string(required(f, &path, "name")?, &format!("{path}.name"))?;
                if !seen.insert(name.clone()) {
                    return Ok(schema(&path, format!("フィールド {name:?} の定義が重複しています"))?);
                }
                fields.push((
                    name,
                    parse_type_inner(required(f, &path, "type")?, &format!("{path}.type"), enums)?,
                ));
            }
            Ok(SType::Record(fields))
        }
        "option" => Ok(SType::Option(Box::new(parse_type_inner(body, &path, enums)?))),
        "set" => {
            let t = parse_type_inner(body, &path, enums)?;
            keyable(&t, "set の要素")?;
            Ok(SType::Set(Box::new(t)))
        }
        "map" => {
            let m = object(body, &path, &["key", "value"])?;
            let k = parse_type_inner(required(m, &path, "key")?, &format!("{path}.key"), enums)?;
            keyable(&k, "map のキー")?;
            let v = parse_type_inner(required(m, &path, "value")?, &format!("{path}.value"), enums)?;
            Ok(SType::Map(Box::new(k), Box::new(v)))
        }
        _ => {
            let m = object(body, &path, &["of", "max"])?;
            let t = parse_type_inner(required(m, &path, "of")?, &format!("{path}.of"), enums)?;
            let max = match required(m, &path, "max")?.as_u64() {
                Some(n) if n as usize <= MAX_LIST => n as usize,
                _ => {
                    return Ok(schema(
                        &format!("{path}.max"),
                        format!("0以上 {MAX_LIST} 以下の整数が必要です"),
                    )?)
                }
            };
            Ok(SType::List(Box::new(t), max))
        }
    }
}

pub(crate) fn type_name(enums: &[EnumNames], t: &XType) -> String {
    match t {
        XType::Bool => "bool".to_string(),
        XType::Int => "int".to_string(),
        XType::Enum(id) => format!("enum {}", enums.get(*id).map(|e| e.name.as_str()).unwrap_or("?")),
        XType::Tuple(ts) => format!(
            "tuple({})",
            ts.iter().map(|t| type_name(enums, t)).collect::<Vec<_>>().join(", ")
        ),
        XType::Record(fs) => format!(
            "record({})",
            fs.iter()
                .map(|(n, t)| format!("{n}: {}", type_name(enums, t)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        XType::Option(t) => format!("option({})", type_name(enums, t)),
        XType::Set(t) => format!("set({})", type_name(enums, &t.xtype())),
        XType::Map(k, v) => format!(
            "map({}, {})",
            type_name(enums, &k.xtype()),
            type_name(enums, &v.xtype())
        ),
        XType::List(t, n) => format!("list({}, max {n})", type_name(enums, &t.xtype())),
    }
}

/// 値の符号の、スロットごとの中核の値。
pub(crate) fn const_values(enums: &[EnumNames], st: &SType, codes: &[i64]) -> Vec<CV> {
    let mut tys = Vec::new();
    st.slot_types(enums, &mut tys);
    tys.iter().zip(codes).map(|(t, x)| core_value(t, *x)).collect()
}

// ---- 下ろし ----

impl<'a> Ctx<'a> {
    pub(crate) fn expect(&self, path: &str, t: &XType, want: &XType) -> Res<()> {
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

    pub(crate) fn expect_fits(&self, path: &str, t: &XType, st: &SType) -> Res<()> {
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

    pub(crate) fn set_elem(&self, t: &XType, path: &str) -> Res<SType> {
        match t {
            XType::Set(e) => Ok((**e).clone()),
            _ => type_error(path, format!("set が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    pub(crate) fn map_types(&self, t: &XType, path: &str) -> Res<(SType, SType)> {
        match t {
            XType::Map(k, v) => Ok(((**k).clone(), (**v).clone())),
            _ => type_error(path, format!("map が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    pub(crate) fn list_type(&self, t: &XType, path: &str) -> Res<(SType, usize)> {
        match t {
            XType::List(e, n) => Ok(((**e).clone(), *n)),
            _ => type_error(path, format!("list が必要ですが、{} です", type_name(self.enums, t))),
        }
    }

    /// 述語（guard、不変条件、遷移契約、終端条件）として下ろす。
    pub(crate) fn prop(&self, v: &Value, path: &str) -> Res<C> {
        let r = Resolver::new(self);
        let e = r.prop(v, path)?;
        match fmspec_core::lowering::lower_prop(&e, &r.lower_ctx()) {
            Some(x) => Ok(x),
            None => type_error(path, "内部エラー: 中核の下ろしが式を受理しません"),
        }
    }

    /// 値を型 `st` の場所に置くスロット（正規形）。整数の範囲は検査しない（中核の範囲外更新で検出する）。
    pub(crate) fn stored(&self, v: &Value, path: &str, st: &SType, depth: usize) -> Res<Vec<C>> {
        let r = Resolver::new(self);
        let (_, e) = r.stored(v, path, st)?;
        match fmspec_core::lowering::lower_stored(&e, &r.lower_ctx(), &r.fields().stype(st), depth) {
            Some(xs) => Ok(xs),
            None => type_error(path, "内部エラー: 中核の下ろしが式を受理しません"),
        }
    }
}

/// 中核の式を、局所変数のない環境で評価して符号にする（初期値と定数）。
/// 整数の範囲は検査しない。初期値の範囲は中核のIR検証が検査する。
pub(crate) fn eval_const(e: &C, ty: &Type) -> Result<i64, fmspec_core::eval::ErrKind> {
    use fmspec_core::eval::{eval, Ctx as ECtx};
    let none_t: Vec<Type> = Vec::new();
    let none_v: Vec<i64> = Vec::new();
    let ctx = ECtx {
        st_tys: &none_t,
        arg_tys: &none_t,
        pre: &none_v,
        args: &none_v,
        post: &none_v,
        out: None,
    };
    let v = eval(e, &ctx)?;
    let x = crate::types::core_code(&v);
    let ok = matches!(
        (ty, v),
        (Type::Bool, CV::Bool(_)) | (Type::Enum(_), CV::Enum(_, _)) | (Type::Int(_, _), CV::Int(_))
    );
    if ok {
        Ok(x)
    } else {
        Err(fmspec_core::eval::ErrKind::TypeMismatch)
    }
}
