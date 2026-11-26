//! IRのJSONを読み込み、名前を添字に解決して、中核のモデルを組み立てる。

use crate::canonical;
use crate::IR_VERSION;
use fmspec_core::gate::{validate, CheckedModel};
use fmspec_core::model::{Action, BinOp, Contract, Expr, Output, RawModel, Type, Update, Value as CoreValue};
use fmspec_core::typing::InvalidModel;
use serde_json::{Map, Value};
use std::collections::HashSet;
use std::fmt;

/// 定義のソース位置。診断に使うだけで、モデルの意味には関わらない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    pub file: String,
    pub line: u64,
}

#[derive(Clone, Debug)]
pub struct EnumNames {
    pub name: String,
    pub variants: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ActionNames {
    pub name: String,
    pub params: Vec<String>,
    pub choices: Vec<String>,
    pub source: Option<Source>,
}

/// 添字に解決する前の名前。中核のモデルは名前を持たないので、表示と直列化のためにここで持つ。
#[derive(Clone, Debug)]
pub struct Names {
    pub model: String,
    pub enums: Vec<EnumNames>,
    pub states: Vec<String>,
    pub state_sources: Vec<Option<Source>>,
    pub actions: Vec<ActionNames>,
    pub invariants: Vec<String>,
    pub invariant_sources: Vec<Option<Source>>,
    pub contracts: Vec<String>,
    pub contract_sources: Vec<Option<Source>>,
}

impl Names {
    pub fn action_index(&self, name: &str) -> Option<usize> {
        self.actions.iter().position(|a| a.name == name)
    }

    pub fn invariant_index(&self, name: &str) -> Option<usize> {
        self.invariants.iter().position(|n| n == name)
    }

    pub fn contract_index(&self, name: &str) -> Option<usize> {
        self.contracts.iter().position(|n| n == name)
    }
}

/// IR検証を通過したモデルと、その名前、digest。
pub struct Model {
    pub names: Names,
    pub digest: String,
    checked: CheckedModel,
}

impl Model {
    pub fn checked(&self) -> &CheckedModel {
        &self.checked
    }

    pub fn raw(&self) -> &RawModel {
        self.checked.raw()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// JSONとして読めない。
    Json(String),
    /// IRの形式に合わない。未知のバージョンや演算子、未定義の名前、重複した定義など。
    Schema { path: String, message: String },
    /// 中核のIR検証がモデルを拒否した。
    Invalid { reason: InvalidModel, message: String },
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoadError::Json(message) => write!(f, "JSONとして読めません: {message}"),
            LoadError::Schema { path, message } => write!(f, "{path}: {message}"),
            LoadError::Invalid { message, .. } => write!(f, "{message}"),
        }
    }
}

type Res<T> = Result<T, LoadError>;

fn schema<T>(path: &str, message: impl Into<String>) -> Res<T> {
    Err(LoadError::Schema {
        path: path.to_string(),
        message: message.into(),
    })
}

fn object<'a>(v: &'a Value, path: &str, allowed: &[&str]) -> Res<&'a Map<String, Value>> {
    let Some(map) = v.as_object() else {
        return schema(path, "オブジェクトが必要です");
    };
    for key in map.keys() {
        if !allowed.contains(&key.as_str()) {
            return schema(path, format!("未知のキー {key:?}"));
        }
    }
    Ok(map)
}

fn required<'a>(map: &'a Map<String, Value>, path: &str, key: &str) -> Res<&'a Value> {
    match map.get(key) {
        Some(v) => Ok(v),
        None => schema(path, format!("キー {key:?} が必要です")),
    }
}

fn array<'a>(v: &'a Value, path: &str) -> Res<&'a Vec<Value>> {
    match v.as_array() {
        Some(a) => Ok(a),
        None => schema(path, "配列が必要です"),
    }
}

fn optional_array<'a>(map: &'a Map<String, Value>, path: &str, key: &str) -> Res<&'a [Value]> {
    match map.get(key) {
        None | Some(Value::Null) => Ok(&[]),
        Some(v) => Ok(array(v, &format!("{path}.{key}"))?),
    }
}

fn string(v: &Value, path: &str) -> Res<String> {
    match v.as_str() {
        Some(s) => Ok(s.to_string()),
        None => schema(path, "文字列が必要です"),
    }
}

fn int(v: &Value, path: &str) -> Res<i64> {
    match v.as_i64() {
        Some(i) if v.is_i64() || v.is_u64() => Ok(i),
        _ => schema(path, "符号付き64ビット整数が必要です"),
    }
}

fn index(v: &Value, path: &str) -> Res<usize> {
    match v.as_u64().and_then(|i| usize::try_from(i).ok()) {
        Some(i) => Ok(i),
        None => schema(path, "0以上の整数の添字が必要です"),
    }
}

fn unique(seen: &mut HashSet<String>, name: &str, path: &str, what: &str) -> Res<()> {
    if seen.insert(name.to_string()) {
        Ok(())
    } else {
        schema(path, format!("{what} {name:?} の定義が重複しています"))
    }
}

fn source(map: &Map<String, Value>, path: &str) -> Res<Option<Source>> {
    let Some(v) = map.get("source") else {
        return Ok(None);
    };
    if v.is_null() {
        return Ok(None);
    }
    let path = format!("{path}.source");
    let map = object(v, &path, &["file", "line"])?;
    let file = string(required(map, &path, "file")?, &format!("{path}.file"))?;
    let line = match required(map, &path, "line")?.as_u64() {
        Some(n) => n,
        None => return schema(&format!("{path}.line"), "0以上の整数が必要です"),
    };
    Ok(Some(Source { file, line }))
}

struct Scope<'a> {
    enums: &'a [EnumNames],
    /// 操作の公開引数の個数。操作の外では `0`。
    n_params: usize,
}

fn parse_type(v: &Value, path: &str, enums: &[EnumNames]) -> Res<Type> {
    let map = object(v, path, &["bool", "int", "enum"])?;
    if map.len() != 1 {
        return schema(path, "型は bool、int、enum のいずれか1つのキーを持つオブジェクトです");
    }
    let (key, body) = map.iter().next().unwrap();
    let path = format!("{path}.{key}");
    match key.as_str() {
        "bool" => {
            object(body, &path, &[])?;
            Ok(Type::Bool)
        }
        "int" => {
            let range = object(body, &path, &["min", "max"])?;
            let min = int(required(range, &path, "min")?, &format!("{path}.min"))?;
            let max = int(required(range, &path, "max")?, &format!("{path}.max"))?;
            Ok(Type::Int(min, max))
        }
        _ => {
            let name = string(body, &path)?;
            match enums.iter().position(|e| e.name == name) {
                Some(id) => Ok(Type::Enum(id)),
                None => schema(&path, format!("未定義の列挙型 {name:?}")),
            }
        }
    }
}

fn parse_enum_literal(v: &Value, path: &str, enums: &[EnumNames]) -> Res<CoreValue> {
    let map = object(v, path, &["type", "variant"])?;
    let ty = string(required(map, path, "type")?, &format!("{path}.type"))?;
    let variant = string(required(map, path, "variant")?, &format!("{path}.variant"))?;
    let Some(id) = enums.iter().position(|e| e.name == ty) else {
        return schema(path, format!("未定義の列挙型 {ty:?}"));
    };
    let Some(k) = enums[id].variants.iter().position(|x| *x == variant) else {
        return schema(path, format!("列挙型 {ty:?} に未定義のラベル {variant:?}"));
    };
    Ok(CoreValue::Enum(id, k as i64))
}

/// リテラル（`int`、`bool`、`enum`）を読む。リテラルでなければ `None`。
fn parse_literal(key: &str, body: &Value, path: &str, enums: &[EnumNames]) -> Res<Option<CoreValue>> {
    match key {
        "int" => Ok(Some(CoreValue::Int(int(body, path)?))),
        "bool" => match body.as_bool() {
            Some(b) => Ok(Some(CoreValue::Bool(b))),
            None => schema(path, "真偽値が必要です"),
        },
        "enum" => Ok(Some(parse_enum_literal(body, path, enums)?)),
        _ => Ok(None),
    }
}

fn operands<'a>(body: &'a Value, path: &str, n: usize) -> Res<&'a Vec<Value>> {
    let items = array(body, path)?;
    if items.len() != n {
        return schema(path, format!("オペランドは{n}個必要です（{}個あります）", items.len()));
    }
    Ok(items)
}

/// n項の `all` / `any` を二項の式の木にたたむ。評価順と打ち切りは、記述順の評価と一致する。
fn fold(mut items: Vec<Expr>, make: fn(Box<Expr>, Box<Expr>) -> Expr, unit: bool) -> Expr {
    match items.len() {
        0 => Expr::Const(CoreValue::Bool(unit)),
        1 => make(
            Box::new(items.pop().unwrap()),
            Box::new(Expr::Const(CoreValue::Bool(unit))),
        ),
        2 => {
            let b = items.pop().unwrap();
            let a = items.pop().unwrap();
            make(Box::new(a), Box::new(b))
        }
        n => {
            let right = items.split_off(n / 2);
            make(Box::new(fold(items, make, unit)), Box::new(fold(right, make, unit)))
        }
    }
}

fn parse_expr(v: &Value, path: &str, scope: &Scope) -> Res<Expr> {
    let Some(map) = v.as_object() else {
        return schema(path, "式はオブジェクトです");
    };
    if map.len() != 1 {
        return schema(path, "式は演算子を表すキーを1つだけ持つオブジェクトです");
    }
    let (key, body) = map.iter().next().unwrap();
    let path = format!("{path}.{key}");
    if let Some(lit) = parse_literal(key, body, &path, scope.enums)? {
        return Ok(Expr::Const(lit));
    }
    let bin = |op: BinOp| -> Res<Expr> {
        let items = operands(body, &path, 2)?;
        let a = parse_expr(&items[0], &format!("{path}[0]"), scope)?;
        let b = parse_expr(&items[1], &format!("{path}[1]"), scope)?;
        Ok(Expr::Bin(op, Box::new(a), Box::new(b)))
    };
    let list = |n: Option<usize>| -> Res<Vec<Expr>> {
        let items = match n {
            Some(n) => operands(body, &path, n)?,
            None => array(body, &path)?,
        };
        items
            .iter()
            .enumerate()
            .map(|(i, item)| parse_expr(item, &format!("{path}[{i}]"), scope))
            .collect()
    };
    match key.as_str() {
        "var" => Ok(Expr::Var(index(body, &path)?)),
        "param" => Ok(Expr::Arg(index(body, &path)?)),
        "choice" => match scope.n_params.checked_add(index(body, &path)?) {
            Some(i) => Ok(Expr::Arg(i)),
            None => schema(&path, "添字が大きすぎます"),
        },
        "next" => Ok(Expr::Next(index(body, &path)?)),
        "output" => {
            object(body, &path, &[])?;
            Ok(Expr::Out)
        }
        "add" => bin(BinOp::Add),
        "sub" => bin(BinOp::Sub),
        "mul" => bin(BinOp::Mul),
        "lt" => bin(BinOp::Lt),
        "le" => bin(BinOp::Le),
        "gt" => bin(BinOp::Gt),
        "ge" => bin(BinOp::Ge),
        "eq" => bin(BinOp::Eq),
        "ne" => bin(BinOp::Ne),
        "not" => {
            let mut items = list(Some(1))?;
            Ok(Expr::Not(Box::new(items.pop().unwrap())))
        }
        "all" => Ok(fold(list(None)?, Expr::And, true)),
        "any" => Ok(fold(list(None)?, Expr::Or, false)),
        "implies" => {
            let mut items = list(Some(2))?;
            let q = items.pop().unwrap();
            let p = items.pop().unwrap();
            Ok(Expr::Implies(Box::new(p), Box::new(q)))
        }
        "ite" => {
            let mut items = list(Some(3))?;
            let b = items.pop().unwrap();
            let a = items.pop().unwrap();
            let c = items.pop().unwrap();
            Ok(Expr::Ite(Box::new(c), Box::new(a), Box::new(b)))
        }
        _ => schema(&path, format!("未知の演算子 {key:?}")),
    }
}

/// 初期値のリテラルを、宣言した型の符号に変換する。
fn parse_initial(v: &Value, path: &str, ty: &Type, enums: &[EnumNames]) -> Res<i64> {
    let map = object(v, path, &["int", "bool", "enum"])?;
    if map.len() != 1 {
        return schema(path, "初期値は int、bool、enum のいずれかのリテラルです");
    }
    let (key, body) = map.iter().next().unwrap();
    let lit = parse_literal(key, body, &format!("{path}.{key}"), enums)?.unwrap();
    match (ty, lit) {
        (Type::Bool, CoreValue::Bool(b)) => Ok(i64::from(b)),
        (Type::Int(_, _), CoreValue::Int(x)) => Ok(x),
        (Type::Enum(id), CoreValue::Enum(id2, k)) if *id == id2 => Ok(k),
        _ => schema(path, "初期値の型が状態変数の型と合いません"),
    }
}

fn parse_bindings(
    items: &[Value],
    path: &str,
    enums: &[EnumNames],
    seen: &mut HashSet<String>,
) -> Res<(Vec<String>, Vec<Type>)> {
    let mut names = Vec::new();
    let mut types = Vec::new();
    for (i, item) in items.iter().enumerate() {
        let path = format!("{path}[{i}]");
        let map = object(item, &path, &["name", "type"])?;
        let name = string(required(map, &path, "name")?, &format!("{path}.name"))?;
        unique(seen, &name, &path, "引数")?;
        types.push(parse_type(
            required(map, &path, "type")?,
            &format!("{path}.type"),
            enums,
        )?);
        names.push(name);
    }
    Ok((names, types))
}

fn parse_action(v: &Value, path: &str, enums: &[EnumNames]) -> Res<(ActionNames, Action)> {
    let map = object(
        v,
        path,
        &["name", "params", "choices", "guard", "updates", "output", "source"],
    )?;
    let name = string(required(map, path, "name")?, &format!("{path}.name"))?;
    let mut seen = HashSet::new();
    let (params, mut domains) = parse_bindings(
        optional_array(map, path, "params")?,
        &format!("{path}.params"),
        enums,
        &mut seen,
    )?;
    let (choices, choice_types) = parse_bindings(
        optional_array(map, path, "choices")?,
        &format!("{path}.choices"),
        enums,
        &mut seen,
    )?;
    let n_params = domains.len();
    domains.extend(choice_types);
    let scope = Scope { enums, n_params };
    let guard = match map.get("guard") {
        None | Some(Value::Null) => Expr::Const(CoreValue::Bool(true)),
        Some(g) => parse_expr(g, &format!("{path}.guard"), &scope)?,
    };
    let mut updates = Vec::new();
    for (i, item) in optional_array(map, path, "updates")?.iter().enumerate() {
        let path = format!("{path}.updates[{i}]");
        let up = object(item, &path, &["target", "expr"])?;
        let target = index(required(up, &path, "target")?, &format!("{path}.target"))?;
        let expr = parse_expr(required(up, &path, "expr")?, &format!("{path}.expr"), &scope)?;
        updates.push(Update { target, expr });
    }
    let output = match map.get("output") {
        None | Some(Value::Null) => None,
        Some(o) => {
            let path = format!("{path}.output");
            let out = object(o, &path, &["type", "expr"])?;
            let ty = parse_type(required(out, &path, "type")?, &format!("{path}.type"), enums)?;
            let expr = parse_expr(required(out, &path, "expr")?, &format!("{path}.expr"), &scope)?;
            Some(Output { ty, expr })
        }
    };
    let names = ActionNames {
        name,
        params,
        choices,
        source: source(map, path)?,
    };
    Ok((
        names,
        Action {
            n_params,
            domains,
            guard,
            updates,
            output,
        },
    ))
}

/// IRのJSONを読み、名前を解決したモデルを組み立てる。中核のIR検証はまだ通していない。
pub fn parse(json: &str) -> Result<(RawModel, Names, String), LoadError> {
    let root: Value = serde_json::from_str(json).map_err(|e| LoadError::Json(e.to_string()))?;
    let path = "$";
    let map = object(
        &root,
        path,
        &[
            "ir_version",
            "name",
            "enums",
            "states",
            "actions",
            "invariants",
            "contracts",
            "terminal",
        ],
    )?;
    let version = required(map, path, "ir_version")?;
    if version.as_i64() != Some(IR_VERSION) {
        return schema(
            "$.ir_version",
            format!("未対応のIRバージョン {version}（対応しているのは {IR_VERSION}）"),
        );
    }
    let model_name = string(required(map, path, "name")?, "$.name")?;

    let mut enums: Vec<EnumNames> = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "enums")?.iter().enumerate() {
        let path = format!("$.enums[{i}]");
        let e = object(item, &path, &["name", "variants"])?;
        let name = string(required(e, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "列挙型")?;
        let mut variants = Vec::new();
        let mut seen_variants = HashSet::new();
        for (j, label) in array(required(e, &path, "variants")?, &format!("{path}.variants"))?
            .iter()
            .enumerate()
        {
            let label = string(label, &format!("{path}.variants[{j}]"))?;
            unique(&mut seen_variants, &label, &path, "ラベル")?;
            variants.push(label);
        }
        enums.push(EnumNames { name, variants });
    }

    let mut states = Vec::new();
    let mut state_sources = Vec::new();
    let mut state_types = Vec::new();
    let mut init = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in array(required(map, path, "states")?, "$.states")?.iter().enumerate() {
        let path = format!("$.states[{i}]");
        let s = object(item, &path, &["id", "name", "type", "initial", "source"])?;
        if let Some(id) = s.get("id") {
            if index(id, &format!("{path}.id"))? != i {
                return schema(&format!("{path}.id"), format!("id は定義順の添字 {i} と一致させます"));
            }
        }
        let name = string(required(s, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "状態変数")?;
        let ty = parse_type(required(s, &path, "type")?, &format!("{path}.type"), &enums)?;
        init.push(parse_initial(
            required(s, &path, "initial")?,
            &format!("{path}.initial"),
            &ty,
            &enums,
        )?);
        state_types.push(ty);
        state_sources.push(source(s, &path)?);
        states.push(name);
    }

    let mut action_names = Vec::new();
    let mut actions = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "actions")?.iter().enumerate() {
        let path = format!("$.actions[{i}]");
        let (names, action) = parse_action(item, &path, &enums)?;
        unique(&mut seen, &names.name, &path, "操作")?;
        action_names.push(names);
        actions.push(action);
    }

    let scope = Scope {
        enums: &enums,
        n_params: 0,
    };
    let mut invariant_names = Vec::new();
    let mut invariant_sources = Vec::new();
    let mut invariants = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "invariants")?.iter().enumerate() {
        let path = format!("$.invariants[{i}]");
        let inv = object(item, &path, &["name", "expr", "source"])?;
        let name = string(required(inv, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "不変条件")?;
        invariants.push(parse_expr(
            required(inv, &path, "expr")?,
            &format!("{path}.expr"),
            &scope,
        )?);
        invariant_sources.push(source(inv, &path)?);
        invariant_names.push(name);
    }

    let mut contract_names = Vec::new();
    let mut contract_sources = Vec::new();
    let mut contracts = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "contracts")?.iter().enumerate() {
        let path = format!("$.contracts[{i}]");
        let con = object(item, &path, &["name", "action", "expr", "source"])?;
        let name = string(required(con, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "遷移契約")?;
        let action_name = string(required(con, &path, "action")?, &format!("{path}.action"))?;
        let Some(action) = action_names.iter().position(|a| a.name == action_name) else {
            return schema(&format!("{path}.action"), format!("未定義の操作 {action_name:?}"));
        };
        let scope = Scope {
            enums: &enums,
            n_params: actions[action].n_params,
        };
        contracts.push(Contract {
            action,
            expr: parse_expr(required(con, &path, "expr")?, &format!("{path}.expr"), &scope)?,
        });
        contract_sources.push(source(con, &path)?);
        contract_names.push(name);
    }

    let terminal = match map.get("terminal") {
        None | Some(Value::Null) => None,
        Some(t) => Some(parse_expr(t, "$.terminal", &scope)?),
    };

    let raw = RawModel {
        enums: enums.iter().map(|e| e.variants.len() as i64).collect(),
        state_types,
        init,
        actions,
        invariants,
        contracts,
        terminal,
    };
    let names = Names {
        model: model_name,
        enums,
        states,
        state_sources,
        actions: action_names,
        invariants: invariant_names,
        invariant_sources,
        contracts: contract_names,
        contract_sources,
    };
    Ok((raw, names, canonical::digest(&root)))
}

fn describe(reason: &InvalidModel, names: &Names) -> String {
    let action = |a: &usize| names.actions[*a].name.as_str();
    match reason {
        InvalidModel::EmptyEnum(i) => format!("列挙型 {:?} にラベルがありません", names.enums[*i].name),
        InvalidModel::StateType(i) => {
            format!(
                "状態変数 {:?} の型が不正です（空の整数範囲、または未定義の列挙型）",
                names.states[*i]
            )
        }
        InvalidModel::Initial => "初期値が状態変数の型の範囲外です".to_string(),
        InvalidModel::Params(a) => format!("操作 {:?} の引数の個数が不正です", action(a)),
        InvalidModel::Domain(a, d) => {
            let act = &names.actions[*a];
            let name = act
                .params
                .iter()
                .chain(act.choices.iter())
                .nth(*d)
                .map(String::as_str)
                .unwrap_or("?");
            format!(
                "操作 {:?} の引数 {name:?} のドメインが不正です（空の整数範囲、または未定義の列挙型）",
                act.name
            )
        }
        InvalidModel::Guard(a) => {
            format!(
                "操作 {:?} の guard が Bool 式でないか、未定義の参照を含みます",
                action(a)
            )
        }
        InvalidModel::Update(a, u) => format!(
            "操作 {:?} の {} 番目の更新が不正です（対象が未定義、または式の型が対象と合わない）",
            action(a),
            u + 1
        ),
        InvalidModel::DuplicateUpdate(a, u) => {
            format!(
                "操作 {:?} の {} 番目の更新は、同じ状態変数への重複代入です",
                action(a),
                u + 1
            )
        }
        InvalidModel::Output(a) => format!("操作 {:?} の出力の型または式が不正です", action(a)),
        InvalidModel::Invariant(i) => {
            format!(
                "不変条件 {:?} が Bool 式でないか、未定義の参照を含みます",
                names.invariants[*i]
            )
        }
        InvalidModel::Contract(c) => {
            format!(
                "遷移契約 {:?} が Bool 式でないか、未定義の参照を含みます",
                names.contracts[*c]
            )
        }
        InvalidModel::Terminal => "終端条件が Bool 式でないか、未定義の参照を含みます".to_string(),
    }
}

/// IRのJSONを読み込み、中核のIR検証を通したモデルを返す。
pub fn load(json: &str) -> Result<Model, LoadError> {
    let (raw, names, digest) = parse(json)?;
    match validate(raw) {
        Ok(checked) => Ok(Model { names, digest, checked }),
        Err(reason) => Err(LoadError::Invalid {
            message: describe(&reason, &names),
            reason,
        }),
    }
}
