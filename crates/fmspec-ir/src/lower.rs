//! IRの式の型検査と、中核の式への変換（下ろし）。
//!
//! 複合型の値は、`types` の配置に従ってスロットの列で表す。式は、スロットごとの中核の式に下ろす。
//!
//! 部分式の評価の順序と打ち切りは、複合型の値を直接評価する意味論と一致させる。
//! そのために、下ろした式は「束縛の列」と「スロットの式」の組で表す。
//! 束縛は、評価の順に `let` で局所変数に束縛する式で、失敗しうる計算はすべてここに置く。
//! スロットの式は失敗せず、束縛子（`let`、量化）も含まないので、どの深さで評価しても同じ値になる。
//! 短絡する演算（`all`、`any`、`implies`、`ite`）と量化の本体は、評価する位置の深さで
//! 独立に下ろし、外側の束縛の列には混ぜない。
//!
//! 局所変数は外側から数えた添字で指すので、下ろした式は評価する深さに依存する。
//! 束縛子を含む式は、作った深さでただちに束縛する。

use crate::json::{array, int, object, operands, required, schema, single, string};
use crate::model::{EnumNames, LoadError};
use crate::types::{core_value, SType, XType, MAX_KEYS, MAX_LIST, MAX_WIDTH};
use fmspec_core::map_lookup::{require_map_key, select_map_slot, MISSING_KEY};
use fmspec_core::model::{BinOp, Expr as C, Type, Value as CV};
use serde_json::Value;
use std::collections::HashSet;

/// `Expr::Fail` の番号。
pub const FAIL_NONE: i64 = 1;
pub const FAIL_MISSING_KEY: i64 = MISSING_KEY;
pub const FAIL_INDEX: i64 = 3;
pub const FAIL_FULL: i64 = 4;
pub const FAIL_EMPTY: i64 = 5;
pub const FAIL_NOT_IN_DOMAIN: i64 = 6;

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

fn type_error<T>(path: &str, message: impl Into<String>) -> Res<T> {
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

/// 局所変数（`let` と量化の束縛）。
#[derive(Clone)]
struct Bound {
    name: String,
    ty: XType,
    slots: Vec<C>,
}

// ---- 中核の式の組み立て ----

fn b(e: C) -> Box<C> {
    Box::new(e)
}

fn cb(x: bool) -> C {
    C::Const(CV::Bool(x))
}

fn ci(x: i64) -> C {
    C::Const(CV::Int(x))
}

fn bin(op: BinOp, x: C, y: C) -> C {
    C::Bin(op, b(x), b(y))
}

fn and(x: C, y: C) -> C {
    match (&x, &y) {
        (C::Const(CV::Bool(true)), _) => y,
        (_, C::Const(CV::Bool(true))) => x,
        _ => C::And(b(x), b(y)),
    }
}

fn or(x: C, y: C) -> C {
    match (&x, &y) {
        (C::Const(CV::Bool(false)), _) => y,
        (_, C::Const(CV::Bool(false))) => x,
        _ => C::Or(b(x), b(y)),
    }
}

fn not(x: C) -> C {
    C::Not(b(x))
}

fn ite(c: C, x: C, y: C) -> C {
    C::Ite(b(c), b(x), b(y))
}

fn implies(x: C, y: C) -> C {
    match &y {
        C::Const(CV::Bool(true)) => y,
        _ => C::Implies(b(x), b(y)),
    }
}

fn eq(x: C, y: C) -> C {
    bin(BinOp::Eq, x, y)
}

/// 平衡した二分木にたたむ。空なら `unit`。
fn tree(mut items: Vec<C>, unit: C, make: fn(C, C) -> C) -> C {
    match items.len() {
        0 => unit,
        1 => items.pop().unwrap_or(unit),
        n => {
            let right = items.split_off(n / 2);
            make(tree(items, unit.clone(), make), tree(right, unit, make))
        }
    }
}

fn all_of(items: Vec<C>) -> C {
    tree(items, cb(true), and)
}

fn any_of(items: Vec<C>) -> C {
    tree(items, cb(false), or)
}

fn sum(items: Vec<C>) -> C {
    tree(items, ci(0), |x, y| bin(BinOp::Add, x, y))
}

/// 評価が失敗しうる。整数の演算は、値によってはオーバーフローするので失敗しうるとみなす。
fn may_fail(e: &C) -> bool {
    match e {
        C::Bin(op, x, y) => {
            matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod) || may_fail(x) || may_fail(y)
        }
        C::Fail(_, _) => true,
        C::Not(x) | C::Code(x) => may_fail(x),
        C::And(x, y) | C::Or(x, y) | C::Implies(x, y) | C::Let(x, y) => may_fail(x) || may_fail(y),
        C::Ite(c, x, y) => may_fail(c) || may_fail(x) || may_fail(y),
        C::Forall(_, _, _, body) | C::Exists(_, _, _, body) => may_fail(body),
        C::Const(_) | C::Var(_) | C::Arg(_) | C::Next(_) | C::Out | C::Local(_) => false,
    }
}

/// 束縛子を含む。
fn binds(e: &C) -> bool {
    match e {
        C::Let(_, _) | C::Forall(_, _, _, _) | C::Exists(_, _, _, _) => true,
        C::Bin(_, x, y) | C::And(x, y) | C::Or(x, y) | C::Implies(x, y) => binds(x) || binds(y),
        C::Not(x) | C::Code(x) => binds(x),
        C::Ite(c, x, y) => binds(c) || binds(x) || binds(y),
        C::Const(_) | C::Var(_) | C::Arg(_) | C::Next(_) | C::Out | C::Local(_) | C::Fail(_, _) => false,
    }
}

fn atomic(e: &C) -> bool {
    matches!(
        e,
        C::Const(_) | C::Var(_) | C::Arg(_) | C::Next(_) | C::Out | C::Local(_)
    )
}

/// 評価の順に並べた束縛の列。`base` は最初の束縛の局所変数の添字。
struct Block {
    base: usize,
    binds: Vec<C>,
}

impl Block {
    fn new(base: usize) -> Block {
        Block {
            base,
            binds: Vec::new(),
        }
    }

    fn depth(&self) -> usize {
        self.base + self.binds.len()
    }

    fn bind(&mut self, e: C) -> C {
        let i = self.depth();
        self.binds.push(e);
        C::Local(i)
    }

    /// 失敗しうる式と束縛子を含む式は束縛し、それ以外はそのまま返す。
    fn keep(&mut self, e: C) -> C {
        if may_fail(&e) || binds(&e) {
            self.bind(e)
        } else {
            e
        }
    }

    /// 何度も参照する式を束縛する。
    fn atom(&mut self, e: C) -> C {
        if atomic(&e) {
            e
        } else {
            self.bind(e)
        }
    }

    /// `cond` が偽なら、番号 `code` で失敗する。
    fn check(&mut self, cond: C, code: i64) {
        if !matches!(cond, C::Const(CV::Bool(true))) {
            self.bind(ite(cond, cb(true), C::Fail(Type::Bool, code)));
        }
    }

    fn wrap(binds: &[C], e: C) -> C {
        binds.iter().rev().fold(e, |acc, x| C::Let(b(x.clone()), b(acc)))
    }
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

fn type_name(enums: &[EnumNames], t: &XType) -> String {
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

// ---- スロットの操作 ----

/// 型 `st` の既定値のスロット。
fn defaults(enums: &[EnumNames], st: &SType) -> Vec<C> {
    let mut tys = Vec::new();
    st.slot_types(enums, &mut tys);
    tys.iter()
        .map(|t| C::Const(core_value(t, crate::types::default_code(t))))
        .collect()
}

/// 値の符号のスロット。
fn consts(enums: &[EnumNames], st: &SType, codes: &[i64]) -> Vec<C> {
    let mut tys = Vec::new();
    st.slot_types(enums, &mut tys);
    tys.iter()
        .zip(codes)
        .map(|(t, x)| C::Const(core_value(t, *x)))
        .collect()
}

/// 添字 `idx`（`0..rows.len()` に収まる）の行を選ぶ。二分木の `ite` にする。
fn select(rows: &[Vec<C>], idx: &C, fallback: &[C]) -> Vec<C> {
    fn pick(rows: &[Vec<C>], lo: usize, hi: usize, j: usize, idx: &C) -> C {
        if hi - lo == 1 {
            rows[lo][j].clone()
        } else {
            let mid = (lo + hi) / 2;
            ite(
                bin(BinOp::Lt, idx.clone(), ci(mid as i64)),
                pick(rows, lo, mid, j, idx),
                pick(rows, mid, hi, j, idx),
            )
        }
    }
    if rows.is_empty() {
        return fallback.to_vec();
    }
    (0..rows[0].len()).map(|j| pick(rows, 0, rows.len(), j, idx)).collect()
}

/// 要素の型ごとのスロットの区切り。
fn split<'s>(enums: &[EnumNames], tys: impl Iterator<Item = &'s XType>, slots: &[C]) -> Vec<Vec<C>> {
    let mut at = 0;
    tys.map(|t| {
        let w = t.width(enums);
        let part = slots[at..at + w].to_vec();
        at += w;
        part
    })
    .collect()
}

/// 構造の等しさ。Option が空なら中身は比べない。
fn eq_slots(enums: &[EnumNames], t: &XType, x: &[C], y: &[C]) -> C {
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => eq(x[0].clone(), y[0].clone()),
        XType::Tuple(ts) => {
            let xs = split(enums, ts.iter(), x);
            let ys = split(enums, ts.iter(), y);
            all_of(
                ts.iter()
                    .zip(xs.iter().zip(&ys))
                    .map(|(t, (a, b))| eq_slots(enums, t, a, b))
                    .collect(),
            )
        }
        XType::Record(fs) => {
            let xs = split(enums, fs.iter().map(|(_, t)| t), x);
            let ys = split(enums, fs.iter().map(|(_, t)| t), y);
            all_of(
                fs.iter()
                    .zip(xs.iter().zip(&ys))
                    .map(|((_, t), (a, b))| eq_slots(enums, t, a, b))
                    .collect(),
            )
        }
        XType::Option(t) => and(
            eq(x[0].clone(), y[0].clone()),
            implies(x[0].clone(), eq_slots(enums, t, &x[1..], &y[1..])),
        ),
        // Set、Map、List は正規形なので、スロットの一致が値の一致である。
        XType::Set(_) | XType::Map(_, _) | XType::List(_, _) => {
            all_of(x.iter().zip(y).map(|(a, b)| eq(a.clone(), b.clone())).collect())
        }
    }
}

/// 値を型 `st` の場所に置く。値が型に属する条件と、正規形にしたスロットを返す。
/// `t` は `st` に合う（`fits`）ものとする。
fn store(enums: &[EnumNames], t: &XType, slots: &[C], st: &SType) -> (C, Vec<C>) {
    match (t, st) {
        (XType::Int, SType::Int(lo, hi)) => (
            and(
                bin(BinOp::Le, ci(*lo), slots[0].clone()),
                bin(BinOp::Le, slots[0].clone(), ci(*hi)),
            ),
            slots.to_vec(),
        ),
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            let parts = split(enums, xs.iter(), slots);
            let mut conds = Vec::new();
            let mut out = Vec::new();
            for ((x, t), p) in xs.iter().zip(ts).zip(&parts) {
                let (c, s) = store(enums, x, p, t);
                conds.push(c);
                out.extend(s);
            }
            (all_of(conds), out)
        }
        (XType::Record(xs), SType::Record(ts)) => {
            let parts = split(enums, xs.iter().map(|(_, t)| t), slots);
            let mut conds = Vec::new();
            let mut out = Vec::new();
            for (((_, x), (_, t)), p) in xs.iter().zip(ts).zip(&parts) {
                let (c, s) = store(enums, x, p, t);
                conds.push(c);
                out.extend(s);
            }
            (all_of(conds), out)
        }
        (XType::Option(x), SType::Option(t)) => {
            let tag = slots[0].clone();
            let (c, payload) = store(enums, x, &slots[1..], t);
            let mut out = vec![tag.clone()];
            out.extend(
                payload
                    .into_iter()
                    .zip(defaults(enums, t))
                    .map(|(p, d)| ite(tag.clone(), p, d)),
            );
            (implies(tag, c), out)
        }
        _ => (cb(true), slots.to_vec()),
    }
}

/// 要素の型 `st` での番号。値が型に属するときに限って評価する。
fn rank_expr(enums: &[EnumNames], t: &XType, slots: &[C], st: &SType) -> C {
    match (t, st) {
        (XType::Int, SType::Int(lo, _)) => {
            if *lo == 0 {
                slots[0].clone()
            } else {
                bin(BinOp::Sub, slots[0].clone(), ci(*lo))
            }
        }
        (XType::Bool, _) | (XType::Enum(_), _) => C::Code(b(slots[0].clone())),
        (XType::Tuple(xs), SType::Tuple(ts)) => mixed(enums, xs.iter().zip(ts), slots),
        (XType::Record(xs), SType::Record(ts)) => {
            mixed(enums, xs.iter().map(|(_, x)| x).zip(ts.iter().map(|(_, t)| t)), slots)
        }
        (XType::Option(x), SType::Option(t)) => ite(
            slots[0].clone(),
            bin(BinOp::Add, ci(1), rank_expr(enums, x, &slots[1..], t)),
            ci(0),
        ),
        _ => ci(0),
    }
}

fn mixed<'s>(enums: &[EnumNames], parts: impl Iterator<Item = (&'s XType, &'s SType)>, slots: &[C]) -> C {
    let mut r: Option<C> = None;
    let mut at = 0;
    for (x, t) in parts {
        let w = x.width(enums);
        let k = rank_expr(enums, x, &slots[at..at + w], t);
        at += w;
        let n = t.keys(enums).unwrap_or(1) as i64;
        r = Some(match r {
            None => k,
            Some(prev) => bin(BinOp::Add, bin(BinOp::Mul, prev, ci(n)), k),
        });
    }
    r.unwrap_or_else(|| ci(0))
}

/// 値が要素の型に属すれば、その番号。属さなければ -1。
fn rank_or_neg(enums: &[EnumNames], t: &XType, slots: &[C], st: &SType) -> C {
    let (in_dom, _) = store(enums, t, slots, st);
    let r = rank_expr(enums, t, slots, st);
    match in_dom {
        C::Const(CV::Bool(true)) => r,
        c => ite(c, r, ci(-1)),
    }
}

/// 型 `st` の値として正規形である（Option が空なら中身が既定値、など）。
/// 引数と量化の束縛は、スロットごとに値を列挙するので、正規形でない組を除く。
pub(crate) fn canonical(enums: &[EnumNames], st: &SType, slots: &[C]) -> C {
    match st {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) | SType::Set(_) => cb(true),
        SType::Tuple(ts) => {
            let xs: Vec<XType> = ts.iter().map(SType::xtype).collect();
            let parts = split(enums, xs.iter(), slots);
            all_of(ts.iter().zip(&parts).map(|(t, p)| canonical(enums, t, p)).collect())
        }
        SType::Record(fs) => {
            let xs: Vec<XType> = fs.iter().map(|(_, t)| t.xtype()).collect();
            let parts = split(enums, xs.iter(), slots);
            all_of(
                fs.iter()
                    .zip(&parts)
                    .map(|((_, t), p)| canonical(enums, t, p))
                    .collect(),
            )
        }
        SType::Option(t) => {
            let payload = &slots[1..];
            let inner = canonical(enums, t, payload);
            let empty = all_of(
                payload
                    .iter()
                    .zip(defaults(enums, t))
                    .map(|(p, d)| eq(p.clone(), d))
                    .collect(),
            );
            match (&inner, &empty) {
                (C::Const(CV::Bool(true)), C::Const(CV::Bool(true))) => cb(true),
                _ => ite(slots[0].clone(), inner, empty),
            }
        }
        SType::Map(k, v) => {
            let n = k.keys(enums).unwrap_or(0) as usize;
            let w = v.width(enums);
            let defs = defaults(enums, v);
            all_of(
                (0..n)
                    .map(|i| {
                        let at = i * (1 + w);
                        let vals = &slots[at + 1..at + 1 + w];
                        let empty = all_of(vals.iter().zip(&defs).map(|(p, d)| eq(p.clone(), d.clone())).collect());
                        ite(slots[at].clone(), canonical(enums, v, vals), empty)
                    })
                    .collect(),
            )
        }
        SType::List(t, max) => {
            let w = t.width(enums);
            let defs = defaults(enums, t);
            all_of(
                (0..*max)
                    .map(|p| {
                        let item = &slots[1 + p * w..1 + (p + 1) * w];
                        let empty = all_of(item.iter().zip(&defs).map(|(x, d)| eq(x.clone(), d.clone())).collect());
                        ite(
                            bin(BinOp::Lt, ci(p as i64), slots[0].clone()),
                            canonical(enums, t, item),
                            empty,
                        )
                    })
                    .collect(),
            )
        }
    }
}

/// Map のスロットの、キーごとの有無と値。
fn map_parts(enums: &[EnumNames], k: &SType, v: &SType, slots: &[C]) -> (Vec<C>, Vec<Vec<C>>) {
    let n = k.keys(enums).unwrap_or(0) as usize;
    let w = v.width(enums);
    let present = (0..n).map(|i| slots[i * (1 + w)].clone()).collect();
    let values = (0..n)
        .map(|i| slots[i * (1 + w) + 1..(i + 1) * (1 + w)].to_vec())
        .collect();
    (present, values)
}

fn map_join(present: Vec<C>, values: Vec<Vec<C>>) -> Vec<C> {
    let mut out = Vec::new();
    for (p, vs) in present.into_iter().zip(values) {
        out.push(p);
        out.extend(vs);
    }
    out
}

/// List のスロットの、長さと要素。
fn list_parts(enums: &[EnumNames], t: &SType, max: usize, slots: &[C]) -> (C, Vec<Vec<C>>) {
    let w = t.width(enums);
    let items = (0..max).map(|p| slots[1 + p * w..1 + (p + 1) * w].to_vec()).collect();
    (slots[0].clone(), items)
}

fn list_join(len: C, items: Vec<Vec<C>>) -> Vec<C> {
    let mut out = vec![len];
    out.extend(items.into_iter().flatten());
    out
}

/// 量化で束縛する型の、スロットごとの範囲。
fn quant_ranges(enums: &[EnumNames], st: &SType) -> Vec<(Type, i64, i64)> {
    let mut tys = Vec::new();
    st.slot_types(enums, &mut tys);
    tys.into_iter()
        .map(|t| {
            let (lo, hi) = match t {
                Type::Bool => (0, 1),
                Type::Int(lo, hi) => (lo, hi),
                Type::Enum(id) => (0, enums.get(id).map(|e| e.variants.len() as i64).unwrap_or(0) - 1),
            };
            (t, lo, hi)
        })
        .collect()
}

// ---- 下ろし ----

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

    /// 深さ `depth` で単独に評価できるように下ろす。スロットごとに、束縛を含む式を返す。
    fn closed_in(&self, v: &Value, path: &str, sc: &[Bound], depth: usize) -> Res<(XType, Vec<C>)> {
        let mut blk = Block::new(depth);
        let (t, slots) = self.expr(v, path, sc, &mut blk)?;
        Ok((t, slots.into_iter().map(|s| Block::wrap(&blk.binds, s)).collect()))
    }

    /// スカラー型の式として下ろす。
    fn scalar_in(&self, v: &Value, path: &str, sc: &[Bound], depth: usize) -> Res<(XType, C)> {
        let (t, mut slots) = self.closed_in(v, path, sc, depth)?;
        match (t.is_scalar(), slots.pop()) {
            (true, Some(e)) => Ok((t, e)),
            _ => type_error(
                path,
                format!("スカラー型の式が必要ですが、{} です", type_name(self.enums, &t)),
            ),
        }
    }

    /// 述語（guard、不変条件、遷移契約、終端条件）として下ろす。
    pub(crate) fn prop(&self, v: &Value, path: &str) -> Res<C> {
        self.bool_in(v, path, &[], 0)
    }

    fn bool_in(&self, v: &Value, path: &str, sc: &[Bound], depth: usize) -> Res<C> {
        let (t, e) = self.scalar_in(v, path, sc, depth)?;
        self.expect(path, &t, &XType::Bool)?;
        Ok(e)
    }

    /// 値を型 `st` の場所に置くスロット（正規形）。整数の範囲は検査しない（中核の範囲外更新で検出する）。
    pub(crate) fn stored(&self, v: &Value, path: &str, st: &SType, depth: usize) -> Res<Vec<C>> {
        let mut blk = Block::new(depth);
        let (t, slots) = self.expr(v, path, &[], &mut blk)?;
        self.expect_fits(path, &t, st)?;
        let (_, slots) = store(self.enums, &t, &slots, st);
        Ok(slots.into_iter().map(|s| Block::wrap(&blk.binds, s)).collect())
    }

    fn sub(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block) -> Res<(XType, Vec<C>)> {
        self.expr(v, path, sc, blk)
    }

    fn sub_scalar(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block, want: &XType) -> Res<C> {
        let (t, mut slots) = self.expr(v, path, sc, blk)?;
        self.expect(path, &t, want)?;
        Ok(slots.pop().unwrap_or_else(|| cb(false)))
    }

    /// 要素を集合の型に合わせて評価し、属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。正規形のスロットを返す。
    fn element(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block, st: &SType) -> Res<Vec<C>> {
        let (t, slots) = self.expr(v, path, sc, blk)?;
        self.expect_fits(path, &t, st)?;
        let (cond, slots) = store(self.enums, &t, &slots, st);
        blk.check(cond, FAIL_NOT_IN_DOMAIN);
        Ok(slots.into_iter().map(|s| blk.atom(s)).collect())
    }

    /// 要素の番号。属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
    fn element_rank(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block, st: &SType) -> Res<C> {
        let (t, slots) = self.expr(v, path, sc, blk)?;
        self.expect_fits(path, &t, st)?;
        let (cond, _) = store(self.enums, &t, &slots, st);
        blk.check(cond, FAIL_NOT_IN_DOMAIN);
        let r = rank_expr(self.enums, &t, &slots, st);
        Ok(blk.atom(r))
    }

    /// 要素の番号。属さなければ -1。
    fn lookup_rank(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block, st: &SType) -> Res<C> {
        let (t, slots) = self.expr(v, path, sc, blk)?;
        self.expect_fits(path, &t, st)?;
        let r = rank_or_neg(self.enums, &t, &slots, st);
        Ok(blk.atom(r))
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

    fn layout_slots(&self, l: &Layout, make: fn(usize) -> C) -> (XType, Vec<C>) {
        let w = l.ty.width(self.enums);
        (l.ty.xtype(), (l.offset..l.offset + w).map(make).collect())
    }

    /// 式を `blk` の中に下ろす。部分式の束縛は評価の順に `blk` に追加し、失敗しないスロットの式を返す。
    fn expr(&self, v: &Value, path: &str, sc: &[Bound], blk: &mut Block) -> Res<(XType, Vec<C>)> {
        let Some(map) = v.as_object() else {
            return Ok(schema(path, "式はオブジェクトです")?);
        };
        let (key, body) = single(map, path, "式は演算子を表すキーを1つだけ持つオブジェクトです")?;
        let path = format!("{path}.{key}");
        let path = path.as_str();
        let enums = self.enums;
        let ops = |n: usize| operands(body, path, n);
        let at = |i: usize| format!("{path}[{i}]");
        match key.as_str() {
            "int" => Ok((XType::Int, vec![ci(int(body, path)?)])),
            "bool" => match body.as_bool() {
                Some(x) => Ok((XType::Bool, vec![cb(x)])),
                None => Ok(schema(path, "真偽値が必要です")?),
            },
            "enum" => {
                let m = object(body, path, &["type", "variant"])?;
                let ty = string(required(m, path, "type")?, &format!("{path}.type"))?;
                let variant = string(required(m, path, "variant")?, &format!("{path}.variant"))?;
                let Some(id) = enums.iter().position(|e| e.name == ty) else {
                    return Ok(schema(path, format!("未定義の列挙型 {ty:?}"))?);
                };
                let Some(k) = enums[id].variants.iter().position(|x| *x == variant) else {
                    return Ok(schema(path, format!("列挙型 {ty:?} に未定義のラベル {variant:?}"))?);
                };
                Ok((XType::Enum(id), vec![C::Const(CV::Enum(id, k as i64))]))
            }
            "var" | "next" => {
                let Some(states) = self.states else {
                    return type_error(path, "ここでは状態変数を参照できません");
                };
                if key == "next" && !self.next {
                    return type_error(path, "next は遷移契約でだけ使えます");
                }
                let i = crate::json::index(body, path)?;
                let Some(l) = states.get(i) else {
                    return type_error(path, format!("未定義の状態変数 {i}"));
                };
                Ok(self.layout_slots(l, if key == "var" { C::Var } else { C::Next }))
            }
            "param" | "choice" => {
                let i = crate::json::index(body, path)?;
                let (i, n) = if key == "param" {
                    (i, self.n_params)
                } else {
                    (self.n_params.saturating_add(i), self.args.len())
                };
                match self.args.get(i) {
                    Some(l) if i < n => Ok(self.layout_slots(l, C::Arg)),
                    _ => type_error(
                        path,
                        format!("未定義の{} {}", if key == "param" { "引数" } else { "内部選択" }, i),
                    ),
                }
            }
            "output" => {
                object(body, path, &[])?;
                match self.output {
                    Some(st) if self.next => Ok((st.xtype(), vec![C::Out])),
                    _ => type_error(path, "output は出力を宣言した操作の遷移契約でだけ使えます"),
                }
            }
            "local" => {
                let name = string(body, path)?;
                match sc.iter().rev().find(|x| x.name == name) {
                    Some(x) => Ok((x.ty.clone(), x.slots.clone())),
                    None => Ok(schema(path, format!("未定義の局所変数 {name:?}"))?),
                }
            }
            "const" => {
                let name = string(body, path)?;
                match self.constants.iter().find(|c| c.name == name) {
                    Some(c) => Ok((c.ty.xtype(), consts(enums, &c.ty, &c.codes))),
                    None => Ok(schema(path, format!("未定義の定数 {name:?}"))?),
                }
            }
            "add" | "sub" | "mul" | "div" | "mod" => {
                let items = ops(2)?;
                let x = self.sub_scalar(&items[0], &at(0), sc, blk, &XType::Int)?;
                let y = self.sub_scalar(&items[1], &at(1), sc, blk, &XType::Int)?;
                let op = match key.as_str() {
                    "add" => BinOp::Add,
                    "sub" => BinOp::Sub,
                    "mul" => BinOp::Mul,
                    "div" => BinOp::Div,
                    _ => BinOp::Mod,
                };
                Ok((XType::Int, vec![blk.keep(bin(op, x, y))]))
            }
            "lt" | "le" | "gt" | "ge" => {
                let items = ops(2)?;
                let x = self.sub_scalar(&items[0], &at(0), sc, blk, &XType::Int)?;
                let y = self.sub_scalar(&items[1], &at(1), sc, blk, &XType::Int)?;
                let op = match key.as_str() {
                    "lt" => BinOp::Lt,
                    "le" => BinOp::Le,
                    "gt" => BinOp::Gt,
                    _ => BinOp::Ge,
                };
                Ok((XType::Bool, vec![bin(op, x, y)]))
            }
            "eq" | "ne" => {
                let items = ops(2)?;
                let (tx, x) = self.sub(&items[0], &at(0), sc, blk)?;
                let (ty, y) = self.sub(&items[1], &at(1), sc, blk)?;
                self.expect(&at(1), &ty, &tx)?;
                let e = eq_slots(enums, &tx, &x, &y);
                Ok((XType::Bool, vec![if key == "eq" { e } else { not(e) }]))
            }
            "not" => {
                let items = ops(1)?;
                let x = self.sub_scalar(&items[0], &at(0), sc, blk, &XType::Bool)?;
                Ok((XType::Bool, vec![not(x)]))
            }
            "all" | "any" => {
                let items = array(body, path)?;
                let Some(first) = items.first() else {
                    return Ok((XType::Bool, vec![cb(key == "all")]));
                };
                let x = self.sub_scalar(first, &at(0), sc, blk, &XType::Bool)?;
                let depth = blk.depth();
                let mut terms = vec![x];
                for (i, item) in items.iter().enumerate().skip(1) {
                    terms.push(self.bool_in(item, &at(i), sc, depth)?);
                }
                let make: fn(C, C) -> C = if key == "all" {
                    |x, y| C::And(b(x), b(y))
                } else {
                    |x, y| C::Or(b(x), b(y))
                };
                Ok((XType::Bool, vec![blk.keep(tree(terms, cb(key == "all"), make))]))
            }
            "implies" => {
                let items = ops(2)?;
                let p = self.sub_scalar(&items[0], &at(0), sc, blk, &XType::Bool)?;
                let q = self.bool_in(&items[1], &at(1), sc, blk.depth())?;
                Ok((XType::Bool, vec![blk.keep(C::Implies(b(p), b(q)))]))
            }
            "ite" => {
                let items = ops(3)?;
                let c = self.sub_scalar(&items[0], &at(0), sc, blk, &XType::Bool)?;
                let depth = blk.depth();
                let (tx, xs) = self.closed_in(&items[1], &at(1), sc, depth)?;
                let (ty, ys) = self.closed_in(&items[2], &at(2), sc, depth)?;
                self.expect(&at(2), &ty, &tx)?;
                if tx.is_scalar() {
                    return Ok((tx, vec![blk.keep(ite(c, xs[0].clone(), ys[0].clone()))]));
                }
                let simple = xs.iter().chain(&ys).all(|e| !may_fail(e) && !binds(e));
                if simple {
                    let c = blk.atom(c);
                    let slots = xs.into_iter().zip(ys).map(|(x, y)| ite(c.clone(), x, y)).collect();
                    return Ok((tx, slots));
                }
                // 枝が失敗しうるなら、スロットごとに、その位置の深さで枝を下ろし直して束縛する。
                // 式は純粋なので、同じ枝を何度評価しても結果は同じで、最初の失敗も同じになる。
                let c = blk.atom(c);
                let mut slots = Vec::new();
                for j in 0..tx.width(enums) {
                    let depth = blk.depth();
                    let (_, xs) = self.closed_in(&items[1], &at(1), sc, depth)?;
                    let (_, ys) = self.closed_in(&items[2], &at(2), sc, depth)?;
                    slots.push(blk.keep(ite(c.clone(), xs[j].clone(), ys[j].clone())));
                }
                Ok((tx, slots))
            }
            "let" => {
                let m = object(body, path, &["name", "value", "body"])?;
                let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
                let (t, slots) = self.sub(required(m, path, "value")?, &format!("{path}.value"), sc, blk)?;
                let slots = slots.into_iter().map(|s| blk.atom(s)).collect();
                let mut inner = sc.to_vec();
                inner.push(Bound { name, ty: t, slots });
                self.sub(required(m, path, "body")?, &format!("{path}.body"), &inner, blk)
            }
            "forall" | "exists" => self.quantifier(key == "forall", body, path, sc, blk),
            "tuple" => {
                let items = array(body, path)?;
                if items.is_empty() {
                    return Ok(schema(path, "tuple は1つ以上の要素を持ちます")?);
                }
                let mut ts = Vec::new();
                let mut slots = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    let (t, s) = self.sub(item, &at(i), sc, blk)?;
                    ts.push(t);
                    slots.extend(s);
                }
                Ok((XType::Tuple(ts), slots))
            }
            "record" => {
                let items = array(body, path)?;
                if items.is_empty() {
                    return Ok(schema(path, "record は1つ以上のフィールドを持ちます")?);
                }
                let mut seen = HashSet::new();
                let mut fs = Vec::new();
                let mut slots = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    let path = at(i);
                    let f = object(item, &path, &["name", "expr"])?;
                    let name = string(required(f, &path, "name")?, &format!("{path}.name"))?;
                    if !seen.insert(name.clone()) {
                        return Ok(schema(&path, format!("フィールド {name:?} が重複しています"))?);
                    }
                    let (t, s) = self.sub(required(f, &path, "expr")?, &format!("{path}.expr"), sc, blk)?;
                    fs.push((name, t));
                    slots.extend(s);
                }
                Ok((XType::Record(fs), slots))
            }
            "nth" => {
                let m = object(body, path, &["of", "index"])?;
                let (t, slots) = self.sub(required(m, path, "of")?, &format!("{path}.of"), sc, blk)?;
                let i = crate::json::index(required(m, path, "index")?, &format!("{path}.index"))?;
                let XType::Tuple(ts) = &t else {
                    return type_error(path, format!("tuple が必要ですが、{} です", type_name(enums, &t)));
                };
                let parts = split(enums, ts.iter(), &slots);
                match (ts.get(i), parts.get(i)) {
                    (Some(t), Some(p)) => Ok((t.clone(), p.clone())),
                    _ => type_error(path, format!("tuple の要素は {} 個です", ts.len())),
                }
            }
            "field" => {
                let m = object(body, path, &["of", "name"])?;
                let (t, slots) = self.sub(required(m, path, "of")?, &format!("{path}.of"), sc, blk)?;
                let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
                let XType::Record(fs) = &t else {
                    return type_error(path, format!("record が必要ですが、{} です", type_name(enums, &t)));
                };
                let parts = split(enums, fs.iter().map(|(_, t)| t), &slots);
                match fs.iter().position(|(n, _)| *n == name) {
                    Some(i) => Ok((fs[i].1.clone(), parts[i].clone())),
                    None => type_error(path, format!("record にフィールド {name:?} がありません")),
                }
            }
            "none" => {
                let st = parse_type(body, path, enums)?;
                let mut slots = vec![cb(false)];
                slots.extend(defaults(enums, &st));
                Ok((XType::Option(Box::new(st.xtype())), slots))
            }
            "some" => {
                let items = ops(1)?;
                let (t, s) = self.sub(&items[0], &at(0), sc, blk)?;
                let mut slots = vec![cb(true)];
                slots.extend(s);
                Ok((XType::Option(Box::new(t)), slots))
            }
            "is_some" | "is_none" => {
                let items = ops(1)?;
                let (t, s) = self.sub(&items[0], &at(0), sc, blk)?;
                if !matches!(t, XType::Option(_)) {
                    return type_error(path, format!("option が必要ですが、{} です", type_name(enums, &t)));
                }
                let tag = s[0].clone();
                Ok((XType::Bool, vec![if key == "is_some" { tag } else { not(tag) }]))
            }
            "unwrap" => {
                let items = ops(1)?;
                let (t, s) = self.sub(&items[0], &at(0), sc, blk)?;
                let XType::Option(inner) = t else {
                    return type_error(path, format!("option が必要ですが、{} です", type_name(enums, &t)));
                };
                blk.check(s[0].clone(), FAIL_NONE);
                Ok((*inner, s[1..].to_vec()))
            }
            "set" => {
                let m = object(body, path, &["of", "items"])?;
                let st = parse_type(&serde_json::json!({"set": required(m, path, "of")?}), path, enums)?;
                let SType::Set(elem) = &st else {
                    return type_error(path, "set の型が不正です");
                };
                let n = elem.keys(enums).unwrap_or(0) as usize;
                let mut bits: Vec<C> = vec![cb(false); n];
                for (i, item) in array(required(m, path, "items")?, &format!("{path}.items"))?
                    .iter()
                    .enumerate()
                {
                    let r = self.element_rank(item, &format!("{path}.items[{i}]"), sc, blk, elem)?;
                    bits = bits
                        .into_iter()
                        .enumerate()
                        .map(|(k, bit)| or(bit, eq(r.clone(), ci(k as i64))))
                        .collect();
                }
                Ok((st.xtype(), bits))
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
                let mut slots = defaults(enums, &st);
                for (i, item) in array(required(m, path, "items")?, &format!("{path}.items"))?
                    .iter()
                    .enumerate()
                {
                    let ipath = format!("{path}.items[{i}]");
                    let pair = operands(item, &ipath, 2)?;
                    slots = self.put(&slots, k, val, &pair[0], &pair[1], &ipath, sc, blk)?;
                }
                Ok((st.xtype(), slots))
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
                let mut out = vec![ci(items.len() as i64)];
                for (i, item) in items.iter().enumerate() {
                    out.extend(self.element(item, &format!("{path}.items[{i}]"), sc, blk, t)?);
                }
                let defs = defaults(enums, t);
                for _ in items.len()..*max {
                    out.extend(defs.iter().cloned());
                }
                Ok((st.xtype(), out))
            }
            "contains" => {
                let items = ops(2)?;
                let (tc, cs) = self.sub(&items[0], &at(0), sc, blk)?;
                match &tc {
                    XType::Set(elem) => {
                        let r = self.lookup_rank(&items[1], &at(1), sc, blk, elem)?;
                        let fallback = [cb(false)];
                        let rows: Vec<Vec<C>> = cs.iter().map(|x| vec![x.clone()]).collect();
                        let hit = select(&rows, &r, &fallback).pop().unwrap_or_else(|| cb(false));
                        Ok((XType::Bool, vec![and(bin(BinOp::Ge, r, ci(0)), hit)]))
                    }
                    XType::List(elem, max) => {
                        let (tx, x) = self.sub(&items[1], &at(1), sc, blk)?;
                        self.expect_fits(&at(1), &tx, elem)?;
                        let (len, rows) = list_parts(enums, elem, *max, &cs);
                        let et = elem.xtype();
                        let hits = rows
                            .iter()
                            .enumerate()
                            .map(|(p, row)| {
                                and(bin(BinOp::Lt, ci(p as i64), len.clone()), eq_slots(enums, &et, row, &x))
                            })
                            .collect();
                        Ok((XType::Bool, vec![any_of(hits)]))
                    }
                    _ => type_error(
                        path,
                        format!("set か list が必要ですが、{} です", type_name(enums, &tc)),
                    ),
                }
            }
            "insert" | "remove" => {
                let items = ops(2)?;
                let (ts, bits) = self.sub(&items[0], &at(0), sc, blk)?;
                let elem = self.set_elem(&ts, &at(0))?;
                let slots = if key == "insert" {
                    let r = self.element_rank(&items[1], &at(1), sc, blk, &elem)?;
                    bits.into_iter()
                        .enumerate()
                        .map(|(k, bit)| or(bit, eq(r.clone(), ci(k as i64))))
                        .collect()
                } else {
                    let r = self.lookup_rank(&items[1], &at(1), sc, blk, &elem)?;
                    bits.into_iter()
                        .enumerate()
                        .map(|(k, bit)| and(bit, bin(BinOp::Ne, r.clone(), ci(k as i64))))
                        .collect()
                };
                Ok((ts, slots))
            }
            "union" | "intersection" | "difference" | "subset" => {
                let items = ops(2)?;
                let (ta, xs) = self.sub(&items[0], &at(0), sc, blk)?;
                let (tb, ys) = self.sub(&items[1], &at(1), sc, blk)?;
                self.set_elem(&ta, &at(0))?;
                self.expect(&at(1), &tb, &ta)?;
                let pairs = xs.into_iter().zip(ys);
                Ok(match key.as_str() {
                    "union" => (ta, pairs.map(|(x, y)| or(x, y)).collect()),
                    "intersection" => (ta, pairs.map(|(x, y)| and(x, y)).collect()),
                    "difference" => (ta, pairs.map(|(x, y)| and(x, not(y))).collect()),
                    _ => (XType::Bool, vec![all_of(pairs.map(|(x, y)| implies(x, y)).collect())]),
                })
            }
            "size" | "is_empty" => {
                let items = ops(1)?;
                let (t, s) = self.sub(&items[0], &at(0), sc, blk)?;
                let flags: Vec<C> = match &t {
                    XType::Set(_) => s.clone(),
                    XType::Map(k, v) => map_parts(enums, k, v, &s).0,
                    XType::List(_, _) => {
                        let len = s[0].clone();
                        return Ok(if key == "size" {
                            (XType::Int, vec![len])
                        } else {
                            (XType::Bool, vec![eq(len, ci(0))])
                        });
                    }
                    _ => {
                        return type_error(
                            path,
                            format!("set、map、list が必要ですが、{} です", type_name(enums, &t)),
                        )
                    }
                };
                Ok(if key == "size" {
                    (
                        XType::Int,
                        vec![blk.keep(sum(flags.into_iter().map(|f| C::Code(b(f))).collect()))],
                    )
                } else {
                    (XType::Bool, vec![not(any_of(flags))])
                })
            }
            "has_key" | "get" => {
                let items = ops(2)?;
                let (tm, ms) = self.sub(&items[0], &at(0), sc, blk)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                let r = self.lookup_rank(&items[1], &at(1), sc, blk, &k)?;
                let (present, values) = map_parts(enums, &k, &v, &ms);
                if key == "has_key" {
                    let rows: Vec<Vec<C>> = present.into_iter().map(|p| vec![p]).collect();
                    let hit = and(
                        bin(BinOp::Ge, r.clone(), ci(0)),
                        select(&rows, &r, &[cb(false)]).pop().unwrap_or_else(|| cb(false)),
                    );
                    return Ok((XType::Bool, vec![hit]));
                }
                let rank_local = match r {
                    C::Local(index) => index,
                    _ => {
                        let index = blk.depth();
                        blk.bind(r);
                        index
                    }
                };
                let presence = select_map_slot(present, rank_local, cb(false));
                blk.bind(require_map_key(presence, rank_local));
                let slots = defaults(enums, &v)
                    .into_iter()
                    .enumerate()
                    .map(|(index, fallback)| {
                        let column = values.iter().map(|row| row[index].clone()).collect();
                        select_map_slot(column, rank_local, fallback)
                    })
                    .collect();
                Ok((v.xtype(), slots))
            }
            "put" => {
                let items = ops(3)?;
                let (tm, ms) = self.sub(&items[0], &at(0), sc, blk)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                let slots = self.put(&ms, &k, &v, &items[1], &items[2], path, sc, blk)?;
                Ok((tm, slots))
            }
            "delete" => {
                let items = ops(2)?;
                let (tm, ms) = self.sub(&items[0], &at(0), sc, blk)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                let r = self.lookup_rank(&items[1], &at(1), sc, blk, &k)?;
                let (present, values) = map_parts(enums, &k, &v, &ms);
                let defs = defaults(enums, &v);
                let present = present
                    .into_iter()
                    .enumerate()
                    .map(|(i, p)| and(p, bin(BinOp::Ne, r.clone(), ci(i as i64))))
                    .collect();
                let values = values
                    .into_iter()
                    .enumerate()
                    .map(|(i, vs)| {
                        let hit = eq(r.clone(), ci(i as i64));
                        vs.into_iter()
                            .zip(&defs)
                            .map(|(x, d)| ite(hit.clone(), d.clone(), x))
                            .collect()
                    })
                    .collect();
                Ok((tm, map_join(present, values)))
            }
            "keys" => {
                let items = ops(1)?;
                let (tm, ms) = self.sub(&items[0], &at(0), sc, blk)?;
                let (k, v) = self.map_types(&tm, &at(0))?;
                Ok((XType::Set(Box::new(k.clone())), map_parts(enums, &k, &v, &ms).0))
            }
            "at" => {
                let items = ops(2)?;
                let (tl, ls) = self.sub(&items[0], &at(0), sc, blk)?;
                let (t, max) = self.list_type(&tl, &at(0))?;
                let i = self.sub_scalar(&items[1], &at(1), sc, blk, &XType::Int)?;
                let i = blk.atom(i);
                let (len, rows) = list_parts(enums, &t, max, &ls);
                blk.check(
                    and(bin(BinOp::Ge, i.clone(), ci(0)), bin(BinOp::Lt, i.clone(), len)),
                    FAIL_INDEX,
                );
                Ok((t.xtype(), select(&rows, &i, &defaults(enums, &t))))
            }
            "first" | "last" => {
                let items = ops(1)?;
                let (tl, ls) = self.sub(&items[0], &at(0), sc, blk)?;
                let (t, max) = self.list_type(&tl, &at(0))?;
                let (len, rows) = list_parts(enums, &t, max, &ls);
                blk.check(bin(BinOp::Gt, len.clone(), ci(0)), FAIL_EMPTY);
                if key == "first" {
                    return Ok((t.xtype(), rows.first().cloned().unwrap_or_else(|| defaults(enums, &t))));
                }
                let i = blk.bind(bin(BinOp::Sub, len, ci(1)));
                Ok((t.xtype(), select(&rows, &i, &defaults(enums, &t))))
            }
            "push" => {
                let items = ops(2)?;
                let (tl, ls) = self.sub(&items[0], &at(0), sc, blk)?;
                let (t, max) = self.list_type(&tl, &at(0))?;
                let x = self.element(&items[1], &at(1), sc, blk, &t)?;
                let (len, rows) = list_parts(enums, &t, max, &ls);
                blk.check(bin(BinOp::Lt, len.clone(), ci(max as i64)), FAIL_FULL);
                let new_len = blk.bind(bin(BinOp::Add, len.clone(), ci(1)));
                let rows = rows
                    .into_iter()
                    .enumerate()
                    .map(|(p, row)| {
                        let hit = eq(len.clone(), ci(p as i64));
                        row.into_iter()
                            .zip(&x)
                            .map(|(old, new)| ite(hit.clone(), new.clone(), old))
                            .collect()
                    })
                    .collect();
                Ok((tl, list_join(new_len, rows)))
            }
            "pop" | "shift" => {
                let items = ops(1)?;
                let (tl, ls) = self.sub(&items[0], &at(0), sc, blk)?;
                let (t, max) = self.list_type(&tl, &at(0))?;
                let (len, rows) = list_parts(enums, &t, max, &ls);
                blk.check(bin(BinOp::Gt, len.clone(), ci(0)), FAIL_EMPTY);
                let new_len = blk.bind(bin(BinOp::Sub, len, ci(1)));
                let defs = defaults(enums, &t);
                let rows: Vec<Vec<C>> = if key == "pop" {
                    rows.into_iter()
                        .enumerate()
                        .map(|(p, row)| {
                            let hit = eq(new_len.clone(), ci(p as i64));
                            row.into_iter()
                                .zip(&defs)
                                .map(|(old, d)| ite(hit.clone(), d.clone(), old))
                                .collect()
                        })
                        .collect()
                } else {
                    let mut shifted: Vec<Vec<C>> = rows.into_iter().skip(1).collect();
                    shifted.push(defs);
                    shifted
                };
                Ok((tl, list_join(new_len, rows)))
            }
            _ => Ok(schema(path, format!("未知の演算子 {key:?}"))?),
        }
    }

    /// `m` のキー `k` に値 `v` を置く。キーと値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
    #[allow(clippy::too_many_arguments)]
    fn put(
        &self,
        ms: &[C],
        k: &SType,
        v: &SType,
        key: &Value,
        value: &Value,
        path: &str,
        sc: &[Bound],
        blk: &mut Block,
    ) -> Res<Vec<C>> {
        let r = self.element_rank(key, &format!("{path}[1]"), sc, blk, k)?;
        let x = self.element(value, &format!("{path}[2]"), sc, blk, v)?;
        let (present, values) = map_parts(self.enums, k, v, ms);
        let present = present
            .into_iter()
            .enumerate()
            .map(|(i, p)| or(p, eq(r.clone(), ci(i as i64))))
            .collect();
        let values = values
            .into_iter()
            .enumerate()
            .map(|(i, vs)| {
                let hit = eq(r.clone(), ci(i as i64));
                vs.into_iter()
                    .zip(&x)
                    .map(|(old, new)| ite(hit.clone(), new.clone(), old))
                    .collect()
            })
            .collect();
        Ok(map_join(present, values))
    }

    /// `forall` と `exists`。集合（Set の要素、Map のキー、List の要素）か、型の全体をたどる。
    fn quantifier(&self, all: bool, body: &Value, path: &str, sc: &[Bound], blk: &mut Block) -> Res<(XType, Vec<C>)> {
        let enums = self.enums;
        let m = object(body, path, &["name", "in", "type", "body"])?;
        let name = string(required(m, path, "name")?, &format!("{path}.name"))?;
        let body_v = required(m, path, "body")?;
        let body_path = format!("{path}.body");
        let quant = |ty: Type, lo: i64, hi: i64, e: C| -> C {
            if all {
                C::Forall(ty, lo, hi, b(e))
            } else {
                C::Exists(ty, lo, hi, b(e))
            }
        };
        let combine = |guard: C, e: C| -> C {
            match (&guard, all) {
                (C::Const(CV::Bool(true)), _) => e,
                (_, true) => C::Implies(b(guard), b(e)),
                (_, false) => C::And(b(guard), b(e)),
            }
        };
        // 束縛する値の型と、その値が対象に含まれる条件（束縛した局所変数のスロットに対する式）。
        enum Over {
            Type(SType, Option<Vec<C>>),
            List(SType, usize, Vec<C>),
        }
        let over = match (m.get("in"), m.get("type")) {
            (Some(c), None) => {
                let (t, cs) = self.sub(c, &format!("{path}.in"), sc, blk)?;
                match t {
                    XType::Set(e) => Over::Type(*e, Some(cs)),
                    XType::Map(k, v) => {
                        let (present, _) = map_parts(enums, &k, &v, &cs);
                        Over::Type(*k, Some(present))
                    }
                    XType::List(e, max) => Over::List(*e, max, cs),
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
                    return Ok(schema(
                        &format!("{path}.type"),
                        format!("量化する型は、値の数が {MAX_KEYS} 以下で、set、map、list を含まない型に限ります"),
                    )?);
                }
                Over::Type(st, None)
            }
            _ => return Ok(schema(path, "in と type のどちらか一方が必要です")?),
        };
        let depth = blk.depth();
        let e = match over {
            Over::Type(st, flags) => {
                let ranges = quant_ranges(enums, &st);
                let k = ranges.len();
                let x: Vec<C> = (depth..depth + k).map(C::Local).collect();
                let mut guard = canonical(enums, &st, &x);
                if let Some(flags) = flags {
                    let r = rank_expr(enums, &st.xtype(), &x, &st);
                    let rows: Vec<Vec<C>> = flags.iter().map(|f| vec![f.clone()]).collect();
                    let hit = select(&rows, &r, &[cb(false)]).pop().unwrap_or_else(|| cb(false));
                    guard = and(guard, hit);
                }
                let mut inner = sc.to_vec();
                inner.push(Bound {
                    name,
                    ty: st.xtype(),
                    slots: x,
                });
                let body = self.bool_in(body_v, &body_path, &inner, depth + k)?;
                let mut e = combine(guard, body);
                for (ty, lo, hi) in ranges.into_iter().rev() {
                    e = quant(ty, lo, hi, e);
                }
                e
            }
            Over::List(st, max, cs) => {
                let (len, rows) = list_parts(enums, &st, max, &cs);
                let i = C::Local(depth);
                let w = st.width(enums);
                let picked = select(&rows, &i, &defaults(enums, &st));
                let x: Vec<C> = (depth + 1..depth + 1 + w).map(C::Local).collect();
                let mut inner = sc.to_vec();
                inner.push(Bound {
                    name,
                    ty: st.xtype(),
                    slots: x,
                });
                let body = self.bool_in(body_v, &body_path, &inner, depth + 1 + w)?;
                let body = Block::wrap(&picked, body);
                let guard = bin(BinOp::Lt, i, len);
                let (lo, hi) = if max == 0 { (0, -1) } else { (0, max as i64 - 1) };
                quant(Type::Int(0, max.max(1) as i64 - 1), lo, hi, combine(guard, body))
            }
        };
        Ok((XType::Bool, vec![blk.keep(e)]))
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
