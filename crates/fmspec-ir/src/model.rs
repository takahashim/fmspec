//! IRのJSONを読み込み、名前を添字に解決して、中核のモデルを組み立てる。

use crate::canonical;
use crate::json::{array, index, object, optional_array, required, schema, source, string, unique, Res};
use crate::lower::{self, Constant, Ctx, Layout};
use crate::types::SType;
use crate::IR_VERSION;
use fmspec_core::gate::{validate, CheckedModel};
use fmspec_core::model::{Action, Contract, Expr, Output, RawModel, Type, Update, Value as CoreValue};
use fmspec_core::typing::InvalidModel;
use serde_json::Value;
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

/// 中核の更新が、どの更新のどのスロットに当たるか。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpdateSlot {
    /// IRの更新の添字。
    pub update: usize,
    /// 更新する状態変数。
    pub var: usize,
    /// 状態変数の中のスロットの添字。
    pub slot: usize,
}

#[derive(Clone, Debug)]
pub struct ActionNames {
    pub name: String,
    pub params: Vec<String>,
    pub choices: Vec<String>,
    /// 公開引数に続けて内部選択の型。
    pub arg_types: Vec<SType>,
    /// 各引数の、中核の引数の列での最初のスロット。
    pub arg_offsets: Vec<usize>,
    pub output: Option<SType>,
    /// 中核の更新ごとの、IRの更新とスロット。
    pub updates: Vec<UpdateSlot>,
    pub source: Option<Source>,
}

impl ActionNames {
    /// 引数の名前。公開引数に続けて内部選択。
    pub fn arg_names(&self) -> impl Iterator<Item = &String> {
        self.params.iter().chain(self.choices.iter())
    }

    /// 中核の引数のスロットが、どの引数のどのスロットか。
    pub fn arg_of_slot(&self, slot: usize) -> Option<(usize, usize)> {
        let i = self.arg_offsets.iter().rposition(|o| *o <= slot)?;
        Some((i, slot - self.arg_offsets[i]))
    }
}

/// 添字に解決する前の名前。中核のモデルは名前を持たないので、表示と直列化のためにここで持つ。
#[derive(Clone, Debug)]
pub struct Names {
    pub model: String,
    pub enums: Vec<EnumNames>,
    pub states: Vec<String>,
    pub state_types: Vec<SType>,
    /// 各状態変数の、状態のスロットの列での最初のスロット。
    pub state_offsets: Vec<usize>,
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

    pub fn state_index(&self, name: &str) -> Option<usize> {
        self.states.iter().position(|n| n == name)
    }

    /// 状態のスロットが、どの状態変数のどのスロットか。
    pub fn state_of_slot(&self, slot: usize) -> Option<(usize, usize)> {
        let i = self.state_offsets.iter().rposition(|o| *o <= slot)?;
        Some((i, slot - self.state_offsets[i]))
    }

    /// 状態変数のスロットの範囲。
    pub fn state_slots(&self, var: usize) -> std::ops::Range<usize> {
        let start = self.state_offsets[var];
        start..start + self.state_types[var].width(&self.enums)
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

fn lowered<T>(r: lower::Res<T>, site: impl FnOnce(String) -> LoadError) -> Res<T> {
    match r {
        Ok(x) => Ok(x),
        Err(lower::Error::Schema(e)) => Err(e),
        Err(lower::Error::Type(detail)) => Err(site(detail)),
    }
}

fn invalid(reason: InvalidModel, message: String) -> LoadError {
    LoadError::Invalid { reason, message }
}

fn parse_stype(v: &Value, path: &str, enums: &[EnumNames]) -> Res<SType> {
    lowered(lower::parse_type(v, path, enums), |detail| LoadError::Schema {
        path: path.to_string(),
        message: detail,
    })
}

/// 局所変数のない環境で値を評価し、スロットごとの符号にする（初期値と定数）。
fn constant_codes(ctx: &Ctx, v: &Value, path: &str, st: &SType) -> Result<Vec<i64>, LoadError> {
    let slots = lowered(ctx.stored(v, path, st, 0), |detail| LoadError::Schema {
        path: path.to_string(),
        message: format!("初期値の型が状態変数の型と合いません（{detail}）"),
    })?;
    let mut tys = Vec::new();
    st.slot_types(ctx.enums, &mut tys);
    let mut codes = Vec::new();
    for (e, ty) in slots.iter().zip(&tys) {
        match lower::eval_const(e, ty) {
            Ok(x) => codes.push(x),
            Err(kind) => return schema(path, format!("値を評価できません（{kind:?}）")),
        }
    }
    Ok(codes)
}

/// 初期値の候補の組み合わせのうち、調べる数の上限。
pub const MAX_INITIAL_CANDIDATES: usize = 1 << 20;

/// 初期状態の集合。状態変数ごとの候補の直積から、`initial_constraint` を満たすものを残し、
/// 符号化列の辞書順に整列して重複を除く。
fn initial_states(
    choices: &[Vec<Vec<i64>>],
    state_types: &Vec<Type>,
    enums: &[EnumNames],
    layouts: &[Layout],
    constants: &[Constant],
    map: &serde_json::Map<String, Value>,
) -> Res<Vec<Vec<i64>>> {
    let total = choices.iter().try_fold(1usize, |n, c| {
        n.checked_mul(c.len()).filter(|n| *n <= MAX_INITIAL_CANDIDATES)
    });
    if total.is_none() {
        return schema(
            "$.states",
            format!("初期値の候補の組み合わせが {MAX_INITIAL_CANDIDATES} 個を超えます"),
        );
    }
    let mut inits: Vec<Vec<i64>> = vec![Vec::new()];
    for c in choices {
        inits = inits
            .iter()
            .flat_map(|prefix| c.iter().map(move |codes| [prefix.as_slice(), codes].concat()))
            .collect();
    }
    if let Some(e) = map.get("initial_constraint").filter(|e| !e.is_null()) {
        let no_args: Vec<Layout> = Vec::new();
        let ctx = Ctx {
            enums,
            states: Some(layouts),
            args: &no_args,
            n_params: 0,
            next: false,
            output: None,
            constants,
        };
        let path = "$.initial_constraint";
        let expr = lowered(ctx.prop(e, path), |d| LoadError::Schema {
            path: path.to_string(),
            message: format!("初期条件が Bool 式でないか、未定義の参照を含みます（{d}）"),
        })?;
        let mut kept = Vec::new();
        for s in inits {
            let no_tys: Vec<Type> = Vec::new();
            let no_vals: Vec<i64> = Vec::new();
            let ctx = fmspec_core::eval::Ctx {
                st_tys: state_types,
                arg_tys: &no_tys,
                pre: &s,
                args: &no_vals,
                post: &no_vals,
                out: None,
            };
            match fmspec_core::eval::eval_prop(&expr, &ctx) {
                Ok(true) => kept.push(s),
                Ok(false) => {}
                Err(kind) => return schema(path, format!("初期条件を評価できません（{kind:?}）")),
            }
        }
        inits = kept;
    }
    if inits.is_empty() {
        return schema("$.initial_constraint", "初期条件を満たす初期状態がありません");
    }
    inits.sort();
    inits.dedup();
    Ok(inits)
}

/// 引数の宣言。`domain` は動的ドメイン（`in`）の式。
struct Bindings<'v> {
    names: Vec<String>,
    types: Vec<SType>,
    domains: Vec<Option<&'v Value>>,
}

fn parse_bindings<'v>(
    items: &'v [Value],
    path: &str,
    enums: &[EnumNames],
    seen: &mut HashSet<String>,
) -> Res<Bindings<'v>> {
    let mut out = Bindings {
        names: Vec::new(),
        types: Vec::new(),
        domains: Vec::new(),
    };
    for (i, item) in items.iter().enumerate() {
        let path = format!("{path}[{i}]");
        let map = object(item, &path, &["name", "type", "in"])?;
        let name = string(required(map, &path, "name")?, &format!("{path}.name"))?;
        unique(seen, &name, &path, "引数")?;
        out.types.push(parse_stype(
            required(map, &path, "type")?,
            &format!("{path}.type"),
            enums,
        )?);
        out.names.push(name);
        out.domains.push(map.get("in"));
    }
    Ok(out)
}

fn layouts(enums: &[EnumNames], types: &[SType]) -> Vec<Layout> {
    let mut offset = 0;
    types
        .iter()
        .map(|ty| {
            let l = Layout { ty: ty.clone(), offset };
            offset += ty.width(enums);
            l
        })
        .collect()
}

fn slot_types(enums: &[EnumNames], types: &[SType]) -> Vec<Type> {
    let mut out = Vec::new();
    for t in types {
        t.slot_types(enums, &mut out);
    }
    out
}

fn arg_names_at<'n>(params: &'n [String], choices: &'n [String], i: usize) -> &'n str {
    params.iter().chain(choices).nth(i).map(String::as_str).unwrap_or("?")
}

struct Parsed<'a> {
    enums: &'a [EnumNames],
    states: &'a [Layout],
    state_names: &'a [String],
    constants: &'a [Constant],
}

fn parse_action(v: &Value, path: &str, a: usize, p: &Parsed) -> Res<(ActionNames, Action)> {
    let enums = p.enums;
    let map = object(
        v,
        path,
        &["name", "params", "choices", "guard", "updates", "output", "source"],
    )?;
    let name = string(required(map, path, "name")?, &format!("{path}.name"))?;
    let mut seen = HashSet::new();
    let Bindings {
        names: params,
        types: mut arg_types,
        mut domains,
    } = parse_bindings(
        optional_array(map, path, "params")?,
        &format!("{path}.params"),
        enums,
        &mut seen,
    )?;
    let Bindings {
        names: choices,
        types: choice_types,
        domains: choice_domains,
    } = parse_bindings(
        optional_array(map, path, "choices")?,
        &format!("{path}.choices"),
        enums,
        &mut seen,
    )?;
    let n_user_params = arg_types.len();
    arg_types.extend(choice_types);
    domains.extend(choice_domains);
    let args = layouts(enums, &arg_types);
    let n_params = args
        .get(n_user_params)
        .map(|l| l.offset)
        .unwrap_or_else(|| args.last().map(|l| l.offset + l.ty.width(enums)).unwrap_or(0));
    let ctx = Ctx {
        enums,
        states: Some(p.states),
        args: &args,
        n_params: n_user_params,
        next: false,
        output: None,
        constants: p.constants,
    };
    let what = |kind: &str| format!("操作 {name:?} の{kind}");
    let user_guard = match map.get("guard") {
        None | Some(Value::Null) => Expr::Const(CoreValue::Bool(true)),
        Some(g) => lowered(ctx.prop(g, &format!("{path}.guard")), |d| {
            invalid(
                InvalidModel::Guard(a),
                format!("{}が Bool 式でないか、未定義の参照を含みます（{d}）", what(" guard ")),
            )
        })?,
    };
    // スロットごとに列挙した引数の組のうち、正規形でないものは無効にする。
    let mut canon = Vec::new();
    for l in &args {
        let slots: Vec<Expr> = (l.offset..l.offset + l.ty.width(enums)).map(Expr::Arg).collect();
        let c = lower::canonical(enums, &l.ty, &slots);
        if !matches!(c, Expr::Const(CoreValue::Bool(true))) {
            canon.push(c);
        }
    }
    // 動的ドメイン。引数がドメインの式の値に含まれなければ、その組は無効にする。
    // ドメインの式は、状態と、それより前の引数だけを参照できる。
    let mut members = Vec::new();
    for (i, domain) in domains.iter().enumerate() {
        let Some(domain) = domain else { continue };
        let (kind, j) = if i < n_user_params {
            ("params", i)
        } else {
            ("choices", i - n_user_params)
        };
        let dpath = format!("{path}.{kind}[{j}].in");
        let fail = |d: String| {
            invalid(
                InvalidModel::Guard(a),
                format!(
                    "{}の引数 {:?} のドメインが不正です（{d}）",
                    what(""),
                    arg_names_at(&params, &choices, i)
                ),
            )
        };
        let before = Ctx {
            args: &args[..i],
            n_params: n_user_params.min(i),
            ..ctx
        };
        lowered(before.prop(&serde_json::json!({"is_empty": [domain]}), &dpath), fail)?;
        let me = if i < n_user_params {
            serde_json::json!({"param": i})
        } else {
            serde_json::json!({"choice": i - n_user_params})
        };
        members.push(lowered(
            ctx.prop(&serde_json::json!({"contains": [domain, me]}), &dpath),
            fail,
        )?);
    }
    let guard = members
        .into_iter()
        .rev()
        .fold(user_guard, |acc, c| Expr::And(Box::new(c), Box::new(acc)));
    let guard = canon
        .into_iter()
        .rev()
        .fold(guard, |acc, c| Expr::And(Box::new(c), Box::new(acc)));
    let mut updates = Vec::new();
    let mut owners = Vec::new();
    for (u, item) in optional_array(map, path, "updates")?.iter().enumerate() {
        let path = format!("{path}.updates[{u}]");
        let up = object(item, &path, &["target", "expr"])?;
        let target = index(required(up, &path, "target")?, &format!("{path}.target"))?;
        let Some(l) = p.states.get(target) else {
            return Err(invalid(
                InvalidModel::Update(a, u),
                format!("{} {} 番目の更新の対象 {target} は未定義です", what(""), u + 1),
            ));
        };
        let slots = lowered(
            ctx.stored(required(up, &path, "expr")?, &format!("{path}.expr"), &l.ty, 0),
            |d| {
                invalid(
                    InvalidModel::Update(a, u),
                    format!(
                        "{} {} 番目の更新（{:?}）が不正です（{d}）",
                        what(""),
                        u + 1,
                        p.state_names[target]
                    ),
                )
            },
        )?;
        for (j, expr) in slots.into_iter().enumerate() {
            updates.push(Update {
                target: l.offset + j,
                expr,
            });
            owners.push(UpdateSlot {
                update: u,
                var: target,
                slot: j,
            });
        }
    }
    let (output, output_type) = match map.get("output") {
        None | Some(Value::Null) => (None, None),
        Some(o) => {
            let path = format!("{path}.output");
            let out = object(o, &path, &["type", "expr"])?;
            let st = parse_stype(required(out, &path, "type")?, &format!("{path}.type"), enums)?;
            let Some(ty) = st.core() else {
                return schema(&format!("{path}.type"), "出力の型は bool、int、enum に限ります");
            };
            let mut slots = lowered(
                ctx.stored(required(out, &path, "expr")?, &format!("{path}.expr"), &st, 0),
                |d| {
                    invalid(
                        InvalidModel::Output(a),
                        format!("{}出力の型または式が不正です（{d}）", what("")),
                    )
                },
            )?;
            let expr = slots.pop().unwrap_or(Expr::Const(CoreValue::Bool(false)));
            (Some(Output { ty, expr }), Some(st))
        }
    };
    let names = ActionNames {
        name,
        params,
        choices,
        arg_offsets: args.iter().map(|l| l.offset).collect(),
        arg_types,
        output: output_type,
        updates: owners,
        source: source(map, path)?,
    };
    Ok((
        names,
        Action {
            n_params,
            domains: slot_types(enums, &args.iter().map(|l| l.ty.clone()).collect::<Vec<_>>()),
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
            "constants",
            "states",
            "actions",
            "invariants",
            "contracts",
            "terminal",
            "initial_constraint",
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

    let no_args: Vec<Layout> = Vec::new();
    let mut constants: Vec<Constant> = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "constants")?.iter().enumerate() {
        let path = format!("$.constants[{i}]");
        let c = object(item, &path, &["name", "type", "value"])?;
        let name = string(required(c, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "定数")?;
        let ty = parse_stype(required(c, &path, "type")?, &format!("{path}.type"), &enums)?;
        let ctx = Ctx {
            enums: &enums,
            states: None,
            args: &no_args,
            n_params: 0,
            next: false,
            output: None,
            constants: &constants,
        };
        let codes = constant_codes(&ctx, required(c, &path, "value")?, &format!("{path}.value"), &ty)?;
        let mut tys = Vec::new();
        ty.slot_types(&enums, &mut tys);
        if let Some(x) = tys.iter().zip(&codes).find_map(|(t, x)| match t {
            Type::Int(lo, hi) if x < lo || x > hi => Some(*x),
            _ => None,
        }) {
            return schema(
                &format!("{path}.value"),
                format!("定数 {name:?} の値 {x} が型の範囲の外です"),
            );
        }
        constants.push(Constant { name, ty, codes });
    }

    let mut states = Vec::new();
    let mut state_sources = Vec::new();
    let mut state_stypes = Vec::new();
    // 状態変数ごとの初期値の候補。
    let mut choices: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in array(required(map, path, "states")?, "$.states")?.iter().enumerate() {
        let path = format!("$.states[{i}]");
        let s = object(item, &path, &["id", "name", "type", "initial", "initial_in", "source"])?;
        if let Some(id) = s.get("id") {
            if index(id, &format!("{path}.id"))? != i {
                return schema(&format!("{path}.id"), format!("id は定義順の添字 {i} と一致させます"));
            }
        }
        let name = string(required(s, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "状態変数")?;
        let ty = parse_stype(required(s, &path, "type")?, &format!("{path}.type"), &enums)?;
        let ctx = Ctx {
            enums: &enums,
            states: None,
            args: &no_args,
            n_params: 0,
            next: false,
            output: None,
            constants: &constants,
        };
        choices.push(match (s.get("initial"), s.get("initial_in")) {
            (Some(v), None) => vec![constant_codes(&ctx, v, &format!("{path}.initial"), &ty)?],
            (None, Some(vs)) => {
                let path = format!("{path}.initial_in");
                let vs = array(vs, &path)?;
                if vs.is_empty() {
                    return schema(&path, "initial_in は空でない配列です");
                }
                vs.iter()
                    .enumerate()
                    .map(|(j, v)| constant_codes(&ctx, v, &format!("{path}[{j}]"), &ty))
                    .collect::<Res<_>>()?
            }
            _ => return schema(&path, "initial と initial_in のどちらか一方を書きます"),
        });
        state_stypes.push(ty);
        state_sources.push(source(s, &path)?);
        states.push(name);
    }
    let state_layouts = layouts(&enums, &state_stypes);
    let state_types = slot_types(&enums, &state_stypes);
    let inits = initial_states(&choices, &state_types, &enums, &state_layouts, &constants, map)?;
    let parsed = Parsed {
        enums: &enums,
        states: &state_layouts,
        state_names: &states,
        constants: &constants,
    };

    let mut action_names = Vec::new();
    let mut actions = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "actions")?.iter().enumerate() {
        let path = format!("$.actions[{i}]");
        let (names, action) = parse_action(item, &path, i, &parsed)?;
        unique(&mut seen, &names.name, &path, "操作")?;
        action_names.push(names);
        actions.push(action);
    }

    let ctx = Ctx {
        enums: &enums,
        states: Some(&state_layouts),
        args: &no_args,
        n_params: 0,
        next: false,
        output: None,
        constants: &constants,
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
        invariants.push(lowered(
            ctx.prop(required(inv, &path, "expr")?, &format!("{path}.expr")),
            |d| {
                invalid(
                    InvalidModel::Invariant(i),
                    format!("不変条件 {name:?} が Bool 式でないか、未定義の参照を含みます（{d}）"),
                )
            },
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
        let act = &action_names[action];
        let args: Vec<Layout> = act
            .arg_types
            .iter()
            .zip(&act.arg_offsets)
            .map(|(ty, offset)| Layout {
                ty: ty.clone(),
                offset: *offset,
            })
            .collect();
        let cctx = Ctx {
            enums: &enums,
            states: Some(&state_layouts),
            args: &args,
            n_params: act.params.len(),
            next: true,
            output: act.output.as_ref(),
            constants: &constants,
        };
        let expr = lowered(cctx.prop(required(con, &path, "expr")?, &format!("{path}.expr")), |d| {
            invalid(
                InvalidModel::Contract(i),
                format!("遷移契約 {name:?} が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?;
        contracts.push(Contract { action, expr });
        contract_sources.push(source(con, &path)?);
        contract_names.push(name);
    }

    let terminal = match map.get("terminal") {
        None | Some(Value::Null) => None,
        Some(t) => Some(lowered(ctx.prop(t, "$.terminal"), |d| {
            invalid(
                InvalidModel::Terminal,
                format!("終端条件が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?),
    };

    let raw = RawModel {
        enums: enums.iter().map(|e| e.variants.len() as i64).collect(),
        state_types,
        inits,
        actions,
        invariants,
        contracts,
        terminal,
    };
    let names = Names {
        model: model_name,
        enums,
        states,
        state_offsets: state_layouts.iter().map(|l| l.offset).collect(),
        state_types: state_stypes,
        state_sources,
        actions: action_names,
        invariants: invariant_names,
        invariant_sources,
        contracts: contract_names,
        contract_sources,
    };
    Ok((raw, names, canonical::digest(&root)))
}

/// 中核のIR検証が返した理由の添字（スロットと中核の更新）を、IRの定義の添字に戻す。
fn user_reason(reason: InvalidModel, names: &Names) -> InvalidModel {
    let update = |a: usize, k: usize| {
        names
            .actions
            .get(a)
            .and_then(|act| act.updates.get(k))
            .map(|o| o.update)
            .unwrap_or(k)
    };
    match reason {
        InvalidModel::StateType(i) => InvalidModel::StateType(names.state_of_slot(i).map(|(v, _)| v).unwrap_or(i)),
        InvalidModel::Domain(a, d) => InvalidModel::Domain(
            a,
            names
                .actions
                .get(a)
                .and_then(|act| act.arg_of_slot(d))
                .map(|(x, _)| x)
                .unwrap_or(d),
        ),
        InvalidModel::Update(a, k) => InvalidModel::Update(a, update(a, k)),
        InvalidModel::DuplicateUpdate(a, k) => InvalidModel::DuplicateUpdate(a, update(a, k)),
        other => other,
    }
}

fn describe(reason: &InvalidModel, names: &Names) -> String {
    let action = |a: &usize| names.actions[*a].name.as_str();
    match reason {
        InvalidModel::EmptyEnum(i) => format!("列挙型 {:?} にラベルがありません", names.enums[*i].name),
        InvalidModel::StateType(i) => {
            format!(
                "状態変数 {:?} の型が不正です（空の整数範囲、または未定義の列挙型）",
                names.states.get(*i).map(String::as_str).unwrap_or("?")
            )
        }
        InvalidModel::NoInitial => "初期状態がありません".to_string(),
        InvalidModel::Initial(_) => "初期値が状態変数の型の範囲外です".to_string(),
        InvalidModel::Params(a) => format!("操作 {:?} の引数の個数が不正です", action(a)),
        InvalidModel::Domain(a, d) => {
            let act = &names.actions[*a];
            let name = act.arg_names().nth(*d).map(String::as_str).unwrap_or("?");
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
        Err(reason) => {
            let reason = user_reason(reason, &names);
            Err(LoadError::Invalid {
                message: describe(&reason, &names),
                reason,
            })
        }
    }
}
