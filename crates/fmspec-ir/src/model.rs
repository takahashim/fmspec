//! IRのJSONを読み込み、名前を添字に解決して、中核のモデルを組み立てる。

use crate::canonical;
use crate::json::{array, index, object, optional_array, required, schema, source, string, unique, Res};
use crate::resolve::{self, Constant, Ctx, Fields, Layout};
use crate::type_syntax::parse_type;
use crate::types::SType;
use crate::IR_VERSION;
use fmspec_core::eval::ErrKind;
use fmspec_core::gate::{validate, CheckedModel};
use fmspec_core::model::{RawModel, Value as CoreValue};
use fmspec_core::model_lower::{lower_model, MAX_INITIAL_CANDIDATES};
use fmspec_core::smodel::{Fault, LowerError, SAction, SConst, SContract, SModel, SOutput, SUpdate};
use fmspec_core::source::TExpr;
use fmspec_core::typing::InvalidModel;
use serde_json::{json, Value};
use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

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
    checked: Arc<CheckedModel>,
}

impl Model {
    pub fn checked(&self) -> &CheckedModel {
        &self.checked
    }

    /// 検証済みのモデルを共有する。Model-Based Testing のセッションが保持する。
    pub fn shared(&self) -> Arc<CheckedModel> {
        Arc::clone(&self.checked)
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

/// 名前解決の結果を読み込みの結果にする。型の誤りには、どの定義で起きたかを `site` で付ける。
fn resolved<T>(r: resolve::Res<T>, site: impl FnOnce(String) -> LoadError) -> Res<T> {
    match r {
        Ok(x) => Ok(x),
        Err(resolve::Error::Schema(e)) => Err(e),
        Err(resolve::Error::Type(detail)) => Err(site(detail)),
    }
}

fn invalid(reason: InvalidModel, message: String) -> LoadError {
    LoadError::Invalid { reason, message }
}

/// 局所変数のない環境に置く値を名前解決する（初期値と定数）。値は中核の下ろしが評価する。
fn stored_tree(ctx: &Ctx, v: &Value, path: &str, st: &SType) -> Result<TExpr, LoadError> {
    resolved(ctx.stored(v, path, st), |detail| LoadError::Schema {
        path: path.to_string(),
        message: format!("初期値の型が状態変数の型と合いません（{detail}）"),
    })
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
        out.types.push(parse_type(
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

fn arg_names_at<'n>(params: &'n [String], choices: &'n [String], i: usize) -> &'n str {
    params.iter().chain(choices).nth(i).map(String::as_str).unwrap_or("?")
}

/// 操作を読む。`base` は状態を参照できる文脈で、これに操作の引数を加えて名前解決する。
fn parse_action(v: &Value, path: &str, a: usize, base: &Ctx, state_names: &[String]) -> Res<(ActionNames, SAction)> {
    let enums = base.enums;
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
    // 公開引数のスロット数。
    let n_param_slots = arg_types.iter().map(|t| t.width(enums)).sum();
    arg_types.extend(choice_types);
    domains.extend(choice_domains);
    let args = layouts(enums, &arg_types);
    let ctx = Ctx {
        args: &args,
        n_params: n_user_params,
        ..*base
    };
    let user_guard = match map.get("guard") {
        None | Some(Value::Null) => TExpr::Lit(CoreValue::Bool(true)),
        Some(g) => resolved(ctx.prop(g, &format!("{path}.guard")), |d| {
            invalid(
                InvalidModel::Guard(a),
                format!("操作 {name:?} の guard が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?,
    };
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
                    "操作 {name:?} のの引数 {:?} のドメインが不正です（{d}）",
                    arg_names_at(&params, &choices, i)
                ),
            )
        };
        let before = Ctx {
            args: &args[..i],
            n_params: n_user_params.min(i),
            ..ctx
        };
        resolved(before.prop(&json!({"is_empty": [domain]}), &dpath), fail)?;
        let me = if i < n_user_params {
            json!({"param": i})
        } else {
            json!({"choice": i - n_user_params})
        };
        members.push(resolved(ctx.prop(&json!({"contains": [domain, me]}), &dpath), fail)?);
    }
    // 正規形でない引数の組を無効にする判定は、中核の下ろしがこの guard の前に置く。
    let guard = if members.is_empty() {
        user_guard
    } else {
        members.push(user_guard);
        TExpr::Fold(true, members)
    };
    let (updates, owners) = parse_updates(optional_array(map, path, "updates")?, path, a, &name, &ctx, state_names)?;
    let (output, output_type) = match map.get("output") {
        None | Some(Value::Null) => (None, None),
        Some(o) => {
            let (output, st) = parse_output(o, &format!("{path}.output"), a, &name, &ctx)?;
            (Some(output), Some(st))
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
        SAction {
            n_params: n_param_slots,
            args: args.iter().map(|l| ctx.fields.stype(&l.ty)).collect(),
            guard,
            updates,
            output,
        },
    ))
}

/// 操作の更新を読む。中核の更新と、その各スロットがどの更新に当たるかを返す。
fn parse_updates(
    items: &[Value],
    path: &str,
    a: usize,
    name: &str,
    ctx: &Ctx,
    state_names: &[String],
) -> Res<(Vec<SUpdate>, Vec<UpdateSlot>)> {
    let states = ctx.states.unwrap_or(&[]);
    let mut updates = Vec::new();
    let mut owners = Vec::new();
    for (u, item) in items.iter().enumerate() {
        let path = format!("{path}.updates[{u}]");
        let up = object(item, &path, &["target", "expr"])?;
        let target = index(required(up, &path, "target")?, &format!("{path}.target"))?;
        let Some(l) = states.get(target) else {
            return Err(invalid(
                InvalidModel::Update(a, u),
                format!("操作 {name:?} の {} 番目の更新の対象 {target} は未定義です", u + 1),
            ));
        };
        let expr = resolved(
            ctx.stored(required(up, &path, "expr")?, &format!("{path}.expr"), &l.ty),
            |d| {
                invalid(
                    InvalidModel::Update(a, u),
                    format!(
                        "操作 {name:?} の {} 番目の更新（{:?}）が不正です（{d}）",
                        u + 1,
                        state_names[target]
                    ),
                )
            },
        )?;
        owners.extend((0..l.ty.width(ctx.enums)).map(|slot| UpdateSlot {
            update: u,
            var: target,
            slot,
        }));
        updates.push(SUpdate { var: target, expr });
    }
    Ok((updates, owners))
}

/// 操作の出力を読む。出力の型はスカラー型に限る。
fn parse_output(v: &Value, path: &str, a: usize, name: &str, ctx: &Ctx) -> Res<(SOutput, SType)> {
    let out = object(v, path, &["type", "expr"])?;
    let st = parse_type(required(out, path, "type")?, &format!("{path}.type"), ctx.enums)?;
    if st.core().is_none() {
        return schema(&format!("{path}.type"), "出力の型は bool、int、enum に限ります");
    }
    let expr = resolved(
        ctx.stored(required(out, path, "expr")?, &format!("{path}.expr"), &st),
        |d| {
            invalid(
                InvalidModel::Output(a),
                format!("操作 {name:?} の出力の型または式が不正です（{d}）"),
            )
        },
    )?;
    let ty = ctx.fields.stype(&st);
    Ok((SOutput { ty, expr }, st))
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
    let enums = parse_enums(optional_array(map, path, "enums")?)?;
    let fields = Fields::default();
    let (constants, sconsts) = parse_constants(optional_array(map, path, "constants")?, &enums, &fields)?;
    let closed = Ctx::closed(&enums, &constants, &fields);
    let states = parse_states(array(required(map, path, "states")?, "$.states")?, &closed)?;
    let state_layouts = layouts(&enums, &states.types);
    let ctx = Ctx {
        states: Some(&state_layouts),
        ..closed
    };
    let constraint = match map.get("initial_constraint").filter(|e| !e.is_null()) {
        None => None,
        Some(e) => {
            let path = "$.initial_constraint";
            Some(resolved(ctx.prop(e, path), |d| LoadError::Schema {
                path: path.to_string(),
                message: format!("初期条件が Bool 式でないか、未定義の参照を含みます（{d}）"),
            })?)
        }
    };

    let mut action_names = Vec::new();
    let mut actions = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in optional_array(map, path, "actions")?.iter().enumerate() {
        let path = format!("$.actions[{i}]");
        let (names, action) = parse_action(item, &path, i, &ctx, &states.names)?;
        unique(&mut seen, &names.name, &path, "操作")?;
        action_names.push(names);
        actions.push(action);
    }

    let invariants = parse_invariants(optional_array(map, path, "invariants")?, &ctx)?;
    let contracts = parse_contracts(optional_array(map, path, "contracts")?, &ctx, &action_names)?;

    let terminal = match map.get("terminal") {
        None | Some(Value::Null) => None,
        Some(t) => Some(resolved(ctx.prop(t, "$.terminal"), |d| {
            invalid(
                InvalidModel::Terminal,
                format!("終端条件が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?),
    };

    let sm = SModel {
        enums: enums.iter().map(|e| e.variants.len() as i64).collect(),
        consts: sconsts,
        states: states.types.iter().map(|t| fields.stype(t)).collect(),
        inits: states.inits,
        constraint,
        actions,
        invariants: invariants.items,
        contracts: contracts.items,
        terminal,
    };
    let names = Names {
        model: model_name,
        enums,
        states: states.names,
        state_offsets: state_layouts.iter().map(|l| l.offset).collect(),
        state_types: states.types,
        state_sources: states.sources,
        actions: action_names,
        invariants: invariants.names,
        invariant_sources: invariants.sources,
        contracts: contracts.names,
        contract_sources: contracts.sources,
    };
    let raw = lower_model(&sm).map_err(|e| lower_error(e, &names, &constants, &states.init_paths))?;
    Ok((raw, names, canonical::digest(&root)))
}

fn parse_enums(items: &[Value]) -> Res<Vec<EnumNames>> {
    let mut enums = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in items.iter().enumerate() {
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
    Ok(enums)
}

/// 定数を読む。定数の値の式は、それより前の定数だけを参照できる。
fn parse_constants(items: &[Value], enums: &[EnumNames], fields: &Fields) -> Res<(Vec<Constant>, Vec<SConst>)> {
    let mut constants: Vec<Constant> = Vec::new();
    let mut sconsts = Vec::new();
    let mut seen = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        let path = format!("$.constants[{i}]");
        let c = object(item, &path, &["name", "type", "value"])?;
        let name = string(required(c, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "定数")?;
        let ty = parse_type(required(c, &path, "type")?, &format!("{path}.type"), enums)?;
        let ctx = Ctx::closed(enums, &constants, fields);
        let expr = stored_tree(&ctx, required(c, &path, "value")?, &format!("{path}.value"), &ty)?;
        sconsts.push(SConst {
            ty: fields.stype(&ty),
            expr,
        });
        constants.push(Constant { name, ty });
    }
    Ok((constants, sconsts))
}

/// 状態変数の宣言。
struct States {
    names: Vec<String>,
    types: Vec<SType>,
    sources: Vec<Option<Source>>,
    /// 状態変数ごとの初期値の候補と、その位置。
    inits: Vec<Vec<TExpr>>,
    init_paths: Vec<Vec<String>>,
}

fn parse_states(items: &[Value], ctx: &Ctx) -> Res<States> {
    let mut out = States {
        names: Vec::new(),
        types: Vec::new(),
        sources: Vec::new(),
        inits: Vec::new(),
        init_paths: Vec::new(),
    };
    let mut seen = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        let path = format!("$.states[{i}]");
        let s = object(item, &path, &["id", "name", "type", "initial", "initial_in", "source"])?;
        if let Some(id) = s.get("id") {
            if index(id, &format!("{path}.id"))? != i {
                return schema(&format!("{path}.id"), format!("id は定義順の添字 {i} と一致させます"));
            }
        }
        let name = string(required(s, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "状態変数")?;
        let ty = parse_type(required(s, &path, "type")?, &format!("{path}.type"), ctx.enums)?;
        let candidates: Vec<(String, &Value)> = match (s.get("initial"), s.get("initial_in")) {
            (Some(v), None) => vec![(format!("{path}.initial"), v)],
            (None, Some(vs)) => {
                let path = format!("{path}.initial_in");
                let vs = array(vs, &path)?;
                if vs.is_empty() {
                    return schema(&path, "initial_in は空でない配列です");
                }
                vs.iter()
                    .enumerate()
                    .map(|(j, v)| (format!("{path}[{j}]"), v))
                    .collect()
            }
            _ => return schema(&path, "initial と initial_in のどちらか一方を書きます"),
        };
        let mut exprs = Vec::new();
        for (p, v) in &candidates {
            exprs.push(stored_tree(ctx, v, p, &ty)?);
        }
        out.inits.push(exprs);
        out.init_paths.push(candidates.into_iter().map(|(p, _)| p).collect());
        out.types.push(ty);
        out.sources.push(source(s, &path)?);
        out.names.push(name);
    }
    Ok(out)
}

/// 名前付きの定義（不変条件と遷移契約）の、名前、ソース位置、中身。
struct Defs<T> {
    names: Vec<String>,
    sources: Vec<Option<Source>>,
    items: Vec<T>,
}

impl<T> Defs<T> {
    fn new() -> Self {
        Defs {
            names: Vec::new(),
            sources: Vec::new(),
            items: Vec::new(),
        }
    }

    fn push(&mut self, name: String, source: Option<Source>, item: T) {
        self.names.push(name);
        self.sources.push(source);
        self.items.push(item);
    }
}

fn parse_invariants(items: &[Value], ctx: &Ctx) -> Res<Defs<TExpr>> {
    let mut out = Defs::new();
    let mut seen = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        let path = format!("$.invariants[{i}]");
        let inv = object(item, &path, &["name", "expr", "source"])?;
        let name = string(required(inv, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "不変条件")?;
        let expr = resolved(ctx.prop(required(inv, &path, "expr")?, &format!("{path}.expr")), |d| {
            invalid(
                InvalidModel::Invariant(i),
                format!("不変条件 {name:?} が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?;
        out.push(name, source(inv, &path)?, expr);
    }
    Ok(out)
}

/// 遷移契約を読む。遷移契約は、対象の操作の引数と出力、遷移後の状態を参照できる。
fn parse_contracts(items: &[Value], ctx: &Ctx, actions: &[ActionNames]) -> Res<Defs<SContract>> {
    let mut out = Defs::new();
    let mut seen = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        let path = format!("$.contracts[{i}]");
        let con = object(item, &path, &["name", "action", "expr", "source"])?;
        let name = string(required(con, &path, "name")?, &format!("{path}.name"))?;
        unique(&mut seen, &name, &path, "遷移契約")?;
        let action_name = string(required(con, &path, "action")?, &format!("{path}.action"))?;
        let Some(action) = actions.iter().position(|a| a.name == action_name) else {
            return schema(&format!("{path}.action"), format!("未定義の操作 {action_name:?}"));
        };
        let act = &actions[action];
        let args = layouts(ctx.enums, &act.arg_types);
        let cctx = Ctx {
            args: &args,
            n_params: act.params.len(),
            next: true,
            output: act.output.as_ref(),
            ..*ctx
        };
        let expr = resolved(cctx.prop(required(con, &path, "expr")?, &format!("{path}.expr")), |d| {
            invalid(
                InvalidModel::Contract(i),
                format!("遷移契約 {name:?} が Bool 式でないか、未定義の参照を含みます（{d}）"),
            )
        })?;
        out.push(name, source(con, &path)?, SContract { action, expr });
    }
    Ok(out)
}

/// 中核の下ろしの失敗を、読み込みの誤りにする。
/// 型の誤りと未定義の参照は名前解決で報告するので、残るのは値の評価の失敗と、型の不正である。
fn lower_error(e: LowerError, names: &Names, constants: &[Constant], choice_paths: &[Vec<String>]) -> LoadError {
    let internal = |path: &str| LoadError::Schema {
        path: path.to_string(),
        message: "内部エラー: 中核の下ろしが式を受理しません".to_string(),
    };
    let too_deep = |path: &str| LoadError::Schema {
        path: path.to_string(),
        message: "式が大きすぎます（局所変数の束縛が深すぎます）".to_string(),
    };
    let eval = |path: &str, k: ErrKind| LoadError::Schema {
        path: path.to_string(),
        message: format!("値を評価できません（{k:?}）"),
    };
    let reason = |r: InvalidModel| invalid(r, describe(&r, names));
    match e {
        LowerError::State(i) => reason(InvalidModel::StateType(i)),
        LowerError::Const(i, f) => {
            let path = format!("$.constants[{i}].value");
            match f {
                Fault::Lower => internal(&path),
                Fault::Depth => too_deep(&path),
                Fault::Eval(ErrKind::OutOfRange(x)) => LoadError::Schema {
                    message: format!("定数 {:?} の値 {x} が型の範囲の外です", constants[i].name),
                    path,
                },
                Fault::Eval(k) => eval(&path, k),
            }
        }
        LowerError::Init(i, j, f) => {
            let path = &choice_paths[i][j];
            match f {
                Fault::Lower => internal(path),
                Fault::Depth => too_deep(path),
                Fault::Eval(ErrKind::OutOfRange(x)) => invalid(
                    InvalidModel::Initial(j),
                    format!(
                        "{path}: 状態変数 {:?} の初期値 {x} が型の範囲外です",
                        names.states.get(i).map(String::as_str).unwrap_or("?")
                    ),
                ),
                Fault::Eval(k) => eval(path, k),
            }
        }
        LowerError::InitCount => LoadError::Schema {
            path: "$.states".to_string(),
            message: format!("初期値の候補の組み合わせが {MAX_INITIAL_CANDIDATES} 個を超えます"),
        },
        LowerError::Constraint(Fault::Lower) => internal("$.initial_constraint"),
        LowerError::Constraint(Fault::Depth) => too_deep("$.initial_constraint"),
        LowerError::Constraint(Fault::Eval(k)) => LoadError::Schema {
            path: "$.initial_constraint".to_string(),
            message: format!("初期条件を評価できません（{k:?}）"),
        },
        LowerError::NoInit => LoadError::Schema {
            path: "$.initial_constraint".to_string(),
            message: "初期条件を満たす初期状態がありません".to_string(),
        },
        LowerError::Args(a, d) => reason(InvalidModel::Domain(a, d)),
        LowerError::Guard(a) => reason(InvalidModel::Guard(a)),
        LowerError::Update(a, u) => reason(InvalidModel::Update(a, u)),
        LowerError::Output(a) => reason(InvalidModel::Output(a)),
        LowerError::Invariant(i) => reason(InvalidModel::Invariant(i)),
        LowerError::Contract(k) => reason(InvalidModel::Contract(k)),
        LowerError::Terminal => reason(InvalidModel::Terminal),
        LowerError::Type => LoadError::Schema {
            path: "$".to_string(),
            message: "内部エラー: fmspec-ir と中核の型検査が食い違います".to_string(),
        },
        LowerError::Depth => too_deep("$"),
    }
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
        Ok(checked) => Ok(Model {
            names,
            digest,
            checked: Arc::new(checked),
        }),
        Err(reason) => {
            let reason = user_reason(reason, &names);
            Err(LoadError::Invalid {
                message: describe(&reason, &names),
                reason,
            })
        }
    }
}
