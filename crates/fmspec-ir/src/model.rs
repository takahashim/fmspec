//! IRのJSONを読み込み、名前を添字に解決して、中核のモデルを組み立てる。

use crate::canonical;
use crate::diagnostics::{describe, lower_error, user_reason};
use crate::json::{array, index, object, optional_array, required, schema, source, string, unique, Res};
use crate::resolve::{self, Constant, Ctx, Fields, Layout};
use crate::type_syntax::parse_type;
use crate::types::SType;
use crate::IR_VERSION;
use fmspec_core::checked::{validate, CheckedModel};
use fmspec_core::expr_copy::copy_expr;
use fmspec_core::ir_check::lower_checked;
use fmspec_core::lower_error::LowerError;
use fmspec_core::model::{Expr, RawModel, Value as CoreValue};
use fmspec_core::model_lower::SMap;
use fmspec_core::smodel::{SAction, SConst, SContract, SModel, SOutput, SUpdate};
use fmspec_core::source::TExpr;
use fmspec_core::sym_check::renamed_eq;
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
    /// 対称性による削減の入れ替え。隣り合うブロックの入れ替えごとの、状態のスロットの置換。
    pub symmetry: Vec<Vec<usize>>,
    /// 宣言した対称性の、グループごとのブロックの数。
    pub symmetry_groups: Vec<usize>,
    /// 中核の不変条件ごとの、元の不変条件の添字。対称性を宣言したモデルでは、不変条件の入れ替えの像を
    /// 元と同じ名前の不変条件として加える。元の不変条件では自分自身の添字である。
    pub invariant_family: Vec<usize>,
}

impl Names {
    pub fn action_index(&self, name: &str) -> Option<usize> {
        self.actions.iter().position(|a| a.name == name)
    }

    /// 不変条件の選択を、入れ替えの像にも広げる。像は、元の不変条件と同じく選ぶ。
    pub fn spread_invariants(&self, mask: &mut [bool]) {
        for (j, &f) in self.invariant_family.iter().enumerate() {
            if f != j && j < mask.len() && f < mask.len() {
                mask[j] = mask[f];
            }
        }
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

pub(crate) fn invalid(reason: InvalidModel, message: String) -> LoadError {
    LoadError::Invalid { reason, message }
}

/// 局所変数のない環境に置く値を名前解決する（初期値と定数）。値は中核の下ろしが評価する。
/// `what` は型の誤りのメッセージで、何の型が合わないかを言う。
fn stored_tree(ctx: &Ctx, v: &Value, path: &str, st: &SType, what: &str) -> Result<TExpr, LoadError> {
    resolved(ctx.stored(v, path, st), |detail| LoadError::Schema {
        path: path.to_string(),
        message: format!("{what}（{detail}）"),
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
                    "操作 {name:?} の引数 {:?} のドメインが不正です（{d}）",
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
    let (raw, names, _) = parse_value(&root, &[])?;
    Ok((raw, names, canonical::digest(&root)))
}

/// 写像の1つの式（詳細化の検査）。`expr` を具体モデルの状態の上で評価し、型 `ty`（抽象モデルの状態変数の型のJSON）の値にする。
/// `path` は誤りの報告に使う位置。
pub(crate) struct MapSource<'a> {
    pub path: String,
    pub expr: &'a Value,
    pub ty: &'a Value,
}

/// 名前を解決したモデルと、その組み立てに使った表。
pub(crate) struct Built {
    pub sm: SModel,
    pub smaps: Vec<SMap>,
    pub names: Names,
    pub ir_names: fmspec_core::ir_json::IrNames,
    constants: Vec<Constant>,
    init_paths: Vec<Vec<String>>,
}

/// IRのJSONを読み、名前を解決したモデルと名前の表を組み立てる。中核の検査はまだ通していない。
pub(crate) fn build(root: &Value, maps: &[MapSource]) -> Result<Built, LoadError> {
    let path = "$";
    let map = object(
        root,
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
            "symmetry",
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

    let mut smaps = Vec::new();
    for m in maps {
        let ty = parse_type(m.ty, &m.path, &enums)?;
        let expr = stored_tree(
            &ctx,
            m.expr,
            &m.path,
            &ty,
            "写像の式の型が、抽象モデルの状態変数の型と合いません",
        )?;
        smaps.push(SMap {
            expr,
            ty: fields.stype(&ty),
        });
    }
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
    let mut names = Names {
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
        symmetry: Vec::new(),
        symmetry_groups: Vec::new(),
        invariant_family: Vec::new(),
    };
    if let Some(groups) = map.get("symmetry").filter(|v| !v.is_null()) {
        parse_symmetry(groups, &mut names)?;
    }
    let ir_names = crate::ir_json::ir_names(&crate::ir_json::NameParts {
        enums: &names.enums,
        consts: constants.iter().map(|c| c.name.clone()).collect(),
        states: &names.states,
        actions: &names.actions,
        invariants: &names.invariants,
        contracts: &names.contracts,
        fields: fields.names(),
    });
    Ok(Built {
        sm,
        smaps,
        names,
        ir_names,
        constants,
        init_paths: states.init_paths,
    })
}

/// 値になったIRを読み込む。`maps` の式を、このモデルの状態の上の式として下ろし、スロットごとの式の列を返す。
pub(crate) fn parse_value(root: &Value, maps: &[MapSource]) -> Result<(RawModel, Names, Vec<Expr>), LoadError> {
    let Built {
        sm,
        smaps,
        mut names,
        ir_names,
        constants,
        init_paths,
    } = build(root, maps)?;
    // 組み立てたモデルと名前の表が入力のIRと対応することを、中核の検証済みの検査で確かめてから下ろす。
    let lowered =
        lower_checked(&crate::ir_json::to_json(root), &ir_names, &sm, &smaps).ok_or_else(|| LoadError::Schema {
            path: "$".to_string(),
            message: "内部エラー: 名前を解決したモデルがIRと対応しません".to_string(),
        })?;
    let (mut raw, slots) = lowered.map_err(|e| match e {
        LowerError::Mapping(i) => LoadError::Schema {
            path: maps.get(i).map_or("$".to_string(), |m| m.path.clone()),
            message: "内部エラー: 中核の下ろしが写像の式を受理しません".to_string(),
        },
        e => lower_error(e, &names, &constants, &init_paths),
    })?;
    names.invariant_family = (0..raw.invariants.len()).collect();
    if !names.symmetry.is_empty() {
        close_invariants(&mut raw, &mut names);
    }
    Ok((raw, names, slots))
}

/// 1つの不変条件に加える入れ替えの像の数の上限。超えたら、それ以上は加えない（判定ゲートが対称性を拒否する）。
const MAX_IMAGES: usize = 720;

/// 状態のスロットの添字を `p` で付け替えた式（中核の `sym::rename` の実行版）。
fn rename_expr(e: &Expr, p: &[usize]) -> Expr {
    let r = |x: &Expr| Box::new(rename_expr(x, p));
    let slot = |i: usize| p.get(i).copied().unwrap_or(i);
    match e {
        Expr::Var(i) => Expr::Var(slot(*i)),
        Expr::Next(i) => Expr::Next(slot(*i)),
        Expr::Bin(op, a, b) => Expr::Bin(*op, r(a), r(b)),
        Expr::Not(a) => Expr::Not(r(a)),
        Expr::And(a, b) => Expr::And(r(a), r(b)),
        Expr::Or(a, b) => Expr::Or(r(a), r(b)),
        Expr::Implies(a, b) => Expr::Implies(r(a), r(b)),
        Expr::Ite(c, a, b) => Expr::Ite(r(c), r(a), r(b)),
        Expr::Let(a, b) => Expr::Let(r(a), r(b)),
        Expr::Forall(ty, lo, hi, b) => Expr::Forall(*ty, *lo, *hi, r(b)),
        Expr::Exists(ty, lo, hi, b) => Expr::Exists(*ty, *lo, *hi, r(b)),
        Expr::Code(a) => Expr::Code(r(a)),
        other => copy_expr(other),
    }
}

/// 対称性を宣言したモデルで、各不変条件に、入れ替えの像を元と同じ名前の不変条件として加える。
/// モデルが対称なら、不変条件がすべての到達可能な状態で成り立つことと、その像が成り立つことは同値なので、
/// 検査する性質は変わらない。像を加えたモデルが対称であることは、判定ゲートが確かめる。
fn close_invariants(raw: &mut RawModel, names: &mut Names) {
    let identity: Vec<usize> = (0..raw.state_types.len()).collect();
    let n = raw.invariants.len();
    for j in 0..n {
        let mut images: Vec<Expr> = vec![copy_expr(&raw.invariants[j])];
        let mut k = 0;
        while k < images.len() && images.len() < MAX_IMAGES {
            for p in &names.symmetry {
                let image = rename_expr(&images[k], p);
                if !images.iter().any(|e| renamed_eq(e, &image, &identity)) {
                    images.push(image);
                }
            }
            k += 1;
        }
        for image in images.into_iter().skip(1) {
            raw.invariants.push(image);
            names.invariants.push(names.invariants[j].clone());
            names.invariant_sources.push(names.invariant_sources[j].clone());
            names.invariant_family.push(j);
        }
    }
}

/// 対称性の宣言を読む（docs/ir.md の「対称性」）。
///
/// `symmetry` はグループの配列で、グループはブロックの配列、ブロックは状態変数の名前の配列である。
/// 同じグループのブロックは、同じ数の状態変数を持ち、対応する状態変数は同じ型を持つ。
/// 1つの状態変数は、1つのブロックにだけ現れる。
/// 隣り合う2つのブロックごとに、対応する状態変数のスロットを入れ替える置換を作る。
/// 置換がモデルの対称性であることは、ここでは確かめない。判定ゲートが確かめる。
fn parse_symmetry(groups: &Value, names: &mut Names) -> Res<()> {
    let n_slots = names.state_offsets.last().map_or(0, |&o| {
        o + names.state_types.last().map_or(0, |t| t.width(&names.enums))
    });
    let mut used = HashSet::new();
    for (g, group) in array(groups, "$.symmetry")?.iter().enumerate() {
        let gpath = format!("$.symmetry[{g}]");
        let mut blocks: Vec<Vec<usize>> = Vec::new();
        for (b, block) in array(group, &gpath)?.iter().enumerate() {
            let bpath = format!("{gpath}[{b}]");
            let mut vars = Vec::new();
            for (k, name) in array(block, &bpath)?.iter().enumerate() {
                let path = format!("{bpath}[{k}]");
                let name = string(name, &path)?;
                let Some(v) = names.state_index(&name) else {
                    return schema(&path, format!("未定義の状態変数 {name:?}"));
                };
                if !used.insert(v) {
                    return schema(&path, format!("状態変数 {name:?} は、別のブロックにも現れます"));
                }
                vars.push(v);
            }
            if let Some(first) = blocks.first() {
                if first.len() != vars.len() {
                    return schema(&bpath, "同じグループのブロックは、同じ数の状態変数を持ちます");
                }
                for (x, y) in first.iter().zip(&vars) {
                    if names.state_types[*x] != names.state_types[*y] {
                        return schema(
                            &bpath,
                            format!(
                                "状態変数 {:?} と {:?} の型が違います",
                                names.states[*x], names.states[*y]
                            ),
                        );
                    }
                }
            }
            blocks.push(vars);
        }
        if blocks.len() < 2 {
            return schema(&gpath, "グループには2つ以上のブロックが必要です");
        }
        for pair in blocks.windows(2) {
            let mut p: Vec<usize> = (0..n_slots).collect();
            for (x, y) in pair[0].iter().zip(&pair[1]) {
                for (i, j) in names.state_slots(*x).zip(names.state_slots(*y)) {
                    p[i] = j;
                    p[j] = i;
                }
            }
            names.symmetry.push(p);
        }
        names.symmetry_groups.push(blocks.len());
    }
    Ok(())
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
        let expr = stored_tree(
            &ctx,
            required(c, &path, "value")?,
            &format!("{path}.value"),
            &ty,
            "定数の値の型が定数の型と合いません",
        )?;
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
            exprs.push(stored_tree(ctx, v, p, &ty, "初期値の型が状態変数の型と合いません")?);
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

/// IRのJSONを読み込み、中核のIR検証を通したモデルを返す。
pub fn load(json: &str) -> Result<Model, LoadError> {
    let (raw, names, digest) = parse(json)?;
    checked_model(raw, names, digest)
}

/// 中核のIR検証を通して、モデルにする。
pub(crate) fn checked_model(raw: RawModel, names: Names, digest: String) -> Result<Model, LoadError> {
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
