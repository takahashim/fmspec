//! 型規則、モデルの整形式性、IR検証、型健全性。
//!
//! `wf` が整形式性の定義で、`validate_raw` は `wf` をちょうど判定する（仕様書 §14.1 IR Validation）。
//! `lemma_type_sound` は、受理した式の評価が型エラーや未束縛の参照で失敗せず、
//! 成功した結果が型規則の与える型を持つことを述べる（Type Soundness）。

#[allow(unused_imports)]
use crate::kernel::eval::*;
use crate::kernel::model::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::state_enc::{args_ok, encode_spec, in_type, state_ok, type_range, vals_ok};
use crate::kernel::state_enc::{type_range_exec, vals_ok_exec};
#[cfg(verus_keep_ghost)]
use crate::kernel::step::{act_env, apply_updates, step_spec, Step};
use vstd::prelude::*;

verus! {

/// 式の型。整数の範囲は状態型の側にだけあり、中間演算の型は範囲を持たない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ETy {
    Bool,
    Int,
    Enum(usize),
}

/// 型検査の文脈。
pub struct TyEnv {
    pub enums: Seq<i64>,
    pub st_tys: Seq<Type>,
    pub arg_tys: Seq<Type>,
    /// 遷移後の状態を参照できる（遷移契約）。
    pub next: bool,
    /// 参照できる出力の型。
    pub out: Option<ETy>,
}

pub open spec fn ety_of(ty: Type) -> ETy {
    match ty {
        Type::Bool => ETy::Bool,
        Type::Int(_, _) => ETy::Int,
        Type::Enum(id) => ETy::Enum(id),
    }
}

/// 値の型。存在しない列挙型やラベルを指す値は型を持たない。
pub open spec fn const_ety(enums: Seq<i64>, v: Value) -> Option<ETy> {
    match v {
        Value::Bool(_) => Some(ETy::Bool),
        Value::Int(_) => Some(ETy::Int),
        Value::Enum(id, k) => if id < enums.len() && 0 <= k < enums[id as int] {
            Some(ETy::Enum(id))
        } else {
            None
        },
    }
}

pub open spec fn binop_ety(op: BinOp, x: ETy, y: ETy) -> Option<ETy> {
    match op {
        BinOp::Eq => if x == y {
            Some(ETy::Bool)
        } else {
            None
        },
        BinOp::Ne => if x == y {
            Some(ETy::Bool)
        } else {
            None
        },
        _ => if x == ETy::Int && y == ETy::Int {
            match op {
                BinOp::Add => Some(ETy::Int),
                BinOp::Sub => Some(ETy::Int),
                BinOp::Mul => Some(ETy::Int),
                BinOp::Div => Some(ETy::Int),
                BinOp::Mod => Some(ETy::Int),
                _ => Some(ETy::Bool),
            }
        } else {
            None
        },
    }
}

/// 量化の範囲 `lo..=hi` が型 `ty` の符号に収まる。空の範囲はどの型でもよい。
pub open spec fn quant_dom_ok(enums: Seq<i64>, ty: Type, lo: i64, hi: i64) -> bool {
    &&& type_ok(enums, ty)
    &&& lo > hi || (type_range(enums, ty).0 <= lo && hi <= type_range(enums, ty).1)
}

pub open spec fn var_ety(tys: Seq<Type>, i: usize) -> Option<ETy> {
    if i < tys.len() {
        Some(ety_of(tys[i as int]))
    } else {
        None
    }
}

pub open spec fn both_bool(x: Option<ETy>, y: Option<ETy>) -> Option<ETy> {
    if x == Some(ETy::Bool) && y == Some(ETy::Bool) {
        Some(ETy::Bool)
    } else {
        None
    }
}

/// 型規則。すべての枝を検査する。型が付かなければ `None`。`lt` は局所変数の型。
pub open spec fn type_l(e: Expr, t: TyEnv, lt: Seq<ETy>) -> Option<ETy>
    decreases e,
{
    match e {
        Expr::Const(v) => const_ety(t.enums, v),
        Expr::Var(i) => var_ety(t.st_tys, i),
        Expr::Arg(i) => var_ety(t.arg_tys, i),
        Expr::Next(i) => if t.next {
            var_ety(t.st_tys, i)
        } else {
            None
        },
        Expr::Out => t.out,
        Expr::Bin(op, a, b) => match (type_l(*a, t, lt), type_l(*b, t, lt)) {
            (Some(x), Some(y)) => binop_ety(op, x, y),
            _ => None,
        },
        Expr::Not(a) => both_bool(type_l(*a, t, lt), Some(ETy::Bool)),
        Expr::And(a, b) => both_bool(type_l(*a, t, lt), type_l(*b, t, lt)),
        Expr::Or(a, b) => both_bool(type_l(*a, t, lt), type_l(*b, t, lt)),
        Expr::Implies(a, b) => both_bool(type_l(*a, t, lt), type_l(*b, t, lt)),
        Expr::Ite(c, a, b) => match (type_l(*c, t, lt), type_l(*a, t, lt), type_l(*b, t, lt)) {
            (Some(ETy::Bool), Some(x), Some(y)) => if x == y {
                Some(x)
            } else {
                None
            },
            _ => None,
        },
        Expr::Local(i) => if i < lt.len() {
            Some(lt[i as int])
        } else {
            None
        },
        Expr::Let(a, b) => match type_l(*a, t, lt) {
            Some(x) => type_l(*b, t, lt.push(x)),
            None => None,
        },
        Expr::Forall(ty, lo, hi, body) => if quant_dom_ok(t.enums, ty, lo, hi) && type_l(
            *body,
            t,
            lt.push(ety_of(ty)),
        ) == Some(ETy::Bool) {
            Some(ETy::Bool)
        } else {
            None
        },
        Expr::Exists(ty, lo, hi, body) => if quant_dom_ok(t.enums, ty, lo, hi) && type_l(
            *body,
            t,
            lt.push(ety_of(ty)),
        ) == Some(ETy::Bool) {
            Some(ETy::Bool)
        } else {
            None
        },
        Expr::Code(a) => match type_l(*a, t, lt) {
            Some(_) => Some(ETy::Int),
            None => None,
        },
        Expr::Fail(ty, _) => if type_ok(t.enums, ty) {
            Some(ety_of(ty))
        } else {
            None
        },
    }
}

/// 局所変数のない文脈での型規則。
pub open spec fn type_of_spec(e: Expr, t: TyEnv) -> Option<ETy> {
    type_l(e, t, Seq::empty())
}



// ---- 型検査の実装 ----

pub struct TyCtx<'a> {
    pub enums: &'a Vec<i64>,
    pub st_tys: &'a Vec<Type>,
    pub arg_tys: &'a Vec<Type>,
    pub next: bool,
    pub out: Option<ETy>,
}

impl<'a> TyCtx<'a> {
    pub open spec fn view(&self) -> TyEnv {
        TyEnv { enums: self.enums@, st_tys: self.st_tys@, arg_tys: self.arg_tys@, next: self.next, out: self.out }
    }
}

fn ety_eq(x: &ETy, y: &ETy) -> (r: bool)
    ensures
        r == (*x == *y),
{
    match (x, y) {
        (ETy::Bool, ETy::Bool) => true,
        (ETy::Int, ETy::Int) => true,
        (ETy::Enum(a), ETy::Enum(b)) => *a == *b,
        _ => false,
    }
}

fn ety_of_exec(ty: &Type) -> (r: ETy)
    ensures
        r == ety_of(*ty),
{
    match ty {
        Type::Bool => ETy::Bool,
        Type::Int(_, _) => ETy::Int,
        Type::Enum(id) => ETy::Enum(*id),
    }
}

fn const_ety_exec(enums: &Vec<i64>, v: &Value) -> (r: Option<ETy>)
    ensures
        r == const_ety(enums@, *v),
{
    match v {
        Value::Bool(_) => Some(ETy::Bool),
        Value::Int(_) => Some(ETy::Int),
        Value::Enum(id, k) => if *id < enums.len() && 0 <= *k && *k < enums[*id] {
            Some(ETy::Enum(*id))
        } else {
            None
        },
    }
}

fn binop_ety_exec(op: &BinOp, x: &ETy, y: &ETy) -> (r: Option<ETy>)
    ensures
        r == binop_ety(*op, *x, *y),
{
    match op {
        BinOp::Eq => if ety_eq(x, y) {
            Some(ETy::Bool)
        } else {
            None
        },
        BinOp::Ne => if ety_eq(x, y) {
            Some(ETy::Bool)
        } else {
            None
        },
        _ => if ety_eq(x, &ETy::Int) && ety_eq(y, &ETy::Int) {
            match op {
                BinOp::Add => Some(ETy::Int),
                BinOp::Sub => Some(ETy::Int),
                BinOp::Mul => Some(ETy::Int),
                BinOp::Div => Some(ETy::Int),
                BinOp::Mod => Some(ETy::Int),
                _ => Some(ETy::Bool),
            }
        } else {
            None
        },
    }
}

fn quant_dom_ok_exec(enums: &Vec<i64>, ty: &Type, lo: i64, hi: i64) -> (r: bool)
    ensures
        r == quant_dom_ok(enums@, *ty, lo, hi),
{
    let (tlo, thi) = type_range_exec(enums, ty);
    type_ok_exec(enums, ty) && (lo > hi || (tlo <= lo as i128 && hi as i128 <= thi))
}

fn var_ety_exec(tys: &Vec<Type>, i: usize) -> (r: Option<ETy>)
    ensures
        r == var_ety(tys@, i),
{
    if i < tys.len() {
        Some(ety_of_exec(&tys[i]))
    } else {
        None
    }
}

fn is_bool(x: &Option<ETy>) -> (r: bool)
    ensures
        r == (*x == Some(ETy::Bool)),
{
    match x {
        Some(ETy::Bool) => true,
        _ => false,
    }
}

fn both_bool_exec(x: &Option<ETy>, y: &Option<ETy>) -> (r: Option<ETy>)
    ensures
        r == both_bool(*x, *y),
{
    if is_bool(x) && is_bool(y) {
        Some(ETy::Bool)
    } else {
        None
    }
}

fn copy_etys(v: &Vec<ETy>) -> (r: Vec<ETy>)
    ensures
        r@ == v@,
{
    let mut r: Vec<ETy> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        assert(r@ =~= v@.subrange(0, i as int));
    }
    assert(v@.subrange(0, v@.len() as int) =~= v@);
    r
}

/// 式の型を求める。結果は型規則 `type_of_spec` と一致する。
pub fn type_of(e: &Expr, t: &TyCtx) -> (r: Option<ETy>)
    ensures
        r == type_of_spec(*e, t@),
{
    let lt: Vec<ETy> = Vec::new();
    assert(lt@ =~= Seq::<ETy>::empty());
    type_in(e, t, &lt)
}

fn with_ety(lt: &Vec<ETy>, x: ETy) -> (r: Vec<ETy>)
    ensures
        r@ == lt@.push(x),
{
    let mut r = copy_etys(lt);
    r.push(x);
    r
}

/// 局所変数の型 `lt` の下で式の型を求める。結果は型規則 `type_l` と一致する。
fn type_in(e: &Expr, t: &TyCtx, lt: &Vec<ETy>) -> (r: Option<ETy>)
    ensures
        r == type_l(*e, t@, lt@),
    decreases e,
{
    match e {
        Expr::Const(v) => const_ety_exec(t.enums, v),
        Expr::Var(i) => var_ety_exec(t.st_tys, *i),
        Expr::Arg(i) => var_ety_exec(t.arg_tys, *i),
        Expr::Next(i) => if t.next {
            var_ety_exec(t.st_tys, *i)
        } else {
            None
        },
        Expr::Out => t.out,
        Expr::Bin(op, a, b) => match (type_in(a, t, lt), type_in(b, t, lt)) {
            (Some(x), Some(y)) => binop_ety_exec(op, &x, &y),
            _ => None,
        },
        Expr::Not(a) => both_bool_exec(&type_in(a, t, lt), &Some(ETy::Bool)),
        Expr::And(a, b) => both_bool_exec(&type_in(a, t, lt), &type_in(b, t, lt)),
        Expr::Or(a, b) => both_bool_exec(&type_in(a, t, lt), &type_in(b, t, lt)),
        Expr::Implies(a, b) => both_bool_exec(&type_in(a, t, lt), &type_in(b, t, lt)),
        Expr::Ite(c, a, b) => match (type_in(c, t, lt), type_in(a, t, lt), type_in(b, t, lt)) {
            (Some(ETy::Bool), Some(x), Some(y)) => if ety_eq(&x, &y) {
                Some(x)
            } else {
                None
            },
            _ => None,
        },
        Expr::Local(i) => if *i < lt.len() {
            Some(lt[*i])
        } else {
            None
        },
        Expr::Let(a, b) => match type_in(a, t, lt) {
            Some(x) => type_in(b, t, &with_ety(lt, x)),
            None => None,
        },
        Expr::Forall(ty, lo, hi, body) => if quant_dom_ok_exec(t.enums, ty, *lo, *hi) && is_bool(
            &type_in(body, t, &with_ety(lt, ety_of_exec(ty))),
        ) {
            Some(ETy::Bool)
        } else {
            None
        },
        Expr::Exists(ty, lo, hi, body) => if quant_dom_ok_exec(t.enums, ty, *lo, *hi) && is_bool(
            &type_in(body, t, &with_ety(lt, ety_of_exec(ty))),
        ) {
            Some(ETy::Bool)
        } else {
            None
        },
        Expr::Code(a) => match type_in(a, t, lt) {
            Some(_) => Some(ETy::Int),
            None => None,
        },
        Expr::Fail(ty, _) => if type_ok_exec(t.enums, ty) {
            Some(ety_of_exec(ty))
        } else {
            None
        },
    }
}

// ---- 整形式性 ----

pub open spec fn type_ok(enums: Seq<i64>, ty: Type) -> bool {
    match ty {
        Type::Bool => true,
        Type::Int(lo, hi) => lo <= hi,
        Type::Enum(id) => id < enums.len(),
    }
}

pub open spec fn types_ok(enums: Seq<i64>, tys: Seq<Type>) -> bool {
    forall|i: int| 0 <= i < tys.len() ==> type_ok(enums, #[trigger] tys[i])
}

/// 不変条件と終端条件の文脈。
pub open spec fn inv_tyenv(m: RawModel) -> TyEnv {
    TyEnv { enums: m.enums@, st_tys: m.state_types@, arg_tys: Seq::empty(), next: false, out: None }
}

/// guard、更新式、出力式の文脈。
pub open spec fn act_tyenv(m: RawModel, a: int) -> TyEnv {
    TyEnv { enums: m.enums@, st_tys: m.state_types@, arg_tys: m.actions@[a].domains@, next: false, out: None }
}

pub open spec fn out_ety(m: RawModel, a: int) -> Option<ETy> {
    match m.actions@[a].output {
        Some(o) => Some(ety_of(o.ty)),
        None => None,
    }
}

/// 遷移契約の文脈。
pub open spec fn con_tyenv(m: RawModel, a: int) -> TyEnv {
    TyEnv {
        enums: m.enums@,
        st_tys: m.state_types@,
        arg_tys: m.actions@[a].domains@,
        next: true,
        out: out_ety(m, a),
    }
}

pub open spec fn update_wf(m: RawModel, a: int, u: int) -> bool {
    let up = m.actions@[a].updates@[u];
    &&& up.target < m.state_types@.len()
    &&& type_of_spec(up.expr, act_tyenv(m, a)) == Some(ety_of(m.state_types@[up.target as int]))
}

/// `u` 番目の更新の対象は、それより前の更新の対象と重ならない。
pub open spec fn update_fresh(m: RawModel, a: int, u: int) -> bool {
    forall|w: int| 0 <= w < u ==> (#[trigger] m.actions@[a].updates@[w]).target != m.actions@[a].updates@[u].target
}

pub open spec fn output_wf(m: RawModel, a: int) -> bool {
    match m.actions@[a].output {
        None => true,
        Some(o) => type_ok(m.enums@, o.ty) && type_of_spec(o.expr, act_tyenv(m, a)) == Some(ety_of(o.ty)),
    }
}

pub open spec fn action_wf(m: RawModel, a: int) -> bool {
    let act = m.actions@[a];
    &&& act.n_params <= act.domains@.len()
    &&& types_ok(m.enums@, act.domains@)
    &&& type_of_spec(act.guard, act_tyenv(m, a)) == Some(ETy::Bool)
    &&& forall|u: int| 0 <= u < act.updates@.len() ==> #[trigger] update_wf(m, a, u)
    &&& forall|u: int| 0 <= u < act.updates@.len() ==> #[trigger] update_fresh(m, a, u)
    &&& output_wf(m, a)
}

pub open spec fn contract_wf(m: RawModel, c: int) -> bool {
    let con = m.contracts@[c];
    &&& con.action < m.actions@.len()
    &&& type_of_spec(con.expr, con_tyenv(m, con.action as int)) == Some(ETy::Bool)
}

pub open spec fn invariant_wf(m: RawModel, i: int) -> bool {
    type_of_spec(m.invariants@[i], inv_tyenv(m)) == Some(ETy::Bool)
}

pub open spec fn terminal_wf(m: RawModel) -> bool {
    match m.terminal {
        None => true,
        Some(e) => type_of_spec(e, inv_tyenv(m)) == Some(ETy::Bool),
    }
}

/// モデルの整形式性。
pub open spec fn wf(m: RawModel) -> bool {
    &&& forall|i: int| 0 <= i < m.enums@.len() ==> 1 <= #[trigger] m.enums@[i]
    &&& types_ok(m.enums@, m.state_types@)
    &&& m.inits@.len() >= 1
    &&& forall|i: int| 0 <= i < m.inits@.len() ==> state_ok(m, (#[trigger] m.inits@[i])@)
    &&& forall|a: int| 0 <= a < m.actions@.len() ==> #[trigger] action_wf(m, a)
    &&& forall|i: int| 0 <= i < m.invariants@.len() ==> #[trigger] invariant_wf(m, i)
    &&& forall|c: int| 0 <= c < m.contracts@.len() ==> #[trigger] contract_wf(m, c)
    &&& terminal_wf(m)
}

/// IR検証でモデルを拒否した理由。添字は該当する定義を指す。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvalidModel {
    /// ラベルのない列挙型。
    EmptyEnum(usize),
    /// 状態変数の型が不正（空の整数範囲、未定義の列挙型）。
    StateType(usize),
    /// 初期状態がない。
    NoInitial,
    /// 初期状態（添字）が状態型に従わない（個数の不一致、範囲外）。
    Initial(usize),
    /// 操作の公開引数の個数が引数の個数を超える。
    Params(usize),
    /// 操作の引数のドメインが不正。
    Domain(usize, usize),
    /// 操作の guard が Bool 式でない、または未定義の参照を含む。
    Guard(usize),
    /// 更新の対象が未定義、または更新式の型が対象と合わない。
    Update(usize, usize),
    /// 同じ状態変数への重複代入。
    DuplicateUpdate(usize, usize),
    /// 出力の型または出力式が不正。
    Output(usize),
    /// 不変条件が Bool 式でない、または未定義の参照を含む。
    Invariant(usize),
    /// 遷移契約の対象の操作が未定義、または契約が Bool 式でない。
    Contract(usize),
    /// 終端条件が Bool 式でない、または未定義の参照を含む。
    Terminal,
}

fn type_ok_exec(enums: &Vec<i64>, ty: &Type) -> (r: bool)
    ensures
        r == type_ok(enums@, *ty),
{
    match ty {
        Type::Bool => true,
        Type::Int(lo, hi) => *lo <= *hi,
        Type::Enum(id) => *id < enums.len(),
    }
}

/// 型の列を検査する。不正な型があれば、最初のものの添字を返す。
fn check_types(enums: &Vec<i64>, tys: &Vec<Type>) -> (r: Option<usize>)
    ensures
        r is None <==> types_ok(enums@, tys@),
{
    let mut i: usize = 0;
    while i < tys.len()
        invariant
            i <= tys@.len(),
            forall|j: int| 0 <= j < i ==> type_ok(enums@, #[trigger] tys@[j]),
        decreases tys@.len() - i,
    {
        if !type_ok_exec(enums, &tys[i]) {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

fn is_ety(x: &Option<ETy>, want: &ETy) -> (r: bool)
    ensures
        r == (*x == Some(*want)),
{
    match x {
        Some(t) => ety_eq(t, want),
        None => false,
    }
}

#[verifier::loop_isolation(false)]
fn check_action(m: &RawModel, a: usize) -> (r: Result<(), InvalidModel>)
    requires
        a < m.actions@.len(),
    ensures
        r is Ok <==> action_wf(*m, a as int),
{
    let act = &m.actions[a];
    if act.n_params > act.domains.len() {
        return Err(InvalidModel::Params(a));
    }
    match check_types(&m.enums, &act.domains) {
        Some(d) => {
            return Err(InvalidModel::Domain(a, d));
        },
        None => {},
    }
    let t = TyCtx { enums: &m.enums, st_tys: &m.state_types, arg_tys: &act.domains, next: false, out: None };
    assert(t@ == act_tyenv(*m, a as int));
    if !is_bool(&type_of(&act.guard, &t)) {
        return Err(InvalidModel::Guard(a));
    }
    let mut u: usize = 0;
    while u < act.updates.len()
        invariant
            u <= act.updates@.len(),
            forall|j: int| 0 <= j < u ==> #[trigger] update_wf(*m, a as int, j),
            forall|j: int| 0 <= j < u ==> #[trigger] update_fresh(*m, a as int, j),
        decreases act.updates@.len() - u,
    {
        let up = &act.updates[u];
        if up.target >= m.state_types.len() {
            assert(!update_wf(*m, a as int, u as int));
            return Err(InvalidModel::Update(a, u));
        }
        let want = ety_of_exec(&m.state_types[up.target]);
        if !is_ety(&type_of(&up.expr, &t), &want) {
            assert(!update_wf(*m, a as int, u as int));
            return Err(InvalidModel::Update(a, u));
        }
        let mut w: usize = 0;
        while w < u
            invariant
                w <= u,
                forall|j: int| 0 <= j < w ==> (#[trigger] act.updates@[j]).target != up.target,
            decreases u - w,
        {
            if act.updates[w].target == up.target {
                assert(!update_fresh(*m, a as int, u as int));
                return Err(InvalidModel::DuplicateUpdate(a, u));
            }
            w = w + 1;
        }
        assert(update_wf(*m, a as int, u as int));
        assert(update_fresh(*m, a as int, u as int));
        u = u + 1;
    }
    match &act.output {
        None => {},
        Some(o) => {
            if !type_ok_exec(&m.enums, &o.ty) {
                return Err(InvalidModel::Output(a));
            }
            let want = ety_of_exec(&o.ty);
            if !is_ety(&type_of(&o.expr, &t), &want) {
                return Err(InvalidModel::Output(a));
            }
        },
    }
    Ok(())
}

/// モデルの整形式性を検査する。`Ok` を返すのは、モデルが整形式であるとき、かつそのときに限る。
#[verifier::loop_isolation(false)]
pub fn validate_raw(m: &RawModel) -> (r: Result<(), InvalidModel>)
    ensures
        r is Ok <==> wf(*m),
{
    let mut i: usize = 0;
    while i < m.enums.len()
        invariant
            i <= m.enums@.len(),
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] m.enums@[j],
        decreases m.enums@.len() - i,
    {
        if m.enums[i] < 1 {
            return Err(InvalidModel::EmptyEnum(i));
        }
        i = i + 1;
    }
    match check_types(&m.enums, &m.state_types) {
        Some(k) => {
            return Err(InvalidModel::StateType(k));
        },
        None => {},
    }
    if m.inits.len() == 0 {
        return Err(InvalidModel::NoInitial);
    }
    let mut i: usize = 0;
    while i < m.inits.len()
        invariant
            i <= m.inits@.len(),
            forall|j: int| 0 <= j < i ==> state_ok(*m, (#[trigger] m.inits@[j])@),
        decreases m.inits@.len() - i,
    {
        if !vals_ok_exec(&m.enums, &m.state_types, &m.inits[i]) {
            return Err(InvalidModel::Initial(i));
        }
        i = i + 1;
    }
    let mut a: usize = 0;
    while a < m.actions.len()
        invariant
            a <= m.actions@.len(),
            forall|j: int| 0 <= j < a ==> #[trigger] action_wf(*m, j),
        decreases m.actions@.len() - a,
    {
        match check_action(m, a) {
            Err(e) => {
                assert(!action_wf(*m, a as int));
                return Err(e);
            },
            Ok(()) => {},
        }
        a = a + 1;
    }
    let empty: Vec<Type> = Vec::new();
    assert(empty@ =~= Seq::<Type>::empty());
    let t = TyCtx { enums: &m.enums, st_tys: &m.state_types, arg_tys: &empty, next: false, out: None };
    assert(t@ == inv_tyenv(*m));
    let mut i: usize = 0;
    while i < m.invariants.len()
        invariant
            i <= m.invariants@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] invariant_wf(*m, j),
        decreases m.invariants@.len() - i,
    {
        if !is_bool(&type_of(&m.invariants[i], &t)) {
            assert(!invariant_wf(*m, i as int));
            return Err(InvalidModel::Invariant(i));
        }
        i = i + 1;
    }
    let mut c: usize = 0;
    while c < m.contracts.len()
        invariant
            c <= m.contracts@.len(),
            forall|j: int| 0 <= j < c ==> #[trigger] contract_wf(*m, j),
        decreases m.contracts@.len() - c,
    {
        let con = &m.contracts[c];
        if con.action >= m.actions.len() {
            assert(!contract_wf(*m, c as int));
            return Err(InvalidModel::Contract(c));
        }
        let act = &m.actions[con.action];
        let out = match &act.output {
            Some(o) => Some(ety_of_exec(&o.ty)),
            None => None,
        };
        let ct = TyCtx { enums: &m.enums, st_tys: &m.state_types, arg_tys: &act.domains, next: true, out };
        assert(ct@ == con_tyenv(*m, con.action as int));
        if !is_bool(&type_of(&con.expr, &ct)) {
            assert(!contract_wf(*m, c as int));
            return Err(InvalidModel::Contract(c));
        }
        assert(contract_wf(*m, c as int));
        c = c + 1;
    }
    match &m.terminal {
        None => {},
        Some(e) => {
            if !is_bool(&type_of(e, &t)) {
                return Err(InvalidModel::Terminal);
            }
        },
    }
    Ok(())
}

// ---- 型健全性 ----

/// 値 `v` は型 `t` を持つ。
pub open spec fn val_has(enums: Seq<i64>, v: Value, t: ETy) -> bool {
    const_ety(enums, v) == Some(t)
}

/// 環境が型検査の文脈に従う。
pub open spec fn env_ok(env: Env, t: TyEnv) -> bool {
    &&& env.st_tys == t.st_tys
    &&& env.arg_tys == t.arg_tys
    &&& vals_ok(t.enums, t.st_tys, env.pre)
    &&& vals_ok(t.enums, t.arg_tys, env.args)
    &&& t.next ==> vals_ok(t.enums, t.st_tys, env.post)
    &&& match t.out {
        None => true,
        Some(ot) => match env.out {
            Some(v) => val_has(t.enums, v, ot),
            None => false,
        },
    }
}

/// 型の付いた式の評価で起きうる失敗。オーバーフロー、0による除算、`Expr::Fail` の失敗である。
pub open spec fn eval_failure(k: ErrKind) -> bool {
    k is Overflow || k is DivByZero || k is Failed
}

/// 型の付いた式の評価結果。成功なら型 `ty` の値で、失敗は `eval_failure` である。
pub open spec fn typed_result(enums: Seq<i64>, r: Result<Value, ErrKind>, ty: ETy) -> bool {
    match r {
        Ok(v) => val_has(enums, v, ty),
        Err(k) => eval_failure(k),
    }
}

/// 局所変数の値が、局所変数の型に従う。
pub open spec fn locals_ok(enums: Seq<i64>, ls: Seq<Value>, lt: Seq<ETy>) -> bool {
    &&& ls.len() == lt.len()
    &&& forall|i: int| 0 <= i < ls.len() ==> val_has(enums, #[trigger] ls[i], lt[i])
}

proof fn lemma_locals_push(enums: Seq<i64>, ls: Seq<Value>, lt: Seq<ETy>, v: Value, x: ETy)
    requires
        locals_ok(enums, ls, lt),
        val_has(enums, v, x),
    ensures
        locals_ok(enums, ls.push(v), lt.push(x)),
{
    assert forall|i: int| 0 <= i < ls.push(v).len() implies val_has(enums, #[trigger] ls.push(v)[i], lt.push(x)[i]) by {
        if i < ls.len() {
            assert(ls.push(v)[i] == ls[i]);
            assert(lt.push(x)[i] == lt[i]);
        }
    }
}

/// 型に属する符号を値に戻すと、その型の値になる。
proof fn lemma_decode_typed(enums: Seq<i64>, ty: Type, x: i64)
    requires
        type_ok(enums, ty),
        in_type(enums, ty, x),
    ensures
        val_has(enums, decode(ty, x), ety_of(ty)),
{
}

proof fn lemma_lookup_typed(enums: Seq<i64>, tys: Seq<Type>, xs: Seq<i64>, i: usize)
    requires
        vals_ok(enums, tys, xs),
        var_ety(tys, i) is Some,
    ensures
        typed_result(enums, lookup(tys, xs, i), var_ety(tys, i).unwrap()),
{
    assert(in_type(enums, tys[i as int], xs[i as int]));
}

/// 型健全性。型の付いた式を文脈に従う環境で評価すると、型どおりの値になるか、`eval_failure` の失敗になる。
/// 型エラーと未束縛の参照は起きない。
pub proof fn lemma_type_sound(e: Expr, t: TyEnv, env: Env)
    requires
        env_ok(env, t),
        type_of_spec(e, t) is Some,
    ensures
        typed_result(t.enums, eval_spec(e, env), type_of_spec(e, t).unwrap()),
{
    lemma_type_sound_l(e, t, env, Seq::empty(), Seq::empty());
}

/// 局所変数を持つ文脈での型健全性。
pub proof fn lemma_type_sound_l(e: Expr, t: TyEnv, env: Env, ls: Seq<Value>, lt: Seq<ETy>)
    requires
        env_ok(env, t),
        locals_ok(t.enums, ls, lt),
        type_l(e, t, lt) is Some,
    ensures
        typed_result(t.enums, eval_l(e, env, ls), type_l(e, t, lt).unwrap()),
    decreases e, 0int,
{
    match e {
        Expr::Const(v) => {},
        Expr::Var(i) => {
            lemma_lookup_typed(t.enums, t.st_tys, env.pre, i);
        },
        Expr::Arg(i) => {
            lemma_lookup_typed(t.enums, t.arg_tys, env.args, i);
        },
        Expr::Next(i) => {
            lemma_lookup_typed(t.enums, t.st_tys, env.post, i);
        },
        Expr::Out => {},
        Expr::Bin(op, a, b) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
            lemma_type_sound_l(*b, t, env, ls, lt);
        },
        Expr::Not(a) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
        },
        Expr::And(a, b) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
            lemma_type_sound_l(*b, t, env, ls, lt);
        },
        Expr::Or(a, b) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
            lemma_type_sound_l(*b, t, env, ls, lt);
        },
        Expr::Implies(a, b) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
            lemma_type_sound_l(*b, t, env, ls, lt);
        },
        Expr::Ite(c, a, b) => {
            lemma_type_sound_l(*c, t, env, ls, lt);
            lemma_type_sound_l(*a, t, env, ls, lt);
            lemma_type_sound_l(*b, t, env, ls, lt);
        },
        Expr::Local(i) => {},
        Expr::Let(a, b) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
            match eval_l(*a, env, ls) {
                Err(_) => {},
                Ok(v) => {
                    let x = type_l(*a, t, lt).unwrap();
                    lemma_locals_push(t.enums, ls, lt, v, x);
                    lemma_type_sound_l(*b, t, env, ls.push(v), lt.push(x));
                },
            }
        },
        Expr::Forall(ty, lo, hi, body) => {
            lemma_quant_sound(true, ty, lo, hi, *body, t, env, ls, lt, lo as int, None);
        },
        Expr::Exists(ty, lo, hi, body) => {
            lemma_quant_sound(false, ty, lo, hi, *body, t, env, ls, lt, lo as int, None);
        },
        Expr::Code(a) => {
            lemma_type_sound_l(*a, t, env, ls, lt);
        },
        Expr::Fail(_, _) => {},
    }
}

/// 量化の型健全性。範囲の各符号を束縛した本体は型どおりに評価されるので、結果は Bool 値か `eval_failure` である。
proof fn lemma_quant_sound(
    all: bool,
    ty: Type,
    lo: i64,
    hi: i64,
    body: Expr,
    t: TyEnv,
    env: Env,
    ls: Seq<Value>,
    lt: Seq<ETy>,
    x: int,
    pend: Option<ErrKind>,
)
    requires
        env_ok(env, t),
        locals_ok(t.enums, ls, lt),
        quant_dom_ok(t.enums, ty, lo, hi),
        type_l(body, t, lt.push(ety_of(ty))) == Some(ETy::Bool),
        lo <= x,
        pend matches Some(k) ==> eval_failure(k),
    ensures
        typed_result(t.enums, quant_l(all, ty, body, env, ls, x, hi as int, pend), ETy::Bool),
    decreases body, hi - x + 1,
{
    if x <= hi {
        let d = decode(ty, x as i64);
        assert(in_type(t.enums, ty, x as i64));
        lemma_decode_typed(t.enums, ty, x as i64);
        lemma_locals_push(t.enums, ls, lt, d, ety_of(ty));
        lemma_type_sound_l(body, t, env, ls.push(d), lt.push(ety_of(ty)));
        let r = as_bool(eval_l(body, env, ls.push(d)));
        let next = if r is Err && !(pend is Some) { Some(r->Err_0) } else { pend };
        lemma_quant_sound(all, ty, lo, hi, body, t, env, ls, lt, x + 1, next);
    }
}

/// 型の付いた Bool 式を述語として評価すると、真偽が定まるか、オーバーフローで失敗する。
pub proof fn lemma_prop_typed(e: Expr, t: TyEnv, env: Env)
    requires
        env_ok(env, t),
        type_of_spec(e, t) == Some(ETy::Bool),
    ensures
        match prop_spec(e, env) {
            Ok(_) => true,
            Err(k) => eval_failure(k),
        },
{
    lemma_type_sound(e, t, env);
}

/// 遷移の失敗として起きうるのは、式の評価の失敗（`eval_failure`）と範囲外更新だけである。
pub open spec fn range_error(k: ErrKind) -> bool {
    eval_failure(k) || k is OutOfRange
}

proof fn lemma_encode_typed(enums: Seq<i64>, ty: Type, v: Value)
    requires
        val_has(enums, v, ety_of(ty)),
    ensures
        match encode_spec(enums, ty, v) {
            Ok(x) => in_type(enums, ty, x),
            Err(k) => k is OutOfRange,
        },
{
}

proof fn lemma_updates_typed(m: RawModel, a: int, env: Env, k: nat, acc: Seq<i64>)
    requires
        0 <= a < m.actions@.len(),
        action_wf(m, a),
        env_ok(env, act_tyenv(m, a)),
        state_ok(m, acc),
    ensures
        match apply_updates(m, a, env, k, acc) {
            Ok(t) => state_ok(m, t),
            Err((_, e)) => range_error(e),
        },
    decreases m.actions@[a].updates@.len() - k,
{
    let ups = m.actions@[a].updates@;
    if k < ups.len() {
        let u = ups[k as int];
        assert(update_wf(m, a, k as int));
        lemma_type_sound(u.expr, act_tyenv(m, a), env);
        match eval_spec(u.expr, env) {
            Err(e) => {},
            Ok(v) => {
                let ty = m.state_types@[u.target as int];
                lemma_encode_typed(m.enums@, ty, v);
                match encode_spec(m.enums@, ty, v) {
                    Err(e) => {},
                    Ok(x) => {
                        let acc2 = acc.update(u.target as int, x);
                        assert(state_ok(m, acc2)) by {
                            assert forall|i: int| 0 <= i < m.state_types@.len() implies in_type(
                                m.enums@,
                                #[trigger] m.state_types@[i],
                                acc2[i],
                            ) by {
                                if i != u.target as int {
                                    assert(acc2[i] == acc[i]);
                                }
                            }
                        }
                        lemma_updates_typed(m, a, env, k + 1, acc2);
                    },
                }
            },
        }
    }
}

/// 遷移の結果が型に従う。次状態は状態型に、出力は宣言した出力型に属し、失敗は `range_error` である。
pub open spec fn step_typed(m: RawModel, a: int, r: Step) -> bool {
    match r {
        Step::Disabled => true,
        Step::Fail(_, k) => range_error(k),
        Step::To(t, o) => state_ok(m, t) && match (m.actions@[a].output, o) {
            (Some(out), Some(x)) => in_type(m.enums@, out.ty, x),
            (None, None) => true,
            _ => false,
        },
    }
}

/// 整形式なモデルでは、型に従う状態と引数からの遷移は型に従う。
/// したがって、初期状態から到達できる状態はすべて状態型に従う。
pub proof fn lemma_step_typed(m: RawModel, a: int, args: Seq<i64>, s: Seq<i64>)
    requires
        wf(m),
        0 <= a < m.actions@.len(),
        state_ok(m, s),
        args_ok(m, a, args),
    ensures
        step_typed(m, a, step_spec(m, a, args, s)),
{
    let env = act_env(m, a, args, s);
    let t = act_tyenv(m, a);
    assert(action_wf(m, a));
    assert(env_ok(env, t));
    lemma_prop_typed(m.actions@[a].guard, t, env);
    lemma_updates_typed(m, a, env, 0, s);
    match m.actions@[a].output {
        None => {},
        Some(o) => {
            lemma_type_sound(o.expr, t, env);
            match eval_spec(o.expr, env) {
                Err(e) => {},
                Ok(v) => {
                    lemma_encode_typed(m.enums@, o.ty, v);
                },
            }
        },
    }
}

} // verus!
