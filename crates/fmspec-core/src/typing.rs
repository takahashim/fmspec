//! 型規則、モデルの整形式性、IR検証、型健全性。
//!
//! `wf` が整形式性の定義で、`validate_raw` は `wf` をちょうど判定する（仕様書 §14.1 IR Validation）。
//! `lemma_type_sound` は、受理した式の評価が型エラーや未束縛の参照で失敗せず、
//! 成功した結果が型規則の与える型を持つことを述べる（Type Soundness）。

#[allow(unused_imports)]
use crate::eval::*;
use crate::model::*;
use crate::step::*;
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
                _ => Some(ETy::Bool),
            }
        } else {
            None
        },
    }
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

/// 型規則。すべての枝を検査する。型が付かなければ `None`。
pub open spec fn type_of_spec(e: Expr, t: TyEnv) -> Option<ETy>
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
        Expr::Bin(op, a, b) => match (type_of_spec(*a, t), type_of_spec(*b, t)) {
            (Some(x), Some(y)) => binop_ety(op, x, y),
            _ => None,
        },
        Expr::Not(a) => both_bool(type_of_spec(*a, t), Some(ETy::Bool)),
        Expr::And(a, b) => both_bool(type_of_spec(*a, t), type_of_spec(*b, t)),
        Expr::Or(a, b) => both_bool(type_of_spec(*a, t), type_of_spec(*b, t)),
        Expr::Implies(a, b) => both_bool(type_of_spec(*a, t), type_of_spec(*b, t)),
        Expr::Ite(c, a, b) => match (type_of_spec(*c, t), type_of_spec(*a, t), type_of_spec(*b, t)) {
            (Some(ETy::Bool), Some(x), Some(y)) => if x == y {
                Some(x)
            } else {
                None
            },
            _ => None,
        },
    }
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
                _ => Some(ETy::Bool),
            }
        } else {
            None
        },
    }
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

/// 式の型を求める。結果は型規則 `type_of_spec` と一致する。
pub fn type_of(e: &Expr, t: &TyCtx) -> (r: Option<ETy>)
    ensures
        r == type_of_spec(*e, t@),
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
        Expr::Bin(op, a, b) => match (type_of(a, t), type_of(b, t)) {
            (Some(x), Some(y)) => binop_ety_exec(op, &x, &y),
            _ => None,
        },
        Expr::Not(a) => both_bool_exec(&type_of(a, t), &Some(ETy::Bool)),
        Expr::And(a, b) => both_bool_exec(&type_of(a, t), &type_of(b, t)),
        Expr::Or(a, b) => both_bool_exec(&type_of(a, t), &type_of(b, t)),
        Expr::Implies(a, b) => both_bool_exec(&type_of(a, t), &type_of(b, t)),
        Expr::Ite(c, a, b) => match (type_of(c, t), type_of(a, t), type_of(b, t)) {
            (Some(ETy::Bool), Some(x), Some(y)) => if ety_eq(&x, &y) {
                Some(x)
            } else {
                None
            },
            _ => None,
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
    &&& state_ok(m, m.init@)
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
    /// 初期状態が状態型に従わない（個数の不一致、範囲外）。
    Initial,
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
    if !vals_ok_exec(&m.enums, &m.state_types, &m.init) {
        return Err(InvalidModel::Initial);
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

/// 型の付いた式の評価結果。成功なら型 `ty` の値で、失敗はオーバーフローだけである。
pub open spec fn typed_result(enums: Seq<i64>, r: Result<Value, ErrKind>, ty: ETy) -> bool {
    match r {
        Ok(v) => val_has(enums, v, ty),
        Err(k) => k == ErrKind::Overflow,
    }
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

/// 型健全性。型の付いた式を文脈に従う環境で評価すると、型どおりの値になるか、オーバーフローで失敗する。
/// 型エラーと未束縛の参照は起きない。
pub proof fn lemma_type_sound(e: Expr, t: TyEnv, env: Env)
    requires
        env_ok(env, t),
        type_of_spec(e, t) is Some,
    ensures
        typed_result(t.enums, eval_spec(e, env), type_of_spec(e, t).unwrap()),
    decreases e,
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
            lemma_type_sound(*a, t, env);
            lemma_type_sound(*b, t, env);
        },
        Expr::Not(a) => {
            lemma_type_sound(*a, t, env);
        },
        Expr::And(a, b) => {
            lemma_type_sound(*a, t, env);
            lemma_type_sound(*b, t, env);
        },
        Expr::Or(a, b) => {
            lemma_type_sound(*a, t, env);
            lemma_type_sound(*b, t, env);
        },
        Expr::Implies(a, b) => {
            lemma_type_sound(*a, t, env);
            lemma_type_sound(*b, t, env);
        },
        Expr::Ite(c, a, b) => {
            lemma_type_sound(*c, t, env);
            lemma_type_sound(*a, t, env);
            lemma_type_sound(*b, t, env);
        },
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
            Err(k) => k == ErrKind::Overflow,
        },
{
    lemma_type_sound(e, t, env);
}

/// 遷移の失敗として起きうるのは、オーバーフローと範囲外更新だけである。
pub open spec fn range_error(k: ErrKind) -> bool {
    k is Overflow || k is OutOfRange
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

/// 遷移の結果が型に従う。次状態は状態型に、出力は宣言した出力型に属し、失敗はオーバーフローか範囲外更新である。
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
