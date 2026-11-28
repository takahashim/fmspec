//! IRのJSONと、名前を解決したモデルの対応の検査。IR検証（[`crate::kernel::checked::validate`]）とは別である。
//!
//! [`check_ir`] が真を返すなら、[`crate::ir::ir::ir_rel`] が成り立つ。
//! [`lower_checked`] は、対応を確かめてからモデルを下ろす。

#[cfg(verus_keep_ghost)]
use crate::ir::ir::{act_ctx, action_rel, binds_rel, const_rel, contract_rel, doms, enum_rel, ECtx};
#[cfg(verus_keep_ghost)]
use crate::ir::ir::{ex_at, ex_rel, exs_rel, field_rel, field_ty_rel, form_rel, guard_rel};
#[cfg(verus_keep_ghost)]
use crate::ir::ir::{invariant_rel, ir_rel, lemma_arr_dec, lemma_get_dec, lemma_one_dec, member_rel};
#[cfg(verus_keep_ghost)]
use crate::ir::ir::{name_is, op_form, opt_ex_rel, over_rel, state_rel, ty_at, ty_rel, tys_rel};
#[cfg(verus_keep_ghost)]
use crate::ir::ir::{update_rel, user_guard_rel};
use crate::ir::ir_json::str_exec;
#[cfg(verus_keep_ghost)]
use crate::ir::ir_json::{arr, at, distinct, get, index_of, names_ok, one, opt_arr, str_of, strs};
use crate::ir::ir_json::{arr_exec, chars_eq, copy_chars, distinct_exec, eqk, get_exec, index_of_exec};
use crate::ir::ir_json::{is_empty_obj, is_nat, last_of_exec, one_exec, present, IrNames, Json};
use crate::kernel::model::{BinOp, Expr, RawModel, Value};
use crate::model::lower_error::LowerError;
use crate::model::model_lower::{lower_model_map, SMap};
use crate::value::encoding::SType;
use crate::value::smodel::{SAction, SModel};
use crate::value::source::{Over, SetOp, TExpr};
use vstd::prelude::*;

verus! {

// ---- 型 ----

/// 型のJSON `j` が型 `t` を表すかを確かめる。
fn check_ty(j: &Json, ns: &IrNames, t: &SType) -> (r: bool)
    ensures
        r ==> ty_rel(*j, *ns, *t),
    decreases j, 1nat,
{
    let (k, b) = match one_exec(j) {
        Some(x) => x,
        None => return false,
    };
    proof {
        lemma_one_dec(*j);
        lemma_arr_dec(*b);
        reveal_strlit("bool");
        reveal_strlit("int");
        reveal_strlit("enum");
        reveal_strlit("tuple");
        reveal_strlit("record");
        reveal_strlit("option");
        reveal_strlit("set");
        reveal_strlit("map");
        reveal_strlit("list");
        reveal_strlit("min");
        reveal_strlit("max");
        reveal_strlit("key");
        reveal_strlit("value");
        reveal_strlit("of");
    }
    match t {
        SType::Bool => eqk(k, "bool") && is_empty_obj(b),
        SType::Int(lo, hi) => eqk(k, "int") && match (get_exec(b, "min"), get_exec(b, "max")) {
            (Some(Json::Int(x)), Some(Json::Int(y))) => *x == *lo && *y == *hi,
            _ => false,
        },
        SType::Enum(id) => eqk(k, "enum") && match str_exec(b) {
            Some(n) => match index_of_exec(&ns.enums, n) {
                Some(i) => i == *id,
                None => false,
            },
            None => false,
        },
        SType::Tuple(ts) => eqk(k, "tuple") && check_tys(b, ts, ns),
        SType::Record(ids, ts) => {
            if !eqk(k, "record") {
                return false;
            }
            let xs = match arr_exec(b) {
                Some(xs) => xs,
                None => return false,
            };
            if xs.len() != ts.len() || xs.len() != ids.len() {
                return false;
            }
            let mut i = 0;
            while i < xs.len()
                invariant
                    i <= xs@.len(),
                    xs@.len() == ts@.len(),
                    xs@.len() == ids@.len(),
                    arr(*b) == Some(xs@),
                    one(*j) == Some((k@, *b)),
                    k@ == "record"@,
                    *t == SType::Record(*ids, *ts),
                    forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*j => #[trigger] xs@[q]),
                    forall|q: int| 0 <= q < i ==> field_ty_rel(#[trigger] xs@[q], *ns, ids@[q], ts@[q]),
                decreases xs.len() - i,
            {
                if !check_field_ty(&xs[i], ns, ids[i], &ts[i]) {
                    return false;
                }
                i += 1;
            }
            true
        },
        SType::Option(x) => eqk(k, "option") && check_ty(b, ns, x),
        SType::Set(x) => eqk(k, "set") && check_ty(b, ns, x),
        SType::Map(x, y) => eqk(k, "map") && check_ty_at(b, "key", ns, x) && check_ty_at(b, "value", ns, y),
        SType::List(x, max) => eqk(k, "list") && check_ty_at(b, "of", ns, x) && match get_exec(b, "max") {
            Some(m) => is_nat(m, *max),
            None => false,
        },
    }
}

/// オブジェクト `b` のキー `k` の値が型 `t` を表すかを確かめる。
fn check_ty_at(b: &Json, k: &str, ns: &IrNames, t: &SType) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        r ==> ty_at(*b, k@, *ns, *t),
    decreases b, 0nat,
{
    proof {
        lemma_get_dec(*b);
    }
    match get_exec(b, k) {
        Some(x) => check_ty(x, ns, t),
        None => false,
    }
}

/// 配列 `b` の各要素が型の列 `ts` を表すかを確かめる。
fn check_tys(b: &Json, ts: &Vec<SType>, ns: &IrNames) -> (r: bool)
    ensures
        r ==> tys_rel(*b, ts@, *ns),
    decreases b, 0nat,
{
    let xs = match arr_exec(b) {
        Some(xs) => xs,
        None => return false,
    };
    if xs.len() != ts.len() {
        return false;
    }
    proof {
        lemma_arr_dec(*b);
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ts@.len(),
            arr(*b) == Some(xs@),
            forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
            forall|q: int| 0 <= q < i ==> ty_rel(#[trigger] xs@[q], *ns, ts@[q]),
        decreases xs.len() - i,
    {
        if !check_ty(&xs[i], ns, &ts[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn check_field_ty(j: &Json, ns: &IrNames, id: usize, t: &SType) -> (r: bool)
    ensures
        r ==> field_ty_rel(*j, *ns, id, *t),
    decreases j, 1nat,
{
    proof {
        reveal_strlit("name");
        reveal_strlit("type");
    }
    id < ns.fields.len() && check_name(j, "name", &ns.fields[id]) && check_ty_at(j, "type", ns, t)
}

// ---- 式 ----

pub open spec fn ectx(np: usize, nc: usize) -> ECtx {
    ECtx { np: np as nat, nc: nc as nat }
}

pub open spec fn derefs(s: Seq<&TExpr>) -> Seq<TExpr> {
    s.map_values(|x: &TExpr| *x)
}

proof fn lemma_strs_push(v: Seq<Vec<char>>, x: Vec<char>)
    ensures
        strs(v.push(x)) == strs(v).push(x@),
{
    assert(strs(v.push(x)) =~= strs(v).push(x@));
}

fn r1(x: &TExpr) -> (r: Vec<&TExpr>)
    ensures
        derefs(r@) == seq![*x],
{
    let mut v = Vec::new();
    v.push(x);
    proof {
        assert(derefs(v@) =~= seq![*x]);
    }
    v
}

fn r2<'a>(x: &'a TExpr, y: &'a TExpr) -> (r: Vec<&'a TExpr>)
    ensures
        derefs(r@) == seq![*x, *y],
{
    let mut v = Vec::new();
    v.push(x);
    v.push(y);
    proof {
        assert(derefs(v@) =~= seq![*x, *y]);
    }
    v
}

fn r3<'a>(x: &'a TExpr, y: &'a TExpr, z: &'a TExpr) -> (r: Vec<&'a TExpr>)
    ensures
        derefs(r@) == seq![*x, *y, *z],
{
    let mut v = Vec::new();
    v.push(x);
    v.push(y);
    v.push(z);
    proof {
        assert(derefs(v@) =~= seq![*x, *y, *z]);
    }
    v
}

fn rs(es: &Vec<TExpr>) -> (r: Vec<&TExpr>)
    ensures
        derefs(r@) == es@,
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            derefs(v@) == es@.subrange(0, i as int),
        decreases es.len() - i,
    {
        let ghost v0 = v@;
        v.push(&es[i]);
        proof {
            assert(derefs(v@) =~= derefs(v0).push(es@[i as int]));
            assert(es@.subrange(0, i + 1) =~= es@.subrange(0, i as int).push(es@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(es@.subrange(0, es@.len() as int) =~= es@);
    }
    v
}

/// 演算子の表 [`op_form`] の実装。
fn op_form_exec(e: &TExpr) -> (r: Option<(&'static str, Vec<&TExpr>)>)
    ensures
        match r {
            Some((k, es)) => k.is_ascii() && op_form(*e) == Some((k@, derefs(es@))),
            None => op_form(*e) is None,
        },
{
    proof {
        reveal_strlit("add");
        reveal_strlit("sub");
        reveal_strlit("mul");
        reveal_strlit("div");
        reveal_strlit("mod");
        reveal_strlit("lt");
        reveal_strlit("le");
        reveal_strlit("gt");
        reveal_strlit("ge");
        reveal_strlit("eq");
        reveal_strlit("ne");
        reveal_strlit("not");
        reveal_strlit("all");
        reveal_strlit("any");
        reveal_strlit("implies");
        reveal_strlit("ite");
        reveal_strlit("tuple");
        reveal_strlit("some");
        reveal_strlit("is_some");
        reveal_strlit("is_none");
        reveal_strlit("unwrap");
        reveal_strlit("contains");
        reveal_strlit("insert");
        reveal_strlit("remove");
        reveal_strlit("union");
        reveal_strlit("intersection");
        reveal_strlit("difference");
        reveal_strlit("subset");
        reveal_strlit("size");
        reveal_strlit("is_empty");
        reveal_strlit("has_key");
        reveal_strlit("get");
        reveal_strlit("put");
        reveal_strlit("delete");
        reveal_strlit("keys");
        reveal_strlit("at");
        reveal_strlit("first");
        reveal_strlit("last");
        reveal_strlit("push");
        reveal_strlit("pop");
        reveal_strlit("shift");
    }
    match e {
        TExpr::Bin(op, x, y) => match op {
            BinOp::Add => Some(("add", r2(x, y))),
            BinOp::Sub => Some(("sub", r2(x, y))),
            BinOp::Mul => Some(("mul", r2(x, y))),
            BinOp::Div => Some(("div", r2(x, y))),
            BinOp::Mod => Some(("mod", r2(x, y))),
            BinOp::Lt => Some(("lt", r2(x, y))),
            BinOp::Le => Some(("le", r2(x, y))),
            BinOp::Gt => Some(("gt", r2(x, y))),
            BinOp::Ge => Some(("ge", r2(x, y))),
            _ => None,
        },
        TExpr::Eq(pos, x, y) => Some((if *pos { "eq" } else { "ne" }, r2(x, y))),
        TExpr::Not(x) => Some(("not", r1(x))),
        TExpr::Fold(all, es) => Some((if *all { "all" } else { "any" }, rs(es))),
        TExpr::Implies(x, y) => Some(("implies", r2(x, y))),
        TExpr::Ite(p, x, y) => Some(("ite", r3(p, x, y))),
        TExpr::Tuple(es) => Some(("tuple", rs(es))),
        TExpr::Some(x) => Some(("some", r1(x))),
        TExpr::IsSome(x) => Some(("is_some", r1(x))),
        TExpr::IsNone(x) => Some(("is_none", r1(x))),
        TExpr::Unwrap(x) => Some(("unwrap", r1(x))),
        TExpr::SetContains(_, x, y) => Some(("contains", r2(x, y))),
        TExpr::ListContains(x, y) => Some(("contains", r2(x, y))),
        TExpr::Insert(_, x, y) => Some(("insert", r2(x, y))),
        TExpr::Remove(_, x, y) => Some(("remove", r2(x, y))),
        TExpr::SetBin(op, x, y) => match op {
            SetOp::Union => Some(("union", r2(x, y))),
            SetOp::Intersection => Some(("intersection", r2(x, y))),
            SetOp::Difference => Some(("difference", r2(x, y))),
            SetOp::Subset => Some(("subset", r2(x, y))),
        },
        TExpr::Size(x) => Some(("size", r1(x))),
        TExpr::IsEmpty(x) => Some(("is_empty", r1(x))),
        TExpr::HasKey(_, x, y) => Some(("has_key", r2(x, y))),
        TExpr::Get(_, x, y) => Some(("get", r2(x, y))),
        TExpr::Put(_, _, x, y, z) => Some(("put", r3(x, y, z))),
        TExpr::Delete(_, x, y) => Some(("delete", r2(x, y))),
        TExpr::Keys(x) => Some(("keys", r1(x))),
        TExpr::At(x, y) => Some(("at", r2(x, y))),
        TExpr::First(x) => Some(("first", r1(x))),
        TExpr::Last(x) => Some(("last", r1(x))),
        TExpr::Push(_, _, x, y) => Some(("push", r2(x, y))),
        TExpr::Pop(x) => Some(("pop", r1(x))),
        TExpr::Shift(x) => Some(("shift", r1(x))),
        _ => None,
    }
}

/// 式のJSON `j` が、局所変数の名前の列 `sc` のもとで式 `e` を表すかを確かめる。
pub fn check_ex(j: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases j, 4nat,
{
    let (k, b) = match one_exec(j) {
        Some(x) => x,
        None => return false,
    };
    proof {
        lemma_one_dec(*j);
    }
    match op_form_exec(e) {
        Some((key, es)) => eqk(k, key) && check_args(b, &es, ns, np, nc, sc),
        None => check_form(k, b, e, ns, np, nc, sc),
    }
}

/// 配列 `b` の各要素が、式の列 `es` を表すかを確かめる。
fn check_args(b: &Json, es: &Vec<&TExpr>, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> exs_rel(*b, derefs(es@), *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 0nat,
{
    let xs = match arr_exec(b) {
        Some(xs) => xs,
        None => return false,
    };
    if xs.len() != es.len() {
        return false;
    }
    proof {
        lemma_arr_dec(*b);
    }
    let ghost s0 = sc@;
    let mut i = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            xs@.len() == es@.len(),
            arr(*b) == Some(xs@),
            sc@ == s0,
            s0 == old(sc)@,
            forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
            forall|q: int| 0 <= q < i ==> ex_rel(#[trigger] xs@[q], derefs(es@)[q], *ns, ectx(np, nc), strs(s0)),
        decreases es.len() - i,
    {
        if !check_ex(&xs[i], es[i], ns, np, nc, sc) {
            return false;
        }
        i += 1;
    }
    true
}

/// 配列 `b` の各要素が、式の列 `es` を表すかを確かめる。
fn check_exs(b: &Json, es: &Vec<TExpr>, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> exs_rel(*b, es@, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    check_args(b, &rs(es), ns, np, nc, sc)
}

/// オブジェクト `b` のキー `k` の値が、式 `e` を表すかを確かめる。
fn check_ex_at(b: &Json, k: &str, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_at(*b, k@, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 0nat,
{
    proof {
        lemma_get_dec(*b);
    }
    match get_exec(b, k) {
        Some(x) => check_ex(x, e, ns, np, nc, sc),
        None => false,
    }
}

/// オペランドの配列でない式を確かめる（[`form_rel`]）。
fn check_form(k: &Vec<char>, b: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> form_rel(k@, *b, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 3nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_) => check_ref(
            k,
            b,
            e,
            ns,
            np,
            nc,
            sc,
        ),
        TExpr::Let(..) | TExpr::Quant(..) => check_bind(k, b, e, ns, np, nc, sc),
        _ => check_shape(k, b, e, ns, np, nc, sc),
    }
}

/// リテラルと参照。
fn check_ref(k: &Vec<char>, b: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r ==> form_rel(k@, *b, *e, *ns, ectx(np, nc), strs(sc@)),
{
    proof {
        reveal_strlit("int");
        reveal_strlit("bool");
        reveal_strlit("enum");
        reveal_strlit("var");
        reveal_strlit("next");
        reveal_strlit("param");
        reveal_strlit("choice");
        reveal_strlit("output");
        reveal_strlit("local");
        reveal_strlit("const");
        reveal_strlit("type");
        reveal_strlit("variant");
    }
    match e {
        TExpr::Lit(Value::Int(n)) => eqk(k, "int") && match b {
            Json::Int(m) => *m == *n,
            _ => false,
        },
        TExpr::Lit(Value::Bool(x)) => eqk(k, "bool") && match b {
            Json::Bool(y) => *y == *x,
            _ => false,
        },
        TExpr::Lit(Value::Enum(id, v)) => {
            if !eqk(k, "enum") || *id >= ns.variants.len() {
                return false;
            }
            match (get_exec(b, "type"), get_exec(b, "variant")) {
                (Some(Json::Str(tn)), Some(Json::Str(vn))) => match (
                    index_of_exec(&ns.enums, tn),
                    index_of_exec(&ns.variants[*id], vn),
                ) {
                    (Some(a), Some(q)) => a == *id && *v >= 0 && (*v as u128) == (q as u128),
                    _ => false,
                },
                _ => false,
            }
        },
        TExpr::Var(x) => eqk(k, "var") && is_nat(b, *x),
        TExpr::Next(x) => eqk(k, "next") && is_nat(b, *x),
        TExpr::Arg(x) => {
            if eqk(k, "param") {
                *x < np && is_nat(b, *x)
            } else if eqk(k, "choice") {
                *x >= np && *x - np < nc && is_nat(b, *x - np)
            } else {
                false
            }
        },
        TExpr::Out => eqk(k, "output") && is_empty_obj(b),
        TExpr::Local(i) => eqk(k, "local") && match str_exec(b) {
            Some(n) => match last_of_exec(sc, n) {
                Some(q) => q == *i,
                None => false,
            },
            None => false,
        },
        TExpr::Const(i) => eqk(k, "const") && match str_exec(b) {
            Some(n) => match index_of_exec(&ns.consts, n) {
                Some(q) => q == *i,
                None => false,
            },
            None => false,
        },
        _ => false,
    }
}

/// `let` と量化。本体は名前を束縛して確かめる。
#[allow(unused_variables)]
fn check_bind(k: &Vec<char>, b: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> form_rel(k@, *b, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 2nat,
{
    proof {
        reveal_strlit("let");
        reveal_strlit("forall");
        reveal_strlit("exists");
        reveal_strlit("name");
        reveal_strlit("value");
        reveal_strlit("body");
    }
    let n = match get_exec(b, "name") {
        Some(Json::Str(n)) => n,
        _ => return false,
    };
    let body = match e {
        TExpr::Let(x, y) => {
            if !eqk(k, "let") || !check_ex_at(b, "value", x, ns, np, nc, sc) {
                return false;
            }
            y
        },
        TExpr::Quant(all, over, y) => {
            if !eqk(k, if *all { "forall" } else { "exists" }) || !check_over(b, over, ns, np, nc, sc) {
                return false;
            }
            y
        },
        _ => return false,
    };
    let ghost v0 = sc@;
    sc.push(copy_chars(n));
    proof {
        lemma_strs_push(v0, sc@.last());
        assert(sc@ == v0.push(sc@.last()));
    }
    let ok = check_ex_at(b, "body", body, ns, np, nc, sc);
    sc.pop();
    proof {
        assert(sc@ =~= v0);
    }
    ok
}

/// 量化のたどる値。
fn check_over(b: &Json, over: &Over, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> over_rel(*b, *over, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    proof {
        reveal_strlit("in");
        reveal_strlit("type");
    }
    match over {
        Over::Set(_, x) => get_exec(b, "type").is_none() && check_ex_at(b, "in", x, ns, np, nc, sc),
        Over::Map(_, x) => get_exec(b, "type").is_none() && check_ex_at(b, "in", x, ns, np, nc, sc),
        Over::List(x) => get_exec(b, "type").is_none() && check_ex_at(b, "in", x, ns, np, nc, sc),
        Over::Type(t) => get_exec(b, "in").is_none() && check_ty_at(b, "type", ns, t),
    }
}

/// Record、`nth`、`field`、`none`、Set・Map・List のリテラル。
fn check_shape(k: &Vec<char>, b: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> form_rel(k@, *b, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 2nat,
{
    proof {
        lemma_get_dec(*b);
        lemma_arr_dec(*b);
        reveal_strlit("record");
        reveal_strlit("nth");
        reveal_strlit("field");
        reveal_strlit("none");
        reveal_strlit("set");
        reveal_strlit("map");
        reveal_strlit("list");
        reveal_strlit("of");
        reveal_strlit("index");
        reveal_strlit("name");
        reveal_strlit("key");
        reveal_strlit("value");
        reveal_strlit("items");
        reveal_strlit("max");
    }
    match e {
        TExpr::Record(ids, es) => {
            if !eqk(k, "record") {
                return false;
            }
            let xs = match arr_exec(b) {
                Some(xs) => xs,
                None => return false,
            };
            if xs.len() != ids.len() || xs.len() != es.len() {
                return false;
            }
            let ghost s0 = sc@;
            let mut i = 0;
            while i < xs.len()
                invariant
                    i <= xs@.len(),
                    xs@.len() == ids@.len(),
                    xs@.len() == es@.len(),
                    arr(*b) == Some(xs@),
                    sc@ == s0,
                    s0 == old(sc)@,
                    forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
                    forall|q: int| 0 <= q < i ==> field_rel(#[trigger] xs@[q], ids@[q], es@[q], *ns, ectx(np, nc), strs(s0)),
                decreases xs.len() - i,
            {
                if !check_field(&xs[i], ids[i], &es[i], ns, np, nc, sc) {
                    return false;
                }
                i += 1;
            }
            true
        },
        TExpr::Nth(x, idx) => eqk(k, "nth") && match get_exec(b, "index") {
            Some(ij) => is_nat(ij, *idx) && check_ex_at(b, "of", x, ns, np, nc, sc),
            None => false,
        },
        TExpr::Field(x, id, _) => eqk(k, "field") && *id < ns.fields.len() && check_name(b, "name", &ns.fields[*id])
            && check_ex_at(b, "of", x, ns, np, nc, sc),
        TExpr::None(t) => eqk(k, "none") && check_ty(b, ns, t),
        TExpr::SetLit(t, es) => eqk(k, "set") && check_ty_at(b, "of", ns, t) && match get_exec(b, "items") {
            Some(itj) => check_exs(itj, es, ns, np, nc, sc),
            None => false,
        },
        TExpr::ListLit(t, max, es) => eqk(k, "list") && check_ty_at(b, "of", ns, t) && match (
            get_exec(b, "max"),
            get_exec(b, "items"),
        ) {
            (Some(mj), Some(itj)) => is_nat(mj, *max) && check_exs(itj, es, ns, np, nc, sc),
            _ => false,
        },
        TExpr::MapLit(kt, vt, items) => {
            if !eqk(k, "map") || !check_ty_at(b, "key", ns, kt) || !check_ty_at(b, "value", ns, vt) {
                return false;
            }
            let itj = match get_exec(b, "items") {
                Some(x) => x,
                None => return false,
            };
            let xs = match arr_exec(itj) {
                Some(xs) => xs,
                None => return false,
            };
            if xs.len() != items.len() {
                return false;
            }
            proof {
                lemma_arr_dec(*itj);
                assert forall|q: int| 0 <= q < xs@.len() implies decreases_to!(*b => #[trigger] xs@[q]) by {
                    assert(decreases_to!(*itj => xs@[q]));
                }
            }
            let ghost s0 = sc@;
            let mut i = 0;
            while i < xs.len()
                invariant
                    i <= xs@.len(),
                    xs@.len() == items@.len(),
                    arr(*itj) == Some(xs@),
                    sc@ == s0,
                    s0 == old(sc)@,
                    forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
                    forall|q: int|
                        0 <= q < i ==> exs_rel(#[trigger] xs@[q], seq![items@[q].key, items@[q].value], *ns, ectx(np, nc), strs(s0)),
                decreases xs.len() - i,
            {
                let it = &items[i];
                let pair = r2(&it.key, &it.value);
                if !check_args(&xs[i], &pair, ns, np, nc, sc) {
                    return false;
                }
                i += 1;
            }
            true
        },
        _ => false,
    }
}

/// Recordの式のフィールド。
fn check_field(j: &Json, id: usize, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> field_rel(*j, id, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases j, 1nat,
{
    proof {
        reveal_strlit("name");
        reveal_strlit("expr");
    }
    id < ns.fields.len() && check_name(j, "name", &ns.fields[id]) && check_ex_at(j, "expr", e, ns, np, nc, sc)
}

// ---- モデル ----

/// 局所変数のない文脈で、式のJSON `j` が式 `e` を表すかを確かめる。
fn check_top(j: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    ensures
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), Seq::empty()),
{
    let mut sc: Vec<Vec<char>> = Vec::new();
    proof {
        assert(strs(sc@) =~= Seq::<Seq<char>>::empty());
    }
    check_ex(j, e, ns, np, nc, &mut sc)
}

/// キー `k` の値（省略できない）が、局所変数のない文脈で式 `e` を表す。
fn check_top_at(j: &Json, k: &str, e: &TExpr, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        r ==> get(*j, k@) is Some && ex_rel(at(*j, k@), *e, *ns, ectx(np, nc), Seq::empty()),
{
    match get_exec(j, k) {
        Some(x) => check_top(x, e, ns, np, nc),
        None => false,
    }
}

/// キー `k` の値が、名前 `n` の文字列である。
fn check_name(j: &Json, k: &str, n: &Vec<char>) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        r ==> get(*j, k@) is Some && str_of(at(*j, k@)) == Some(n@),
{
    match get_exec(j, k) {
        Some(x) => match str_exec(x) {
            Some(s) => chars_eq(s, n),
            None => false,
        },
        None => false,
    }
}

/// 省略できる配列のキー。
fn opt_arr_exec<'a>(j: &'a Json, k: &str) -> (r: Option<&'a [Json]>)
    requires
        k.is_ascii(),
    ensures
        match r {
            Some(xs) => opt_arr(*j, k@) == Some(xs@),
            None => opt_arr(*j, k@) is None,
        },
{
    match present(j, k) {
        None => {
            let e: &[Json] = &[];
            proof {
                assert(e@ =~= Seq::<Json>::empty());
            }
            Some(e)
        },
        Some(x) => match arr_exec(x) {
            Some(xs) => Some(xs.as_slice()),
            None => None,
        },
    }
}

/// 名前の表の名前に重複がない。
fn check_names(ns: &IrNames) -> (r: bool)
    ensures
        r ==> names_ok(*ns),
{
    if !distinct_exec(&ns.enums) || ns.variants.len() != ns.enums.len() || !distinct_exec(&ns.consts)
        || !distinct_exec(&ns.actions) || !distinct_exec(&ns.fields) {
        return false;
    }
    let mut i = 0;
    while i < ns.variants.len()
        invariant
            i <= ns.variants@.len(),
            forall|q: int| 0 <= q < i ==> distinct(#[trigger] strs(ns.variants@[q]@)),
        decreases ns.variants.len() - i,
    {
        if !distinct_exec(&ns.variants[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn check_enum(j: &Json, ns: &IrNames, i: usize, n: i64) -> (r: bool)
    requires
        i < ns.enums@.len(),
        i < ns.variants@.len(),
    ensures
        r ==> enum_rel(*j, *ns, i as int, n),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("variants");
    }
    if !check_name(j, "name", &ns.enums[i]) {
        return false;
    }
    let vs = match get_exec(j, "variants") {
        Some(v) => match arr_exec(v) {
            Some(xs) => xs,
            None => return false,
        },
        None => return false,
    };
    let labels = &ns.variants[i];
    if vs.len() != labels.len() || (vs.len() as u128) != (n as u128) || n < 0 {
        return false;
    }
    let mut q = 0;
    while q < vs.len()
        invariant
            q <= vs@.len(),
            vs@.len() == labels@.len(),
            forall|p: int| 0 <= p < q ==> #[trigger] str_of(vs@[p]) == Some(labels@[p]@),
        decreases vs.len() - q,
    {
        match str_exec(&vs[q]) {
            Some(x) => if !chars_eq(x, &labels[q]) {
                return false;
            },
            None => return false,
        }
        q += 1;
    }
    true
}

fn check_const(j: &Json, ns: &IrNames, i: usize, sm: &SModel) -> (r: bool)
    requires
        i < ns.consts@.len(),
        i < sm.consts@.len(),
    ensures
        r ==> const_rel(*j, *ns, i as int, *sm),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("type");
        reveal_strlit("value");
    }
    check_name(j, "name", &ns.consts[i]) && check_ty_at(j, "type", ns, &sm.consts[i].ty) && check_top_at(
        j,
        "value",
        &sm.consts[i].expr,
        ns,
        0,
        0,
    )
}

fn check_state(j: &Json, ns: &IrNames, i: usize, sm: &SModel) -> (r: bool)
    requires
        i < ns.states@.len(),
        i < sm.states@.len(),
        i < sm.inits@.len(),
    ensures
        r ==> state_rel(*j, *ns, i as int, *sm),
{
    proof {
        reveal_strlit("id");
        reveal_strlit("name");
        reveal_strlit("type");
        reveal_strlit("initial");
        reveal_strlit("initial_in");
    }
    match get_exec(j, "id") {
        Some(x) => if !is_nat(x, i) {
            return false;
        },
        None => {},
    }
    if !check_name(j, "name", &ns.states[i]) || !check_ty_at(j, "type", ns, &sm.states[i]) {
        return false;
    }
    let inits = &sm.inits[i];
    match (get_exec(j, "initial"), get_exec(j, "initial_in")) {
        (Some(x), None) => inits.len() == 1 && check_top(x, &inits[0], ns, 0, 0),
        (None, Some(xs)) => {
            let mut sc: Vec<Vec<char>> = Vec::new();
            proof {
                assert(strs(sc@) =~= Seq::<Seq<char>>::empty());
            }
            check_exs(xs, inits, ns, 0, 0, &mut sc)
        },
        _ => false,
    }
}

proof fn lemma_doms_step(xs: Seq<Json>, i: int)
    requires
        0 <= i < xs.len(),
    ensures
        doms(xs.skip(i), i as nat) == (if get(xs[i], "in"@) is Some {
            seq![(i as nat, at(xs[i], "in"@))]
        } else {
            Seq::empty()
        }) + doms(xs.skip(i + 1), (i + 1) as nat),
{
    let s = xs.skip(i);
    assert(s.drop_first() =~= xs.skip(i + 1));
    assert(s[0] == xs[i]);
    if get(xs[i], "in"@) is None {
        assert(Seq::<(nat, Json)>::empty() + doms(xs.skip(i + 1), (i + 1) as nat) =~= doms(xs.skip(i + 1), (i + 1) as nat));
    }
}

/// 動的ドメインを持つ引数の、番号とドメインの式。
fn domains<'a>(px: &'a [Json], cx: &'a [Json]) -> (r: Option<(Vec<usize>, Vec<&'a Json>)>)
    ensures
        r matches Some(r) ==> r.0@.len() == r.1@.len() && r.0@.len() == doms(px@ + cx@, 0).len() && forall|q: int|
            0 <= q < r.0@.len() ==> #[trigger] doms(px@ + cx@, 0)[q] == (r.0@[q] as nat, *r.1@[q]),
{
    let ghost xs = px@ + cx@;
    let n = match px.len().checked_add(cx.len()) {
        Some(n) => n,
        None => return None,
    };
    proof {
        reveal_strlit("in");
    }
    let mut idx: Vec<usize> = Vec::new();
    let mut ds: Vec<&Json> = Vec::new();
    let ghost mut built: Seq<(nat, Json)> = Seq::empty();
    proof {
        assert(xs.skip(0) =~= xs);
    }
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == xs.len(),
            n == px@.len() + cx@.len(),
            xs == px@ + cx@,
            idx@.len() == ds@.len(),
            idx@.len() == built.len(),
            forall|q: int| 0 <= q < built.len() ==> #[trigger] built[q] == (idx@[q] as nat, *ds@[q]),
            doms(xs, 0) == built + doms(xs.skip(i as int), i as nat),
        decreases n - i,
    {
        proof {
            lemma_doms_step(xs, i as int);
            reveal_strlit("in");
        }
        let ghost b0 = built;
        let x: &Json = if i < px.len() {
            &px[i]
        } else {
            &cx[i - px.len()]
        };
        proof {
            assert(*x == xs[i as int]);
        }
        match get_exec(x, "in") {
            Some(d) => {
                idx.push(i);
                ds.push(d);
                proof {
                    built = built.push((i as nat, *d));
                    assert(b0 + (seq![(i as nat, *d)] + doms(xs.skip(i + 1), (i + 1) as nat)) =~= built + doms(
                        xs.skip(i + 1),
                        (i + 1) as nat,
                    ));
                }
            },
            None => {},
        }
        i += 1;
    }
    proof {
        assert(xs.skip(xs.len() as int) =~= Seq::<Json>::empty());
        assert(built + Seq::<(nat, Json)>::empty() =~= built);
    }
    Some((idx, ds))
}

/// 利用者の guard。
fn check_user_guard(j: &Json, u: &TExpr, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    ensures
        r ==> user_guard_rel(*j, *u, *ns, ectx(np, nc)),
{
    proof {
        reveal_strlit("guard");
    }
    match present(j, "guard") {
        None => match u {
            TExpr::Lit(Value::Bool(true)) => true,
            _ => false,
        },
        Some(g) => check_top(g, u, ns, np, nc),
    }
}

/// 動的ドメインの検査。
fn check_member(i: usize, d: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    ensures
        r ==> member_rel((i as nat, *d), *e, *ns, ectx(np, nc)),
{
    match e {
        TExpr::SetContains(_, x, y) => match &**y {
            TExpr::Arg(a) => *a == i && check_top(d, x, ns, np, nc),
            _ => false,
        },
        TExpr::ListContains(x, y) => match &**y {
            TExpr::Arg(a) => *a == i && check_top(d, x, ns, np, nc),
            _ => false,
        },
        _ => false,
    }
}

fn check_guard(j: &Json, px: &[Json], cx: &[Json], g: &TExpr, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    ensures
        r ==> guard_rel(*j, doms(px@ + cx@, 0), *g, *ns, ectx(np, nc)),
{
    let ghost all = px@ + cx@;
    let (idx, ds) = match domains(px, cx) {
        Some(r) => r,
        None => return false,
    };
    if idx.len() == 0 {
        return check_user_guard(j, g, ns, np, nc);
    }
    match g {
        TExpr::Fold(a, es) => {
            if !*a || es.len() == 0 || es.len() - 1 != idx.len() {
                return false;
            }
            if !check_user_guard(j, &es[idx.len()], ns, np, nc) {
                return false;
            }
            let mut q = 0;
            while q < idx.len()
                invariant
                    q <= idx@.len(),
                    idx@.len() == ds@.len(),
                    idx@.len() == doms(all, 0).len(),
                    es@.len() == idx@.len() + 1,
                    forall|p: int| 0 <= p < idx@.len() ==> #[trigger] doms(all, 0)[p] == (idx@[p] as nat, *ds@[p]),
                    forall|p: int| 0 <= p < q ==> #[trigger] member_rel(doms(all, 0)[p], es@[p], *ns, ectx(np, nc)),
                decreases idx.len() - q,
            {
                if !check_member(idx[q], ds[q], &es[q], ns, np, nc) {
                    return false;
                }
                q += 1;
            }
            true
        },
        _ => false,
    }
}

/// 引数の宣言の列 `xs` の名前と型が、`names` と `tys[off..]` に対応する。
fn check_binds(xs: &[Json], names: &Vec<Vec<char>>, tys: &Vec<SType>, off: usize, ns: &IrNames) -> (r: bool)
    requires
        off <= tys@.len(),
    ensures
        r ==> xs@.len() == names@.len() && off + xs@.len() <= tys@.len() && binds_rel(
            xs@,
            names@,
            tys@.subrange(off as int, off + xs@.len()),
            *ns,
        ),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("type");
    }
    if xs.len() != names.len() || xs.len() > tys.len() - off {
        return false;
    }
    let ghost ts = tys@.subrange(off as int, off + xs@.len());
    let _tl = tys.len();
    let mut i = 0;
    while i < xs.len()
        invariant
            _tl == tys@.len(),
            i <= xs@.len(),
            xs@.len() == names@.len(),
            off + xs@.len() <= tys@.len(),
            ts == tys@.subrange(off as int, off + xs@.len()),
            forall|q: int|
                0 <= q < i ==> name_is(#[trigger] xs@[q], "name"@, names@[q]@) && ty_at(xs@[q], "type"@, *ns, ts[q]),
        decreases xs.len() - i,
    {
        proof {
            reveal_strlit("name");
            reveal_strlit("type");
            assert(off + i < tys@.len());
        }
        if !check_name(&xs[i], "name", &names[i]) || !check_ty_at(&xs[i], "type", ns, &tys[off + i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// 型の列の幅の和。
fn widths(ts: &Vec<SType>, n: usize, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        n <= ts@.len(),
    ensures
        r matches Some(w) ==> w as int == crate::value::encoding::width_sum(crate::value::encoding::stys(ts@.take(n as int)), enums@),
{
    let mut w: usize = 0;
    let mut i = 0;
    proof {
        crate::value::encoding::lemma_stys(ts@.take(0));
    }
    while i < n
        invariant
            i <= n <= ts@.len(),
            w as int == crate::value::encoding::width_sum(crate::value::encoding::stys(ts@.take(i as int)), enums@),
        decreases n - i,
    {
        let x = match crate::value::stype_exec::stype_width(&ts[i], enums) {
            Some(x) => x,
            None => return None,
        };
        w = match w.checked_add(x) {
            Some(y) => y,
            None => return None,
        };
        proof {
            let a = ts@.take(i as int);
            let b = ts@.take(i + 1);
            crate::value::encoding::lemma_stys(a);
            crate::value::encoding::lemma_stys(b);
            assert(b.drop_last() =~= a);
            assert(crate::value::encoding::stys(b).drop_last() =~= crate::value::encoding::stys(a));
            assert(crate::value::encoding::stys(b).last() == crate::value::encoding::sty(ts@[i as int]));
        }
        i += 1;
    }
    Some(w)
}

fn check_update(j: &Json, u: &crate::value::smodel::SUpdate, ns: &IrNames, np: usize, nc: usize) -> (r: bool)
    ensures
        r ==> update_rel(*j, *u, *ns, ectx(np, nc)),
{
    proof {
        reveal_strlit("target");
        reveal_strlit("expr");
    }
    match get_exec(j, "target") {
        Some(t) => is_nat(t, u.var) && check_top_at(j, "expr", &u.expr, ns, np, nc),
        None => false,
    }
}

fn check_action(j: &Json, ns: &IrNames, a: usize, sa: &SAction, enums: &Vec<i64>) -> (r: bool)
    requires
        a < ns.actions@.len(),
        a < ns.params@.len(),
        a < ns.choices@.len(),
    ensures
        r ==> action_rel(*j, *ns, a as int, *sa, enums@),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("params");
        reveal_strlit("choices");
        reveal_strlit("updates");
        reveal_strlit("output");
        reveal_strlit("type");
        reveal_strlit("expr");
    }
    let ps = &ns.params[a];
    let cs = &ns.choices[a];
    let np = ps.len();
    let nc = cs.len();
    if !check_name(j, "name", &ns.actions[a]) {
        return false;
    }
    let (px, cx) = match (opt_arr_exec(j, "params"), opt_arr_exec(j, "choices")) {
        (Some(p), Some(c)) => (p, c),
        _ => return false,
    };
    if sa.args.len() < np || sa.args.len() - np != nc {
        return false;
    }
    if !check_binds(px, ps, &sa.args, 0, ns) || !check_binds(cx, cs, &sa.args, np, ns) {
        return false;
    }
    proof {
        assert(sa.args@.subrange(0, px@.len() as int) =~= sa.args@.take(ps@.len() as int));
        assert(sa.args@.subrange(np as int, np + cx@.len()) =~= sa.args@.skip(ps@.len() as int));
    }
    match widths(&sa.args, np, enums) {
        Some(w) => if w != sa.n_params {
            return false;
        },
        None => return false,
    }
    if !check_guard(j, px, cx, &sa.guard, ns, np, nc) {
        return false;
    }
    let us = match opt_arr_exec(j, "updates") {
        Some(us) => us,
        None => return false,
    };
    if us.len() != sa.updates.len() {
        return false;
    }
    let mut u = 0;
    while u < us.len()
        invariant
            u <= us@.len(),
            us@.len() == sa.updates@.len(),
            a < ns.params@.len(),
            a < ns.choices@.len(),
            np == ns.params@[a as int]@.len(),
            nc == ns.choices@[a as int]@.len(),
            forall|q: int| 0 <= q < u ==> #[trigger] update_rel(us@[q], sa.updates@[q], *ns, act_ctx(*ns, a as int)),
        decreases us.len() - u,
    {
        if !check_update(&us[u], &sa.updates[u], ns, np, nc) {
            return false;
        }
        u += 1;
    }
    match (present(j, "output"), &sa.output) {
        (None, None) => true,
        (Some(o), Some(so)) => check_ty_at(o, "type", ns, &so.ty) && check_top_at(o, "expr", &so.expr, ns, np, nc),
        _ => false,
    }
}


fn check_invariant(j: &Json, ns: &IrNames, i: usize, sm: &SModel) -> (r: bool)
    requires
        i < ns.invariants@.len(),
        i < sm.invariants@.len(),
    ensures
        r ==> invariant_rel(*j, *ns, i as int, *sm),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("expr");
    }
    check_name(j, "name", &ns.invariants[i]) && check_top_at(j, "expr", &sm.invariants[i], ns, 0, 0)
}

fn check_contract(j: &Json, ns: &IrNames, k: usize, sm: &SModel) -> (r: bool)
    requires
        k < ns.contracts@.len(),
        k < sm.contracts@.len(),
        ns.params@.len() == ns.actions@.len(),
        ns.choices@.len() == ns.actions@.len(),
    ensures
        r ==> contract_rel(*j, *ns, k as int, *sm),
{
    proof {
        reveal_strlit("name");
        reveal_strlit("action");
        reveal_strlit("expr");
    }
    let con = &sm.contracts[k];
    if !check_name(j, "name", &ns.contracts[k]) {
        return false;
    }
    let an = match get_exec(j, "action") {
        Some(x) => match str_exec(x) {
            Some(n) => n,
            None => return false,
        },
        None => return false,
    };
    match index_of_exec(&ns.actions, an) {
        Some(a) => {
            if a != con.action {
                return false;
            }
            proof {
                lemma_index_of_bound(strs(ns.actions@), an@);
            }
            check_top_at(j, "expr", &con.expr, ns, ns.params[a].len(), ns.choices[a].len())
        },
        None => false,
    }
}

proof fn lemma_index_of_bound(s: Seq<Seq<char>>, x: Seq<char>)
    ensures
        index_of(s, x) matches Some(i) ==> 0 <= i < s.len(),
    decreases s.len(),
{
    if s.len() > 0 && s[0] != x {
        lemma_index_of_bound(s.drop_first(), x);
    }
}

/// 省略できる式のキー。
fn check_opt_ex(j: &Json, k: &str, e: &Option<TExpr>, ns: &IrNames) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        r ==> opt_ex_rel(*j, k@, *e, *ns),
{
    match (present(j, k), e) {
        (None, None) => true,
        (Some(x), Some(y)) => check_top(x, y, ns, 0, 0),
        _ => false,
    }
}

/// `check_enum` を、列 `xs` のすべての要素について確かめる。
fn check_all_enums(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.enums@.len(),
        xs@.len() == sm.enums@.len(),
        ns.variants@.len() == ns.enums@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] enum_rel(xs@[q], *ns, q, sm.enums@[q]),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.enums@.len(),
            xs@.len() == sm.enums@.len(),
            ns.variants@.len() == ns.enums@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] enum_rel(xs@[q], *ns, q, sm.enums@[q]),
        decreases xs.len() - i,
    {
        if !check_enum(&xs[i], ns, i, sm.enums[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// `check_const` を、列 `xs` のすべての要素について確かめる。
fn check_all_consts(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.consts@.len(),
        xs@.len() == sm.consts@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] const_rel(xs@[q], *ns, q, *sm),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.consts@.len(),
            xs@.len() == sm.consts@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] const_rel(xs@[q], *ns, q, *sm),
        decreases xs.len() - i,
    {
        if !check_const(&xs[i], ns, i, sm) {
            return false;
        }
        i += 1;
    }
    true
}

/// `check_state` を、列 `xs` のすべての要素について確かめる。
fn check_all_states(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.states@.len(),
        xs@.len() == sm.states@.len(),
        xs@.len() == sm.inits@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] state_rel(xs@[q], *ns, q, *sm),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.states@.len(),
            xs@.len() == sm.states@.len(),
            xs@.len() == sm.inits@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] state_rel(xs@[q], *ns, q, *sm),
        decreases xs.len() - i,
    {
        if !check_state(&xs[i], ns, i, sm) {
            return false;
        }
        i += 1;
    }
    true
}

/// `check_action` を、列 `xs` のすべての要素について確かめる。
fn check_all_actions(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.actions@.len(),
        xs@.len() == sm.actions@.len(),
        xs@.len() == ns.params@.len(),
        xs@.len() == ns.choices@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] action_rel(xs@[q], *ns, q, sm.actions@[q], sm.enums@),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.actions@.len(),
            xs@.len() == sm.actions@.len(),
            xs@.len() == ns.params@.len(),
            xs@.len() == ns.choices@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] action_rel(xs@[q], *ns, q, sm.actions@[q], sm.enums@),
        decreases xs.len() - i,
    {
        if !check_action(&xs[i], ns, i, &sm.actions[i], &sm.enums) {
            return false;
        }
        i += 1;
    }
    true
}

/// `check_invariant` を、列 `xs` のすべての要素について確かめる。
fn check_all_invariants(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.invariants@.len(),
        xs@.len() == sm.invariants@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] invariant_rel(xs@[q], *ns, q, *sm),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.invariants@.len(),
            xs@.len() == sm.invariants@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] invariant_rel(xs@[q], *ns, q, *sm),
        decreases xs.len() - i,
    {
        if !check_invariant(&xs[i], ns, i, sm) {
            return false;
        }
        i += 1;
    }
    true
}

/// `check_contract` を、列 `xs` のすべての要素について確かめる。
fn check_all_contracts(xs: &[Json], ns: &IrNames, sm: &SModel) -> (r: bool)
    requires
        xs@.len() == ns.contracts@.len(),
        xs@.len() == sm.contracts@.len(),
        ns.params@.len() == ns.actions@.len(),
        ns.choices@.len() == ns.actions@.len(),
    ensures
        r ==> forall|q: int| 0 <= q < xs@.len() ==> #[trigger] contract_rel(xs@[q], *ns, q, *sm),
{
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            xs@.len() == ns.contracts@.len(),
            xs@.len() == sm.contracts@.len(),
            ns.params@.len() == ns.actions@.len(),
            ns.choices@.len() == ns.actions@.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] contract_rel(xs@[q], *ns, q, *sm),
        decreases xs.len() - i,
    {
        if !check_contract(&xs[i], ns, i, sm) {
            return false;
        }
        i += 1;
    }
    true
}

/// IRのJSON `j` が、名前の表 `ns` のもとで、名前を解決したモデル `sm` を表すかを確かめる。
pub fn check_ir(j: &Json, ns: &IrNames, sm: &SModel) -> (r: bool)
    ensures
        r ==> ir_rel(*j, *ns, *sm),
{
    proof {
        reveal_strlit("enums");
        reveal_strlit("constants");
        reveal_strlit("states");
        reveal_strlit("initial_constraint");
        reveal_strlit("actions");
        reveal_strlit("invariants");
        reveal_strlit("contracts");
        reveal_strlit("terminal");
    }
    if !check_names(ns) {
        return false;
    }
    // 列挙型
    let es = match opt_arr_exec(j, "enums") {
        Some(x) => x,
        None => return false,
    };
    if es.len() != ns.enums.len() || es.len() != sm.enums.len() {
        return false;
    }
    if !check_all_enums(es, ns, sm) {
        return false;
    }
    // 定数
    let cs = match opt_arr_exec(j, "constants") {
        Some(x) => x,
        None => return false,
    };
    if cs.len() != ns.consts.len() || cs.len() != sm.consts.len() {
        return false;
    }
    if !check_all_consts(cs, ns, sm) {
        return false;
    }
    // 状態変数
    let ss = match get_exec(j, "states") {
        Some(x) => match arr_exec(x) {
            Some(xs) => xs,
            None => return false,
        },
        None => return false,
    };
    if ss.len() != ns.states.len() || ss.len() != sm.states.len() || ss.len() != sm.inits.len() {
        return false;
    }
    if !check_all_states(ss, ns, sm) {
        return false;
    }
    if !check_opt_ex(j, "initial_constraint", &sm.constraint, ns) {
        return false;
    }
    // 操作
    let acts = match opt_arr_exec(j, "actions") {
        Some(x) => x,
        None => return false,
    };
    if acts.len() != ns.actions.len() || acts.len() != sm.actions.len() || acts.len() != ns.params.len() || acts.len()
        != ns.choices.len() {
        return false;
    }
    if !check_all_actions(acts, ns, sm) {
        return false;
    }
    // 不変条件
    let is = match opt_arr_exec(j, "invariants") {
        Some(x) => x,
        None => return false,
    };
    if is.len() != ns.invariants.len() || is.len() != sm.invariants.len() {
        return false;
    }
    if !check_all_invariants(is, ns, sm) {
        return false;
    }
    // 遷移契約
    let ks = match opt_arr_exec(j, "contracts") {
        Some(x) => x,
        None => return false,
    };
    if ks.len() != ns.contracts.len() || ks.len() != sm.contracts.len() {
        return false;
    }
    if !check_all_contracts(ks, ns, sm) {
        return false;
    }
    check_opt_ex(j, "terminal", &sm.terminal, ns)
}

/// IRのJSON `j` と、`fmspec-ir` が組み立てた名前の表 `ns` とモデル `sm` の対応を確かめてから、モデルを下ろす。
/// 対応しなければ `None` を返す。
pub fn lower_checked(j: &Json, ns: &IrNames, sm: &SModel, maps: &Vec<SMap>) -> (r: Option<
    Result<(RawModel, Vec<Expr>), LowerError>,
>)
    ensures
        r is Some ==> ir_rel(*j, *ns, *sm),
        r matches Some(Ok((m, _))) ==> crate::model::model_lower::lowers_model(*sm, m),
        r matches Some(Ok((m, _))) ==> crate::model::model_wf::sm_wf(*sm) ==> crate::kernel::typing::wf(m),
        r matches Some(Err(e)) ==> crate::model::lower_error::user_err(e) || (crate::model::lower_error::type_err(e)
            && !crate::model::model_total::model_typed(*sm)) || (e is Mapping && maps@.len() > 0),
{
    if !check_ir(j, ns, sm) {
        return None;
    }
    Some(lower_model_map(sm, maps))
}

} // verus!
