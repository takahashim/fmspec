//! IRのJSONと、名前を解決したモデルの対応の検査。
//!
//! [`check_ir`] が真を返すなら、[`crate::ir::ir_rel`] が成り立つ。
//! [`lower_checked`] は、対応を確かめてからモデルを下ろす。

use crate::encoding::SType;
use crate::expr_copy::copy_expr;
use crate::ir::*;
use crate::model::{BinOp, Expr, RawModel, Value};
use crate::model_lower::{lower_model_map, SMap};
use crate::smodel::LowerError;
use crate::smodel::{SAction, SModel};
use crate::source::{Over, SetOp, TExpr};
use vstd::prelude::*;

verus! {

// ---- 文字列 ----

/// 文字の列が、ASCIIの文字列リテラル `s` と等しい。
fn eqk(a: &Vec<char>, s: &str) -> (r: bool)
    requires
        s.is_ascii(),
    ensures
        r == (a@ == s@),
{
    let n = s.unicode_len();
    if a.len() != n {
        return false;
    }
    let mut i = 0;
    while i < n
        invariant
            n == s@.len(),
            a@.len() == n,
            i <= n,
            s.is_ascii(),
            forall|j: int| 0 <= j < i ==> a@[j] == s@[j],
        decreases n - i,
    {
        if a[i] != s.get_char(i) {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= s@);
    }
    true
}

fn chars_eq(a: &Vec<char>, b: &Vec<char>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

fn copy_chars(a: &Vec<char>) -> (r: Vec<char>)
    ensures
        r@ == a@,
{
    let mut out = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            out@ == a@.subrange(0, i as int),
        decreases a.len() - i,
    {
        out.push(a[i]);
        i += 1;
    }
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }
    out
}

// ---- 名前の探索 ----

proof fn lemma_index_of(s: Seq<Seq<char>>, x: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        forall|q: int| 0 <= q < i ==> s[q] != x,
    ensures
        i < s.len() && s[i] == x ==> index_of(s, x) == Some(i),
        i == s.len() ==> index_of(s, x) is None,
    decreases i,
{
    if i > 0 {
        assert forall|q: int| 0 <= q < i - 1 implies s.drop_first()[q] != x by {
            assert(s.drop_first()[q] == s[q + 1]);
        }
        if i < s.len() && s[i] == x {
            assert(s.drop_first()[i - 1] == s[i]);
        }
        lemma_index_of(s.drop_first(), x, i - 1);
    }
}

/// 名前の表で、名前 `x` の最初の位置。
fn index_of_exec(v: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => index_of(strs(v@), x@) == Some(i as int),
            None => index_of(strs(v@), x@) is None,
        },
{
    let ghost s = strs(v@);
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|q: int| 0 <= q < i ==> s[q] != x@,
        decreases v.len() - i,
    {
        if chars_eq(&v[i], x) {
            proof {
                lemma_index_of(s, x@, i as int);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_index_of(s, x@, i as int);
    }
    None
}

proof fn lemma_last_of(s: Seq<Seq<char>>, x: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        forall|q: int| i <= q < s.len() ==> s[q] != x,
    ensures
        i > 0 && s[i - 1] == x ==> last_of(s, x) == Some(i - 1),
        i == 0 ==> last_of(s, x) is None,
    decreases s.len(),
{
    if s.len() > 0 && i < s.len() {
        assert(s.last() != x);
        let t = s.drop_last();
        assert forall|q: int| i <= q < t.len() implies t[q] != x by {
            assert(t[q] == s[q]);
        }
        if i > 0 && s[i - 1] == x {
            assert(t[i - 1] == s[i - 1]);
        }
        lemma_last_of(t, x, i);
    }
}

/// 局所変数の名前の列で、名前 `x` の最後の位置。
fn last_of_exec(v: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => last_of(strs(v@), x@) == Some(i as int),
            None => last_of(strs(v@), x@) is None,
        },
{
    let ghost s = strs(v@);
    let mut i = v.len();
    while i > 0
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|q: int| i <= q < s.len() ==> s[q] != x@,
        decreases i,
    {
        if chars_eq(&v[i - 1], x) {
            proof {
                lemma_last_of(s, x@, i as int);
            }
            return Some(i - 1);
        }
        i -= 1;
    }
    proof {
        lemma_last_of(s, x@, 0);
    }
    None
}

/// 名前の列に重複がない。
fn distinct_exec(v: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r ==> distinct(strs(v@)),
{
    let ghost s = strs(v@);
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|p: int, q: int| 0 <= p < q < i ==> s[p] != s[q],
        decreases v.len() - i,
    {
        let mut j = 0;
        while j < i
            invariant
                j <= i < v@.len(),
                s == strs(v@),
                forall|p: int, q: int| 0 <= p < q < i ==> s[p] != s[q],
                forall|p: int| 0 <= p < j ==> s[p] != s[i as int],
            decreases i - j,
        {
            if chars_eq(&v[j], &v[i]) {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

// ---- JSONの読み方 ----

proof fn lemma_find_at(ms: Seq<Member>, k: Seq<char>, i: int)
    requires
        0 <= i <= ms.len(),
        forall|q: int| 0 <= q < i ==> ms[q].key@ != k,
    ensures
        i < ms.len() && ms[i].key@ == k ==> find(ms, k) == Some(i),
        i == ms.len() ==> find(ms, k) is None,
    decreases i,
{
    if i > 0 {
        assert forall|q: int| 0 <= q < i - 1 implies ms.drop_first()[q].key@ != k by {
            assert(ms.drop_first()[q] == ms[q + 1]);
        }
        if i < ms.len() && ms[i].key@ == k {
            assert(ms.drop_first()[i - 1] == ms[i]);
        }
        lemma_find_at(ms.drop_first(), k, i - 1);
    }
}

/// オブジェクトのキー `k` の値。
fn get_exec<'a>(j: &'a Json, k: &str) -> (r: Option<&'a Json>)
    requires
        k.is_ascii(),
    ensures
        match r {
            Some(v) => get(*j, k@) == Some(*v),
            None => get(*j, k@) is None,
        },
{
    match j {
        Json::Obj(ms) => {
            let mut i = 0;
            while i < ms.len()
                invariant
                    i <= ms@.len(),
                    k.is_ascii(),
                    *j == Json::Obj(*ms),
                    forall|q: int| 0 <= q < i ==> ms@[q].key@ != k@,
                decreases ms.len() - i,
            {
                if eqk(&ms[i].key, k) {
                    proof {
                        lemma_find_at(ms@, k@, i as int);
                    }
                    return Some(&ms[i].value);
                }
                i += 1;
            }
            proof {
                lemma_find_at(ms@, k@, i as int);
            }
            None
        },
        _ => None,
    }
}

/// キー `k` の値が省略か `null` でなければ、その値。
fn present<'a>(j: &'a Json, k: &str) -> (r: Option<&'a Json>)
    requires
        k.is_ascii(),
    ensures
        match r {
            Some(v) => !absent(*j, k@) && at(*j, k@) == *v,
            None => absent(*j, k@),
        },
{
    match get_exec(j, k) {
        Some(Json::Null) => None,
        Some(v) => Some(v),
        None => None,
    }
}

fn one_exec(j: &Json) -> (r: Option<(&Vec<char>, &Json)>)
    ensures
        match r {
            Some((k, b)) => one(*j) == Some((k@, *b)),
            None => one(*j) is None,
        },
{
    match j {
        Json::Obj(ms) => if ms.len() == 1 {
            Some((&ms[0].key, &ms[0].value))
        } else {
            None
        },
        _ => None,
    }
}

fn arr_exec(j: &Json) -> (r: Option<&Vec<Json>>)
    ensures
        match r {
            Some(xs) => arr(*j) == Some(xs@) && *j == Json::Arr(*xs),
            None => arr(*j) is None,
        },
{
    match j {
        Json::Arr(xs) => Some(xs),
        _ => None,
    }
}

fn str_exec(j: &Json) -> (r: Option<&Vec<char>>)
    ensures
        match r {
            Some(s) => str_of(*j) == Some(s@),
            None => str_of(*j) is None,
        },
{
    match j {
        Json::Str(s) => Some(s),
        _ => None,
    }
}

/// JSONの値が、0以上の整数 `x` である。
fn is_nat(j: &Json, x: usize) -> (r: bool)
    ensures
        r ==> nat_of(*j) == Some(x as nat),
{
    match j {
        Json::Int(n) => *n >= 0 && (*n as u128) == (x as u128),
        _ => false,
    }
}

fn nat_exec(j: &Json) -> (r: Option<u64>)
    ensures
        match r {
            Some(n) => nat_of(*j) == Some(n as nat),
            None => nat_of(*j) is None,
        },
{
    match j {
        Json::Int(n) => if *n >= 0 {
            Some(*n as u64)
        } else {
            None
        },
        _ => None,
    }
}

fn is_empty_obj(j: &Json) -> (r: bool)
    ensures
        r == empty_obj(*j),
{
    match j {
        Json::Obj(ms) => ms.len() == 0,
        _ => false,
    }
}

/// 長さ `n` の配列。
fn ops_exec(j: &Json, n: usize) -> (r: Option<&Vec<Json>>)
    ensures
        match r {
            Some(xs) => ops(*j, n as nat) == Some(xs@) && *j == Json::Arr(*xs),
            None => ops(*j, n as nat) is None,
        },
{
    match j {
        Json::Arr(xs) => if xs.len() == n {
            Some(xs)
        } else {
            None
        },
        _ => None,
    }
}

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
        lemma_get_dec(*b);
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
        SType::Bool => {
            let r = eqk(k, "bool") && is_empty_obj(b);
            proof { if r { assert(ty_rel(*j, *ns, *t)); } }
            r
        },
        SType::Int(lo, hi) => {
            if !eqk(k, "int") {
                return false;
            }
            match (get_exec(b, "min"), get_exec(b, "max")) {
                (Some(Json::Int(x)), Some(Json::Int(y))) => {
                    let r = *x == *lo && *y == *hi;
                    proof { if r { assert(ty_rel(*j, *ns, *t)); } }
                    r
                },
                _ => false,
            }
        },
        SType::Enum(id) => {
            if !eqk(k, "enum") {
                return false;
            }
            match str_exec(b) {
                Some(n) => match index_of_exec(&ns.enums, n) {
                    Some(i) => {
                        proof { if i == *id { assert(ty_rel(*j, *ns, *t)); } }
                        i == *id
                    },
                    None => false,
                },
                None => false,
            }
        },
        SType::Tuple(ts) => {
            if !eqk(k, "tuple") {
                return false;
            }
            let xs = match arr_exec(b) {
                Some(xs) => xs,
                None => return false,
            };
            if xs.len() != ts.len() {
                return false;
            }
            let mut i = 0;
            while i < xs.len()
                invariant
                    i <= xs@.len(),
                    xs@.len() == ts@.len(),
                    arr(*b) == Some(xs@),
                    one(*j) == Some((k@, *b)),
                    k@ == "tuple"@,
                    *t == SType::Tuple(*ts),
                    forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*j => #[trigger] xs@[q]),
                    forall|q: int| 0 <= q < i ==> ty_rel(#[trigger] xs@[q], *ns, ts@[q]),
                decreases xs.len() - i,
            {
                if !check_ty(&xs[i], ns, &ts[i]) {
                    return false;
                }
                i += 1;
            }
            true
        },
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
        SType::Map(x, y) => {
            if !eqk(k, "map") {
                return false;
            }
            match (present(b, "key"), present(b, "value")) {
                (Some(kj), Some(vj)) => check_ty(kj, ns, x) && check_ty(vj, ns, y),
                _ => false,
            }
        },
        SType::List(x, max) => {
            if !eqk(k, "list") {
                return false;
            }
            match (present(b, "of"), get_exec(b, "max")) {
                (Some(oj), Some(mj)) => check_ty(oj, ns, x) && is_nat(mj, *max),
                _ => false,
            }
        },
    }
}

fn check_field_ty(j: &Json, ns: &IrNames, id: usize, t: &SType) -> (r: bool)
    ensures
        r ==> field_ty_rel(*j, *ns, id, *t),
    decreases j, 0nat,
{
    proof {
        lemma_get_dec(*j);
        reveal_strlit("name");
        reveal_strlit("type");
    }
    if id >= ns.fields.len() {
        return false;
    }
    match (get_exec(j, "name"), get_exec(j, "type")) {
        (Some(nj), Some(tj)) => match str_exec(nj) {
            Some(n) => chars_eq(n, &ns.fields[id]) && check_ty(tj, ns, t),
            None => false,
        },
        _ => false,
    }
}

fn check_ty_at(j: &Json, k: &str, ns: &IrNames, t: &SType) -> (r: bool)
    requires
        k.is_ascii(),
    ensures
        r ==> ty_rel_at(*j, k@, *ns, *t),
{
    match get_exec(j, k) {
        Some(x) => check_ty(x, ns, t),
        None => false,
    }
}


// ---- 式 ----

pub open spec fn ectx(np: usize, nc: usize) -> ECtx {
    ECtx { np: np as nat, nc: nc as nat }
}

proof fn lemma_strs_push(v: Seq<Vec<char>>, x: Vec<char>)
    ensures
        strs(v.push(x)) == strs(v).push(x@),
{
    assert(strs(v.push(x)) =~= strs(v).push(x@));
}

/// 二項演算子のキー。`Eq` と `Ne` は `TExpr::Bin` に現れないので、どのキーとも一致しない空の文字列にする。
fn bin_key(op: BinOp) -> (r: &'static str)
    ensures
        r.is_ascii(),
        !(op is Eq || op is Ne) ==> bin_op(r@) == Some(op),
        r@.len() > 0 ==> !(op is Eq || op is Ne),
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
        reveal_strlit("");
    }
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Mod => "mod",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        _ => "",
    }
}

fn set_key(op: &SetOp) -> (r: &'static str)
    ensures
        r.is_ascii(),
        set_op(r@) == Some(*op),
{
    proof {
        reveal_strlit("union");
        reveal_strlit("intersection");
        reveal_strlit("difference");
        reveal_strlit("subset");
    }
    match op {
        SetOp::Union => "union",
        SetOp::Intersection => "intersection",
        SetOp::Difference => "difference",
        SetOp::Subset => "subset",
    }
}

/// 式のJSON `j` が、局所変数の名前の列 `sc` のもとで式 `e` を表すかを確かめる。
pub fn check_ex(j: &Json, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases j, 2nat,
{
    let (k, b) = match one_exec(j) {
        Some(x) => x,
        None => return false,
    };
    proof {
        lemma_one_dec(*j);
    }
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_) => check_leaf(
            j,
            k,
            b,
            e,
            ns,
            np,
            nc,
            sc,
        ),
        TExpr::Bin(..) | TExpr::Eq(..) | TExpr::Not(..) | TExpr::Fold(..) | TExpr::Implies(..) | TExpr::Ite(..) | TExpr::Let(
            ..,
        ) | TExpr::Quant(..) => check_core(j, k, b, e, ns, np, nc, sc),
        TExpr::Tuple(..) | TExpr::Record(..) | TExpr::Nth(..) | TExpr::Field(..) | TExpr::None(..) | TExpr::Some(..)
        | TExpr::IsSome(..) | TExpr::IsNone(..) | TExpr::Unwrap(..) => check_struct(j, k, b, e, ns, np, nc, sc),
        TExpr::SetLit(..) | TExpr::MapLit(..) | TExpr::ListLit(..) => check_lit(j, k, b, e, ns, np, nc, sc),
        _ => check_coll(j, k, b, e, ns, np, nc, sc),
    }
}

/// リテラルと参照。
fn check_leaf(
    j: &Json,
    k: &Vec<char>,
    b: &Json,
    e: &TExpr,
    ns: &IrNames,
    np: usize,
    nc: usize,
    sc: &mut Vec<Vec<char>>,
) -> (r: bool)
    requires
        one(*j) == Some((k@, *b)),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
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
            let (tj, vj) = match (get_exec(b, "type"), get_exec(b, "variant")) {
                (Some(x), Some(y)) => (x, y),
                _ => return false,
            };
            let (tn, vn) = match (str_exec(tj), str_exec(vj)) {
                (Some(x), Some(y)) => (x, y),
                _ => return false,
            };
            match (index_of_exec(&ns.enums, tn), index_of_exec(&ns.variants[*id], vn)) {
                (Some(a), Some(q)) => a == *id && *v >= 0 && (*v as u128) == (q as u128),
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
        TExpr::Local(i) => {
            if !eqk(k, "local") {
                return false;
            }
            match str_exec(b) {
                Some(n) => match last_of_exec(sc, n) {
                    Some(q) => q == *i,
                    None => false,
                },
                None => false,
            }
        },
        TExpr::Const(i) => {
            if !eqk(k, "const") {
                return false;
            }
            match str_exec(b) {
                Some(n) => match index_of_exec(&ns.consts, n) {
                    Some(q) => q == *i,
                    None => false,
                },
                None => false,
            }
        },
        _ => false,
    }
}

/// 長さ `n` の配列 `b` の各要素が、式の列 `es` を表す（オペランド）。
fn check_args(b: &Json, es: &[&TExpr], ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> (ops(*b, es@.len()) matches Some(xs) && forall|i: int|
            0 <= i < es@.len() ==> ex_rel(#[trigger] xs[i], *es@[i], *ns, ectx(np, nc), strs(old(sc)@))),
    decreases b, 0nat,
{
    let xs = match ops_exec(b, es.len()) {
        Some(xs) => xs,
        None => return false,
    };
    proof {
        lemma_arr_dec(*b);
    }
    let ghost s0 = sc@;
    let mut i = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            xs@.len() == es@.len(),
            *b == Json::Arr(*xs),
            ops(*b, es@.len()) == Some(xs@),
            sc@ == s0,
            s0 == old(sc)@,
            forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
            forall|q: int| 0 <= q < i ==> ex_rel(#[trigger] xs@[q], *es@[q], *ns, ectx(np, nc), strs(s0)),
        decreases es.len() - i,
    {
        if !check_ex(&xs[i], es[i], ns, np, nc, sc) {
            return false;
        }
        i += 1;
    }
    true
}

/// 配列 `b` の各要素が、式の列 `es` を表す。
fn check_exs(b: &Json, es: &Vec<TExpr>, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> exs_rel(*b, es@, *ns, ectx(np, nc), strs(old(sc)@)),
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
            *b == Json::Arr(*xs),
            sc@ == s0,
            s0 == old(sc)@,
            forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
            forall|q: int| 0 <= q < i ==> ex_rel(#[trigger] xs@[q], es@[q], *ns, ectx(np, nc), strs(s0)),
        decreases es.len() - i,
    {
        if !check_ex(&xs[i], &es[i], ns, np, nc, sc) {
            return false;
        }
        i += 1;
    }
    true
}

/// オブジェクト `b` のキー `key` の値が、式 `e` を表す。
fn check_key(b: &Json, key: &str, e: &TExpr, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    requires
        key.is_ascii(),
    ensures
        final(sc)@ == old(sc)@,
        r ==> get(*b, key@) is Some && ex_rel(at(*b, key@), *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 0nat,
{
    proof {
        lemma_get_dec(*b);
    }
    match get_exec(b, key) {
        Some(x) => check_ex(x, e, ns, np, nc, sc),
        None => false,
    }
}

/// 演算子、`let`、量化。
fn check_core(
    j: &Json,
    k: &Vec<char>,
    b: &Json,
    e: &TExpr,
    ns: &IrNames,
    np: usize,
    nc: usize,
    sc: &mut Vec<Vec<char>>,
) -> (r: bool)
    requires
        one(*j) == Some((k@, *b)),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    proof {
        lemma_get_dec(*b);
        reveal_strlit("eq");
        reveal_strlit("ne");
        reveal_strlit("not");
        reveal_strlit("all");
        reveal_strlit("any");
        reveal_strlit("implies");
        reveal_strlit("ite");
        reveal_strlit("let");
        reveal_strlit("forall");
        reveal_strlit("exists");
        reveal_strlit("name");
        reveal_strlit("value");
        reveal_strlit("body");
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
    }
    let ghost s0 = strs(sc@);
    match e {
        TExpr::Bin(op, x, y) => {
            let key = bin_key(*op);
            if key.unicode_len() == 0 || !eqk(k, key) {
                return false;
            }
            check_args(b, &[&**x, &**y], ns, np, nc, sc)
        },
        TExpr::Eq(pos, x, y) => {
            if !eqk(k, if *pos { "eq" } else { "ne" }) {
                return false;
            }
            check_args(b, &[&**x, &**y], ns, np, nc, sc)
        },
        TExpr::Not(x) => eqk(k, "not") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::Fold(all, es) => eqk(k, if *all { "all" } else { "any" }) && check_exs(b, es, ns, np, nc, sc),
        TExpr::Implies(x, y) => eqk(k, "implies") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Ite(p, x, y) => eqk(k, "ite") && check_args(b, &[&**p, &**x, &**y], ns, np, nc, sc),
        TExpr::Let(x, y) => {
            if !eqk(k, "let") {
                return false;
            }
            let n = match get_exec(b, "name") {
                Some(nj) => match str_exec(nj) {
                    Some(n) => n,
                    None => return false,
                },
                None => return false,
            };
            if !check_key(b, "value", x, ns, np, nc, sc) {
                return false;
            }
            let bj = match get_exec(b, "body") {
                Some(bj) => bj,
                None => return false,
            };
            let ghost v0 = sc@;
            sc.push(copy_chars(n));
            proof {
                lemma_strs_push(v0, sc@.last());
                assert(sc@ == v0.push(sc@.last()));
            }
            let ok = check_ex(bj, y, ns, np, nc, sc);
            sc.pop();
            proof {
                assert(sc@ =~= v0);
            }
            ok
        },
        TExpr::Quant(all, over, y) => {
            if !eqk(k, if *all { "forall" } else { "exists" }) {
                return false;
            }
            let n = match get_exec(b, "name") {
                Some(nj) => match str_exec(nj) {
                    Some(n) => n,
                    None => return false,
                },
                None => return false,
            };
            if !check_over(b, over, ns, np, nc, sc) {
                return false;
            }
            let bj = match get_exec(b, "body") {
                Some(bj) => bj,
                None => return false,
            };
            let ghost v0 = sc@;
            sc.push(copy_chars(n));
            proof {
                lemma_strs_push(v0, sc@.last());
                assert(sc@ == v0.push(sc@.last()));
            }
            let ok = check_ex(bj, y, ns, np, nc, sc);
            sc.pop();
            proof {
                assert(sc@ =~= v0);
            }
            ok
        },
        _ => false,
    }
}

/// 量化のたどる値。
fn check_over(b: &Json, over: &Over, ns: &IrNames, np: usize, nc: usize, sc: &mut Vec<Vec<char>>) -> (r: bool)
    ensures
        final(sc)@ == old(sc)@,
        r ==> over_rel(*b, *over, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 0nat,
{
    proof {
        lemma_get_dec(*b);
        reveal_strlit("in");
        reveal_strlit("type");
    }
    match (get_exec(b, "in"), get_exec(b, "type")) {
        (Some(x), None) => match over {
            Over::Set(_, y) => check_ex(x, y, ns, np, nc, sc),
            Over::Map(_, y) => check_ex(x, y, ns, np, nc, sc),
            Over::List(y) => check_ex(x, y, ns, np, nc, sc),
            Over::Type(_) => false,
        },
        (None, Some(t)) => match over {
            Over::Type(st) => check_ty(t, ns, st),
            _ => false,
        },
        _ => false,
    }
}

/// Tuple、Record、Option。
fn check_struct(
    j: &Json,
    k: &Vec<char>,
    b: &Json,
    e: &TExpr,
    ns: &IrNames,
    np: usize,
    nc: usize,
    sc: &mut Vec<Vec<char>>,
) -> (r: bool)
    requires
        one(*j) == Some((k@, *b)),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    proof {
        lemma_get_dec(*b);
        lemma_arr_dec(*b);
        reveal_strlit("tuple");
        reveal_strlit("record");
        reveal_strlit("nth");
        reveal_strlit("field");
        reveal_strlit("none");
        reveal_strlit("some");
        reveal_strlit("is_some");
        reveal_strlit("is_none");
        reveal_strlit("unwrap");
        reveal_strlit("of");
        reveal_strlit("index");
        reveal_strlit("name");
        reveal_strlit("expr");
    }
    match e {
        TExpr::Tuple(es) => eqk(k, "tuple") && check_exs(b, es, ns, np, nc, sc),
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
        TExpr::Nth(x, idx) => {
            if !eqk(k, "nth") {
                return false;
            }
            match get_exec(b, "index") {
                Some(ij) => is_nat(ij, *idx) && check_key(b, "of", x, ns, np, nc, sc),
                None => false,
            }
        },
        TExpr::Field(x, id, _) => {
            if !eqk(k, "field") || *id >= ns.fields.len() {
                return false;
            }
            match get_exec(b, "name") {
                Some(nj) => match str_exec(nj) {
                    Some(n) => chars_eq(&ns.fields[*id], n) && check_key(b, "of", x, ns, np, nc, sc),
                    None => false,
                },
                None => false,
            }
        },
        TExpr::None(t) => eqk(k, "none") && check_ty(b, ns, t),
        TExpr::Some(x) => eqk(k, "some") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::IsSome(x) => eqk(k, "is_some") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::IsNone(x) => eqk(k, "is_none") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::Unwrap(x) => eqk(k, "unwrap") && check_args(b, &[&**x], ns, np, nc, sc),
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
    if id >= ns.fields.len() {
        return false;
    }
    match get_exec(j, "name") {
        Some(nj) => match str_exec(nj) {
            Some(n) => chars_eq(n, &ns.fields[id]) && check_key(j, "expr", e, ns, np, nc, sc),
            None => false,
        },
        None => false,
    }
}

/// Set、Map、Listのリテラル。
fn check_lit(
    j: &Json,
    k: &Vec<char>,
    b: &Json,
    e: &TExpr,
    ns: &IrNames,
    np: usize,
    nc: usize,
    sc: &mut Vec<Vec<char>>,
) -> (r: bool)
    requires
        one(*j) == Some((k@, *b)),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    proof {
        lemma_get_dec(*b);
        reveal_strlit("set");
        reveal_strlit("map");
        reveal_strlit("list");
        reveal_strlit("of");
        reveal_strlit("key");
        reveal_strlit("value");
        reveal_strlit("items");
        reveal_strlit("max");
    }
    let itj = match get_exec(b, "items") {
        Some(x) => x,
        None => return false,
    };
    proof {
        lemma_arr_dec(*itj);
    }
    match e {
        TExpr::SetLit(t, es) => eqk(k, "set") && check_ty_at(b, "of", ns, t) && check_exs(itj, es, ns, np, nc, sc),
        TExpr::ListLit(t, max, es) => {
            if !eqk(k, "list") || !check_ty_at(b, "of", ns, t) {
                return false;
            }
            match get_exec(b, "max") {
                Some(mj) => is_nat(mj, *max) && check_exs(itj, es, ns, np, nc, sc),
                None => false,
            }
        },
        TExpr::MapLit(kt, vt, items) => {
            if !eqk(k, "map") || !check_ty_at(b, "key", ns, kt) || !check_ty_at(b, "value", ns, vt) {
                return false;
            }
            let xs = match arr_exec(itj) {
                Some(xs) => xs,
                None => return false,
            };
            if xs.len() != items.len() {
                return false;
            }
            proof {
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
            s0 == old(sc)@,
                    forall|q: int| 0 <= q < xs@.len() ==> decreases_to!(*b => #[trigger] xs@[q]),
                    forall|q: int| 0 <= q < i ==> item_rel(#[trigger] xs@[q], items@[q], *ns, ectx(np, nc), strs(s0)),
                decreases xs.len() - i,
            {
                if !check_args(&xs[i], &[&items[i].key, &items[i].value], ns, np, nc, sc) {
                    return false;
                }
                i += 1;
            }
            true
        },
        _ => false,
    }
}

/// Set、Map、Listの演算。
fn check_coll(
    j: &Json,
    k: &Vec<char>,
    b: &Json,
    e: &TExpr,
    ns: &IrNames,
    np: usize,
    nc: usize,
    sc: &mut Vec<Vec<char>>,
) -> (r: bool)
    requires
        one(*j) == Some((k@, *b)),
    ensures
        final(sc)@ == old(sc)@,
        r ==> ex_rel(*j, *e, *ns, ectx(np, nc), strs(old(sc)@)),
    decreases b, 1nat,
{
    proof {
        reveal_strlit("contains");
        reveal_strlit("insert");
        reveal_strlit("remove");
        reveal_strlit("size");
        reveal_strlit("is_empty");
        reveal_strlit("has_key");
        reveal_strlit("get");
        reveal_strlit("delete");
        reveal_strlit("put");
        reveal_strlit("keys");
        reveal_strlit("at");
        reveal_strlit("first");
        reveal_strlit("last");
        reveal_strlit("push");
        reveal_strlit("pop");
        reveal_strlit("shift");
    }
    match e {
        TExpr::SetContains(_, x, y) => eqk(k, "contains") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::ListContains(x, y) => eqk(k, "contains") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Insert(_, x, y) => eqk(k, "insert") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Remove(_, x, y) => eqk(k, "remove") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::SetBin(op, x, y) => eqk(k, set_key(op)) && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Size(x) => eqk(k, "size") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::IsEmpty(x) => eqk(k, "is_empty") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::HasKey(_, x, y) => eqk(k, "has_key") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Get(_, x, y) => eqk(k, "get") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Delete(_, x, y) => eqk(k, "delete") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Put(_, _, x, y, z) => eqk(k, "put") && check_args(b, &[&**x, &**y, &**z], ns, np, nc, sc),
        TExpr::Keys(x) => eqk(k, "keys") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::At(x, y) => eqk(k, "at") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::First(x) => eqk(k, "first") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::Last(x) => eqk(k, "last") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::Push(_, _, x, y) => eqk(k, "push") && check_args(b, &[&**x, &**y], ns, np, nc, sc),
        TExpr::Pop(x) => eqk(k, "pop") && check_args(b, &[&**x], ns, np, nc, sc),
        TExpr::Shift(x) => eqk(k, "shift") && check_args(b, &[&**x], ns, np, nc, sc),
        _ => false,
    }
}

} // verus!
