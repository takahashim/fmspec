//! 遷移の意味論と遷移列挙。
//!
//! `step_spec` が1つの具体的な遷移の意味論で、`step` はそれと一致する実装である。
//! `enumerate` は、ある状態での1操作の有効な遷移を、漏れなく、かつ有効なものだけ列挙する
//! （仕様書 §14.1 Transition Soundness / Completeness）。

use crate::eval::*;
use crate::model::*;
use vstd::prelude::*;

verus! {

// ---- 符号化列の型 ----

pub open spec fn in_type(enums: Seq<i64>, ty: Type, x: i64) -> bool {
    match ty {
        Type::Bool => 0 <= x <= 1,
        Type::Int(lo, hi) => lo <= x <= hi,
        Type::Enum(id) => id < enums.len() && 0 <= x < enums[id as int],
    }
}

pub open spec fn vals_ok(enums: Seq<i64>, tys: Seq<Type>, xs: Seq<i64>) -> bool {
    &&& xs.len() == tys.len()
    &&& forall|i: int| 0 <= i < tys.len() ==> in_type(enums, #[trigger] tys[i], xs[i])
}

/// 状態の符号化列が状態型に従う。
pub open spec fn state_ok(m: RawModel, s: Seq<i64>) -> bool {
    vals_ok(m.enums@, m.state_types@, s)
}

/// 引数の列（公開引数と内部選択）が操作のドメインに従う。
pub open spec fn args_ok(m: RawModel, a: int, args: Seq<i64>) -> bool {
    vals_ok(m.enums@, m.actions@[a].domains@, args)
}

/// 型に属する値の範囲。`lo > hi` なら空。
pub open spec fn type_range(enums: Seq<i64>, ty: Type) -> (int, int) {
    match ty {
        Type::Bool => (0, 1),
        Type::Int(lo, hi) => (lo as int, hi as int),
        Type::Enum(id) => if id < enums.len() {
            (0, enums[id as int] - 1)
        } else {
            (0, -1)
        },
    }
}

pub fn type_range_exec(enums: &Vec<i64>, ty: &Type) -> (r: (i128, i128))
    ensures
        r.0 == type_range(enums@, *ty).0,
        r.1 == type_range(enums@, *ty).1,
        i64::MIN <= r.0,
        r.1 <= i64::MAX,
        forall|x: i64| in_type(enums@, *ty, x) <==> r.0 <= x <= r.1,
{
    match ty {
        Type::Bool => (0, 1),
        Type::Int(lo, hi) => (*lo as i128, *hi as i128),
        Type::Enum(id) => if *id < enums.len() {
            (0, enums[*id] as i128 - 1)
        } else {
            (0, -1)
        },
    }
}

pub fn in_type_exec(enums: &Vec<i64>, ty: &Type, x: i64) -> (r: bool)
    ensures
        r == in_type(enums@, *ty, x),
{
    match ty {
        Type::Bool => 0 <= x && x <= 1,
        Type::Int(lo, hi) => *lo <= x && x <= *hi,
        Type::Enum(id) => *id < enums.len() && 0 <= x && x < enums[*id],
    }
}

pub fn vals_ok_exec(enums: &Vec<i64>, tys: &Vec<Type>, xs: &Vec<i64>) -> (r: bool)
    ensures
        r == vals_ok(enums@, tys@, xs@),
{
    if xs.len() != tys.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < tys.len()
        invariant
            xs@.len() == tys@.len(),
            i <= tys@.len(),
            forall|j: int| 0 <= j < i ==> in_type(enums@, #[trigger] tys@[j], xs@[j]),
        decreases tys@.len() - i,
    {
        if !in_type_exec(enums, &tys[i], xs[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}

/// 値を型の符号に変換する。範囲外の整数は `OutOfRange`、型が合わなければ `TypeMismatch`。
pub open spec fn encode_spec(enums: Seq<i64>, ty: Type, v: Value) -> Result<i64, ErrKind> {
    match (ty, v) {
        (Type::Bool, Value::Bool(b)) => Ok(
            if b {
                1i64
            } else {
                0i64
            },
        ),
        (Type::Int(lo, hi), Value::Int(x)) => if lo <= x <= hi {
            Ok(x)
        } else {
            Err(ErrKind::OutOfRange(x))
        },
        (Type::Enum(id), Value::Enum(id2, k)) => if id == id2 && in_type(enums, ty, k) {
            Ok(k)
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => Err(ErrKind::TypeMismatch),
    }
}

pub fn encode(enums: &Vec<i64>, ty: &Type, v: &Value) -> (r: Result<i64, ErrKind>)
    ensures
        r == encode_spec(enums@, *ty, *v),
{
    match (ty, v) {
        (Type::Bool, Value::Bool(b)) => Ok(
            if *b {
                1
            } else {
                0
            },
        ),
        (Type::Int(lo, hi), Value::Int(x)) => if *lo <= *x && *x <= *hi {
            Ok(*x)
        } else {
            Err(ErrKind::OutOfRange(*x))
        },
        (Type::Enum(id), Value::Enum(id2, k)) => if *id == *id2 && in_type_exec(enums, ty, *k) {
            Ok(*k)
        } else {
            Err(ErrKind::TypeMismatch)
        },
        _ => Err(ErrKind::TypeMismatch),
    }
}

/// 符号化に成功した値は型に属する。
pub proof fn lemma_encode_in_type(enums: Seq<i64>, ty: Type, v: Value)
    ensures
        encode_spec(enums, ty, v) matches Ok(x) ==> in_type(enums, ty, x),
{
}

/// 型に属する符号は、値と一対一に対応する。
/// 状態の等価性は符号化列の一致で定義するので、型に従う状態が等しいことと、
/// 各状態変数の値が等しいことは一致する（仕様書 §14.1 State Equality）。
pub proof fn lemma_decode_injective(enums: Seq<i64>, ty: Type, x: i64, y: i64)
    requires
        in_type(enums, ty, x),
        in_type(enums, ty, y),
        decode(ty, x) == decode(ty, y),
    ensures
        x == y,
{
}

/// 型に属する符号を値に戻して符号化し直すと、元の符号になる。
pub proof fn lemma_encode_decode(enums: Seq<i64>, ty: Type, x: i64)
    requires
        in_type(enums, ty, x),
    ensures
        encode_spec(enums, ty, decode(ty, x)) == Ok::<i64, ErrKind>(x),
{
}

// ---- 1つの具体的な遷移 ----

/// 評価に失敗した箇所。更新は `updates` の添字で指す。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    Guard,
    Update(usize),
    Output,
}

/// 操作 `a` を引数 `args` で状態 `s` に適用した結果。
pub ghost enum Step {
    /// guard が偽。
    Disabled,
    /// 評価エラーまたは範囲外更新。遷移を黙って除外しない。
    Fail(Site, ErrKind),
    /// 次状態と出力（出力宣言がなければ `None`）。
    To(Seq<i64>, Option<i64>),
}

pub open spec fn act_env(m: RawModel, a: int, args: Seq<i64>, s: Seq<i64>) -> Env {
    Env {
        st_tys: m.state_types@,
        arg_tys: m.actions@[a].domains@,
        pre: s,
        args: args,
        post: Seq::empty(),
        out: None,
    }
}

/// `updates` の `k` 番目以降を順に評価して `acc` に適用する。式は遷移前の環境で評価する（同時代入）。
pub open spec fn apply_updates(m: RawModel, a: int, env: Env, k: nat, acc: Seq<i64>) -> Result<
    Seq<i64>,
    (usize, ErrKind),
>
    decreases m.actions@[a].updates@.len() - k,
{
    let ups = m.actions@[a].updates@;
    if k >= ups.len() {
        Ok(acc)
    } else {
        let u = ups[k as int];
        match eval_spec(u.expr, env) {
            Err(e) => Err((k as usize, e)),
            Ok(v) => if u.target < acc.len() && u.target < m.state_types@.len() {
                match encode_spec(m.enums@, m.state_types@[u.target as int], v) {
                    Err(e) => Err((k as usize, e)),
                    Ok(x) => apply_updates(m, a, env, k + 1, acc.update(u.target as int, x)),
                }
            } else {
                Err((k as usize, ErrKind::Unbound))
            },
        }
    }
}

pub open spec fn output_spec(m: RawModel, a: int, env: Env) -> Result<Option<i64>, ErrKind> {
    match m.actions@[a].output {
        None => Ok(None),
        Some(o) => match eval_spec(o.expr, env) {
            Err(e) => Err(e),
            Ok(v) => match encode_spec(m.enums@, o.ty, v) {
                Err(e) => Err(e),
                Ok(x) => Ok(Some(x)),
            },
        },
    }
}

/// 遷移の意味論（仕様書 §5.1）。guard、更新（記述順）、出力の順に評価し、最初の失敗を報告する。
pub open spec fn step_spec(m: RawModel, a: int, args: Seq<i64>, s: Seq<i64>) -> Step {
    let env = act_env(m, a, args, s);
    match prop_spec(m.actions@[a].guard, env) {
        Err(e) => Step::Fail(Site::Guard, e),
        Ok(false) => Step::Disabled,
        Ok(true) => match apply_updates(m, a, env, 0, s) {
            Err((k, e)) => Step::Fail(Site::Update(k), e),
            Ok(t) => match output_spec(m, a, env) {
                Err(e) => Step::Fail(Site::Output, e),
                Ok(o) => Step::To(t, o),
            },
        },
    }
}

pub enum StepR {
    Disabled,
    Fail(Site, ErrKind),
    To(Vec<i64>, Option<i64>),
}

impl StepR {
    pub open spec fn view(&self) -> Step {
        match *self {
            StepR::Disabled => Step::Disabled,
            StepR::Fail(site, k) => Step::Fail(site, k),
            StepR::To(t, o) => Step::To(t@, o),
        }
    }
}

pub fn copy_vec(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == v@[j],
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
    }
    assert(r@ =~= v@);
    r
}

pub fn vec_eq(a: &Vec<i64>, b: &Vec<i64>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// 1つの具体的な遷移を計算する。結果は `step_spec` と一致する。
#[verifier::loop_isolation(false)]
pub(crate) fn step(m: &RawModel, a: usize, args: &Vec<i64>, s: &Vec<i64>) -> (r: StepR)
    requires
        a < m.actions@.len(),
    ensures
        r@ == step_spec(*m, a as int, args@, s@),
{
    let act = &m.actions[a];
    let empty: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &m.state_types, arg_tys: &act.domains, pre: s, args, post: &empty, out: None };
    let ghost env = act_env(*m, a as int, args@, s@);
    assert(ctx@ == env) by {
        assert(empty@ =~= Seq::<i64>::empty());
    }
    match eval_prop(&act.guard, &ctx) {
        Err(e) => StepR::Fail(Site::Guard, e),
        Ok(false) => StepR::Disabled,
        Ok(true) => {
            let mut t = copy_vec(s);
            let mut k: usize = 0;
            while k < act.updates.len()
                invariant
                    a < m.actions@.len(),
                    act == m.actions@[a as int],
                    ctx@ == env,
                    k <= act.updates@.len(),
                    apply_updates(*m, a as int, env, k as nat, t@) == apply_updates(*m, a as int, env, 0, s@),
                decreases act.updates@.len() - k,
            {
                let u = &act.updates[k];
                match eval(&u.expr, &ctx) {
                    Err(e) => {
                        return StepR::Fail(Site::Update(k), e);
                    },
                    Ok(v) => {
                        if u.target < t.len() && u.target < m.state_types.len() {
                            match encode(&m.enums, &m.state_types[u.target], &v) {
                                Err(e) => {
                                    return StepR::Fail(Site::Update(k), e);
                                },
                                Ok(x) => {
                                    t.set(u.target, x);
                                },
                            }
                        } else {
                            return StepR::Fail(Site::Update(k), ErrKind::Unbound);
                        }
                    },
                }
                k = k + 1;
            }
            match &act.output {
                None => StepR::To(t, None),
                Some(o) => match eval(&o.expr, &ctx) {
                    Err(e) => StepR::Fail(Site::Output, e),
                    Ok(v) => match encode(&m.enums, &o.ty, &v) {
                        Err(e) => StepR::Fail(Site::Output, e),
                        Ok(x) => StepR::To(t, Some(x)),
                    },
                },
            }
        },
    }
}

// ---- 遷移列挙 ----

/// 有効な遷移。`args` は公開引数に続けて内部選択を並べた列。
pub struct Transition {
    pub args: Vec<i64>,
    pub output: Option<i64>,
    pub state: Vec<i64>,
}

/// `t` は状態 `s` から操作 `a` で実際に起きる遷移である。
pub open spec fn tr_sound(m: RawModel, a: int, s: Seq<i64>, t: Transition) -> bool {
    args_ok(m, a, t.args@) && step_spec(m, a, t.args@, s) == Step::To(t.state@, t.output)
}

pub open spec fn has_args(ts: Seq<Transition>, args: Seq<i64>) -> bool {
    exists|i: int| 0 <= i < ts.len() && (#[trigger] ts[i]).args@ == args
}

/// 引数 `args` の遷移は、無効であるか、`ts` に含まれる。評価エラーではない。
pub open spec fn covered(m: RawModel, a: int, s: Seq<i64>, ts: Seq<Transition>, args: Seq<i64>) -> bool {
    match step_spec(m, a, args, s) {
        Step::Disabled => true,
        Step::Fail(_, _) => false,
        Step::To(_, _) => has_args(ts, args),
    }
}

/// `ts` は状態 `s` での操作 `a` の有効な遷移を、漏れなく、かつ有効なものだけ含む。
pub open spec fn enum_ok(m: RawModel, a: int, s: Seq<i64>, ts: Seq<Transition>) -> bool {
    &&& forall|i: int| 0 <= i < ts.len() ==> tr_sound(m, a, s, #[trigger] ts[i])
    &&& forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) ==> covered(m, a, s, ts, args)
}

pub enum Enumerated {
    Ok(Vec<Transition>),
    /// ドメイン内の引数で評価エラーが起きた。
    Fail(Vec<i64>, Site, ErrKind),
}

pub open spec fn enumerated_ok(m: RawModel, a: int, s: Seq<i64>, r: Enumerated) -> bool {
    match r {
        Enumerated::Ok(ts) => enum_ok(m, a, s, ts@),
        Enumerated::Fail(args, site, k) => args_ok(m, a, args@) && step_spec(m, a, args@, s) == Step::Fail(
            site,
            k,
        ),
    }
}

spec fn prefix_ok(m: RawModel, a: int, p: Seq<i64>) -> bool {
    &&& p.len() <= m.actions@[a].domains@.len()
    &&& forall|j: int| 0 <= j < p.len() ==> in_type(m.enums@, #[trigger] m.actions@[a].domains@[j], p[j])
}

spec fn extends(args: Seq<i64>, p: Seq<i64>) -> bool {
    &&& p.len() <= args.len()
    &&& forall|j: int| 0 <= j < p.len() ==> #[trigger] args[j] == p[j]
}

spec fn all_sound(m: RawModel, a: int, s: Seq<i64>, ts: Seq<Transition>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> tr_sound(m, a, s, #[trigger] ts[i])
}

spec fn grows(old_ts: Seq<Transition>, new_ts: Seq<Transition>) -> bool {
    &&& old_ts.len() <= new_ts.len()
    &&& forall|i: int| 0 <= i < old_ts.len() ==> #[trigger] new_ts[i] == old_ts[i]
}

/// `p` を接頭辞に持つドメイン内の引数は、すべて `ts` で覆われている。
spec fn covers_prefix(m: RawModel, a: int, s: Seq<i64>, ts: Seq<Transition>, p: Seq<i64>) -> bool {
    forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) && extends(args, p) ==> covered(m, a, s, ts, args)
}

proof fn lemma_covered_grows(
    m: RawModel,
    a: int,
    s: Seq<i64>,
    old_ts: Seq<Transition>,
    new_ts: Seq<Transition>,
    args: Seq<i64>,
)
    requires
        covered(m, a, s, old_ts, args),
        grows(old_ts, new_ts),
    ensures
        covered(m, a, s, new_ts, args),
{
    if step_spec(m, a, args, s) is To {
        let i = choose|i: int| 0 <= i < old_ts.len() && (#[trigger] old_ts[i]).args@ == args;
        assert(new_ts[i] == old_ts[i]);
    }
}

/// 接頭辞 `prefix` に続く引数を辞書順に列挙し、有効な遷移を `ts` に追加する。
#[verifier::loop_isolation(false)]
fn enum_rec(m: &RawModel, a: usize, s: &Vec<i64>, prefix: &mut Vec<i64>, ts: &mut Vec<Transition>) -> (r:
    Option<(Vec<i64>, Site, ErrKind)>)
    requires
        a < m.actions@.len(),
        prefix_ok(*m, a as int, old(prefix)@),
        all_sound(*m, a as int, s@, old(ts)@),
    ensures
        final(prefix)@ == old(prefix)@,
        match r {
            None => {
                &&& all_sound(*m, a as int, s@, final(ts)@)
                &&& grows(old(ts)@, final(ts)@)
                &&& covers_prefix(*m, a as int, s@, final(ts)@, old(prefix)@)
            },
            Some((args, site, k)) => args_ok(*m, a as int, args@) && step_spec(*m, a as int, args@, s@)
                == Step::Fail(site, k),
        },
    decreases m.actions@[a as int].domains@.len() - old(prefix)@.len(),
{
    let ghost p0 = prefix@;
    let ghost ts0 = ts@;
    let ghost ai = a as int;
    let doms = &m.actions[a].domains;
    let i = prefix.len();
    if i == doms.len() {
        assert(args_ok(*m, ai, p0));
        match step(m, a, prefix, s) {
            StepR::Disabled => {},
            StepR::Fail(site, k) => {
                return Some((copy_vec(prefix), site, k));
            },
            StepR::To(t, o) => {
                let tr = Transition { args: copy_vec(prefix), output: o, state: t };
                ts.push(tr);
                assert(ts@[ts@.len() - 1].args@ == p0);
                assert(has_args(ts@, p0));
            },
        }
        assert(covers_prefix(*m, ai, s@, ts@, p0)) by {
            assert forall|args: Seq<i64>| #[trigger] args_ok(*m, ai, args) && extends(args, p0) implies covered(
                *m,
                ai,
                s@,
                ts@,
                args,
            ) by {
                assert(args =~= p0);
            }
        }
        return None;
    }
    let (lo, hi) = type_range_exec(&m.enums, &doms[i]);
    let mut v: i128 = lo;
    while v <= hi
        invariant
            a < m.actions@.len(),
            ai == a as int,
            doms == m.actions@[ai].domains,
            i == p0.len(),
            i < doms@.len(),
            prefix@ == p0,
            prefix_ok(*m, ai, p0),
            lo == type_range(m.enums@, doms@[i as int]).0,
            hi == type_range(m.enums@, doms@[i as int]).1,
            i64::MIN <= lo <= v,
            hi <= i64::MAX,
            forall|x: i64| in_type(m.enums@, doms@[i as int], x) <==> lo <= x <= hi,
            all_sound(*m, ai, s@, ts@),
            grows(ts0, ts@),
            forall|args: Seq<i64>| #[trigger]
                args_ok(*m, ai, args) && extends(args, p0) && args[i as int] < v ==> covered(*m, ai, s@, ts@, args),
        decreases hi + 1 - v,
    {
        let x = v as i64;
        let ghost ts1 = ts@;
        prefix.push(x);
        let ghost p1 = prefix@;
        assert(prefix_ok(*m, ai, p1)) by {
            assert(in_type(m.enums@, doms@[i as int], x));
        }
        let r = enum_rec(m, a, s, prefix, ts);
        prefix.pop();
        assert(prefix@ =~= p0);
        if r.is_some() {
            return r;
        }
        proof {
            assert forall|args: Seq<i64>| #[trigger]
                args_ok(*m, ai, args) && extends(args, p0) && args[i as int] < v + 1 implies covered(
                *m,
                ai,
                s@,
                ts@,
                args,
            ) by {
                if args[i as int] < v {
                    lemma_covered_grows(*m, ai, s@, ts1, ts@, args);
                } else {
                    assert(extends(args, p1));
                }
            }
        }
        v = v + 1;
    }
    assert(covers_prefix(*m, ai, s@, ts@, p0)) by {
        assert forall|args: Seq<i64>| #[trigger] args_ok(*m, ai, args) && extends(args, p0) implies covered(
            *m,
            ai,
            s@,
            ts@,
            args,
        ) by {
            assert(in_type(m.enums@, doms@[i as int], args[i as int]));
        }
    }
    None
}

/// 状態 `s` での操作 `a` の有効な遷移を、引数の辞書順に列挙する。
pub(crate) fn enumerate(m: &RawModel, a: usize, s: &Vec<i64>) -> (r: Enumerated)
    requires
        a < m.actions@.len(),
    ensures
        enumerated_ok(*m, a as int, s@, r),
{
    let mut prefix: Vec<i64> = Vec::new();
    let mut ts: Vec<Transition> = Vec::new();
    match enum_rec(m, a, s, &mut prefix, &mut ts) {
        None => Enumerated::Ok(ts),
        Some((args, site, k)) => Enumerated::Fail(args, site, k),
    }
}

/// 操作 `a` のどの引数でも guard が偽である。
pub open spec fn all_disabled(m: RawModel, a: int, s: Seq<i64>) -> bool {
    forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) ==> step_spec(m, a, args, s) is Disabled
}

/// 列挙が空なら、その操作に有効な遷移はない。空でなければ、有効な遷移がある。
pub proof fn lemma_enum_enabled(m: RawModel, a: int, s: Seq<i64>, ts: Seq<Transition>)
    requires
        enum_ok(m, a, s, ts),
    ensures
        ts.len() == 0 <==> all_disabled(m, a, s),
{
    if ts.len() == 0 {
        assert forall|args: Seq<i64>| #[trigger] args_ok(m, a, args) implies step_spec(m, a, args, s) is Disabled by {
            assert(covered(m, a, s, ts, args));
        }
    } else {
        assert(tr_sound(m, a, s, ts[0]));
    }
}

pub fn site_eq(a: &Site, b: &Site) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (Site::Guard, Site::Guard) => true,
        (Site::Update(x), Site::Update(y)) => *x == *y,
        (Site::Output, Site::Output) => true,
        _ => false,
    }
}

pub fn opt_eq(a: &Option<i64>, b: &Option<i64>) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => *x == *y,
        _ => false,
    }
}

} // verus!
