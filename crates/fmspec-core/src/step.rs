//! 遷移の意味論と遷移列挙。
//!
//! `step_spec` が1つの具体的な遷移の意味論で、`step` はそれと一致する実装である。
//! `enumerate` は、ある状態での1操作の有効な遷移を、漏れなく、かつ有効なものだけ列挙する
//! （仕様書 §14.1 Transition Soundness / Completeness）。

use crate::eval::*;
use crate::model::*;
#[cfg(verus_keep_ghost)]
use crate::state_enc::{args_ok, encode_spec, in_type, type_range};
use crate::state_enc::{copy_vec, encode, type_range_exec};
use vstd::prelude::*;

verus! {

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

/// 1つの具体的な遷移を計算する。結果は `step_spec` と一致する。
pub(crate) fn step(m: &RawModel, a: usize, args: &Vec<i64>, s: &Vec<i64>) -> (r: StepR)
    requires
        a < m.actions@.len(),
    ensures
        r@ == step_spec(*m, a as int, args@, s@),
{
    let mut ls: Vec<Value> = Vec::new();
    step_with(m, a, args, s, &mut ls)
}

/// `step` に、式の評価に使う作業用の局所変数の列 `ls` を渡すもの。`ls` は空で渡し、空に戻る。
#[verifier::loop_isolation(false)]
fn step_with(m: &RawModel, a: usize, args: &Vec<i64>, s: &Vec<i64>, ls: &mut Vec<Value>) -> (r: StepR)
    requires
        a < m.actions@.len(),
        old(ls)@.len() == 0,
    ensures
        r@ == step_spec(*m, a as int, args@, s@),
        final(ls)@.len() == 0,
{
    let act = &m.actions[a];
    let empty: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &m.state_types, arg_tys: &act.domains, pre: s, args, post: &empty, out: None };
    let ghost env = act_env(*m, a as int, args@, s@);
    assert(ctx@ == env) by {
        assert(empty@ =~= Seq::<i64>::empty());
    }
    match eval_prop_with(&act.guard, &ctx, ls) {
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
                    ls@.len() == 0,
                    k <= act.updates@.len(),
                    apply_updates(*m, a as int, env, k as nat, t@) == apply_updates(*m, a as int, env, 0, s@),
                decreases act.updates@.len() - k,
            {
                let u = &act.updates[k];
                match eval_with(&u.expr, &ctx, ls) {
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
                Some(o) => match eval_with(&o.expr, &ctx, ls) {
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
fn enum_rec(
    m: &RawModel,
    a: usize,
    s: &Vec<i64>,
    prefix: &mut Vec<i64>,
    ts: &mut Vec<Transition>,
    ls: &mut Vec<Value>,
) -> (r: Option<(Vec<i64>, Site, ErrKind)>)
    requires
        a < m.actions@.len(),
        old(ls)@.len() == 0,
        prefix_ok(*m, a as int, old(prefix)@),
        all_sound(*m, a as int, s@, old(ts)@),
    ensures
        final(prefix)@ == old(prefix)@,
        final(ls)@.len() == 0,
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
        match step_with(m, a, prefix, s, ls) {
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
            ls@.len() == 0,
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
        let r = enum_rec(m, a, s, prefix, ts, ls);
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
    let mut ls: Vec<Value> = Vec::new();
    match enum_rec(m, a, s, &mut prefix, &mut ts, &mut ls) {
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
