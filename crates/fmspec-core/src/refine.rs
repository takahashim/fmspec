//! 詳細化の検査（docs/plans/refinement_symmetry_constants.md の2）。
//!
//! 具体モデル `b` の状態から抽象モデル `a` の状態への写像 `f` を、`a` の状態のスロットごとの式で与える。
//! 式は `b` の状態の上で評価する（不変条件と同じ環境）。
//! 検査するのは、`b` の初期状態が `a` の初期状態に写り、`b` の到達可能な状態からの有効な遷移が、
//! `a` の遷移か、写した状態の変わらないステップに写ることである。
//! 活性と公平性の保存は扱わない。
//!
//! 受理側の証拠は `b` の証明書で、検査器は各状態の後続を遷移列挙で計算し直し、
//! 写した状態からの `a` の後続も遷移列挙で計算し直す。探索器の記録した対応は使わない。

use crate::cert::*;
use crate::checked::CheckedModel;
use crate::eval::*;
use crate::evidence::*;
use crate::model::*;
use crate::semantics::*;
#[cfg(verus_keep_ghost)]
use crate::state_enc::{args_ok, encode_spec};
use crate::state_enc::{encode, vec_eq};
use crate::step::*;
use crate::trace::*;
#[cfg(verus_keep_ghost)]
use crate::typing::*;
use vstd::prelude::*;

verus! {

// ---- 写像 ----

/// 写像の `i` 番目のスロットの、具体モデルの状態 `s` での符号。
pub open spec fn map_slot(b: RawModel, a: RawModel, f: Seq<Expr>, s: Seq<i64>, i: int) -> Result<i64, ErrKind> {
    match eval_spec(f[i], inv_env(b, s)) {
        Ok(v) => encode_spec(a.enums@, a.state_types@[i], v),
        Err(k) => Err(k),
    }
}

/// 写像の式の数は、抽象モデルの状態のスロットの数と等しい。
pub open spec fn map_wf(a: RawModel, f: Seq<Expr>) -> bool {
    f.len() == a.state_types@.len()
}

/// 状態 `s` で、写像のどのスロットの評価も成功する。
pub open spec fn maps_ok(b: RawModel, a: RawModel, f: Seq<Expr>, s: Seq<i64>) -> bool {
    &&& map_wf(a, f)
    &&& forall|i: int| 0 <= i < f.len() ==> #[trigger] map_slot(b, a, f, s, i) is Ok
}

/// 状態 `s` を写した抽象モデルの状態。`maps_ok` のときに意味を持つ。
pub open spec fn mapped(b: RawModel, a: RawModel, f: Seq<Expr>, s: Seq<i64>) -> Seq<i64> {
    Seq::new(f.len(), |i: int| map_slot(b, a, f, s, i)->Ok_0)
}

/// 抽象モデルの、操作 `ac` と引数 `args` による `x` から `y` への有効な遷移。出力は `o`。
pub open spec fn a_edge(a: RawModel, x: Seq<i64>, ac: int, args: Seq<i64>, o: Option<i64>, y: Seq<i64>) -> bool {
    0 <= ac < a.actions@.len() && args_ok(a, ac, args) && step_spec(a, ac, args, x) == Step::To(y, o)
}

/// `x` から `y` へは、状態の変わらないステップか、抽象モデルの遷移で移れる。
pub open spec fn abs_move(a: RawModel, x: Seq<i64>, y: Seq<i64>) -> bool {
    y == x || exists|ac: int, args: Seq<i64>, o: Option<i64>| #[trigger] a_edge(a, x, ac, args, o, y)
}

/// 具体モデルの初期状態 `s` は、抽象モデルの初期状態に写る。
pub open spec fn init_maps(b: RawModel, a: RawModel, f: Seq<Expr>, s: Seq<i64>) -> bool {
    maps_ok(b, a, f, s) && is_init(a, mapped(b, a, f, s))
}

/// 具体モデルの遷移 `s` → `t` は、抽象モデルの遷移か、状態の変わらないステップに写る。
pub open spec fn edge_maps(b: RawModel, a: RawModel, f: Seq<Expr>, s: Seq<i64>, t: Seq<i64>) -> bool {
    &&& maps_ok(b, a, f, s)
    &&& maps_ok(b, a, f, t)
    &&& abs_move(a, mapped(b, a, f, s), mapped(b, a, f, t))
}

/// 具体モデル `b`（検査条件 `cb` の対象の操作）は、写像 `f` のもとで抽象モデル `a` を詳細化する。
///
/// - `b` の初期状態は、`a` の初期状態に写る。
/// - `b` の到達可能な状態では、写像の評価が成功する。
/// - `b` の到達可能な状態からの有効な遷移は、`a` の遷移か、状態の変わらないステップに写る。
pub open spec fn refines(b: RawModel, cb: Conditions, a: RawModel, f: Seq<Expr>) -> bool {
    &&& forall|s: Seq<i64>| #[trigger] is_init(b, s) ==> init_maps(b, a, f, s)
    &&& forall|s: Seq<i64>, n: nat| #[trigger] reach(b, cb, s, n) ==> maps_ok(b, a, f, s)
    &&& forall|s: Seq<i64>, n: nat, ac: int, args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
        #[trigger] reach(b, cb, s, n) && #[trigger] is_edge(b, cb, s, ac, args, o, t) ==> edge_maps(b, a, f, s, t)
}

// ---- 証明書による検査の意味 ----

/// 状態 `s` で写像の評価が成功し、`s` からの有効な遷移は、どれも抽象モデルの遷移か状態の変わらないステップに写る。
pub open spec fn ref_state_ok(b: RawModel, cb: Conditions, a: RawModel, f: Seq<Expr>, s: Seq<i64>) -> bool {
    &&& maps_ok(b, a, f, s)
    &&& forall|ac: int, args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
        #[trigger] is_edge(b, cb, s, ac, args, o, t) ==> edge_maps(b, a, f, s, t)
}

/// 証明書の状態と初期状態が、詳細化の条件を満たす。
pub open spec fn ref_closed(b: RawModel, cb: Conditions, a: RawModel, f: Seq<Expr>, cert: Seq<Vec<i64>>) -> bool {
    &&& forall|i: int| 0 <= i < b.inits@.len() ==> init_maps(b, a, f, (#[trigger] b.inits@[i])@)
    &&& forall|j: int| 0 <= j < cert.len() ==> ref_state_ok(b, cb, a, f, (#[trigger] cert[j])@)
}

/// 帰納的な証明書の状態がどれも詳細化の条件を満たすなら、`b` は `a` を詳細化する。
pub proof fn lemma_cert_refines(b: RawModel, cb: Conditions, a: RawModel, f: Seq<Expr>, cert: Seq<Vec<i64>>)
    requires
        inductive(b, cb, cert),
        ref_closed(b, cb, a, f, cert),
    ensures
        refines(b, cb, a, f),
{
    assert forall|s: Seq<i64>| #[trigger] is_init(b, s) implies init_maps(b, a, f, s) by {
        let i = choose|i: int| 0 <= i < b.inits@.len() && (#[trigger] b.inits@[i])@ == s;
        assert(init_maps(b, a, f, b.inits@[i]@));
    }
    assert forall|s: Seq<i64>, n: nat| #[trigger] reach(b, cb, s, n) implies maps_ok(b, a, f, s) by {
        lemma_reach_in_cert(b, cb, cert, s, n);
        let j = choose|j: int| 0 <= j < cert.len() && (#[trigger] cert[j])@ == s;
        assert(ref_state_ok(b, cb, a, f, cert[j]@));
    }
    assert forall|s: Seq<i64>, n: nat, ac: int, args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
        #[trigger] reach(b, cb, s, n) && #[trigger] is_edge(b, cb, s, ac, args, o, t) implies edge_maps(
        b,
        a,
        f,
        s,
        t,
    ) by {
        lemma_reach_in_cert(b, cb, cert, s, n);
        let j = choose|j: int| 0 <= j < cert.len() && (#[trigger] cert[j])@ == s;
        assert(ref_state_ok(b, cb, a, f, cert[j]@));
    }
}

// ---- 不変条件の移送 ----

/// `ca` は抽象モデルのすべての操作を対象にする。
pub open spec fn all_actions(a: RawModel, ca: Conditions) -> bool {
    forall|ac: int| 0 <= ac < a.actions@.len() ==> #[trigger] act_on(a, ca, ac)
}

/// 詳細化するなら、具体モデルの到達可能な状態を写した状態は、抽象モデルで到達可能である。
pub proof fn lemma_refines_reach(b: RawModel, cb: Conditions, a: RawModel, f: Seq<Expr>, ca: Conditions, s: Seq<i64>, n: nat)
    requires
        refines(b, cb, a, f),
        all_actions(a, ca),
        reach(b, cb, s, n),
    ensures
        maps_ok(b, a, f, s),
        exists|m: nat| reach(a, ca, mapped(b, a, f, s), m),
    decreases n,
{
    assert(maps_ok(b, a, f, s));
    if n == 0 {
        assert(is_init(b, s));
        assert(init_maps(b, a, f, s));
        assert(reach(a, ca, mapped(b, a, f, s), 0));
    } else {
        let (p, ac, args, o) = choose|p: Seq<i64>, ac: int, args: Seq<i64>, o: Option<i64>|
            reach(b, cb, p, (n - 1) as nat) && #[trigger] is_edge(b, cb, p, ac, args, o, s);
        lemma_refines_reach(b, cb, a, f, ca, p, (n - 1) as nat);
        let m = choose|m: nat| reach(a, ca, mapped(b, a, f, p), m);
        assert(edge_maps(b, a, f, p, s));
        let x = mapped(b, a, f, p);
        let y = mapped(b, a, f, s);
        if y == x {
            assert(reach(a, ca, y, m));
        } else {
            let (bc, bargs, bo) = choose|bc: int, bargs: Seq<i64>, bo: Option<i64>| #[trigger] a_edge(a, x, bc, bargs, bo, y);
            assert(act_on(a, ca, bc));
            assert(is_edge(a, ca, x, bc, bargs, bo, y));
            assert(reach(a, ca, y, m + 1));
        }
    }
}

/// 詳細化するなら、抽象モデルが安全であるとき、具体モデルの到達可能な状態を写した状態で、抽象モデルの対象の不変条件が成り立つ。
pub proof fn lemma_refines_invariants(
    b: RawModel,
    cb: Conditions,
    a: RawModel,
    f: Seq<Expr>,
    ca: Conditions,
    s: Seq<i64>,
    n: nat,
)
    requires
        refines(b, cb, a, f),
        all_actions(a, ca),
        safe(a, ca),
        reach(b, cb, s, n),
    ensures
        invs_hold(a, ca, mapped(b, a, f, s)),
{
    lemma_refines_reach(b, cb, a, f, ca, s, n);
    let m = choose|m: nat| reach(a, ca, mapped(b, a, f, s), m);
    assert(state_safe(a, ca, mapped(b, a, f, s)));
}

// ---- 写像の評価 ----

pub enum Mapped {
    Ok(Vec<i64>),
    /// スロット（添字）の評価または符号化が失敗した。
    Fail(usize, ErrKind),
    /// 写像の式の数が、抽象モデルの状態のスロットの数と違う。
    Arity,
}

/// 状態 `s` を写す。
pub(crate) fn map_state(b: &RawModel, a: &RawModel, f: &Vec<Expr>, s: &Vec<i64>) -> (r: Mapped)
    ensures
        match r {
            Mapped::Ok(x) => maps_ok(*b, *a, f@, s@) && x@ == mapped(*b, *a, f@, s@),
            Mapped::Fail(i, k) => i < f@.len() && map_slot(*b, *a, f@, s@, i as int) == Err::<i64, ErrKind>(k),
            Mapped::Arity => !map_wf(*a, f@),
        },
{
    if f.len() != a.state_types.len() {
        return Mapped::Arity;
    }
    let no_tys: Vec<Type> = Vec::new();
    let no_vals: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &b.state_types, arg_tys: &no_tys, pre: s, args: &no_vals, post: &no_vals, out: None };
    assert(ctx@ == inv_env(*b, s@)) by {
        assert(no_tys@ =~= Seq::<Type>::empty());
        assert(no_vals@ =~= Seq::<i64>::empty());
    }
    let mut x: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < f.len()
        invariant
            map_wf(*a, f@),
            ctx@ == inv_env(*b, s@),
            i <= f@.len(),
            x@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] map_slot(*b, *a, f@, s@, j) == Ok::<i64, ErrKind>(x@[j]),
        decreases f@.len() - i,
    {
        let r = match eval(&f[i], &ctx) {
            Ok(v) => encode(&a.enums, &a.state_types[i], &v),
            Err(k) => Err(k),
        };
        match r {
            Ok(c) => x.push(c),
            Err(k) => {
                return Mapped::Fail(i, k);
            },
        }
        i = i + 1;
    }
    assert(x@ =~= mapped(*b, *a, f@, s@));
    Mapped::Ok(x)
}

/// 抽象モデルの遷移で移れるかの判定。
pub enum Move {
    /// 状態の変わらないステップか、抽象モデルの遷移で移れる。
    Yes,
    /// 移れない。
    No,
    /// 抽象モデルの操作（添字）の遷移列挙が評価エラーになり、移れないとは言えない。
    Unknown(usize),
}

/// `x` から `y` へ、状態の変わらないステップか、抽象モデルの遷移で移れるか。
#[verifier::loop_isolation(false)]
pub(crate) fn find_move(a: &RawModel, x: &Vec<i64>, y: &Vec<i64>) -> (r: Move)
    ensures
        r is Yes ==> abs_move(*a, x@, y@),
        r is No ==> !abs_move(*a, x@, y@),
{
    if vec_eq(x, y) {
        return Move::Yes;
    }
    let mut unknown: Option<usize> = None;
    let mut ac: usize = 0;
    while ac < a.actions.len()
        invariant
            ac <= a.actions@.len(),
            x@ != y@,
            unknown is None ==> forall|bc: int, args: Seq<i64>, o: Option<i64>|
                0 <= bc < ac ==> !#[trigger] a_edge(*a, x@, bc, args, o, y@),
        decreases a.actions@.len() - ac,
    {
        match enumerate(a, ac, x) {
            Enumerated::Fail(_, _, _) => {
                if unknown.is_none() {
                    unknown = Some(ac);
                }
            },
            Enumerated::Ok(ts) => {
                let mut i: usize = 0;
                while i < ts.len()
                    invariant
                        i <= ts@.len(),
                        enum_ok(*a, ac as int, x@, ts@),
                        forall|j: int| 0 <= j < i ==> (#[trigger] ts@[j]).state@ != y@,
                    decreases ts@.len() - i,
                {
                    if vec_eq(&ts[i].state, y) {
                        proof {
                            assert(tr_sound(*a, ac as int, x@, ts@[i as int]));
                            assert(a_edge(*a, x@, ac as int, ts@[i as int].args@, ts@[i as int].output, y@));
                        }
                        return Move::Yes;
                    }
                    i = i + 1;
                }
                proof {
                    assert forall|args: Seq<i64>, o: Option<i64>| !#[trigger] a_edge(*a, x@, ac as int, args, o, y@) by {
                        if a_edge(*a, x@, ac as int, args, o, y@) {
                            assert(covered(*a, ac as int, x@, ts@, args));
                            let j = choose|j: int| 0 <= j < ts@.len() && (#[trigger] ts@[j]).args@ == args;
                            assert(tr_sound(*a, ac as int, x@, ts@[j]));
                        }
                    }
                }
            },
        }
        ac = ac + 1;
    }
    match unknown {
        Some(u) => Move::Unknown(u),
        None => {
            proof {
                assert forall|bc: int, args: Seq<i64>, o: Option<i64>| !#[trigger] a_edge(*a, x@, bc, args, o, y@) by {
                    if a_edge(*a, x@, bc, args, o, y@) {
                        assert(0 <= bc < a.actions@.len());
                    }
                }
            }
            Move::No
        },
    }
}

// ---- 証明書による検査 ----

/// 具体モデルの、操作 `ac` と引数 `args` による `s` から `t` への有効な遷移。出力は `o`。
pub open spec fn b_step(b: RawModel, ac: int, args: Seq<i64>, s: Seq<i64>, o: Option<i64>, t: Seq<i64>) -> bool {
    args_ok(b, ac, args) && step_spec(b, ac, args, s) == Step::To(t, o)
}

/// 証明書の `k` 番目の状態 `s`（写した状態 `x`）で、対象の操作 `ac` の遷移を検査する。
#[verifier::loop_isolation(false)]
fn check_ref_action(
    b: &RawModel,
    a: &RawModel,
    f: &Vec<Expr>,
    k: usize,
    ac: usize,
    s: &Vec<i64>,
    x: &Vec<i64>,
) -> (r: Option<Reject>)
    requires
        ac < b.actions@.len(),
        map_wf(*a, f@),
        maps_ok(*b, *a, f@, s@),
        x@ == mapped(*b, *a, f@, s@),
    ensures
        r is None ==> forall|args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
            #[trigger] b_step(*b, ac as int, args, s@, o, t) ==> edge_maps(*b, *a, f@, s@, t),
{
    match enumerate(b, ac, s) {
        Enumerated::Fail(_, _, _) => Some(Reject::StepFailed(k, ac)),
        Enumerated::Ok(ts) => {
            let mut i: usize = 0;
            while i < ts.len()
                invariant
                    i <= ts@.len(),
                    enum_ok(*b, ac as int, s@, ts@),
                    forall|j: int| 0 <= j < i ==> edge_maps(*b, *a, f@, s@, (#[trigger] ts@[j]).state@),
                decreases ts@.len() - i,
            {
                match map_state(b, a, f, &ts[i].state) {
                    Mapped::Arity => {
                        return Some(Reject::MappingFailed(k, f.len()));
                    },
                    Mapped::Fail(slot, _) => {
                        return Some(Reject::MappingFailed(k, slot));
                    },
                    Mapped::Ok(y) => match find_move(a, x, &y) {
                        Move::Yes => {},
                        _ => {
                            return Some(Reject::StepNotMapped(k, ac));
                        },
                    },
                }
                i = i + 1;
            }
            proof {
                assert forall|args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
                    #[trigger] b_step(*b, ac as int, args, s@, o, t) implies edge_maps(*b, *a, f@, s@, t) by {
                    assert(covered(*b, ac as int, s@, ts@, args));
                    let j = choose|j: int| 0 <= j < ts@.len() && (#[trigger] ts@[j]).args@ == args;
                    assert(tr_sound(*b, ac as int, s@, ts@[j]));
                    assert(edge_maps(*b, *a, f@, s@, ts@[j].state@));
                }
            }
            None
        },
    }
}

/// 証明書の `k` 番目の状態を検査する。
#[verifier::loop_isolation(false)]
fn check_ref_state(b: &RawModel, cb: &Conditions, a: &RawModel, f: &Vec<Expr>, cert: &Vec<Vec<i64>>, k: usize) -> (r: Option<
    Reject,
>)
    requires
        k < cert@.len(),
        map_wf(*a, f@),
    ensures
        r is None ==> ref_state_ok(*b, *cb, *a, f@, cert@[k as int]@),
{
    let s = &cert[k];
    let x = match map_state(b, a, f, s) {
        Mapped::Arity => {
            return Some(Reject::MappingFailed(k, f.len()));
        },
        Mapped::Fail(slot, _) => {
            return Some(Reject::MappingFailed(k, slot));
        },
        Mapped::Ok(x) => x,
    };
    let mut ac: usize = 0;
    while ac < b.actions.len()
        invariant
            ac <= b.actions@.len(),
            maps_ok(*b, *a, f@, s@),
            x@ == mapped(*b, *a, f@, s@),
            forall|bc: int, args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
                0 <= bc < ac && #[trigger] is_edge(*b, *cb, s@, bc, args, o, t) ==> edge_maps(*b, *a, f@, s@, t),
        decreases b.actions@.len() - ac,
    {
        if act_on_exec(b, cb, ac) {
            match check_ref_action(b, a, f, k, ac, s, &x) {
                Some(r) => {
                    return Some(r);
                },
                None => {},
            }
        }
        proof {
            assert forall|bc: int, args: Seq<i64>, o: Option<i64>, t: Seq<i64>|
                0 <= bc < ac + 1 && #[trigger] is_edge(*b, *cb, s@, bc, args, o, t) implies edge_maps(
                *b,
                *a,
                f@,
                s@,
                t,
            ) by {
                if bc == ac {
                    assert(b_step(*b, ac as int, args, s@, o, t));
                }
            }
        }
        ac = ac + 1;
    }
    None
}

/// 具体モデルの初期状態が、抽象モデルの初期状態に写ることを検査する。
fn check_ref_initials(b: &RawModel, a: &RawModel, f: &Vec<Expr>) -> (r: Option<Reject>)
    requires
        map_wf(*a, f@),
    ensures
        r is None ==> forall|i: int| 0 <= i < b.inits@.len() ==> init_maps(*b, *a, f@, (#[trigger] b.inits@[i])@),
{
    let mut i: usize = 0;
    while i < b.inits.len()
        invariant
            map_wf(*a, f@),
            i <= b.inits@.len(),
            forall|j: int| 0 <= j < i ==> init_maps(*b, *a, f@, (#[trigger] b.inits@[j])@),
        decreases b.inits@.len() - i,
    {
        match map_state(b, a, f, &b.inits[i]) {
            Mapped::Arity => {
                return Some(Reject::InitialMappingFailed(i, f.len()));
            },
            Mapped::Fail(slot, _) => {
                return Some(Reject::InitialMappingFailed(i, slot));
            },
            Mapped::Ok(x) => {
                if !is_initial(a, &x) {
                    return Some(Reject::InitialNotMapped(i));
                }
            },
        }
        i = i + 1;
    }
    None
}

/// 詳細化の証明書を検査する。`None`（受理）を返すなら、`b` は `f` のもとで `a` を詳細化する。
pub(crate) fn check_refinement_certificate(
    b: &RawModel,
    cb: &Conditions,
    a: &RawModel,
    f: &Vec<Expr>,
    cert: &Vec<Vec<i64>>,
) -> (r: Option<Reject>)
    requires
        map_wf(*a, f@),
    ensures
        r is None ==> inductive(*b, *cb, cert@) && safe(*b, *cb) && refines(*b, *cb, *a, f@),
{
    match check_certificate(b, cb, cert) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    match check_ref_initials(b, a, f) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    let mut k: usize = 0;
    while k < cert.len()
        invariant
            map_wf(*a, f@),
            inductive(*b, *cb, cert@),
            safe(*b, *cb),
            forall|i: int| 0 <= i < b.inits@.len() ==> init_maps(*b, *a, f@, (#[trigger] b.inits@[i])@),
            k <= cert@.len(),
            forall|j: int| 0 <= j < k ==> ref_state_ok(*b, *cb, *a, f@, (#[trigger] cert@[j])@),
        decreases cert@.len() - k,
    {
        match check_ref_state(b, cb, a, f, cert, k) {
            Some(r) => {
                return Some(r);
            },
            None => {},
        }
        k = k + 1;
    }
    proof {
        lemma_cert_refines(*b, *cb, *a, f@, cert@);
    }
    None
}

// ---- トレースによる検査 ----

/// 詳細化が破れる事象の主張。トレースの末尾について述べる。
pub enum RefClaim {
    /// 開始状態（トレースの長さは0）を写した状態が、抽象モデルの初期状態でない。
    Init,
    /// 最後の遷移が、抽象モデルの遷移にも、状態の変わらないステップにも写らない。
    Step,
    /// 末尾の状態で、写像のスロット（添字）の評価または符号化が失敗する。
    Map(usize, ErrKind),
    /// 具体モデルそのものについての主張（操作の評価の失敗など）。
    Model(Claim),
}

/// 詳細化が破れる主張か。写像の評価の失敗と、具体モデルの評価エラーは、評価エラーの主張である。
pub open spec fn ref_violation(claim: RefClaim) -> bool {
    match claim {
        RefClaim::Init => true,
        RefClaim::Step => true,
        RefClaim::Map(_, _) => false,
        RefClaim::Model(c) => is_violation(c),
    }
}

/// トレースの末尾で、主張どおりの事象が起きる。
pub open spec fn ref_claim_holds(
    b: RawModel,
    cb: Conditions,
    a: RawModel,
    f: Seq<Expr>,
    start: Seq<i64>,
    steps: Seq<TraceStep>,
    claim: RefClaim,
) -> bool {
    let n = steps.len() as int;
    match claim {
        RefClaim::Init => n == 0 && maps_ok(b, a, f, start) && !is_init(a, mapped(b, a, f, start)),
        RefClaim::Step => {
            let p = state_at(start, steps, n - 1);
            let q = state_at(start, steps, n);
            &&& n >= 1
            &&& maps_ok(b, a, f, p)
            &&& maps_ok(b, a, f, q)
            &&& !abs_move(a, mapped(b, a, f, p), mapped(b, a, f, q))
        },
        RefClaim::Map(i, k) => map_wf(a, f) && i < f.len() && map_slot(b, a, f, state_at(start, steps, n), i as int)
            == Err::<i64, ErrKind>(k),
        RefClaim::Model(c) => claim_holds(b, cb, start, steps, c),
    }
}

/// 主張の成り立つ有効なトレースがあれば、`b` は `a` を詳細化しない。
pub proof fn lemma_refines_excludes_trace(
    b: RawModel,
    cb: Conditions,
    a: RawModel,
    f: Seq<Expr>,
    start: Seq<i64>,
    steps: Seq<TraceStep>,
    claim: RefClaim,
)
    requires
        refines(b, cb, a, f),
        is_init(b, start),
        trace_ok(b, cb, start, steps),
        ref_claim_holds(b, cb, a, f, start, steps, claim),
        !(claim is Model),
    ensures
        false,
{
    let n = steps.len() as int;
    match claim {
        RefClaim::Init => {
            assert(init_maps(b, a, f, start));
        },
        RefClaim::Step => {
            lemma_trace_reach(b, cb, start, steps, (n - 1) as nat);
            assert(step_ok(b, cb, start, steps, n - 1));
            let st = steps[n - 1];
            assert(state_at(start, steps, n) == st.state@);
            assert(is_edge(b, cb, state_at(start, steps, n - 1), st.action as int, st.args@, st.output, st.state@));
            assert(reach(b, cb, state_at(start, steps, n - 1), (n - 1) as nat));
        },
        RefClaim::Map(i, k) => {
            lemma_trace_reach(b, cb, start, steps, n as nat);
            assert(reach(b, cb, state_at(start, steps, n), n as nat));
            assert(maps_ok(b, a, f, state_at(start, steps, n)));
            assert(map_slot(b, a, f, state_at(start, steps, n), i as int) is Ok);
        },
        RefClaim::Model(_) => {},
    }
}

/// 主張を検査する。
fn check_ref_claim(
    b: &RawModel,
    cb: &Conditions,
    a: &RawModel,
    f: &Vec<Expr>,
    start: &Vec<i64>,
    steps: &Vec<TraceStep>,
    claim: &RefClaim,
) -> (r: bool)
    requires
        map_wf(*a, f@),
    ensures
        r ==> ref_claim_holds(*b, *cb, *a, f@, start@, steps@, *claim),
{
    let n = steps.len();
    let last = if n == 0 {
        start
    } else {
        &steps[n - 1].state
    };
    assert(last@ == state_at(start@, steps@, n as int));
    match claim {
        RefClaim::Init => {
            if n != 0 {
                return false;
            }
            match map_state(b, a, f, start) {
                Mapped::Ok(x) => {
                    // 初期状態の列にないことを確かめる。
                    let mut i: usize = 0;
                    while i < a.inits.len()
                        invariant
                            i <= a.inits@.len(),
                            forall|j: int| 0 <= j < i ==> (#[trigger] a.inits@[j])@ != x@,
                        decreases a.inits@.len() - i,
                    {
                        if vec_eq(&a.inits[i], &x) {
                            return false;
                        }
                        i = i + 1;
                    }
                    true
                },
                _ => false,
            }
        },
        RefClaim::Step => {
            if n == 0 {
                return false;
            }
            let prev = if n == 1 {
                start
            } else {
                &steps[n - 2].state
            };
            assert(prev@ == state_at(start@, steps@, n - 1));
            let x = match map_state(b, a, f, prev) {
                Mapped::Ok(x) => x,
                _ => {
                    return false;
                },
            };
            let y = match map_state(b, a, f, last) {
                Mapped::Ok(y) => y,
                _ => {
                    return false;
                },
            };
            match find_move(a, &x, &y) {
                Move::No => true,
                _ => false,
            }
        },
        RefClaim::Map(i, k) => {
            if *i >= f.len() {
                return false;
            }
            match map_state(b, a, f, last) {
                Mapped::Fail(j, k2) => {
                    if j != *i || !errkind_eq(&k2, k) {
                        return false;
                    }
                    true
                },
                _ => false,
            }
        },
        RefClaim::Model(c) => check_claim(b, cb, start, steps, c),
    }
}

/// 詳細化のトレースを検査する。`None`（受理）を返すなら、トレースは有効で、末尾で主張どおりの事象が起きる。
pub(crate) fn check_refinement_trace(
    b: &RawModel,
    cb: &Conditions,
    a: &RawModel,
    f: &Vec<Expr>,
    start: &Vec<i64>,
    steps: &Vec<TraceStep>,
    claim: &RefClaim,
) -> (r: Option<Reject>)
    requires
        map_wf(*a, f@),
    ensures
        r is None ==> is_init(*b, start@) && trace_ok(*b, *cb, start@, steps@) && ref_claim_holds(
            *b,
            *cb,
            *a,
            f@,
            start@,
            steps@,
            *claim,
        ),
{
    if !is_initial(b, start) {
        return Some(Reject::BadStart);
    }
    match replay(b, cb, start, steps) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    if check_ref_claim(b, cb, a, f, start, steps, claim) {
        None
    } else {
        Some(Reject::ClaimNotReproduced)
    }
}

// ---- 判定ゲート ----

/// 詳細化の証拠。
pub enum RefEvidence {
    /// 具体モデルの証明書。
    Certificate(Certificate),
    /// 開始状態、ステップ、末尾の事象の主張。
    Trace(Vec<i64>, Vec<TraceStep>, RefClaim),
    Unavailable(Limit),
}

/// 詳細化の判定の種類。安全性の判定（[`VerdictKind`]）と取り違えないよう、型を分ける。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefVerdictKind {
    /// 証明書を受理した。具体モデルは写像のもとで抽象モデルを詳細化し、到達可能な評価エラーもない。
    Refines,
    /// 詳細化が破れるトレースを受理した。
    NotRefines,
    /// 写像か具体モデルの評価エラーに至るトレースを受理した。
    Error,
    /// 証拠を得られなかった。
    Inconclusive,
    /// モデルが整形式でないか、写像の式の数が抽象モデルの状態のスロットの数と違う。
    InvalidModel,
    /// 証拠を拒否した。探索器が生成した証拠なら、探索器の不具合を示す。
    Rejected,
}

/// 詳細化の判定と、その理由。[`RefVerdict::outcome`] が返す。理由のある判定は、理由を必ず持つ。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefVerdictOutcome {
    /// 証明書を受理した。
    Refines,
    /// 詳細化が破れるトレースを受理した。
    NotRefines,
    /// 写像か具体モデルの評価エラーに至るトレースを受理した。
    Error,
    /// 証拠を得られなかった。理由を持つ。
    Inconclusive(Limit),
    /// モデルが整形式でないか、写像の式の数が抽象モデルの状態のスロットの数と違う。
    InvalidModel,
    /// 証拠を拒否した。拒否の理由を持つ。
    Rejected(Reject),
}

/// 詳細化の判定。`decide_refinement` だけが構築する。
pub struct RefVerdict {
    kind: RefVerdictKind,
    reject: Option<Reject>,
    limit: Option<Limit>,
}

impl RefVerdict {
    /// 理由は、判定の種類に対応するものだけがある（`reasons_ok`）。
    #[verifier::type_invariant]
    spec fn reasons_match(self) -> bool {
        self.reasons_ok()
    }

    pub closed spec fn spec_kind(self) -> RefVerdictKind {
        self.kind
    }

    pub fn kind(&self) -> (k: RefVerdictKind)
        ensures
            k == self.spec_kind(),
    {
        self.kind
    }

    pub closed spec fn spec_reject(self) -> Option<Reject> {
        self.reject
    }

    pub closed spec fn spec_limit(self) -> Option<Limit> {
        self.limit
    }

    /// 理由は、判定の種類に対応するものだけがある。`Rejected` には拒否の理由が、`Inconclusive` には
    /// 証拠を得られなかった理由が必ずあり、それ以外の判定にはない。
    pub open spec fn reasons_ok(self) -> bool {
        &&& (self.spec_kind() is Rejected <==> self.spec_reject() is Some)
        &&& (self.spec_kind() is Inconclusive <==> self.spec_limit() is Some)
    }

    /// 証拠を拒否した理由。判定が `Rejected` のとき、かつそのときに限り `Some`。
    pub fn reject(&self) -> (r: Option<Reject>)
        ensures
            r == self.spec_reject(),
    {
        self.reject
    }

    /// 証拠を得られなかった理由。判定が `Inconclusive` のとき、かつそのときに限り `Some`。
    pub fn limit(&self) -> (r: Option<Limit>)
        ensures
            r == self.spec_limit(),
    {
        self.limit
    }

    /// 判定と、その理由。理由のある判定（`Rejected`、`Inconclusive`）は、その理由を持つ。
    pub fn outcome(&self) -> (o: RefVerdictOutcome)
        ensures
            match o {
                RefVerdictOutcome::Refines => self.spec_kind() is Refines,
                RefVerdictOutcome::NotRefines => self.spec_kind() is NotRefines,
                RefVerdictOutcome::Error => self.spec_kind() is Error,
                RefVerdictOutcome::Inconclusive(l) => self.spec_kind() is Inconclusive && self.spec_limit() == Some(l),
                RefVerdictOutcome::InvalidModel => self.spec_kind() is InvalidModel,
                RefVerdictOutcome::Rejected(r) => self.spec_kind() is Rejected && self.spec_reject() == Some(r),
            },
    {
        proof {
            use_type_invariant(self);
        }
        match self.kind {
            RefVerdictKind::Refines => RefVerdictOutcome::Refines,
            RefVerdictKind::NotRefines => RefVerdictOutcome::NotRefines,
            RefVerdictKind::Error => RefVerdictOutcome::Error,
            RefVerdictKind::Inconclusive => RefVerdictOutcome::Inconclusive(self.limit.unwrap()),
            RefVerdictKind::InvalidModel => RefVerdictOutcome::InvalidModel,
            RefVerdictKind::Rejected => RefVerdictOutcome::Rejected(self.reject.unwrap()),
        }
    }

    fn of(kind: RefVerdictKind) -> (v: RefVerdict)
        requires
            !(kind is Rejected || kind is Inconclusive),
        ensures
            v.spec_kind() == kind,
            v.spec_reject() is None,
            v.spec_limit() is None,
    {
        RefVerdict { kind, reject: None, limit: None }
    }

    fn rejected(r: Reject) -> (v: RefVerdict)
        ensures
            v.spec_kind() == RefVerdictKind::Rejected,
            v.spec_reject() == Some(r),
            v.spec_limit() is None,
    {
        RefVerdict { kind: RefVerdictKind::Rejected, reject: Some(r), limit: None }
    }
}

/// 詳細化の判定の意味。
///
/// - `Refines`: 証拠は証明書で、`b` は検査条件 `cb` のもとで安全であり、写像 `f` のもとで `a` を詳細化する。
/// - `NotRefines` / `Error`: 証拠はトレースで、そのトレースは `b` の初期状態から始まって有効であり、末尾で主張どおりの事象が起きる。
/// - `Inconclusive`: 何も主張しない。
/// - `InvalidModel`: モデルか写像が整形式でない場合に限る。
/// - `Rejected`: 証拠が提示された場合に限る。
pub open spec fn refinement_sound(
    b: RawModel,
    cb: Conditions,
    a: RawModel,
    f: Seq<Expr>,
    ev: RefEvidence,
    k: RefVerdictKind,
) -> bool {
    let ok = wf(b) && wf(a) && map_wf(a, f);
    match k {
        RefVerdictKind::Refines => ok && ev is Certificate && safe(b, cb) && refines(b, cb, a, f),
        RefVerdictKind::NotRefines => ok && match ev {
            RefEvidence::Trace(start, steps, claim) => ref_violation(claim) && is_init(b, start@) && trace_ok(
                b,
                cb,
                start@,
                steps@,
            ) && ref_claim_holds(b, cb, a, f, start@, steps@, claim),
            _ => false,
        },
        RefVerdictKind::Error => ok && match ev {
            RefEvidence::Trace(start, steps, claim) => !ref_violation(claim) && is_init(b, start@) && trace_ok(
                b,
                cb,
                start@,
                steps@,
            ) && ref_claim_holds(b, cb, a, f, start@, steps@, claim),
            _ => false,
        },
        RefVerdictKind::Inconclusive => ok,
        RefVerdictKind::InvalidModel => !ok,
        RefVerdictKind::Rejected => ok && !(ev is Unavailable),
    }
}

fn ref_violation_exec(claim: &RefClaim) -> (r: bool)
    ensures
        r == ref_violation(*claim),
{
    match claim {
        RefClaim::Init => true,
        RefClaim::Step => true,
        RefClaim::Map(_, _) => false,
        RefClaim::Model(c) => is_violation_exec(c),
    }
}

/// 詳細化の判定ゲート。具体モデル `b`、その検査条件 `cb`、抽象モデル `a`、写像 `f` と証拠を受け取り、
/// 証拠を検査してから判定を返す。前提条件を持たない。
pub fn decide_refinement(
    b: &CheckedModel,
    cb: &Conditions,
    a: &CheckedModel,
    f: &Vec<Expr>,
    ev: &RefEvidence,
) -> (v: RefVerdict)
    ensures
        refinement_sound(b@, *cb, a@, f@, *ev, v.spec_kind()),
        v.reasons_ok(),
        match *ev {
            RefEvidence::Unavailable(l) => v.spec_kind() is InvalidModel || (v.spec_kind() is Inconclusive
                && v.spec_limit() == Some(l)),
            _ => true,
        },
{
    let bm = b.raw();
    let am = a.raw();
    if f.len() != am.state_types.len() {
        return RefVerdict::of(RefVerdictKind::InvalidModel);
    }
    match ev {
        RefEvidence::Certificate(cert) => {
            if !conditions_eq(bm, &cert.conditions, cb) {
                return RefVerdict::rejected(Reject::ConditionMismatch);
            }
            match check_refinement_certificate(bm, cb, am, f, &cert.states) {
                None => RefVerdict::of(RefVerdictKind::Refines),
                Some(r) => RefVerdict::rejected(r),
            }
        },
        RefEvidence::Trace(start, steps, claim) => match check_refinement_trace(bm, cb, am, f, start, steps, claim) {
            None => if ref_violation_exec(claim) {
                RefVerdict::of(RefVerdictKind::NotRefines)
            } else {
                RefVerdict::of(RefVerdictKind::Error)
            },
            Some(r) => RefVerdict::rejected(r),
        },
        RefEvidence::Unavailable(limit) => RefVerdict { kind: RefVerdictKind::Inconclusive, reject: None, limit: Some(*limit) },
    }
}


// ---- 未検証コード向けの公開関数 ----

/// 具体モデルの状態 `s` を、写像 `f` で抽象モデルの状態に写す（`map_state` と同じ）。
pub fn map_state_of(b: &CheckedModel, a: &CheckedModel, f: &Vec<Expr>, s: &Vec<i64>) -> (r: Mapped)
    ensures
        match r {
            Mapped::Ok(x) => maps_ok(b@, a@, f@, s@) && x@ == mapped(b@, a@, f@, s@),
            Mapped::Fail(i, k) => i < f@.len() && map_slot(b@, a@, f@, s@, i as int) == Err::<i64, ErrKind>(k),
            Mapped::Arity => !map_wf(a@, f@),
        },
{
    map_state(b.raw(), a.raw(), f, s)
}

/// 抽象モデルで、状態 `x` から `y` へ、1つの遷移か状態の変わらないステップで移れるか（`find_move` と同じ）。
pub fn find_move_of(a: &CheckedModel, x: &Vec<i64>, y: &Vec<i64>) -> (r: Move)
    ensures
        r is Yes ==> abs_move(a@, x@, y@),
        r is No ==> !abs_move(a@, x@, y@),
{
    find_move(a.raw(), x, y)
}

} // verus!
