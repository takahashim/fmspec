//! 下ろしの全域性の前提を、実行時に確かめる検査（計画書 docs/plans/lowering_totality.md の手順7）。
//!
//! 型の大きさの条件（[`lim_s_exec`]、[`lim_x_exec`]）、
//! 式とその部分式の条件（[`check_lim`]）を、仕様と一致する実行関数として持つ。

#[cfg(verus_keep_ghost)]
use crate::slot::equality::lemma_smalls;
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::lemma_smalls_at;
#[cfg(verus_keep_ghost)]
use crate::slot::total::{here_ok, lemma_lim_ok_items_at, lemma_lim_ok_items_intro, lemma_lim_ok_seq_at};
#[cfg(verus_keep_ghost)]
use crate::slot::total::{lemma_lim_ok_seq_intro, lim_ok, lim_ok_items, lim_ok_seq, quant_bound};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_stys, lemma_xtys, sty, stys, width, width_sum, xty, xtys, STy, XTy};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{xwidth, xwidth_sum};
use crate::value::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::value::infer::{agrees, scope_view};
use crate::value::infer::{check, Scope};
#[cfg(verus_keep_ghost)]
use crate::value::limits::*;
use crate::value::source::{Item, Over, TExpr};
use crate::value::stype_exec::wf_xtype_exec;
use crate::value::stype_exec::{keys_exec, keys_or_zero_exec, stype_eq, to_xtype, wf_stype_exec};
use vstd::prelude::*;

verus! {

/// 幅を上限で切った値。上限を超えるなら `lim() + 1`。
pub open spec fn capped(w: nat) -> nat {
    if w <= lim() {
        w
    } else {
        lim() + 1
    }
}

pub proof fn lemma_capped_add(a: nat, b: nat)
    ensures
        capped(capped(a) + capped(b)) == capped(a + b),
{
}

proof fn lemma_capped_mul(n: nat, w: nat)
    ensures
        capped(n * (1 + capped(w))) == capped(n * (1 + w)),
        capped(1 + n * capped(w)) == capped(1 + n * w),
{
    if w > lim() && n >= 1 {
        assert(n * (1 + capped(w)) >= 1 + capped(w)) by (nonlinear_arith)
            requires
                n >= 1,
        ;
        assert(n * (1 + w) >= 1 + w) by (nonlinear_arith)
            requires
                n >= 1,
        ;
        assert(n * capped(w) >= capped(w)) by (nonlinear_arith)
            requires
                n >= 1,
        ;
        assert(n * w >= w) by (nonlinear_arith)
            requires
                n >= 1,
        ;
    }
    if n == 0 {
        assert(n * (1 + capped(w)) == 0);
        assert(n * (1 + w) == 0);
        assert(n * capped(w) == 0);
        assert(n * w == 0);
    }
}

/// 格納の型の幅を上限で切った値。
pub fn cap_s(t: &SType, enums: &Vec<i64>) -> (r: u128)
    ensures
        r == capped(width(sty(*t), enums@)),
    decreases t, 1nat,
{
    match t {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) => 1,
        SType::Tuple(ts) | SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            cap_s_sum(t, ts, enums)
        },
        SType::Option(x) => {
            let w = cap_s(x, enums);
            proof {
                lemma_capped_add(1, width(sty(**x), enums@));
            }
            if 1 + w > 0x7fff_ffff {
                0x8000_0000
            } else {
                1 + w
            }
        },
        SType::Set(e) => keys_or_zero_exec(e, enums) as u128,
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums) as u128;
            let w = cap_s(v, enums);
            proof {
                lemma_capped_mul(n as nat, width(sty(**v), enums@));
                assert(n * (1 + w) <= 4096 * (1 + 0x8000_0000)) by (nonlinear_arith)
                    requires
                        n <= 4096,
                        w <= 0x8000_0000,
                ;
            }
            let p = n * (1 + w);
            if p > 0x7fff_ffff {
                0x8000_0000
            } else {
                p
            }
        },
        SType::List(e, max) => {
            let w = cap_s(e, enums);
            let m = *max as u128;
            proof {
                lemma_capped_mul(m as nat, width(sty(**e), enums@));
                assert(m * w <= 0xffff_ffff_ffff_ffff * 0x8000_0000) by (nonlinear_arith)
                    requires
                        m <= 0xffff_ffff_ffff_ffff,
                        w <= 0x8000_0000,
                ;
            }
            let p = 1 + m * w;
            if p > 0x7fff_ffff {
                0x8000_0000
            } else {
                p
            }
        },
    }
}

fn cap_s_sum(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: u128)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == capped(width_sum(stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let mut acc: u128 = 0;
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            acc == capped(width_sum(stys(ts@).take(i as int), enums@)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        let w = cap_s(&ts[i], enums);
        proof {
            lemma_capped_add(width_sum(stys(ts@).take(i as int), enums@), width(sty(ts@[i as int]), enums@));
        }
        acc = if acc + w > 0x7fff_ffff {
            0x8000_0000
        } else {
            acc + w
        };
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    acc
}

/// 格納の型が大きさの条件を満たすか。
pub fn lim_s_exec(t: &SType, enums: &Vec<i64>) -> (r: bool)
    ensures
        r == lim_s(sty(*t), enums@),
    decreases t, 1nat,
{
    if cap_s(t, enums) > 0x7fff_ffff {
        return false;
    }
    match t {
        SType::Tuple(ts) | SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            lim_ss_exec(t, ts, enums)
        },
        SType::Option(x) => lim_s_exec(x, enums),
        SType::Set(e) => lim_s_exec(e, enums),
        SType::Map(k, v) => lim_s_exec(k, enums) && lim_s_exec(v, enums),
        SType::List(e, max) => *max <= 0x7fff_ffff && lim_s_exec(e, enums),
        _ => true,
    }
}

fn lim_ss_exec(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == lim_ss(stys(ts@), enums@),
    decreases _parent, 0nat,
{
    proof {
        lemma_stys(ts@);
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            forall|j: int| 0 <= j < i ==> lim_s(#[trigger] stys(ts@)[j], enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !lim_s_exec(&ts[i], enums) {
            proof {
                if lim_ss(stys(ts@), enums@) {
                    lemma_lim_ss_at(stys(ts@), enums@, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_lim_ss_intro(stys(ts@), enums@);
    }
    true
}

/// 式の型の幅を上限で切った値。
pub fn cap_x(t: &XType, enums: &Vec<i64>) -> (r: u128)
    ensures
        r == capped(xwidth(xty(*t), enums@)),
    decreases t, 1nat,
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => 1,
        XType::Tuple(ts) | XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            cap_x_sum(t, ts, enums)
        },
        XType::Option(x) => {
            let w = cap_x(x, enums);
            proof {
                lemma_capped_add(1, xwidth(xty(**x), enums@));
            }
            if 1 + w > 0x7fff_ffff {
                0x8000_0000
            } else {
                1 + w
            }
        },
        XType::Set(e) => cap_s(&SType::Set(Box::new(crate::value::stype_exec::copy_stype(e))), enums),
        XType::Map(k, v) => cap_s(
            &SType::Map(Box::new(crate::value::stype_exec::copy_stype(k)), Box::new(crate::value::stype_exec::copy_stype(v))),
            enums,
        ),
        XType::List(e, max) => cap_s(&SType::List(Box::new(crate::value::stype_exec::copy_stype(e)), *max), enums),
    }
}

fn cap_x_sum(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: u128)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == capped(xwidth_sum(xtys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let mut acc: u128 = 0;
    let mut i = 0;
    proof {
        lemma_xtys(ts@);
        assert(xtys(ts@).take(0) =~= Seq::<XTy>::empty());
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            xtys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xtys(ts@)[j] == xty(ts@[j]),
            acc == capped(xwidth_sum(xtys(ts@).take(i as int), enums@)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            let xs = xtys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        let w = cap_x(&ts[i], enums);
        proof {
            lemma_capped_add(xwidth_sum(xtys(ts@).take(i as int), enums@), xwidth(xty(ts@[i as int]), enums@));
        }
        acc = if acc + w > 0x7fff_ffff {
            0x8000_0000
        } else {
            acc + w
        };
        i += 1;
    }
    proof {
        assert(xtys(ts@).take(ts@.len() as int) =~= xtys(ts@));
    }
    acc
}

/// 式の型が大きさの条件を満たすか。
pub fn lim_x_exec(t: &XType, enums: &Vec<i64>) -> (r: bool)
    ensures
        r == lim_x(xty(*t), enums@),
    decreases t, 1nat,
{
    if cap_x(t, enums) > 0x7fff_ffff {
        return false;
    }
    match t {
        XType::Tuple(ts) | XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            lim_xs_exec(t, ts, enums)
        },
        XType::Option(x) => lim_x_exec(x, enums),
        XType::Set(e) => lim_s_exec(e, enums),
        XType::Map(k, v) => lim_s_exec(k, enums) && lim_s_exec(v, enums),
        XType::List(e, max) => *max <= 0x7fff_ffff && lim_s_exec(e, enums),
        _ => true,
    }
}

fn lim_xs_exec(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == lim_xs(xtys(ts@), enums@),
    decreases _parent, 0nat,
{
    proof {
        lemma_xtys(ts@);
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            xtys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xtys(ts@)[j] == xty(ts@[j]),
            forall|j: int| 0 <= j < i ==> lim_x(#[trigger] xtys(ts@)[j], enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !lim_x_exec(&ts[i], enums) {
            proof {
                if lim_xs(xtys(ts@), enums@) {
                    lemma_lim_xs_at(xtys(ts@), enums@, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_lim_xs_intro(xtys(ts@), enums@);
    }
    true
}

// ---- 式の条件 ----

/// 量化でたどる値の型（[`quant_bound`] と一致する）。
fn quant_bound_exec(over: &Over, s: &Scope, lt: &mut Vec<XType>) -> (r: Option<XType>)
    ensures
        final(lt)@ == old(lt)@,
        agrees(r, quant_bound(*over, scope_view(s), xtys(old(lt)@))),
{
    match over {
        Over::Type(t) => if wf_stype_exec(t, &s.enums) && keys_exec(t, &s.enums).is_some() {
            Some(to_xtype(t))
        } else {
            None
        },
        Over::Set(t, a) => match check(a, s, lt) {
            Some(XType::Set(u)) => if stype_eq(&u, t) {
                Some(to_xtype(t))
            } else {
                None
            },
            _ => None,
        },
        Over::Map(t, a) => match check(a, s, lt) {
            Some(XType::Map(k, _)) => if stype_eq(&k, t) {
                Some(to_xtype(t))
            } else {
                None
            },
            _ => None,
        },
        Over::List(a) => match check(a, s, lt) {
            Some(XType::List(u, _)) => Some(to_xtype(&u)),
            _ => None,
        },
    }
}

/// 式とその部分式の型が、整形式で大きさの条件を満たすか（[`lim_ok`] と一致する）。
pub fn check_lim(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok(*e, scope_view(s), xtys(old(lt)@)),
    decreases e, 2nat,
{
    let here = match check(e, s, lt) {
        Some(x) => wf_xtype_exec(&x, &s.enums) && lim_x_exec(&x, &s.enums),
        None => true,
    };
    proof {
        assert(here == here_ok(*e, scope_view(s), xtys(lt@)));
    }
    if !here {
        return false;
    }
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_)
        | TExpr::Const(_) | TExpr::None(_) => true,
        TExpr::Let(_, _) | TExpr::Quant(_, _, _) => check_lim_bind(e, s, lt),
        TExpr::Fold(_, _) | TExpr::Tuple(_) | TExpr::Record(_, _) | TExpr::SetLit(_, _) | TExpr::ListLit(_, _, _)
        | TExpr::MapLit(_, _, _) => check_lim_coll(e, s, lt),
        _ => check_lim_kids(e, s, lt),
    }
}

/// 部分式が1〜3個の式。
fn check_lim_kids(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        !(e is Lit || e is Var || e is Next || e is Arg || e is Out || e is Local || e is Const || e is None || e is Let
            || e is Quant || e is Fold || e is Tuple || e is Record || e is SetLit || e is ListLit || e is MapLit),
        here_ok(*e, scope_view(s), xtys(old(lt)@)),
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok(*e, scope_view(s), xtys(old(lt)@)),
    decreases e, 1nat,
{
    match e {
        TExpr::Bin(_, a, b) | TExpr::Eq(_, a, b) | TExpr::Implies(a, b) | TExpr::SetBin(_, a, b) | TExpr::At(a, b)
        | TExpr::ListContains(a, b) | TExpr::SetContains(_, a, b) | TExpr::Insert(_, a, b) | TExpr::Remove(_, a, b)
        | TExpr::HasKey(_, a, b) | TExpr::Get(_, a, b) | TExpr::Delete(_, a, b) | TExpr::Push(_, _, a, b) => check_lim(
            a,
            s,
            lt,
        ) && check_lim(b, s, lt),
        TExpr::Not(a) | TExpr::Some(a) | TExpr::IsSome(a) | TExpr::IsNone(a) | TExpr::Unwrap(a) | TExpr::Size(a)
        | TExpr::IsEmpty(a) | TExpr::Keys(a) | TExpr::First(a) | TExpr::Last(a) | TExpr::Pop(a) | TExpr::Shift(a)
        | TExpr::Nth(a, _) | TExpr::Field(a, _, _) => check_lim(a, s, lt),
        TExpr::Ite(p, a, b) => check_lim(p, s, lt) && check_lim(a, s, lt) && check_lim(b, s, lt),
        TExpr::Put(_, _, a, x, y) => check_lim(a, s, lt) && check_lim(x, s, lt) && check_lim(y, s, lt),
        _ => false,
    }
}

/// 局所変数を束縛する式。
fn check_lim_bind(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        e is Let || e is Quant,
        here_ok(*e, scope_view(s), xtys(old(lt)@)),
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok(*e, scope_view(s), xtys(old(lt)@)),
    decreases e, 1nat,
{
    match e {
        TExpr::Let(a, b) => {
            if !check_lim(a, s, lt) {
                return false;
            }
            match check(a, s, lt) {
                Some(x) => {
                    let ghost before = lt@;
                    lt.push(x);
                    proof {
                        assert(lt@.drop_last() == before);
                    }
                    let r = check_lim(b, s, lt);
                    lt.pop();
                    proof {
                        assert(lt@ =~= before);
                    }
                    r
                },
                None => true,
            }
        },
        TExpr::Quant(_, over, body) => {
            let first = match over {
                Over::Type(t) => lim_s_exec(t, &s.enums),
                Over::Set(_, a) => check_lim(a, s, lt),
                Over::Map(_, a) => check_lim(a, s, lt),
                Over::List(a) => check_lim(a, s, lt),
            };
            if !first {
                return false;
            }
            match quant_bound_exec(over, s, lt) {
                Some(x) => {
                    let ghost before = lt@;
                    lt.push(x);
                    proof {
                        assert(lt@.drop_last() == before);
                    }
                    let r = check_lim(body, s, lt);
                    lt.pop();
                    proof {
                        assert(lt@ =~= before);
                    }
                    r
                },
                None => true,
            }
        },
        _ => false,
    }
}

/// 部分式の列を持つ式。
fn check_lim_coll(e: &TExpr, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        e is Fold || e is Tuple || e is Record || e is SetLit || e is ListLit || e is MapLit,
        here_ok(*e, scope_view(s), xtys(old(lt)@)),
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok(*e, scope_view(s), xtys(old(lt)@)),
    decreases e, 1nat,
{
    match e {
        TExpr::Fold(_, es) | TExpr::Tuple(es) | TExpr::Record(_, es) | TExpr::SetLit(_, es) | TExpr::ListLit(_, _, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            check_lim_seq(e, es, s, lt)
        },
        TExpr::MapLit(_, _, items) => {
            proof {
                assert(decreases_to!(*e => *items));
            }
            check_lim_items(e, items, s, lt)
        },
        _ => false,
    }
}

fn check_lim_seq(_parent: &TExpr, es: &Vec<TExpr>, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *es),
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok_seq(es@, scope_view(s), xtys(old(lt)@)),
    decreases _parent, 0nat,
{
    let ghost l = xtys(lt@);
    let ghost l0 = lt@;
    let mut i = 0;
    while i < es.len()
        invariant
            decreases_to!(*_parent => *es),
            lt@ == l0,
            l0 == old(lt)@,
            l == xtys(l0),
            i <= es.len(),
            forall|j: int| 0 <= j < i ==> lim_ok(#[trigger] es@[j], scope_view(s), l),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
        }
        if !check_lim(&es[i], s, lt) {
            proof {
                if lim_ok_seq(es@, scope_view(s), l) {
                    lemma_lim_ok_seq_at(es@, scope_view(s), l, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_lim_ok_seq_intro(es@, scope_view(s), l);
    }
    true
}

fn check_lim_items(_parent: &TExpr, items: &Vec<Item>, s: &Scope, lt: &mut Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *items),
    ensures
        final(lt)@ == old(lt)@,
        r == lim_ok_items(items@, scope_view(s), xtys(old(lt)@)),
    decreases _parent, 0nat,
{
    let ghost l = xtys(lt@);
    let ghost l0 = lt@;
    let mut i = 0;
    while i < items.len()
        invariant
            decreases_to!(*_parent => *items),
            lt@ == l0,
            l0 == old(lt)@,
            l == xtys(l0),
            i <= items.len(),
            forall|j: int| 0 <= j < i ==> lim_ok((#[trigger] items@[j]).key, scope_view(s), l) && lim_ok(
                items@[j].value,
                scope_view(s),
                l,
            ),
        decreases items.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*items, i as int);
        }
        let item = &items[i];
        proof {
            assert(decreases_to!(*_parent => item.key));
            assert(decreases_to!(*_parent => item.value));
        }
        if !(check_lim(&item.key, s, lt) && check_lim(&item.value, s, lt)) {
            proof {
                if lim_ok_items(items@, scope_view(s), l) {
                    lemma_lim_ok_items_at(items@, scope_view(s), l, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_lim_ok_items_intro(items@, scope_view(s), l);
    }
    true
}

/// 型の中のどのListも、長さの上限が `0x7fff_ffff` 以下かを判定する。
pub fn small_stype(t: &SType) -> (r: bool)
    ensures
        r == small(sty(*t)),
    decreases t,
{
    match t {
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            small_stypes(t, ts)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            small_stypes(t, ts)
        },
        SType::Option(x) => small_stype(x),
        SType::Map(_, v) => small_stype(v),
        SType::List(e, max) => *max <= 0x7fff_ffffusize && small_stype(e),
        _ => true,
    }
}

pub(crate) fn small_stypes(_parent: &SType, ts: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == smalls(stys(ts@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_stys(ts@);
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            forall|j: int| 0 <= j < i ==> small(sty(#[trigger] ts@[j])),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !small_stype(&ts[i]) {
            proof {
                lemma_stys(ts@);
                if smalls(stys(ts@)) {
                    lemma_smalls_at(stys(ts@), i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys(ts@);
        let ss = stys(ts@);
        assert forall|j: int| 0 <= j < ss.len() implies small(#[trigger] ss[j]) by {
            assert(ss[j] == sty(ts@[j]));
        }
        lemma_smalls(ss);
    }
    true
}

} // verus!
