//! 型（`SType`、`XType`）の上の実行関数。複製、比較、値の数、整形式性、幅。対応する仕様は `encoding` にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{keys, keys_or_zero, keys_product, lemma_stys, lemma_stys_ext, lemma_to_xtys};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_wf_stypes, lemma_wf_stypes_at, lemma_xtys, lemma_xtys_ext, sty, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{stys, to_xty, to_xtys, wf_stype, wf_stypes, wf_xtype, wf_xtypes, width};
#[cfg(verus_keep_ghost)]
use crate::encoding::{width_sum, xty, xtys, xwidth, xwidth_sum, XTy};
use crate::encoding::{SType, XType, MAX_KEYS};
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_ss_at, lemma_lim_xs_at, lemma_width_sum_prefix};
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_xwidth_sum_prefix, lim, lim_s, lim_ss, lim_x, lim_xs};
use vstd::prelude::*;

verus! {

pub fn copy_stype(t: &SType) -> (r: SType)
    ensures
        sty(r) == sty(*t),
    decreases t,
{
    match t {
        SType::Bool => SType::Bool,
        SType::Int(lo, hi) => SType::Int(*lo, *hi),
        SType::Enum(id) => SType::Enum(*id),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            SType::Tuple(copy_stypes(t, ts))
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            SType::Record(names.clone(), copy_stypes(t, ts))
        },
        SType::Option(x) => SType::Option(Box::new(copy_stype(x))),
        SType::Set(e) => SType::Set(Box::new(copy_stype(e))),
        SType::Map(k, v) => SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        SType::List(e, max) => SType::List(Box::new(copy_stype(e)), *max),
    }
}

pub(crate) fn copy_stypes(_parent: &SType, ts: &Vec<SType>) -> (r: Vec<SType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        stys(r@) == stys(ts@),
    decreases _parent, 0nat,
{
    let mut out: Vec<SType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> sty(#[trigger] out@[j]) == sty(ts@[j]),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(copy_stype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_stys_ext(out@, ts@);
    }
    out
}

/// 格納の型の式の型。
pub fn to_xtype(t: &SType) -> (r: XType)
    ensures
        xty(r) == to_xty(sty(*t)),
    decreases t,
{
    match t {
        SType::Bool => XType::Bool,
        SType::Int(_, _) => XType::Int,
        SType::Enum(id) => XType::Enum(*id),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Tuple(to_xtypes(t, ts))
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Record(names.clone(), to_xtypes(t, ts))
        },
        SType::Option(x) => XType::Option(Box::new(to_xtype(x))),
        SType::Set(e) => XType::Set(Box::new(copy_stype(e))),
        SType::Map(k, v) => XType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        SType::List(e, max) => XType::List(Box::new(copy_stype(e)), *max),
    }
}

pub(crate) fn to_xtypes(_parent: &SType, ts: &Vec<SType>) -> (r: Vec<XType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        xtys(r@) == to_xtys(stys(ts@)),
    decreases _parent, 0nat,
{
    let mut out: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> xty(#[trigger] out@[j]) == to_xty(sty(ts@[j])),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(to_xtype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_xtys(out@);
        lemma_stys(ts@);
        lemma_to_xtys(stys(ts@));
        assert(xtys(out@) =~= to_xtys(stys(ts@)));
    }
    out
}

pub fn copy_xtype(t: &XType) -> (r: XType)
    ensures
        xty(r) == xty(*t),
    decreases t,
{
    match t {
        XType::Bool => XType::Bool,
        XType::Int => XType::Int,
        XType::Enum(id) => XType::Enum(*id),
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Tuple(copy_xtypes(t, ts))
        },
        XType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            XType::Record(names.clone(), copy_xtypes(t, ts))
        },
        XType::Option(x) => XType::Option(Box::new(copy_xtype(x))),
        XType::Set(e) => XType::Set(Box::new(copy_stype(e))),
        XType::Map(k, v) => XType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v))),
        XType::List(e, max) => XType::List(Box::new(copy_stype(e)), *max),
    }
}

pub(crate) fn copy_xtypes(_parent: &XType, ts: &Vec<XType>) -> (r: Vec<XType>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        xtys(r@) == xtys(ts@),
    decreases _parent, 0nat,
{
    let mut out: Vec<XType> = Vec::new();
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> xty(#[trigger] out@[j]) == xty(ts@[j]),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        out.push(copy_xtype(&ts[i]));
        i += 1;
    }
    proof {
        lemma_xtys_ext(out@, ts@);
    }
    out
}

pub fn usizes_eq(a: &Vec<usize>, b: &Vec<usize>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// 2つの格納の型が等しいかを判定する。真なら仕様の型が等しい。
pub fn stype_eq(a: &SType, b: &SType) -> (r: bool)
    ensures
        r == (sty(*a) == sty(*b)),
    decreases a,
{
    match (a, b) {
        (SType::Bool, SType::Bool) => true,
        (SType::Int(l1, h1), SType::Int(l2, h2)) => *l1 == *l2 && *h1 == *h2,
        (SType::Enum(x), SType::Enum(y)) => *x == *y,
        (SType::Tuple(xs), SType::Tuple(ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            stypes_eq(a, xs, ys)
        },
        (SType::Record(m, xs), SType::Record(n, ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            usizes_eq(m, n) && stypes_eq(a, xs, ys)
        },
        (SType::Option(x), SType::Option(y)) => stype_eq(x, y),
        (SType::Set(x), SType::Set(y)) => stype_eq(x, y),
        (SType::Map(k1, v1), SType::Map(k2, v2)) => stype_eq(k1, k2) && stype_eq(v1, v2),
        (SType::List(x, m), SType::List(y, n)) => *m == *n && stype_eq(x, y),
        _ => false,
    }
}

pub(crate) fn stypes_eq(_parent: &SType, xs: &Vec<SType>, ys: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r == (stys(xs@) == stys(ys@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_stys(xs@);
        lemma_stys(ys@);
    }
    if xs.len() != ys.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ys.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> sty(#[trigger] xs@[j]) == sty(ys@[j]),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !stype_eq(&xs[i], &ys[i]) {
            proof {
                lemma_stys(xs@);
                lemma_stys(ys@);
                assert(stys(xs@)[i as int] != stys(ys@)[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys_ext(xs@, ys@);
    }
    true
}

/// 2つの式の型が等しいかを判定する。真なら仕様の型が等しい。
pub fn xtype_eq(a: &XType, b: &XType) -> (r: bool)
    ensures
        r == (xty(*a) == xty(*b)),
    decreases a,
{
    match (a, b) {
        (XType::Bool, XType::Bool) => true,
        (XType::Int, XType::Int) => true,
        (XType::Enum(x), XType::Enum(y)) => *x == *y,
        (XType::Tuple(xs), XType::Tuple(ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            xtypes_eq(a, xs, ys)
        },
        (XType::Record(m, xs), XType::Record(n, ys)) => {
            proof {
                assert(decreases_to!(*a => *xs));
            }
            usizes_eq(m, n) && xtypes_eq(a, xs, ys)
        },
        (XType::Option(x), XType::Option(y)) => xtype_eq(x, y),
        (XType::Set(x), XType::Set(y)) => stype_eq(x, y),
        (XType::Map(k1, v1), XType::Map(k2, v2)) => stype_eq(k1, k2) && stype_eq(v1, v2),
        (XType::List(x, m), XType::List(y, n)) => *m == *n && stype_eq(x, y),
        _ => false,
    }
}

pub(crate) fn xtypes_eq(_parent: &XType, xs: &Vec<XType>, ys: &Vec<XType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r == (xtys(xs@) == xtys(ys@)),
    decreases _parent, 0nat,
{
    proof {
        lemma_xtys(xs@);
        lemma_xtys(ys@);
    }
    if xs.len() != ys.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ys.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> xty(#[trigger] xs@[j]) == xty(ys@[j]),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !xtype_eq(&xs[i], &ys[i]) {
            proof {
                lemma_xtys(xs@);
                lemma_xtys(ys@);
                assert(xtys(xs@)[i as int] != xtys(ys@)[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_xtys_ext(xs@, ys@);
    }
    true
}

/// キーの型の値の数。
pub fn keys_exec(t: &SType, enums: &Vec<i64>) -> (r: Option<u64>)
    ensures
        match r {
            Some(k) => keys(sty(*t), enums@) == Some(k as nat),
            None => keys(sty(*t), enums@) is None,
        },
    decreases t,
{
    let n: Option<u64> = match t {
        SType::Bool => Some(2),
        SType::Int(lo, hi) => {
            let d = (*hi as i128) - (*lo as i128) + 1;
            if *lo <= *hi && d <= MAX_KEYS as i128 {
                Some(d as u64)
            } else {
                None
            }
        },
        SType::Enum(id) => if *id < enums.len() && enums[*id] >= 0 {
            Some(enums[*id] as u64)
        } else {
            None
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            keys_product_exec(t, ts, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            keys_product_exec(t, ts, enums)
        },
        SType::Option(x) => match keys_exec(x, enums) {
            Some(k) => Some(k + 1),
            None => None,
        },
        _ => None,
    };
    match n {
        Some(k) => if k <= MAX_KEYS {
            Some(k)
        } else {
            None
        },
        None => None,
    }
}

pub(crate) fn keys_product_exec(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Option<u64>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        match r {
            Some(k) => keys_product(stys(ts@), enums@) == Some(k as nat) && k <= MAX_KEYS,
            None => keys_product(stys(ts@), enums@) is None,
        },
    decreases _parent, 0nat,
{
    let ghost ss = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(ss.take(0) =~= Seq::<STy>::empty());
    }
    let mut acc: Option<u64> = Some(1);
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            ss == stys(ts@),
            ss.len() == ts.len(),
            forall|j: int| 0 <= j < ts.len() ==> #[trigger] ss[j] == sty(ts@[j]),
            i <= ts.len(),
            match acc {
                Some(p) => keys_product(ss.take(i as int), enums@) == Some(p as nat) && p <= MAX_KEYS,
                None => keys_product(ss.take(i as int), enums@) is None,
            },
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            assert(ss.take(i + 1).drop_last() =~= ss.take(i as int));
            assert(ss.take(i + 1).last() == ss[i as int]);
        }
        acc = match acc {
            Some(p) => match keys_exec(&ts[i], enums) {
                Some(k) => {
                    proof {
                        assert(k <= MAX_KEYS);
                        assert(p * k <= MAX_KEYS * MAX_KEYS) by (nonlinear_arith)
                            requires
                                p <= MAX_KEYS,
                                k <= MAX_KEYS,
                        ;
                    }
                    if p * k <= MAX_KEYS {
                        Some(p * k)
                    } else {
                        None
                    }
                },
                None => None,
            },
            None => None,
        };
        i += 1;
    }
    proof {
        assert(ss.take(ts.len() as int) =~= ss);
    }
    acc
}

/// 名前の番号に重複がないかを判定する。真なら重複がない。
pub fn distinct_names(names: &Vec<usize>) -> (r: bool)
    ensures
        r == names@.no_duplicates(),
{
    let mut i = 0;
    while i < names.len()
        invariant
            i <= names.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> names@[a] != names@[b],
        decreases names.len() - i,
    {
        let mut j = 0;
        while j < i
            invariant
                i < names.len(),
                j <= i,
                forall|a: int, b: int| 0 <= a < b < i ==> names@[a] != names@[b],
                forall|a: int| 0 <= a < j ==> names@[a] != names@[i as int],
            decreases i - j,
        {
            if names[j] == names[i] {
                proof {
                    assert(!names@.no_duplicates()) by {
                        assert(names@[j as int] == names@[i as int] && j != i);
                    }
                }
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

/// 格納の型が整形式かを判定する。真なら整形式である。
pub fn wf_stype_exec(t: &SType, enums: &Vec<i64>) -> (r: bool)
    ensures
        r == wf_stype(sty(*t), enums@),
    decreases t,
{
    match t {
        SType::Bool => true,
        SType::Int(lo, hi) => *lo <= *hi,
        SType::Enum(id) => *id < enums.len() && enums[*id] >= 1,
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_stys(ts@);
            }
            ts.len() >= 1 && wf_stypes_exec(t, ts, enums)
        },
        SType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_stys(ts@);
            }
            ts.len() >= 1 && names.len() == ts.len() && distinct_names(names) && wf_stypes_exec(t, ts, enums)
        },
        SType::Option(x) => wf_stype_exec(x, enums),
        SType::Set(e) => wf_stype_exec(e, enums) && keys_exec(e, enums).is_some(),
        SType::Map(k, v) => wf_stype_exec(k, enums) && keys_exec(k, enums).is_some() && wf_stype_exec(v, enums),
        SType::List(e, _) => wf_stype_exec(e, enums),
    }
}

pub(crate) fn wf_stypes_exec(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == wf_stypes(stys(ts@), enums@),
        stys(ts@).len() == ts.len(),
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
            forall|j: int| 0 <= j < i ==> wf_stype(sty(#[trigger] ts@[j]), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !wf_stype_exec(&ts[i], enums) {
            proof {
                lemma_stys(ts@);
                if wf_stypes(stys(ts@), enums@) {
                    lemma_wf_stypes_at(stys(ts@), enums@, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_stys(ts@);
        let ss = stys(ts@);
        assert forall|j: int| 0 <= j < ss.len() implies wf_stype(#[trigger] ss[j], enums@) by {
            assert(ss[j] == sty(ts@[j]));
        }
        lemma_wf_stypes(ss, enums@);
    }
    true
}

/// 式の型が整形式か。
pub fn wf_xtype_exec(t: &XType, enums: &Vec<i64>) -> (r: bool)
    ensures
        r == wf_xtype(xty(*t), enums@),
    decreases t, 1nat,
{
    match t {
        XType::Bool | XType::Int => true,
        XType::Enum(id) => *id < enums.len() && enums[*id] >= 1,
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_xtys(ts@);
            }
            ts.len() >= 1 && wf_xtypes_exec(t, ts, enums)
        },
        XType::Record(names, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
                lemma_xtys(ts@);
            }
            ts.len() >= 1 && names.len() == ts.len() && distinct_names(names) && wf_xtypes_exec(t, ts, enums)
        },
        XType::Option(x) => wf_xtype_exec(x, enums),
        XType::Set(e) => wf_stype_exec(e, enums) && keys_exec(e, enums).is_some(),
        XType::Map(k, v) => wf_stype_exec(k, enums) && keys_exec(k, enums).is_some() && wf_stype_exec(v, enums),
        XType::List(e, _) => wf_stype_exec(e, enums),
    }
}

pub(crate) fn wf_xtypes_exec(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: bool)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r == wf_xtypes(xtys(ts@), enums@),
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
            forall|j: int| 0 <= j < i ==> wf_xtype(#[trigger] xtys(ts@)[j], enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        if !wf_xtype_exec(&ts[i], enums) {
            proof {
                if wf_xtypes(xtys(ts@), enums@) {
                    lemma_wf_xtypes_at(xtys(ts@), enums@, i as int);
                }
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_wf_xtypes_intro(xtys(ts@), enums@);
    }
    true
}

pub fn keys_or_zero_exec(t: &SType, enums: &Vec<i64>) -> (r: usize)
    ensures
        r == keys_or_zero(sty(*t), enums@),
        r <= MAX_KEYS,
{
    match keys_exec(t, enums) {
        Some(k) => k as usize,
        None => 0,
    }
}

/// 格納の型のスロット数。`usize` に収まらなければ `None`。
pub fn stype_width(t: &SType, enums: &Vec<i64>) -> (r: Option<usize>)
    ensures
        r matches Some(w) ==> w == width(sty(*t), enums@),
        lim_s(sty(*t), enums@) ==> r is Some,
    decreases t, 1nat,
{
    match t {
        SType::Bool | SType::Int(_, _) | SType::Enum(_) => Some(1),
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            stype_width_sum(t, ts, enums)
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            stype_width_sum(t, ts, enums)
        },
        SType::Option(x) => {
            let w = stype_width(x, enums)?;
            w.checked_add(1)
        },
        SType::Set(e) => Some(keys_or_zero_exec(e, enums)),
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let w = stype_width(v, enums)?;
            proof {
                assert(usize::MAX >= 0xffff_ffff);
                if lim_s(sty(*t), enums@) {
                    assert(lim_s(sty(**v), enums@));
                    assert(width(sty(**v), enums@) <= lim());
                }
            }
            let w1 = w.checked_add(1)?;
            proof {
                if lim_s(sty(*t), enums@) {
                    assert(n as nat * w1 as nat == width(sty(*t), enums@));
                }
            }
            n.checked_mul(w1)
        },
        SType::List(e, n) => {
            let w = stype_width(e, enums)?;
            proof {
                assert(usize::MAX >= 0xffff_ffff);
                if lim_s(sty(*t), enums@) {
                    assert(*n as nat * w as nat + 1 == width(sty(*t), enums@));
                }
            }
            n.checked_mul(w)?.checked_add(1)
        },
    }
}

pub(crate) fn stype_width_sum(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r matches Some(w) ==> w == width_sum(stys(ts@), enums@),
        lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim() ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim();
    let mut acc: usize = 0;
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
            acc == width_sum(stys(ts@).take(i as int), enums@),
            pre == (lim_ss(stys(ts@), enums@) && width_sum(stys(ts@), enums@) <= lim()),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
            if pre {
                lemma_lim_ss_at(xs, enums@, i as int);
                lemma_width_sum_prefix(xs, enums@, i + 1);
            }
        }
        let w = stype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
    Some(acc)
}

/// 式の型のスロット数。
pub fn xtype_width(t: &XType, enums: &Vec<i64>) -> (r: Option<usize>)
    ensures
        r matches Some(w) ==> w == xwidth(xty(*t), enums@),
        lim_x(xty(*t), enums@) ==> r is Some,
    decreases t, 1nat,
{
    match t {
        XType::Bool | XType::Int | XType::Enum(_) => Some(1),
        XType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            xtype_width_sum(t, ts, enums)
        },
        XType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            xtype_width_sum(t, ts, enums)
        },
        XType::Option(x) => {
            let w = xtype_width(x, enums)?;
            w.checked_add(1)
        },
        XType::Set(e) => Some(keys_or_zero_exec(e, enums)),
        XType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let w = stype_width(v, enums)?;
            n.checked_mul(w.checked_add(1)?)
        },
        XType::List(e, n) => {
            let w = stype_width(e, enums)?;
            n.checked_mul(w)?.checked_add(1)
        },
    }
}

pub(crate) fn xtype_width_sum(_parent: &XType, ts: &Vec<XType>, enums: &Vec<i64>) -> (r: Option<usize>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r matches Some(w) ==> w == xwidth_sum(xtys(ts@), enums@),
        lim_xs(xtys(ts@), enums@) && xwidth_sum(xtys(ts@), enums@) <= lim() ==> r is Some,
    decreases _parent, 0nat,
{
    let ghost pre = lim_xs(xtys(ts@), enums@) && xwidth_sum(xtys(ts@), enums@) <= lim();
    let mut acc: usize = 0;
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
            acc == xwidth_sum(xtys(ts@).take(i as int), enums@),
            pre == (lim_xs(xtys(ts@), enums@) && xwidth_sum(xtys(ts@), enums@) <= lim()),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
            let xs = xtys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
            if pre {
                lemma_lim_xs_at(xs, enums@, i as int);
                lemma_xwidth_sum_prefix(xs, enums@, i + 1);
            }
        }
        let w = xtype_width(&ts[i], enums)?;
        acc = acc.checked_add(w)?;
        proof {
            let xs = xtys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
        }
        i += 1;
    }
    proof {
        assert(xtys(ts@).take(ts@.len() as int) =~= xtys(ts@));
    }
    Some(acc)
}

pub proof fn lemma_wf_xtypes_at(ts: Seq<XTy>, enums: Seq<i64>, i: int)
    requires
        wf_xtypes(ts, enums),
        0 <= i < ts.len(),
    ensures
        wf_xtype(ts[i], enums),
    decreases ts.len(),
{
    if i < ts.len() - 1 {
        assert(ts.drop_last()[i] == ts[i]);
        lemma_wf_xtypes_at(ts.drop_last(), enums, i);
    }
}

pub proof fn lemma_wf_xtypes_intro(ts: Seq<XTy>, enums: Seq<i64>)
    requires
        forall|i: int| 0 <= i < ts.len() ==> wf_xtype(#[trigger] ts[i], enums),
    ensures
        wf_xtypes(ts, enums),
    decreases ts.len(),
{
    if ts.len() > 0 {
        assert forall|i: int| 0 <= i < ts.len() - 1 implies wf_xtype(#[trigger] ts.drop_last()[i], enums) by {
            assert(ts.drop_last()[i] == ts[i]);
        }
        lemma_wf_xtypes_intro(ts.drop_last(), enums);
    }
}

} // verus!
