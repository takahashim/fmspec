//! スロットの型。格納の型の値の符号化がスロットごとに持つ中核の型（`slot_tys`）の仕様と補題、その実行関数（`slot_types`）。

use crate::kernel::model::Type;
#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
use crate::value::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{keys_or_zero, lemma_stys, sty, stys, width, width_sum, STy};
use crate::value::stype_exec::keys_or_zero_exec;
use vstd::prelude::*;

verus! {

pub proof fn lemma_ty_repeat_add(xs: Seq<Type>, a: nat, b: nat)
    ensures
        ty_repeat(xs, a + b) == ty_repeat(xs, a) + ty_repeat(xs, b),
    decreases b,
{
    if b == 0 {
        assert(ty_repeat(xs, a) + ty_repeat(xs, 0) =~= ty_repeat(xs, a));
    } else {
        let c = (b - 1) as nat;
        lemma_ty_repeat_add(xs, a, c);
        assert(ty_repeat(xs, a + b) == ty_repeat(xs, a + c) + xs);
        assert(ty_repeat(xs, a) + ty_repeat(xs, c) + xs =~= ty_repeat(xs, a) + (ty_repeat(xs, c) + xs));
    }
}

pub proof fn lemma_bools(n: nat)
    ensures
        ty_repeat(seq![Type::Bool], n) == Seq::new(n, |_i: int| Type::Bool),
    decreases n,
{
    if n > 0 {
        lemma_bools((n - 1) as nat);
        assert(ty_repeat(seq![Type::Bool], n) =~= Seq::new(n, |_i: int| Type::Bool));
    } else {
        assert(ty_repeat(seq![Type::Bool], n) =~= Seq::new(n, |_i: int| Type::Bool));
    }
}

/// つなげた列の各値がスロットの型の値であることは、それぞれの列についてそうであることである。
pub proof fn lemma_in_slots_concat(a: Seq<Value>, ta: Seq<Type>, b: Seq<Value>, tb: Seq<Type>, enums: Seq<i64>)
    requires
        a.len() == ta.len(),
    ensures
        in_slots(a + b, ta + tb, enums) <==> (in_slots(a, ta, enums) && in_slots(b, tb, enums)),
{
    if in_slots(a, ta, enums) && in_slots(b, tb, enums) {
        assert forall|j: int| 0 <= j < (a + b).len() implies #[trigger] in_slot((ta + tb)[j], (a + b)[j], enums) by {
            if j < a.len() {
                assert(in_slot(ta[j], a[j], enums));
            } else {
                assert(in_slot(tb[j - a.len()], b[j - a.len()], enums));
            }
        }
    }
    if in_slots(a + b, ta + tb, enums) {
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] in_slot(ta[j], a[j], enums) by {
            assert(in_slot((ta + tb)[j], (a + b)[j], enums));
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] in_slot(tb[j], b[j], enums) by {
            assert(in_slot((ta + tb)[j + a.len()], (a + b)[j + a.len()], enums));
        }
    }
}

pub proof fn lemma_in_slots_sub(xs: Seq<Value>, tys: Seq<Type>, lo: int, hi: int, enums: Seq<i64>)
    requires
        in_slots(xs, tys, enums),
        0 <= lo <= hi <= xs.len(),
    ensures
        in_slots(xs.subrange(lo, hi), tys.subrange(lo, hi), enums),
{
    assert forall|j: int| 0 <= j < hi - lo implies #[trigger] in_slot(
        tys.subrange(lo, hi)[j],
        xs.subrange(lo, hi)[j],
        enums,
    ) by {
        assert(in_slot(tys[lo + j], xs[lo + j], enums));
    }
}

/// 同じスロットの型の値は、同じ種類である。
pub proof fn lemma_in_slot_kind(ty: Type, x: Value, y: Value, enums: Seq<i64>)
    requires
        in_slot(ty, x, enums),
        in_slot(ty, y, enums),
    ensures
        crate::kernel::eval::same_kind(x, y),
{
}

/// `xs` を `n` 回、`out` の後ろに加える。
pub(crate) fn push_repeat(xs: &Vec<Type>, n: usize, out: &mut Vec<Type>)
    ensures
        final(out)@ == old(out)@ + ty_repeat(xs@, n as nat),
{
    let ghost prefix = out@;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            out@ == prefix + ty_repeat(xs@, k as nat),
        decreases n - k,
    {
        let ghost before = out@;
        let mut j: usize = 0;
        while j < xs.len()
            invariant
                j <= xs@.len(),
                out@ == before + xs@.take(j as int),
            decreases xs@.len() - j,
        {
            out.push(xs[j]);
            j += 1;
            proof {
                assert(out@ =~= before + xs@.take(j as int));
            }
        }
        proof {
            assert(xs@.take(j as int) =~= xs@);
            assert(ty_repeat(xs@, (k + 1) as nat) == ty_repeat(xs@, k as nat) + xs@);
            assert(out@ =~= prefix + ty_repeat(xs@, (k + 1) as nat));
        }
        k += 1;
    }
}

/// 型 `t` の各スロットの中核の型を、`out` の後ろに加える。
pub fn slot_types(t: &SType, enums: &Vec<i64>, out: &mut Vec<Type>)
    ensures
        final(out)@ == old(out)@ + slot_tys(sty(*t), enums@),
    decreases t, 1nat,
{
    let ghost prefix = out@;
    match t {
        SType::Bool => {
            out.push(Type::Bool);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Int(lo, hi) => {
            out.push(Type::Int(*lo, *hi));
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Enum(id) => {
            out.push(Type::Enum(*id));
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_seq(t, ts, enums, out);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            slot_types_seq(t, ts, enums, out);
        },
        SType::Option(x) => {
            out.push(Type::Bool);
            slot_types(x, enums, out);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut row: Vec<Type> = Vec::new();
            row.push(Type::Bool);
            proof {
                assert(row@ =~= seq![Type::Bool]);
            }
            push_repeat(&row, n, out);
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let mut row: Vec<Type> = Vec::new();
            row.push(Type::Bool);
            slot_types(v, enums, &mut row);
            proof {
                assert(row@ =~= seq![Type::Bool] + slot_tys(sty(**v), enums@));
            }
            push_repeat(&row, n, out);
        },
        SType::List(e, max) => {
            out.push(Type::Int(0, *max as i64));
            let mut row: Vec<Type> = Vec::new();
            slot_types(e, enums, &mut row);
            proof {
                assert(row@ =~= slot_tys(sty(**e), enums@));
            }
            push_repeat(&row, *max, out);
            proof {
                assert(out@ =~= prefix + slot_tys(sty(*t), enums@));
            }
        },
    }
}

pub(crate) fn slot_types_seq(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>, out: &mut Vec<Type>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        final(out)@ == old(out)@ + slot_tys_seq(stys(ts@), enums@),
    decreases _parent, 0nat,
{
    let ghost prefix = out@;
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= prefix + slot_tys_seq(stys(ts@).take(0), enums@));
    }
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            out@ == prefix + slot_tys_seq(stys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        slot_types(&ts[i], enums, out);
        proof {
            let xs = stys(ts@);
            assert(xs.take(i + 1).drop_last() =~= xs.take(i as int));
            assert(xs.take(i + 1).last() == xs[i as int]);
            assert(out@ =~= prefix + slot_tys_seq(xs.take(i + 1), enums@));
        }
        i += 1;
    }
    proof {
        assert(stys(ts@).take(ts@.len() as int) =~= stys(ts@));
    }
}

/// 型の列の各型のスロットの型を、順につなげた列。
pub fn slot_types_list(ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Vec<Type>)
    ensures
        r@ == slot_tys_seq(stys(ts@), enums@),
{
    let mut out: Vec<Type> = Vec::new();
    let mut i = 0;
    proof {
        lemma_stys(ts@);
        assert(stys(ts@).take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= slot_tys_seq(stys(ts@).take(0), enums@));
    }
    while i < ts.len()
        invariant
            i <= ts.len(),
            stys(ts@).len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] stys(ts@)[j] == sty(ts@[j]),
            out@ == slot_tys_seq(stys(ts@).take(i as int), enums@),
        decreases ts.len() - i,
    {
        slot_types(&ts[i], enums, &mut out);
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
    out
}

/// 型の列 `xs` を `n` 回つなげた列。
pub open spec fn ty_repeat(xs: Seq<Type>, n: nat) -> Seq<Type>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        ty_repeat(xs, (n - 1) as nat) + xs
    }
}

/// 格納の型 `t` の各スロットの中核の型。
/// Listの長さのスロットは `0..=max` の整数で、Setの要素とMapのキーの有無はBoolである。
pub open spec fn slot_tys(t: STy, enums: Seq<i64>) -> Seq<Type>
    decreases t,
{
    match t {
        STy::Bool => seq![Type::Bool],
        STy::Int(lo, hi) => seq![Type::Int(lo, hi)],
        STy::Enum(id) => seq![Type::Enum(id)],
        STy::Tuple(ts) => slot_tys_seq(ts, enums),
        STy::Record(_, ts) => slot_tys_seq(ts, enums),
        STy::Option(x) => seq![Type::Bool] + slot_tys(*x, enums),
        STy::Set(e) => ty_repeat(seq![Type::Bool], keys_or_zero(*e, enums)),
        STy::Map(k, v) => ty_repeat(seq![Type::Bool] + slot_tys(*v, enums), keys_or_zero(*k, enums)),
        STy::List(e, max) => seq![Type::Int(0, max as i64)] + ty_repeat(slot_tys(*e, enums), max as nat),
    }
}

/// 型の列の各型のスロットの型を、順につなげた列。
pub open spec fn slot_tys_seq(ts: Seq<STy>, enums: Seq<i64>) -> Seq<Type>
    decreases ts,
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        slot_tys_seq(ts.drop_last(), enums) + slot_tys(ts.last(), enums)
    }
}

/// 値 `x` は、スロットの型 `ty` の値である。
pub open spec fn in_slot(ty: Type, x: Value, enums: Seq<i64>) -> bool {
    match (ty, x) {
        (Type::Bool, Value::Bool(_)) => true,
        (Type::Int(lo, hi), Value::Int(k)) => lo <= k <= hi,
        (Type::Enum(id), Value::Enum(j, k)) => j == id && id < enums.len() && 0 <= k < enums[id as int],
        _ => false,
    }
}

/// 値の列 `xs` の各値は、対応するスロットの型の値である。
pub open spec fn in_slots(xs: Seq<Value>, tys: Seq<Type>, enums: Seq<i64>) -> bool {
    &&& xs.len() == tys.len()
    &&& forall|j: int| 0 <= j < xs.len() ==> #[trigger] in_slot(tys[j], xs[j], enums)
}

pub proof fn lemma_ty_repeat_len(xs: Seq<Type>, n: nat)
    ensures
        ty_repeat(xs, n).len() == n * xs.len(),
    decreases n,
{
    if n == 0 {
        assert(0 * xs.len() == 0) by (nonlinear_arith);
    } else {
        let m = (n - 1) as nat;
        lemma_ty_repeat_len(xs, m);
        assert(m * xs.len() + xs.len() == n * xs.len()) by (nonlinear_arith)
            requires
                m + 1 == n,
        ;
    }
}

/// `n` 回つなげた列の `p` 番目の部分は、もとの列である。
pub proof fn lemma_ty_repeat_sub(xs: Seq<Type>, n: nat, p: int)
    requires
        0 <= p < n,
    ensures
        0 <= p * xs.len(),
        p * xs.len() + xs.len() <= n * xs.len(),
        ty_repeat(xs, n).len() == n * xs.len(),
        ty_repeat(xs, n).subrange(p * xs.len(), p * xs.len() + xs.len()) == xs,
    decreases n,
{
    let w = xs.len();
    let m = (n - 1) as nat;
    lemma_ty_repeat_len(xs, n);
    lemma_ty_repeat_len(xs, m);
    assert(0 <= p * w) by (nonlinear_arith)
        requires
            0 <= p,
    ;
    assert(p * w + w <= n * w) by (nonlinear_arith)
        requires
            0 <= p < n,
    ;
    let s = ty_repeat(xs, n);
    assert(s == ty_repeat(xs, m) + xs);
    if p == m {
        assert(s.subrange(p * w, p * w + w) =~= xs);
    } else {
        lemma_ty_repeat_sub(xs, m, p);
        assert(p * w + w <= m * w) by (nonlinear_arith)
            requires
                0 <= p < m,
        ;
        assert(s.subrange(p * w, p * w + w) =~= ty_repeat(xs, m).subrange(p * w, p * w + w));
    }
}

/// スロットの型の数は、型の幅である。
pub proof fn lemma_slot_tys_len(t: STy, enums: Seq<i64>)
    ensures
        slot_tys(t, enums).len() == width(t, enums),
    decreases t,
{
    match t {
        STy::Tuple(ts) => lemma_slot_tys_seq_len(ts, enums),
        STy::Record(_, ts) => lemma_slot_tys_seq_len(ts, enums),
        STy::Option(x) => lemma_slot_tys_len(*x, enums),
        STy::Set(e) => {
            let n = keys_or_zero(*e, enums);
            lemma_ty_repeat_len(seq![Type::Bool], n);
            assert(n * 1 == n);
        },
        STy::Map(k, v) => {
            let n = keys_or_zero(*k, enums);
            let row = seq![Type::Bool] + slot_tys(*v, enums);
            lemma_slot_tys_len(*v, enums);
            lemma_ty_repeat_len(row, n);
            assert(row.len() == 1 + width(*v, enums));
            assert(ty_repeat(row, n).len() == n * (1 + width(*v, enums)));
        },
        STy::List(e, max) => {
            lemma_slot_tys_len(*e, enums);
            lemma_ty_repeat_len(slot_tys(*e, enums), max as nat);
        },
        _ => {},
    }
}

pub proof fn lemma_slot_tys_seq_len(ts: Seq<STy>, enums: Seq<i64>)
    ensures
        slot_tys_seq(ts, enums).len() == width_sum(ts, enums),
    decreases ts,
{
    if ts.len() > 0 {
        lemma_slot_tys_seq_len(ts.drop_last(), enums);
        lemma_slot_tys_len(ts.last(), enums);
    }
}

/// 列の `i` 番目の型のスロットの型は、つなげた列の部分である。
pub proof fn lemma_slot_tys_seq_sub(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        0 <= i < ts.len(),
    ensures
        width_sum(ts.take(i), enums) + width(ts[i], enums) <= width_sum(ts, enums),
        slot_tys_seq(ts, enums).subrange(
            width_sum(ts.take(i), enums) as int,
            (width_sum(ts.take(i), enums) + width(ts[i], enums)) as int,
        ) == slot_tys(ts[i], enums),
    decreases ts.len(),
{
    let n = ts.len() - 1;
    let a = ts.drop_last();
    lemma_slot_tys_seq_len(ts, enums);
    lemma_slot_tys_seq_len(a, enums);
    lemma_slot_tys_len(ts[i], enums);
    let s = slot_tys_seq(ts, enums);
    assert(s == slot_tys_seq(a, enums) + slot_tys(ts.last(), enums));
    if i == n {
        assert(ts.take(i) =~= a);
        assert(s.subrange(width_sum(a, enums) as int, s.len() as int) =~= slot_tys(ts.last(), enums));
    } else {
        lemma_slot_tys_seq_sub(a, i, enums);
        assert(a.take(i) =~= ts.take(i));
        assert(a[i] == ts[i]);
        let lo = width_sum(ts.take(i), enums) as int;
        let hi = lo + width(ts[i], enums);
        assert(s.subrange(lo, hi) =~= slot_tys_seq(a, enums).subrange(lo, hi));
    }
}

} // verus!
