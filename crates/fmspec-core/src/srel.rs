//! 中核の符号の列と、値の列の対応（`rel`）。中核の更新の列の意味（`c_apply`）と、引数の正規形の仕様。

#[cfg(verus_keep_ghost)]
use crate::canon::lemma_wf_index;
#[cfg(verus_keep_ghost)]
use crate::canon::{canon_ok, canon_wf, lemma_enc_seq_sub, lemma_member_in, lemma_seq_in};
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, enc_seq, lemma_enc_len, member, members, sty, wf_stypes, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{width, width_sum};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, code_of, decode, eval_l, eval_spec, lookup, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::pure_below;
#[cfg(verus_keep_ghost)]
use crate::limits::smalls;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layout_at, layouts_at, Constant, Layout};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{in_slot, in_slots, lemma_slot_tys_len, lemma_slot_tys_seq_len};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_slot_tys_seq_sub, slot_tys, slot_tys_seq};
#[cfg(verus_keep_ghost)]
use crate::model::{Expr, Type, Update, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::{clean, layout_ok, layouts_ok, lemma_members, slot_vals};
#[cfg(verus_keep_ghost)]
use crate::state_enc::{encode_spec, in_type, vals_ok};
use vstd::prelude::*;

verus! {

/// 符号の列 `xs` は型 `tys` に従い、値の列 `vs` を表す。
pub open spec fn rel(ls: Seq<Layout>, vs: Seq<SVal>, tys: Seq<Type>, xs: Seq<i64>, enums: Seq<i64>) -> bool {
    layouts_ok(ls, vs, tys, xs, enums) && vals_ok(enums, tys, xs)
}

/// 値の列の符号。
pub open spec fn codes(xs: Seq<Value>) -> Seq<i64> {
    Seq::new(xs.len(), |q: int| code_of(xs[q]))
}

/// スロットの型の値の符号は型に属し、符号を値に戻すと元の値になる。
pub proof fn lemma_code_in(ty: Type, x: Value, enums: Seq<i64>)
    requires
        in_slot(ty, x, enums),
    ensures
        in_type(enums, ty, code_of(x)),
        decode(ty, code_of(x)) == x,
        encode_spec(enums, ty, x) == Ok::<i64, ErrKind>(code_of(x)),
{
}

/// 型に属する符号を値に戻すと、スロットの型の値で、符号は元の符号である。
pub proof fn lemma_decode_in(ty: Type, x: i64, enums: Seq<i64>)
    requires
        in_type(enums, ty, x),
    ensures
        in_slot(ty, decode(ty, x), enums),
        code_of(decode(ty, x)) == x,
{
}

/// 型の列の幅の累積和は増える。
pub(crate) proof fn lemma_width_mono(ts: Seq<STy>, i: int, j: int, enums: Seq<i64>)
    requires
        0 <= i <= j <= ts.len(),
    ensures
        width_sum(ts.take(i), enums) <= width_sum(ts.take(j), enums),
        j == i + 1 ==> width_sum(ts.take(j), enums) == width_sum(ts.take(i), enums) + width(ts[i], enums),
    decreases j - i,
{
    if i < j {
        lemma_width_mono(ts, i, j - 1, enums);
        assert(ts.take(j).drop_last() =~= ts.take(j - 1));
        assert(ts.take(j).last() == ts[j - 1]);
    }
}

/// 型の列の幅の累積和は増え、全体の幅を超えない。
pub proof fn lemma_width_take(ts: Seq<STy>, i: int, j: int, enums: Seq<i64>)
    requires
        0 <= i <= j <= ts.len(),
    ensures
        width_sum(ts.take(i), enums) <= width_sum(ts.take(j), enums),
        j == i + 1 ==> width_sum(ts.take(j), enums) == width_sum(ts.take(i), enums) + width(ts[i], enums),
        width_sum(ts.take(j), enums) <= width_sum(ts, enums),
{
    lemma_width_mono(ts, i, j, enums);
    lemma_width_mono(ts, j, ts.len() as int, enums);
    assert(ts.take(ts.len() as int) =~= ts);
}

/// 型に属する値の列の符号は、値の列を表す。
pub proof fn lemma_rel_codes(ls: Seq<Layout>, vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(ls, ts, enums),
        members(vs, ts, enums),
        wf_stypes(ts, enums),
        smalls(ts),
    ensures
        rel(ls, vs, slot_tys_seq(ts, enums), codes(enc_seq(vs, ts, enums)), enums),
{
    let s = enc_seq(vs, ts, enums);
    let tys = slot_tys_seq(ts, enums);
    let xs = codes(s);
    lemma_seq_in(vs, ts, enums);
    lemma_members(vs, ts, enums);
    assert forall|q: int| 0 <= q < tys.len() implies in_type(enums, #[trigger] tys[q], xs[q]) by {
        assert(in_slot(tys[q], s[q], enums));
        lemma_code_in(tys[q], s[q], enums);
    }
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] layout_ok(ls[i], vs[i], tys, xs, enums) by {
        assert(layout_at(ls[i], ts, i, enums));
        let t = ts[i];
        let off = width_sum(ts.take(i), enums) as int;
        lemma_enc_seq_sub(vs, ts, i, enums);
        lemma_slot_tys_seq_sub(ts, i, enums);
        lemma_wf_index(ts, i, enums);
        lemma_member_in(vs[i], t, enums);
        lemma_slot_tys_len(t, enums);
        lemma_slot_tys_seq_len(ts, enums);
        assert forall|j: int| 0 <= j < width(t, enums) implies #[trigger] lookup(tys, xs, (ls[i].offset + j) as usize)
            == Ok::<Value, ErrKind>(enc(vs[i], t, enums)[j]) by {
            assert(s.subrange(off, off + width(t, enums))[j] == s[off + j]);
            assert(tys.subrange(off, off + width(t, enums))[j] == tys[off + j]);
            assert(in_slot(slot_tys(t, enums)[j], enc(vs[i], t, enums)[j], enums));
            lemma_code_in(tys[off + j], s[off + j], enums);
        }
    }
}

/// 中核の1つの更新。
pub open spec fn c_write(u: Update, env: Env, enums: Seq<i64>, acc: Seq<i64>) -> Option<Seq<i64>> {
    match eval_spec(u.expr, env) {
        Ok(v) => if u.target < acc.len() && u.target < env.st_tys.len() {
            match encode_spec(enums, env.st_tys[u.target as int], v) {
                Ok(x) => Some(acc.update(u.target as int, x)),
                Err(_) => None,
            }
        } else {
            None
        },
        Err(_) => None,
    }
}

/// 中核の更新の列を、記述の順に適用する。
pub open spec fn c_apply(ups: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>) -> Option<Seq<i64>>
    decreases ups.len(),
{
    if ups.len() == 0 {
        Some(acc)
    } else {
        match c_apply(ups.drop_last(), env, enums, acc) {
            None => None,
            Some(t) => c_write(ups.last(), env, enums, t),
        }
    }
}

pub proof fn lemma_c_apply_concat(a: Seq<Update>, b: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    ensures
        c_apply(a + b, env, enums, acc) == match c_apply(a, env, enums, acc) {
            None => None,
            Some(t) => c_apply(b, env, enums, t),
        },
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        if c_apply(a, env, enums, acc) is Some {
            assert(c_apply(b, env, enums, c_apply(a, env, enums, acc)->Some_0) == c_apply(a, env, enums, acc));
        }
    } else {
        lemma_c_apply_concat(a, b.drop_last(), env, enums, acc);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

pub proof fn lemma_c_apply_first(u: Update, rest: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    ensures
        c_apply(seq![u] + rest, env, enums, acc) == match c_write(u, env, enums, acc) {
            None => None,
            Some(t) => c_apply(rest, env, enums, t),
        },
{
    lemma_c_apply_concat(seq![u], rest, env, enums, acc);
    assert(seq![u].drop_last() =~= Seq::<Update>::empty());
    assert(seq![u].last() == u);
    assert(c_apply(Seq::<Update>::empty(), env, enums, acc) == Some(acc));
    assert(c_apply(seq![u], env, enums, acc) == c_write(u, env, enums, acc));
}

/// 引数 `l` のスロットの式。
pub open spec fn arg_slots(l: Layout, enums: Seq<i64>) -> Seq<Expr> {
    Seq::new(width(sty(l.ty), enums), |j: int| Expr::Arg((l.offset + j) as usize))
}

/// 引数 `la[i]` のスロットの値は、その型のある値の正規形の符号化である。
pub open spec fn canon_at(la: Seq<Layout>, i: int, env: Env, enums: Seq<i64>) -> bool {
    canon_ok(slot_vals(arg_slots(la[i], enums), env, Seq::empty()), sty(la[i].ty), enums)
}

/// `k` 番目以降の引数は正規形である。
pub open spec fn canon_from(la: Seq<Layout>, k: int, env: Env, enums: Seq<i64>) -> bool {
    forall|i: int| k <= i < la.len() ==> #[trigger] canon_at(la, i, env, enums)
}

/// 引数の符号は、ドメインのスロットの型に従う。
pub open spec fn dom_ok(env: Env, doms: Seq<Type>, enums: Seq<i64>) -> bool {
    env.arg_tys == doms && vals_ok(enums, doms, env.args)
}

/// `g` は、`k` 番目以降の引数が正規形なら `body` と同じ真偽になり、そうでなければ偽になる。
pub open spec fn fold_ok(g: Expr, body: Expr, la: Seq<Layout>, k: int, doms: Seq<Type>, enums: Seq<i64>) -> bool {
    forall|env: Env|
        dom_ok(env, doms, enums) ==> if canon_from(la, k, env, enums) {
            as_bool(#[trigger] eval_spec(g, env)) == as_bool(eval_spec(body, env))
        } else {
            eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false))
        }
}

/// 引数のスロットの式は純粋で、値はスロットの型の値である。
pub(crate) proof fn lemma_arg_slots(la: Seq<Layout>, i: int, env: Env, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        0 <= i < la.len(),
    ensures
        clean(arg_slots(la[i], enums), env, Seq::empty()),
        in_slots(slot_vals(arg_slots(la[i], enums), env, Seq::empty()), slot_tys(ts[i], enums), enums),
        la[i].offset + width(ts[i], enums) <= width_sum(ts, enums),
        forall|j: int|
            0 <= j < width(ts[i], enums) ==> #[trigger] eval_l(arg_slots(la[i], enums)[j], env, Seq::empty())
                == lookup(env.arg_tys, env.args, (la[i].offset + j) as usize),
{
    let t = ts[i];
    let doms = slot_tys_seq(ts, enums);
    let s = arg_slots(la[i], enums);
    let off = la[i].offset as int;
    assert(layout_at(la[i], ts, i, enums));
    lemma_slot_tys_seq_sub(ts, i, enums);
    lemma_slot_tys_seq_len(ts, enums);
    lemma_slot_tys_len(t, enums);
    let w = width(t, enums) as int;
    assert forall|j: int| 0 <= j < w implies #[trigger] eval_l(s[j], env, Seq::empty()) == lookup(
        env.arg_tys,
        env.args,
        (la[i].offset + j) as usize,
    ) && eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j]))
        && in_slot(slot_tys(t, enums)[j], decode(doms[off + j], env.args[off + j]), enums) by {
        assert(doms.subrange(off, off + w)[j] == doms[off + j]);
        assert(in_type(enums, doms[off + j], env.args[off + j]));
        lemma_decode_in(doms[off + j], env.args[off + j], enums);
    }
    assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], 0) && eval_l(s[j], env, Seq::empty()) is Ok by {
        assert(eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j])));
    }
    let sv = slot_vals(s, env, Seq::empty());
    assert forall|j: int| 0 <= j < sv.len() implies #[trigger] in_slot(slot_tys(t, enums)[j], sv[j], enums) by {
        assert(eval_l(s[j], env, Seq::empty()) == Ok::<Value, ErrKind>(decode(doms[off + j], env.args[off + j])));
    }
}

/// 引数の正規形の判定式の値。
pub(crate) proof fn lemma_canon_eval(la: Seq<Layout>, i: int, env: Env, ts: Seq<STy>, enums: Seq<i64>, c: Expr)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        wf_stypes(ts, enums),
        smalls(ts),
        0 <= i < la.len(),
        canon_wf(sty(la[i].ty), arg_slots(la[i], enums), enums, c),
    ensures
        eval_spec(c, env) == Ok::<Value, ErrKind>(Value::Bool(canon_at(la, i, env, enums))),
{
    assert(layout_at(la[i], ts, i, enums));
    lemma_wf_index(ts, i, enums);
    lemma_arg_slots(la, i, env, ts, enums);
}

/// 値を表す引数の符号は、どれも正規形である。
pub proof fn lemma_rel_canon(la: Seq<Layout>, vs: Seq<SVal>, env: Env, enums: Seq<i64>)
    requires
        layouts_ok(la, vs, env.arg_tys, env.args, enums),
    ensures
        canon_from(la, 0, env, enums),
{
    assert forall|i: int| 0 <= i < la.len() implies #[trigger] canon_at(la, i, env, enums) by {
        assert(layout_ok(la[i], vs[i], env.arg_tys, env.args, enums));
        let t = sty(la[i].ty);
        let s = arg_slots(la[i], enums);
        let sv = slot_vals(s, env, Seq::empty());
        lemma_enc_len(vs[i], t, enums);
        assert forall|j: int| 0 <= j < sv.len() implies #[trigger] sv[j] == enc(vs[i], t, enums)[j] by {
            assert(lookup(env.arg_tys, env.args, (la[i].offset + j) as usize) == Ok::<Value, ErrKind>(
                enc(vs[i], t, enums)[j],
            ));
        }
        assert(sv =~= enc(vs[i], t, enums));
    }
}

/// 値の候補。引数の符号が正規形なら、その値。
pub open spec fn arg_val(la: Seq<Layout>, i: int, env: Env, enums: Seq<i64>) -> SVal {
    choose|v: SVal|
        member(v, sty(la[i].ty), enums) && #[trigger] enc(v, sty(la[i].ty), enums) == slot_vals(
            arg_slots(la[i], enums),
            env,
            Seq::empty(),
        )
}

pub open spec fn arg_vals(la: Seq<Layout>, env: Env, enums: Seq<i64>) -> Seq<SVal> {
    Seq::new(la.len(), |i: int| arg_val(la, i, env, enums))
}

/// 正規形の引数の符号は、値の列を表す。
pub proof fn lemma_canon_rel(la: Seq<Layout>, env: Env, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(la, ts, enums),
        dom_ok(env, slot_tys_seq(ts, enums), enums),
        canon_from(la, 0, env, enums),
    ensures
        layouts_ok(la, arg_vals(la, env, enums), env.arg_tys, env.args, enums),
{
    let vs = arg_vals(la, env, enums);
    assert forall|i: int| 0 <= i < la.len() implies #[trigger] layout_ok(la[i], vs[i], env.arg_tys, env.args, enums) by {
        assert(canon_at(la, i, env, enums));
        let t = sty(la[i].ty);
        let s = arg_slots(la[i], enums);
        let sv = slot_vals(s, env, Seq::empty());
        let v = vs[i];
        assert(member(v, t, enums) && enc(v, t, enums) == sv);
        lemma_arg_slots(la, i, env, ts, enums);
        assert(layout_at(la[i], ts, i, enums));
        assert forall|j: int| 0 <= j < width(t, enums) implies #[trigger] lookup(
            env.arg_tys,
            env.args,
            (la[i].offset + j) as usize,
        ) == Ok::<Value, ErrKind>(enc(v, t, enums)[j]) by {
            assert(eval_l(s[j], env, Seq::empty()) == lookup(env.arg_tys, env.args, (la[i].offset + j) as usize));
        }
    }
}

/// 定数のスロットは、定数の値の符号化である。
pub open spec fn consts_rel(cs: Seq<Constant>, cv: Seq<SVal>, enums: Seq<i64>) -> bool {
    &&& cs.len() == cv.len()
    &&& forall|i: int|
        0 <= i < cs.len() ==> member(#[trigger] cv[i], sty(cs[i].ty), enums) && cs[i].slots@ == enc(
            cv[i],
            sty(cs[i].ty),
            enums,
        )
}

} // verus!
