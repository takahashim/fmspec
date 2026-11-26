//! 下ろし（[`crate::lowering`]）が意味を保存することの仕様と補題。
//!
//! 下ろしの正しさは、値の上の意味論 [`eval_src`] と中核の意味論 [`eval_l`] の対応として述べる。
//! IRの式 `e` を下ろすと、束縛の列（[`Block`] に加えた分）とスロットの式の列が得られる。
//! 環境が対応するとき（[`ctx_ok`]）、
//!
//! - `eval_src` が `Err(k)` なら、束縛の列の評価も `Err(k)` になる。
//! - `eval_src` が `Ok(v)` なら、束縛の列の評価は成功し、その後の局所変数でスロットの式を評価すると、
//!   値 `v` を表すスロットの値（[`models`]）が得られる。
//!
//! これが [`lowers`] である。スロットの式は束縛子を含まず、その時点の局所変数だけを参照する（[`pure_below`]）。
//! そのため、後に束縛を加えても値は変わらない（[`lemma_weaken`]）。

#[cfg(verus_keep_ghost)]
use crate::bindings::{eval_bindings, eval_bound_body};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_rows, enc_seq, keys, keys_product, lemma_default_len, lemma_enc_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_rows_len, map_rows_member, member, members, models, models_seq, sty, width, xty};
#[cfg(verus_keep_ghost)]
use crate::encoding::{xwidth, xwidth_sum, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, lookup, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, radix, rank, rank_seq};
#[cfg(verus_keep_ghost)]
use crate::lowering::{Bound, Layout, LowerCtx};
use crate::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::model::{Type, Value};
#[cfg(verus_keep_ghost)]
use crate::ranking::mixed_rank_eval;
#[cfg(verus_keep_ghost)]
use crate::slots::{and_s, bool_lit, extends, ite_s, join_s, lits, or_s, tree_s, Block, Join};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_fold, eval_src, of_value, src_bool, to_value, Item, Over, SEnv, TExpr};
use vstd::prelude::*;

verus! {

// ---- スロットの式の純粋さ ----

/// 束縛子（`let`、量化）を含まず、局所変数は `n` 未満だけを参照する。
pub open spec fn pure_below(e: Expr, n: nat) -> bool
    decreases e,
{
    match e {
        Expr::Local(i) => i < n,
        Expr::Bin(_, a, b) => pure_below(*a, n) && pure_below(*b, n),
        Expr::And(a, b) => pure_below(*a, n) && pure_below(*b, n),
        Expr::Or(a, b) => pure_below(*a, n) && pure_below(*b, n),
        Expr::Implies(a, b) => pure_below(*a, n) && pure_below(*b, n),
        Expr::Not(a) => pure_below(*a, n),
        Expr::Code(a) => pure_below(*a, n),
        Expr::Ite(c, a, b) => pure_below(*c, n) && pure_below(*a, n) && pure_below(*b, n),
        Expr::Let(_, _) => false,
        Expr::Forall(_, _, _, _) => false,
        Expr::Exists(_, _, _, _) => false,
        _ => true,
    }
}

/// `a` は `b` の先頭部分である。
pub open spec fn prefix(a: Seq<Value>, b: Seq<Value>) -> bool {
    a.len() <= b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] == a[i]
}

pub proof fn lemma_prefix_refl(a: Seq<Value>)
    ensures
        prefix(a, a),
{
}

pub proof fn lemma_prefix_trans(a: Seq<Value>, b: Seq<Value>, c: Seq<Value>)
    requires
        prefix(a, b),
        prefix(b, c),
    ensures
        prefix(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] c[i] == a[i] by {
        assert(b[i] == a[i]);
    }
}

pub proof fn lemma_pure_mono(e: Expr, n: nat, m: nat)
    requires
        pure_below(e, n),
        n <= m,
    ensures
        pure_below(e, m),
    decreases e,
{
    match e {
        Expr::Bin(_, a, b) => {
            lemma_pure_mono(*a, n, m);
            lemma_pure_mono(*b, n, m);
        },
        Expr::And(a, b) => {
            lemma_pure_mono(*a, n, m);
            lemma_pure_mono(*b, n, m);
        },
        Expr::Or(a, b) => {
            lemma_pure_mono(*a, n, m);
            lemma_pure_mono(*b, n, m);
        },
        Expr::Implies(a, b) => {
            lemma_pure_mono(*a, n, m);
            lemma_pure_mono(*b, n, m);
        },
        Expr::Not(a) => lemma_pure_mono(*a, n, m),
        Expr::Code(a) => lemma_pure_mono(*a, n, m),
        Expr::Ite(c, a, b) => {
            lemma_pure_mono(*c, n, m);
            lemma_pure_mono(*a, n, m);
            lemma_pure_mono(*b, n, m);
        },
        _ => {},
    }
}

/// 純粋な式の値は、局所変数を後ろに加えても変わらない。
pub proof fn lemma_weaken(e: Expr, env: Env, ls: Seq<Value>, ls2: Seq<Value>)
    requires
        pure_below(e, ls.len()),
        prefix(ls, ls2),
    ensures
        eval_l(e, env, ls2) == eval_l(e, env, ls),
    decreases e,
{
    match e {
        Expr::Bin(_, a, b) => {
            lemma_weaken(*a, env, ls, ls2);
            lemma_weaken(*b, env, ls, ls2);
        },
        Expr::And(a, b) => {
            lemma_weaken(*a, env, ls, ls2);
            lemma_weaken(*b, env, ls, ls2);
        },
        Expr::Or(a, b) => {
            lemma_weaken(*a, env, ls, ls2);
            lemma_weaken(*b, env, ls, ls2);
        },
        Expr::Implies(a, b) => {
            lemma_weaken(*a, env, ls, ls2);
            lemma_weaken(*b, env, ls, ls2);
        },
        Expr::Not(a) => lemma_weaken(*a, env, ls, ls2),
        Expr::Code(a) => lemma_weaken(*a, env, ls, ls2),
        Expr::Ite(c, a, b) => {
            lemma_weaken(*c, env, ls, ls2);
            lemma_weaken(*a, env, ls, ls2);
            lemma_weaken(*b, env, ls, ls2);
        },
        Expr::Local(i) => {
            assert(ls2[i as int] == ls[i as int]);
        },
        _ => {},
    }
}

// ---- 束縛の列 ----

/// 束縛の列を先頭から評価した後の局所変数。
pub open spec fn run(bs: Seq<Expr>, env: Env, ls: Seq<Value>) -> Result<Seq<Value>, ErrKind> {
    eval_bindings(bs, bs.len(), env, ls)
}

/// 束縛の評価は、評価する数までの束縛だけで決まる。
pub proof fn lemma_bindings_ext(a: Seq<Expr>, b: Seq<Expr>, n: nat, env: Env, ls: Seq<Value>)
    requires
        n <= a.len(),
        n <= b.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] == b[i],
    ensures
        eval_bindings(a, n, env, ls) == eval_bindings(b, n, env, ls),
    decreases n,
{
    if n > 0 {
        lemma_bindings_ext(a, b, (n - 1) as nat, env, ls);
        assert(a[n - 1] == b[n - 1]);
    }
}

/// 束縛を1つ加えた列の評価。
pub proof fn lemma_run_push(bs: Seq<Expr>, x: Expr, env: Env, ls: Seq<Value>)
    ensures
        run(bs.push(x), env, ls) == match run(bs, env, ls) {
            Err(k) => Err(k),
            Ok(l) => match eval_l(x, env, l) {
                Err(k) => Err(k),
                Ok(v) => Ok(l.push(v)),
            },
        },
{
    let s = bs.push(x);
    lemma_bindings_ext(s, bs, bs.len(), env, ls);
    assert(s[bs.len() as int] == x);
}

/// 束縛の列をつなげた列の評価。
pub proof fn lemma_run_append(a: Seq<Expr>, b: Seq<Expr>, env: Env, ls: Seq<Value>)
    ensures
        run(a + b, env, ls) == match run(a, env, ls) {
            Err(k) => Err(k),
            Ok(l) => run(b, env, l),
        },
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let c = b.drop_last();
        let x = b.last();
        lemma_run_append(a, c, env, ls);
        assert(a + b =~= (a + c).push(x));
        assert(b =~= c.push(x));
        lemma_run_push(a + c, x, env, ls);
        match run(a, env, ls) {
            Ok(l) => lemma_run_push(c, x, env, l),
            Err(_) => {},
        }
    }
}

/// 束縛の列の評価は、局所変数を束縛の数だけ後ろに加える。
pub proof fn lemma_run_prefix(bs: Seq<Expr>, n: nat, env: Env, ls: Seq<Value>)
    requires
        n <= bs.len(),
    ensures
        eval_bindings(bs, n, env, ls) matches Ok(l) ==> l.len() == ls.len() + n && prefix(ls, l),
    decreases n,
{
    if n > 0 {
        lemma_run_prefix(bs, (n - 1) as nat, env, ls);
        match eval_bindings(bs, (n - 1) as nat, env, ls) {
            Ok(l) => {
                match eval_l(bs[n - 1], env, l) {
                    Ok(v) => {
                        lemma_prefix_trans(ls, l, l.push(v));
                    },
                    Err(_) => {},
                }
            },
            Err(_) => {},
        }
    }
}

pub proof fn lemma_run_len(bs: Seq<Expr>, env: Env, ls: Seq<Value>)
    ensures
        run(bs, env, ls) matches Ok(l) ==> l.len() == ls.len() + bs.len() && prefix(ls, l),
{
    lemma_run_prefix(bs, bs.len(), env, ls);
}

/// `b0` から `b1` までに加えた束縛。
pub open spec fn fresh(b0: Block, b1: Block) -> Seq<Expr> {
    b1.binds@.subrange(b0.binds@.len() as int, b1.binds@.len() as int)
}

pub proof fn lemma_fresh_refl(b: Block)
    ensures
        fresh(b, b) =~= Seq::<Expr>::empty(),
{
}

pub proof fn lemma_fresh_concat(b0: Block, b1: Block, b2: Block)
    requires
        extends(b0, b1),
        extends(b1, b2),
    ensures
        fresh(b0, b2) =~= fresh(b0, b1) + fresh(b1, b2),
{
    let n0 = b0.binds@.len() as int;
    let n1 = b1.binds@.len() as int;
    assert forall|i: int| n0 <= i < n1 implies #[trigger] b2.binds@[i] == b1.binds@[i] by {}
}

pub proof fn lemma_fresh_push(b0: Block, b1: Block, x: Expr)
    requires
        b1.binds@ == b0.binds@.push(x),
    ensures
        fresh(b0, b1) =~= seq![x],
{
}

/// 束縛の列の評価を、`b0` から `b1` までと `b1` から `b2` までに分ける。
pub proof fn lemma_run_fresh(b0: Block, b1: Block, b2: Block, env: Env, ls: Seq<Value>)
    requires
        extends(b0, b1),
        extends(b1, b2),
    ensures
        run(fresh(b0, b2), env, ls) == match run(fresh(b0, b1), env, ls) {
            Err(k) => Err(k),
            Ok(l) => run(fresh(b1, b2), env, l),
        },
{
    lemma_fresh_concat(b0, b1, b2);
    lemma_run_append(fresh(b0, b1), fresh(b1, b2), env, ls);
}

/// `b1` は、`b0` に `e` を束縛して `x` で指すか、`e` をそのまま `x` とするかである。
pub open spec fn added(b0: Block, b1: Block, e: Expr, x: Expr) -> bool {
    ||| x == e && b1.binds@ == b0.binds@
    ||| x == Expr::Local(b0.depth_s() as usize) && b1.binds@ == b0.binds@.push(e)
}

/// 純粋で評価が成功する式を [`added`] で加えると、`x` の値はその値になる。
pub proof fn lemma_added(b0: Block, b1: Block, e: Expr, x: Expr, env: Env, l: Seq<Value>, val: Value)
    requires
        extends(b0, b1),
        added(b0, b1, e, x),
        l.len() == b0.depth_s(),
        pure_below(e, l.len()),
        eval_l(e, env, l) == Ok::<Value, ErrKind>(val),
    ensures
        run(fresh(b0, b1), env, l) matches Ok(l2) && prefix(l, l2) && l2.len() == b1.depth_s() && pure_below(x, l2.len())
            && eval_l(x, env, l2) == Ok::<Value, ErrKind>(val),
{
    if x == e && b1.binds@ == b0.binds@ {
        assert(fresh(b0, b1) =~= Seq::<Expr>::empty());
    } else {
        lemma_fresh_push(b0, b1, e);
        lemma_run_push(Seq::empty(), e, env, l);
        assert(seq![e] =~= Seq::<Expr>::empty().push(e));
        lemma_prefix_trans(l, l, l.push(val));
    }
}

// ---- スロットの値 ----

/// スロットの式を評価した値の列。どれも成功するときに意味を持つ。
pub open spec fn slot_vals(slots: Seq<Expr>, env: Env, ls: Seq<Value>) -> Seq<Value> {
    Seq::new(slots.len(), |j: int| eval_l(slots[j], env, ls)->Ok_0)
}

/// スロットの式は純粋で、評価は成功する。
pub open spec fn clean(slots: Seq<Expr>, env: Env, ls: Seq<Value>) -> bool {
    forall|j: int| 0 <= j < slots.len() ==> pure_below(#[trigger] slots[j], ls.len()) && eval_l(slots[j], env, ls) is Ok
}

/// スロットの式は純粋で、評価は成功し、値の列は型 `t` の値 `v` を表す。
pub open spec fn denotes(slots: Seq<Expr>, env: Env, ls: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>) -> bool {
    clean(slots, env, ls) && models(slot_vals(slots, env, ls), v, t, enums)
}

pub proof fn lemma_clean_weaken(slots: Seq<Expr>, env: Env, ls: Seq<Value>, ls2: Seq<Value>)
    requires
        clean(slots, env, ls),
        prefix(ls, ls2),
    ensures
        clean(slots, env, ls2),
        slot_vals(slots, env, ls2) == slot_vals(slots, env, ls),
{
    assert forall|j: int| 0 <= j < slots.len() implies eval_l(#[trigger] slots[j], env, ls2) == eval_l(
        slots[j],
        env,
        ls,
    ) && pure_below(slots[j], ls2.len()) by {
        lemma_weaken(slots[j], env, ls, ls2);
        lemma_pure_mono(slots[j], ls.len(), ls2.len());
    }
    assert(slot_vals(slots, env, ls2) =~= slot_vals(slots, env, ls));
}

/// 部分列のスロットの値は、スロットの値の部分列である。
pub proof fn lemma_clean_sub(slots: Seq<Expr>, env: Env, ls: Seq<Value>, a: int, b: int)
    requires
        clean(slots, env, ls),
        0 <= a <= b <= slots.len(),
    ensures
        clean(slots.subrange(a, b), env, ls),
        slot_vals(slots.subrange(a, b), env, ls) == slot_vals(slots, env, ls).subrange(a, b),
{
    let s = slots.subrange(a, b);
    assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], ls.len()) && eval_l(
        s[j],
        env,
        ls,
    ) is Ok by {
        assert(s[j] == slots[a + j]);
    }
    assert(slot_vals(s, env, ls) =~= slot_vals(slots, env, ls).subrange(a, b));
}

/// つなげたスロットの値は、スロットの値をつなげたものである。
pub proof fn lemma_clean_concat(x: Seq<Expr>, y: Seq<Expr>, env: Env, ls: Seq<Value>)
    requires
        clean(x, env, ls),
        clean(y, env, ls),
    ensures
        clean(x + y, env, ls),
        slot_vals(x + y, env, ls) == slot_vals(x, env, ls) + slot_vals(y, env, ls),
{
    let s = x + y;
    assert forall|j: int| 0 <= j < s.len() implies pure_below(#[trigger] s[j], ls.len()) && eval_l(
        s[j],
        env,
        ls,
    ) is Ok by {
        if j < x.len() {
            assert(s[j] == x[j]);
        } else {
            assert(s[j] == y[j - x.len()]);
        }
    }
    assert(slot_vals(s, env, ls) =~= slot_vals(x, env, ls) + slot_vals(y, env, ls));
}

pub proof fn lemma_denotes_weaken(
    slots: Seq<Expr>,
    env: Env,
    ls: Seq<Value>,
    ls2: Seq<Value>,
    v: SVal,
    t: XTy,
    enums: Seq<i64>,
)
    requires
        denotes(slots, env, ls, v, t, enums),
        prefix(ls, ls2),
    ensures
        denotes(slots, env, ls2, v, t, enums),
        slot_vals(slots, env, ls2) == slot_vals(slots, env, ls),
{
    lemma_clean_weaken(slots, env, ls, ls2);
}

// ---- 値の表現の補題 ----

/// 列 `ts` の `i` 番目の要素のスロットの位置。
pub open spec fn xoff(ts: Seq<XTy>, i: int, enums: Seq<i64>) -> int {
    xwidth_sum(ts.take(i), enums) as int
}

pub proof fn lemma_models_len(s: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        models(s, v, t, enums),
    ensures
        s.len() == xwidth(t, enums),
    decreases t, 1nat,
{
    match t {
        XTy::Tuple(ts) => lemma_models_seq_len(s, v->Tuple_0, ts, enums),
        XTy::Record(_, ts) => lemma_models_seq_len(s, v->Tuple_0, ts, enums),
        XTy::Set(e) => lemma_enc_len(v, STy::Set(e), enums),
        XTy::Map(k, x) => lemma_enc_len(v, STy::Map(k, x), enums),
        XTy::List(e, m) => lemma_enc_len(v, STy::List(e, m), enums),
        _ => {},
    }
}

pub proof fn lemma_models_seq_len(s: Seq<Value>, vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>)
    requires
        models_seq(s, vs, ts, enums),
    ensures
        s.len() == xwidth_sum(ts, enums),
        vs.len() == ts.len(),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let w = xwidth(ts.last(), enums);
        let cut = s.len() - w;
        lemma_models_seq_len(s.take(cut), vs.drop_last(), ts.drop_last(), enums);
        lemma_models_len(s.skip(cut), vs.last(), ts.last(), enums);
    }
}

/// 値の組を表すスロットの列 `s` の `i` 番目の部分は、`i` 番目の要素を表す。
pub open spec fn part_ok(s: Seq<Value>, vs: Seq<SVal>, ts: Seq<XTy>, i: int, enums: Seq<i64>) -> bool {
    &&& xoff(ts, i, enums) + xwidth(ts[i], enums) <= s.len()
    &&& models(s.subrange(xoff(ts, i, enums), xoff(ts, i, enums) + xwidth(ts[i], enums)), vs[i], ts[i], enums)
}

/// 値の組を表すスロットの列を、要素の幅で区切ると、各部分が要素を表す。
pub proof fn lemma_models_seq_parts(s: Seq<Value>, vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>)
    requires
        models_seq(s, vs, ts, enums),
    ensures
        vs.len() == ts.len(),
        s.len() == xwidth_sum(ts, enums),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] part_ok(s, vs, ts, i, enums),
    decreases ts.len(),
{
    lemma_models_seq_len(s, vs, ts, enums);
    if ts.len() > 0 {
        let n = ts.len() - 1;
        let w = xwidth(ts.last(), enums);
        let cut = s.len() - w;
        let s0 = s.take(cut);
        let t0 = ts.drop_last();
        let v0 = vs.drop_last();
        lemma_models_seq_parts(s0, v0, t0, enums);
        lemma_models_seq_len(s0, v0, t0, enums);
        assert forall|i: int| 0 <= i < ts.len() implies #[trigger] part_ok(s, vs, ts, i, enums) by {
            if i < n {
                assert(part_ok(s0, v0, t0, i, enums));
                assert(t0.take(i) =~= ts.take(i));
                let a = xoff(ts, i, enums);
                let b = a + xwidth(ts[i], enums);
                assert(s0.subrange(a, b) =~= s.subrange(a, b));
            } else {
                assert(ts.take(i) =~= t0);
                assert(s.subrange(cut as int, s.len() as int) =~= s.skip(cut as int));
            }
        }
    }
}

/// 値の組を表すスロットの式の、`i` 番目の部分は `i` 番目の要素を表す。
pub proof fn lemma_denotes_part(
    slots: Seq<Expr>,
    env: Env,
    ls: Seq<Value>,
    vs: Seq<SVal>,
    ts: Seq<XTy>,
    i: int,
    enums: Seq<i64>,
)
    requires
        clean(slots, env, ls),
        models_seq(slot_vals(slots, env, ls), vs, ts, enums),
        0 <= i < ts.len(),
    ensures
        vs.len() == ts.len(),
        slots.len() == xwidth_sum(ts, enums),
        0 <= xoff(ts, i, enums),
        xoff(ts, i, enums) + xwidth(ts[i], enums) <= slots.len(),
        denotes(slots.subrange(xoff(ts, i, enums), xoff(ts, i, enums) + xwidth(ts[i], enums)), env, ls, vs[i], ts[i], enums),
{
    let sv = slot_vals(slots, env, ls);
    lemma_models_seq_parts(sv, vs, ts, enums);
    assert(part_ok(sv, vs, ts, i, enums));
    let a = xoff(ts, i, enums);
    let b = a + xwidth(ts[i], enums);
    lemma_clean_sub(slots, env, ls, a, b);
}

pub proof fn lemma_xoff_step(ts: Seq<XTy>, i: int, enums: Seq<i64>)
    requires
        0 <= i < ts.len(),
    ensures
        xoff(ts, i + 1, enums) == xoff(ts, i, enums) + xwidth(ts[i], enums),
{
    assert(ts.take(i + 1).drop_last() =~= ts.take(i));
}

// ---- 組み立ての部品の意味 ----

pub open spec fn all_pure(s: Seq<Expr>, n: nat) -> bool {
    forall|j: int| 0 <= j < s.len() ==> pure_below(#[trigger] s[j], n)
}

pub open spec fn bool_val(r: Result<Value, ErrKind>) -> bool {
    r is Ok && r->Ok_0 is Bool
}

pub proof fn lemma_clean_pure(slots: Seq<Expr>, env: Env, ls: Seq<Value>)
    requires
        clean(slots, env, ls),
    ensures
        all_pure(slots, ls.len()),
{
}

pub proof fn lemma_lits(vs: Seq<Value>, env: Env, ls: Seq<Value>)
    ensures
        clean(lits(vs), env, ls),
        slot_vals(lits(vs), env, ls) == vs,
        forall|n: nat| all_pure(#[trigger] lits(vs), n),
{
    assert(slot_vals(lits(vs), env, ls) =~= vs);
}

pub proof fn lemma_and(x: Expr, y: Expr, env: Env, ls: Seq<Value>, a: bool, b: bool)
    requires
        eval_l(x, env, ls) == Ok::<Value, ErrKind>(Value::Bool(a)),
        eval_l(y, env, ls) == Ok::<Value, ErrKind>(Value::Bool(b)),
    ensures
        eval_l(and_s(x, y), env, ls) == Ok::<Value, ErrKind>(Value::Bool(a && b)),
{
}

pub proof fn lemma_or(x: Expr, y: Expr, env: Env, ls: Seq<Value>, a: bool, b: bool)
    requires
        eval_l(x, env, ls) == Ok::<Value, ErrKind>(Value::Bool(a)),
        eval_l(y, env, ls) == Ok::<Value, ErrKind>(Value::Bool(b)),
    ensures
        eval_l(or_s(x, y), env, ls) == Ok::<Value, ErrKind>(Value::Bool(a || b)),
{
}

pub proof fn lemma_join_pure(k: Join, x: Expr, y: Expr, n: nat)
    requires
        pure_below(x, n),
        pure_below(y, n),
    ensures
        pure_below(join_s(k, x, y), n),
{
}

/// 純粋な式の木は純粋である。
pub proof fn lemma_tree_pure(items: Seq<Expr>, unit: Expr, k: Join, n: nat)
    requires
        all_pure(items, n),
        pure_below(unit, n),
    ensures
        pure_below(tree_s(items, unit, k), n),
    decreases items.len(),
{
    if items.len() > 1 {
        let m = items.len() / 2;
        let l = items.take(m as int);
        let r = items.skip(m as int);
        assert forall|j: int| 0 <= j < l.len() implies pure_below(#[trigger] l[j], n) by {
            assert(l[j] == items[j]);
        }
        assert forall|j: int| 0 <= j < r.len() implies pure_below(#[trigger] r[j], n) by {
            assert(r[j] == items[j + m]);
        }
        lemma_tree_pure(l, unit, k, n);
        lemma_tree_pure(r, unit, k, n);
        lemma_join_pure(k, tree_s(l, unit, k), tree_s(r, unit, k), n);
    } else if items.len() == 1 {
        assert(pure_below(items[0], n));
    }
}

pub open spec fn all_true(items: Seq<Expr>, env: Env, ls: Seq<Value>) -> bool {
    forall|j: int| 0 <= j < items.len() ==> #[trigger] eval_l(items[j], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(true),
    )
}

pub open spec fn any_true(items: Seq<Expr>, env: Env, ls: Seq<Value>) -> bool {
    exists|j: int| 0 <= j < items.len() && #[trigger] eval_l(items[j], env, ls) == Ok::<Value, ErrKind>(
        Value::Bool(true),
    )
}

pub open spec fn all_bool(items: Seq<Expr>, env: Env, ls: Seq<Value>) -> bool {
    forall|j: int| 0 <= j < items.len() ==> bool_val(#[trigger] eval_l(items[j], env, ls))
}

/// `all_of` の値は、すべての項が真であることである。
pub proof fn lemma_all_of(items: Seq<Expr>, env: Env, ls: Seq<Value>)
    requires
        all_bool(items, env, ls),
    ensures
        eval_l(tree_s(items, bool_lit(true), Join::And), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(all_true(items, env, ls)),
        ),
    decreases items.len(),
{
    if items.len() > 1 {
        let m = items.len() / 2;
        let l = items.take(m as int);
        let r = items.skip(m as int);
        assert forall|j: int| 0 <= j < l.len() implies bool_val(#[trigger] eval_l(l[j], env, ls)) by {
            assert(l[j] == items[j]);
        }
        assert forall|j: int| 0 <= j < r.len() implies bool_val(#[trigger] eval_l(r[j], env, ls)) by {
            assert(r[j] == items[j + m]);
        }
        lemma_all_of(l, env, ls);
        lemma_all_of(r, env, ls);
        lemma_and(
            tree_s(l, bool_lit(true), Join::And),
            tree_s(r, bool_lit(true), Join::And),
            env,
            ls,
            all_true(l, env, ls),
            all_true(r, env, ls),
        );
        if all_true(l, env, ls) && all_true(r, env, ls) {
            assert forall|j: int| 0 <= j < items.len() implies #[trigger] eval_l(items[j], env, ls) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true)) by {
                if j < m {
                    assert(l[j] == items[j]);
                } else {
                    assert(r[j - m] == items[j]);
                }
            }
        }
        if all_true(items, env, ls) {
            assert forall|j: int| 0 <= j < l.len() implies #[trigger] eval_l(l[j], env, ls) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true)) by {
                assert(l[j] == items[j]);
            }
            assert forall|j: int| 0 <= j < r.len() implies #[trigger] eval_l(r[j], env, ls) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true)) by {
                assert(r[j] == items[j + m]);
            }
        }
    } else if items.len() == 1 {
        assert(bool_val(eval_l(items[0], env, ls)));
    }
}

/// `any_of` の値は、どれかの項が真であることである。
pub proof fn lemma_any_of(items: Seq<Expr>, env: Env, ls: Seq<Value>)
    requires
        all_bool(items, env, ls),
    ensures
        eval_l(tree_s(items, bool_lit(false), Join::Or), env, ls) == Ok::<Value, ErrKind>(
            Value::Bool(any_true(items, env, ls)),
        ),
    decreases items.len(),
{
    if items.len() > 1 {
        let m = items.len() / 2;
        let l = items.take(m as int);
        let r = items.skip(m as int);
        assert forall|j: int| 0 <= j < l.len() implies bool_val(#[trigger] eval_l(l[j], env, ls)) by {
            assert(l[j] == items[j]);
        }
        assert forall|j: int| 0 <= j < r.len() implies bool_val(#[trigger] eval_l(r[j], env, ls)) by {
            assert(r[j] == items[j + m]);
        }
        lemma_any_of(l, env, ls);
        lemma_any_of(r, env, ls);
        lemma_or(
            tree_s(l, bool_lit(false), Join::Or),
            tree_s(r, bool_lit(false), Join::Or),
            env,
            ls,
            any_true(l, env, ls),
            any_true(r, env, ls),
        );
        if any_true(l, env, ls) {
            let j = choose|j: int| 0 <= j < l.len() && #[trigger] eval_l(l[j], env, ls) == Ok::<Value, ErrKind>(
                Value::Bool(true),
            );
            assert(l[j] == items[j]);
        }
        if any_true(r, env, ls) {
            let j = choose|j: int| 0 <= j < r.len() && #[trigger] eval_l(r[j], env, ls) == Ok::<Value, ErrKind>(
                Value::Bool(true),
            );
            assert(r[j] == items[j + m]);
        }
        if any_true(items, env, ls) {
            let j = choose|j: int| 0 <= j < items.len() && #[trigger] eval_l(items[j], env, ls) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true));
            if j < m {
                assert(l[j] == items[j]);
            } else {
                assert(r[j - m] == items[j]);
            }
        }
    } else if items.len() == 1 {
        assert(bool_val(eval_l(items[0], env, ls)));
        if any_true(items, env, ls) {
            let j = choose|j: int| 0 <= j < items.len() && #[trigger] eval_l(items[j], env, ls) == Ok::<
                Value,
                ErrKind,
            >(Value::Bool(true));
            assert(j == 0);
        }
    }
}

/// 型の列の各値が型に属する。
pub proof fn lemma_members(vs: Seq<SVal>, ts: Seq<STy>, enums: Seq<i64>)
    ensures
        members(vs, ts, enums) <==> (vs.len() == ts.len() && forall|i: int|
            0 <= i < ts.len() ==> #[trigger] member(vs[i], ts[i], enums)),
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_members(vs.drop_last(), ts.drop_last(), enums);
        if vs.len() == ts.len() && forall|i: int| 0 <= i < ts.len() ==> #[trigger] member(vs[i], ts[i], enums) {
            assert forall|i: int| 0 <= i < ts.drop_last().len() implies #[trigger] member(
                vs.drop_last()[i],
                ts.drop_last()[i],
                enums,
            ) by {
                assert(member(vs[i], ts[i], enums));
            }
            assert(member(vs[ts.len() - 1], ts[ts.len() - 1], enums));
        }
        if members(vs, ts, enums) {
            assert forall|i: int| 0 <= i < ts.len() implies #[trigger] member(vs[i], ts[i], enums) by {
                if i < ts.len() - 1 {
                    assert(member(vs.drop_last()[i], ts.drop_last()[i], enums));
                }
            }
        }
    } else {
        if vs.len() == ts.len() {
        }
    }
}

/// 式の列の列をつなげる。
pub open spec fn concat(xss: Seq<Seq<Expr>>) -> Seq<Expr>
    decreases xss.len(),
{
    if xss.len() == 0 {
        Seq::empty()
    } else {
        concat(xss.drop_last()) + xss.last()
    }
}

pub proof fn lemma_concat_push(xss: Seq<Seq<Expr>>, x: Seq<Expr>)
    ensures
        concat(xss.push(x)) == concat(xss) + x,
{
    assert(xss.push(x).drop_last() =~= xss);
}

/// 各部分が要素の正規形の符号化なら、つなげたものは組の正規形の符号化である。
pub proof fn lemma_concat_enc(outs: Seq<Seq<Expr>>, vs: Seq<SVal>, ts: Seq<STy>, env: Env, ls: Seq<Value>, enums: Seq<i64>)
    requires
        outs.len() == vs.len(),
        vs.len() == ts.len(),
        forall|j: int| 0 <= j < outs.len() ==> #[trigger] clean(outs[j], env, ls) && slot_vals(outs[j], env, ls) == enc(
            vs[j],
            ts[j],
            enums,
        ),
    ensures
        clean(concat(outs), env, ls),
        slot_vals(concat(outs), env, ls) == enc_seq(vs, ts, enums),
    decreases outs.len(),
{
    if outs.len() > 0 {
        let n = outs.len() - 1;
        assert forall|j: int| 0 <= j < outs.drop_last().len() implies #[trigger] clean(outs.drop_last()[j], env, ls)
            && slot_vals(outs.drop_last()[j], env, ls) == enc(vs.drop_last()[j], ts.drop_last()[j], enums) by {
            assert(outs.drop_last()[j] == outs[j]);
            assert(clean(outs[j], env, ls));
        }
        lemma_concat_enc(outs.drop_last(), vs.drop_last(), ts.drop_last(), env, ls, enums);
        assert(clean(outs[n], env, ls));
        lemma_clean_concat(concat(outs.drop_last()), outs.last(), env, ls);
    } else {
        assert(slot_vals(concat(outs), env, ls) =~= Seq::<Value>::empty());
    }
}

pub proof fn lemma_concat_pure(outs: Seq<Seq<Expr>>, n: nat)
    requires
        forall|k: int| 0 <= k < outs.len() ==> #[trigger] all_pure(outs[k], n),
    ensures
        all_pure(concat(outs), n),
    decreases outs.len(),
{
    if outs.len() > 0 {
        assert forall|k: int| 0 <= k < outs.drop_last().len() implies #[trigger] all_pure(outs.drop_last()[k], n) by {
            assert(outs.drop_last()[k] == outs[k]);
        }
        lemma_concat_pure(outs.drop_last(), n);
        assert(all_pure(outs[outs.len() - 1], n));
        let a = concat(outs.drop_last());
        let b = outs.last();
        assert forall|j: int| 0 <= j < (a + b).len() implies pure_below(#[trigger] (a + b)[j], n) by {
            if j < a.len() {
                assert((a + b)[j] == a[j]);
            } else {
                assert((a + b)[j] == b[j - a.len()]);
            }
        }
    }
}

pub proof fn lemma_sub_pure(s: Seq<Expr>, a: int, b: int, n: nat)
    requires
        all_pure(s, n),
        0 <= a <= b <= s.len(),
    ensures
        all_pure(s.subrange(a, b), n),
{
    assert forall|j: int| 0 <= j < b - a implies pure_below(#[trigger] s.subrange(a, b)[j], n) by {
        assert(s.subrange(a, b)[j] == s[a + j]);
    }
}

/// Optionの正規形のスロット `[tag, ite(tag, payload[j], defs[j])...]` は純粋である。
pub proof fn lemma_option_out_pure(tag: Expr, payload: Seq<Expr>, defs: Seq<Expr>, out: Seq<Expr>, m: nat)
    requires
        pure_below(tag, m),
        all_pure(payload, m),
        all_pure(defs, m),
        payload.len() == defs.len(),
        out.len() == 1 + defs.len(),
        out[0] == tag,
        forall|j: int| 0 <= j < defs.len() ==> #[trigger] out[1 + j] == ite_s(tag, payload[j], defs[j]),
    ensures
        all_pure(out, m),
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], m) by {
        if j > 0 {
            assert(out[1 + (j - 1)] == ite_s(tag, payload[j - 1], defs[j - 1]));
            assert(pure_below(payload[j - 1], m));
            assert(pure_below(defs[j - 1], m));
        }
    }
}

/// Optionの正規形のスロットの値。`tag` が `on` のとき、真なら値のスロット、偽なら既定値のスロットを選ぶ。
pub proof fn lemma_option_out(tag: Expr, payload: Seq<Expr>, defs: Seq<Expr>, out: Seq<Expr>, env: Env, ls: Seq<Value>, on: bool)
    requires
        eval_l(tag, env, ls) == Ok::<Value, ErrKind>(Value::Bool(on)),
        pure_below(tag, ls.len()),
        on ==> clean(payload, env, ls),
        all_pure(payload, ls.len()),
        clean(defs, env, ls),
        payload.len() == defs.len(),
        out.len() == 1 + defs.len(),
        out[0] == tag,
        forall|j: int| 0 <= j < defs.len() ==> #[trigger] out[1 + j] == ite_s(tag, payload[j], defs[j]),
    ensures
        clean(out, env, ls),
        slot_vals(out, env, ls) == seq![Value::Bool(on)] + if on {
            slot_vals(payload, env, ls)
        } else {
            slot_vals(defs, env, ls)
        },
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], ls.len()) && eval_l(out[j], env, ls)
        == Ok::<Value, ErrKind>((seq![Value::Bool(on)] + if on {
        slot_vals(payload, env, ls)
    } else {
        slot_vals(defs, env, ls)
    })[j]) by {
        if j > 0 {
            assert(out[1 + (j - 1)] == ite_s(tag, payload[j - 1], defs[j - 1]));
            assert(pure_below(payload[j - 1], ls.len()));
            assert(pure_below(defs[j - 1], ls.len()));
            assert(eval_l(defs[j - 1], env, ls) is Ok);
            if on {
                assert(eval_l(payload[j - 1], env, ls) is Ok);
            }
        }
    }
    assert(slot_vals(out, env, ls) =~= seq![Value::Bool(on)] + if on {
        slot_vals(payload, env, ls)
    } else {
        slot_vals(defs, env, ls)
    });
}

/// 値を格納の型の場所に置く条件とスロットの意味。
pub open spec fn store_ok(c: Expr, out: Seq<Expr>, env: Env, ls: Seq<Value>, v: SVal, st: STy, enums: Seq<i64>) -> bool {
    &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(member(v, st, enums)))
    &&& member(v, st, enums) ==> clean(out, env, ls) && slot_vals(out, env, ls) == enc(v, st, enums)
}

/// [`crate::slots::store`] の結果 `(c, out)` の性質。
pub open spec fn store_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, c: Expr, out: Seq<Expr>) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(c, n) && all_pure(out, n)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) ==> store_ok(c, out, env, ls, v, st, enums)
}

/// [`crate::slots::store`] の、TupleとRecordの要素の列についての性質。
pub open spec fn store_parts_spec(xs: Seq<XTy>, slots: Seq<Expr>, ts: Seq<STy>, enums: Seq<i64>, c: Expr, out: Seq<Expr>) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(c, n) && all_pure(out, n)
    &&& forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
        fits_all_s(xs, ts) && clean(slots, env, ls) && #[trigger] models_seq(slot_vals(slots, env, ls), vs, xs, enums)
            ==> {
            &&& eval_l(c, env, ls) == Ok::<Value, ErrKind>(Value::Bool(members(vs, ts, enums)))
            &&& members(vs, ts, enums) ==> clean(out, env, ls) && slot_vals(out, env, ls) == enc_seq(vs, ts, enums)
        }
}

/// [`crate::slots::rank_expr`] の結果 `r` の性質。値が型に属し、型がキーの型なら、番号を表す。
pub open spec fn rank_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) && member(v, st, enums) && keys(st, enums) is Some
            ==> eval_l(r, env, ls) == Ok::<Value, ErrKind>(Value::Int(rank(v, st, enums) as i64))
}

/// TupleとRecordの要素の列についての、番号の性質。
pub open spec fn mixed_spec(xs: Seq<XTy>, slots: Seq<Expr>, ts: Seq<STy>, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|env: Env, ls: Seq<Value>, vs: Seq<SVal>|
        fits_all_s(xs, ts) && clean(slots, env, ls) && #[trigger] models_seq(slot_vals(slots, env, ls), vs, xs, enums)
            && members(vs, ts, enums) && keys_product(ts, enums) is Some ==> eval_l(r, env, ls) == Ok::<Value, ErrKind>(
            Value::Int(rank_seq(vs, ts, enums) as i64),
        )
}

/// [`crate::slots::rank_or_neg`] の結果 `r` の性質。型に属さなければ -1。
pub open spec fn rank_neg_spec(t: XTy, slots: Seq<Expr>, st: STy, enums: Seq<i64>, r: Expr) -> bool {
    &&& forall|n: nat| #[trigger] all_pure(slots, n) ==> pure_below(r, n)
    &&& forall|env: Env, ls: Seq<Value>, v: SVal|
        fits_s(t, st) && #[trigger] denotes(slots, env, ls, v, t, enums) && keys(st, enums) is Some ==> eval_l(r, env, ls)
            == Ok::<Value, ErrKind>(Value::Int(if member(v, st, enums) {
            rank(v, st, enums) as i64
        } else {
            -1i64
        }))
}

/// 値の数の積が `MAX_KEYS` に収まれば、先頭部分の積も収まる。
pub proof fn lemma_keys_product_prefix(ts: Seq<STy>, i: int, enums: Seq<i64>)
    requires
        keys_product(ts, enums) is Some,
        0 <= i <= ts.len(),
    ensures
        keys_product(ts.take(i), enums) is Some,
        i < ts.len() ==> keys(ts[i], enums) is Some,
    decreases ts.len(),
{
    if i == ts.len() {
        assert(ts.take(i) =~= ts);
    } else {
        lemma_keys_product_prefix(ts.drop_last(), i, enums);
        assert(ts.drop_last().take(i) =~= ts.take(i));
        if i < ts.len() - 1 {
            assert(ts.drop_last()[i] == ts[i]);
        }
    }
}

pub open spec fn ranks_pure(parts: Seq<(Expr, i64)>, n: nat) -> bool {
    forall|k: int| 0 <= k < parts.len() ==> pure_below(#[trigger] parts[k].0, n)
}

/// 要素の番号の式を混合基数の桁として左から順にたたむと、組の番号になる。
pub proof fn lemma_mixed_eval(
    parts: Seq<(Expr, i64)>,
    vs: Seq<SVal>,
    ts: Seq<STy>,
    env: Env,
    ls: Seq<Value>,
    i: nat,
    enums: Seq<i64>,
)
    requires
        parts.len() == vs.len(),
        vs.len() == ts.len(),
        i <= ts.len(),
        keys_product(ts, enums) is Some,
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] member(vs[k], ts[k], enums),
        forall|k: int|
            0 <= k < ts.len() ==> #[trigger] eval_l(parts[k].0, env, ls) == Ok::<Value, ErrKind>(
                Value::Int(rank(vs[k], ts[k], enums) as i64),
            ) && parts[k].1 as int == radix(ts[k], enums),
    ensures
        0 <= rank_seq(vs.take(i as int), ts.take(i as int), enums) < keys_product(ts.take(i as int), enums)->0,
        mixed_rank_eval(parts, i, env, ls) == Ok::<Value, ErrKind>(
            Value::Int(rank_seq(vs.take(i as int), ts.take(i as int), enums) as i64),
        ),
    decreases i,
{
    lemma_keys_product_prefix(ts, i as int, enums);
    if i == 0 {
        assert(ts.take(0) =~= Seq::<STy>::empty());
    } else {
        let j = i - 1;
        lemma_mixed_eval(parts, vs, ts, env, ls, j as nat, enums);
        lemma_keys_product_prefix(ts, j, enums);
        let v0 = vs.take(j);
        let t0 = ts.take(j);
        let v1 = vs.take(i as int);
        let t1 = ts.take(i as int);
        assert(v1.drop_last() =~= v0);
        assert(t1.drop_last() =~= t0);
        assert(v1.last() == vs[j]);
        assert(t1.last() == ts[j]);
        assert(member(vs[j], ts[j], enums));
        lemma_rank_in_domain(vs[j], ts[j], enums);
        let rs0 = rank_seq(v0, t0, enums);
        let kp0 = keys_product(t0, enums)->0 as int;
        let k = keys(ts[j], enums)->0 as int;
        let r = rank(vs[j], ts[j], enums);
        assert(rank_seq(v1, t1, enums) == rs0 * radix(ts[j], enums) + r);
        assert(radix(ts[j], enums) == k);
        assert(keys_product(t1, enums) == Some((kp0 * k) as nat));
        assert(kp0 * k <= 4096);
        assert(0 <= rs0 * k) by (nonlinear_arith)
            requires
                0 <= rs0,
                0 <= k,
        ;
        assert(rs0 * k + r < kp0 * k) by (nonlinear_arith)
            requires
                0 <= rs0 < kp0,
                0 <= r < k,
        ;
        if i == 1 {
            assert(v0 =~= Seq::<SVal>::empty());
            assert(rs0 == 0);
            assert(0 * k == 0);
        } else {
            assert(rs0 * k <= kp0 * k) by (nonlinear_arith)
                requires
                    0 <= rs0 < kp0,
                    0 <= k,
            ;
        }
    }
}

/// Mapの行の符号化。有無のBoolと、値（ない行は既定値）の符号化。
pub open spec fn row_slots(o: Option<SVal>, t: STy, enums: Seq<i64>) -> Seq<Value> {
    match o {
        Some(x) => seq![Value::Bool(true)] + enc(x, t, enums),
        None => seq![Value::Bool(false)] + enc(default_val(t, enums), t, enums),
    }
}

pub proof fn lemma_map_rows_member_index(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>, r: int)
    requires
        map_rows_member(rows, t, enums),
        0 <= r < rows.len(),
    ensures
        rows[r] matches Some(x) ==> member(x, t, enums),
    decreases rows.len(),
{
    if r < rows.len() - 1 {
        lemma_map_rows_member_index(rows.drop_last(), t, enums, r);
        assert(rows.drop_last()[r] == rows[r]);
    }
}

/// Mapの符号化の `r` 行目の `i` 番目のスロット。
pub proof fn lemma_enc_rows_index(rows: Seq<Option<SVal>>, t: STy, enums: Seq<i64>, r: int, i: int)
    requires
        map_rows_member(rows, t, enums),
        0 <= r < rows.len(),
        0 <= i <= width(t, enums),
    ensures
        enc_rows(rows, t, enums).len() == rows.len() * (1 + width(t, enums)),
        0 <= r * (1 + width(t, enums)) + i < rows.len() * (1 + width(t, enums)),
        row_slots(rows[r], t, enums).len() == 1 + width(t, enums),
        enc_rows(rows, t, enums)[r * (1 + width(t, enums)) + i] == row_slots(rows[r], t, enums)[i],
    decreases rows.len(),
{
    let w = 1 + width(t, enums);
    let n = rows.len() as int;
    lemma_enc_rows_len(rows, t, enums);
    lemma_map_rows_member_index(rows, t, enums, r);
    match rows[r] {
        Some(x) => lemma_enc_len(x, t, enums),
        None => lemma_default_len(t, enums),
    }
    assert(0 <= r * w) by (nonlinear_arith)
        requires
            0 <= r,
            0 <= w,
    ;
    assert(r * w + i < n * w) by (nonlinear_arith)
        requires
            0 <= r < n,
            0 <= i < w,
    ;
    let pre = rows.drop_last();
    lemma_enc_rows_len(pre, t, enums);
    let p = enc_rows(pre, t, enums);
    assert(p.len() == (n - 1) * w);
    if r < n - 1 {
        lemma_enc_rows_index(pre, t, enums, r, i);
        assert(pre[r] == rows[r]);
        assert(r * w + i < (n - 1) * w) by (nonlinear_arith)
            requires
                0 <= r < n - 1,
                0 <= i < w,
        ;
    } else {
        assert(r * w == (n - 1) * w);
        assert(rows.last() == rows[r]);
    }
}

// ---- 型の適合 ----

/// 式の型 `x` の値を、格納の型 `s` の場所に置ける（整数の範囲は問わない）。
pub open spec fn fits_s(x: XTy, s: STy) -> bool
    decreases x,
{
    match (x, s) {
        (XTy::Bool, STy::Bool) => true,
        (XTy::Int, STy::Int(_, _)) => true,
        (XTy::Enum(a), STy::Enum(b)) => a == b,
        (XTy::Tuple(xs), STy::Tuple(ts)) => fits_all_s(xs, ts),
        (XTy::Record(a, xs), STy::Record(b, ts)) => a == b && fits_all_s(xs, ts),
        (XTy::Option(x), STy::Option(u)) => fits_s(*x, *u),
        (XTy::Set(a), STy::Set(b)) => a == b,
        (XTy::Map(ka, va), STy::Map(kb, vb)) => ka == kb && va == vb,
        (XTy::List(a, n), STy::List(b, m)) => n == m && a == b,
        _ => false,
    }
}

pub open spec fn fits_all_s(xs: Seq<XTy>, ts: Seq<STy>) -> bool
    decreases xs,
{
    if xs.len() == 0 {
        ts.len() == 0
    } else {
        ts.len() == xs.len() && fits_all_s(xs.drop_last(), ts.drop_last()) && fits_s(xs.last(), ts.last())
    }
}

pub proof fn lemma_fits_all(xs: Seq<XTy>, ts: Seq<STy>)
    ensures
        fits_all_s(xs, ts) <==> (xs.len() == ts.len() && forall|i: int|
            0 <= i < xs.len() ==> #[trigger] fits_s(xs[i], ts[i])),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_fits_all(xs.drop_last(), ts.drop_last());
        if xs.len() == ts.len() && forall|i: int| 0 <= i < xs.len() ==> #[trigger] fits_s(xs[i], ts[i]) {
            assert forall|i: int| 0 <= i < xs.drop_last().len() implies #[trigger] fits_s(
                xs.drop_last()[i],
                ts.drop_last()[i],
            ) by {
                assert(fits_s(xs[i], ts[i]));
            }
            assert(fits_s(xs[xs.len() - 1], ts[ts.len() - 1]));
        }
        if fits_all_s(xs, ts) {
            assert forall|i: int| 0 <= i < xs.len() implies #[trigger] fits_s(xs[i], ts[i]) by {
                if i < xs.len() - 1 {
                    assert(fits_s(xs.drop_last()[i], ts.drop_last()[i]));
                }
            }
        }
    }
}

// ---- 環境の対応 ----

/// 位置 `l` の符号化列 `xs` が、値 `v` の正規形の符号化である。
pub open spec fn layout_ok(l: Layout, v: SVal, tys: Seq<Type>, xs: Seq<i64>, enums: Seq<i64>) -> bool {
    let t = sty(l.ty);
    &&& member(v, t, enums)
    &&& l.offset + width(t, enums) <= usize::MAX
    &&& forall|j: int|
        0 <= j < width(t, enums) ==> #[trigger] lookup(tys, xs, (l.offset + j) as usize) == Ok::<
            Value,
            ErrKind,
        >(enc(v, t, enums)[j])
}

pub open spec fn layouts_ok(ls: Seq<Layout>, vs: Seq<SVal>, tys: Seq<Type>, xs: Seq<i64>, enums: Seq<i64>) -> bool {
    &&& vs.len() == ls.len()
    &&& forall|i: int| 0 <= i < ls.len() ==> #[trigger] layout_ok(ls[i], vs[i], tys, xs, enums)
}

/// 中核の環境 `env` と値の環境 `se` が、下ろしの文脈 `cx` のもとで対応する。
pub open spec fn env_rel(cx: LowerCtx, env: Env, se: SEnv) -> bool {
    let enums = cx.enums@;
    &&& se.enums == enums
    &&& match cx.states {
        Some(st) => {
            &&& layouts_ok(st@, se.pre, env.st_tys, env.pre, enums)
            &&& cx.next ==> layouts_ok(st@, se.post, env.st_tys, env.post, enums)
        },
        None => true,
    }
    &&& layouts_ok(cx.args@, se.args, env.arg_tys, env.args, enums)
    &&& cx.next ==> match cx.out {
        Some(t) => match se.out {
            Some(v) => member(v, sty(t), enums) && width(sty(t), enums) == 1 && env.out == Some(
                enc(v, sty(t), enums)[0],
            ),
            None => false,
        },
        None => true,
    }
    &&& se.consts.len() == cx.consts@.len()
    &&& forall|i: int|
        0 <= i < cx.consts@.len() ==> member(#[trigger] se.consts[i], sty(cx.consts@[i].ty), enums)
            && cx.consts@[i].slots@ == enc(se.consts[i], sty(cx.consts@[i].ty), enums)
}

/// 局所変数の対応。各束縛のスロットは、値の局所変数を表す。
pub open spec fn bounds_ok(sc: Seq<Bound>, env: Env, ls: Seq<Value>, sls: Seq<SVal>, enums: Seq<i64>) -> bool {
    &&& sc.len() == sls.len()
    &&& forall|i: int| 0 <= i < sc.len() ==> #[trigger] denotes(sc[i].slots@, env, ls, sls[i], xty(sc[i].ty), enums)
}

pub open spec fn ctx_ok(cx: LowerCtx, sc: Seq<Bound>, env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>) -> bool {
    env_rel(cx, env, se) && bounds_ok(sc, env, ls, sls, se.enums)
}

pub proof fn lemma_ctx_weaken(
    cx: LowerCtx,
    sc: Seq<Bound>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    ls2: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        ctx_ok(cx, sc, env, se, ls, sls),
        prefix(ls, ls2),
    ensures
        ctx_ok(cx, sc, env, se, ls2, sls),
{
    assert forall|i: int| 0 <= i < sc.len() implies #[trigger] denotes(
        sc[i].slots@,
        env,
        ls2,
        sls[i],
        xty(sc[i].ty),
        se.enums,
    ) by {
        lemma_denotes_weaken(sc[i].slots@, env, ls, ls2, sls[i], xty(sc[i].ty), se.enums);
    }
}

// ---- 下ろしの正しさ ----

/// 値の意味論の結果 `src` と、束縛の列の評価の結果 `core` が対応する。
pub open spec fn result_ok(
    src: Result<SVal, ErrKind>,
    core: Result<Seq<Value>, ErrKind>,
    slots: Seq<Expr>,
    env: Env,
    t: XTy,
    enums: Seq<i64>,
) -> bool {
    match src {
        Err(k) => core == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => match core {
            Ok(l) => denotes(slots, env, l, v, t, enums),
            Err(_) => false,
        },
    }
}

/// `e` を `b0` の後に下ろすと、`b1` までの束縛とスロット `slots`（型 `t`）になり、意味が保存される。
pub open spec fn lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, t: XTy, slots: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> result_ok(
            eval_src(e, se, sls),
            run(fresh(b0, b1), env, ls),
            slots,
            env,
            t,
            se.enums,
        )
}

/// 番号の式の下ろしの正しさ。値が型 `st` に属すれば番号、属さなければ -1 を表す。
pub open spec fn rank_result(
    src: Result<SVal, ErrKind>,
    core: Result<Seq<Value>, ErrKind>,
    x: Expr,
    env: Env,
    st: STy,
    enums: Seq<i64>,
) -> bool {
    match src {
        Err(k) => core == Err::<Seq<Value>, ErrKind>(k),
        Ok(v) => match core {
            Ok(l) => pure_below(x, l.len()) && eval_l(x, env, l) == Ok::<Value, ErrKind>(
                Value::Int(if member(v, st, enums) {
                    rank(v, st, enums) as i64
                } else {
                    -1i64
                }),
            ),
            Err(_) => false,
        },
    }
}

pub open spec fn rank_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, st: STy, x: Expr) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> rank_result(
            eval_src(e, se, sls),
            run(fresh(b0, b1), env, ls),
            x,
            env,
            st,
            se.enums,
        )
}

/// 単独に評価するスカラーの式の正しさ。
pub open spec fn scalar_result(src: Result<SVal, ErrKind>, core: Result<Value, ErrKind>, t: XTy, enums: Seq<i64>) -> bool {
    match src {
        Err(k) => core == Err::<Value, ErrKind>(k),
        Ok(v) => core is Ok && models(seq![core->Ok_0], v, t, enums),
    }
}

/// 深さ `d` で単独に評価する式 `x` が、`e` の値を表す。
pub open spec fn closed_lowers(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, d: nat, t: XTy, x: Expr) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == d ==> scalar_result(
            eval_src(e, se, sls),
            eval_l(x, env, ls),
            t,
            se.enums,
        )
}

/// 述語の下ろしの正しさ。
pub open spec fn prop_result(src: Result<SVal, ErrKind>, core: Result<Value, ErrKind>) -> bool {
    match src {
        Err(k) => core == Err::<Value, ErrKind>(k),
        Ok(v) => v is Bool && core == Ok::<Value, ErrKind>(Value::Bool(v->Bool_0)),
    }
}

/// 格納する値の下ろしの正しさ。値が型に属するとき、各スロットは正規形の符号化になる。
pub open spec fn stored_result(src: Result<SVal, ErrKind>, out: Seq<Expr>, env: Env, ls: Seq<Value>, st: STy, enums: Seq<i64>) -> bool {
    match src {
        Err(k) => forall|j: int| 0 <= j < out.len() ==> #[trigger] eval_l(out[j], env, ls) == Err::<Value, ErrKind>(k),
        Ok(v) => member(v, st, enums) ==> out.len() == width(st, enums) && forall|j: int|
            0 <= j < out.len() ==> #[trigger] eval_l(out[j], env, ls) == Ok::<Value, ErrKind>(enc(v, st, enums)[j]),
    }
}

/// 局所変数のない文脈での環境の対応と、局所変数の数。
pub open spec fn top_ok(cx: LowerCtx, env: Env, se: SEnv, ls: Seq<Value>, d: nat) -> bool {
    env_rel(cx, env, se) && ls.len() == d
}

/// `x` は、束縛の列 `binds` を評価してから `body` を評価する式である。
pub open spec fn wraps(x: Expr, binds: Seq<Expr>, body: Expr) -> bool {
    forall|env: Env, ls: Seq<Value>| #[trigger] eval_l(x, env, ls) == eval_bound_body(binds, binds.len(), body, env, ls)
}

/// 状態変数、遷移後の状態変数、引数の参照。
pub open spec fn kind_expr(kind: u8, i: usize) -> Expr {
    if kind == 0 {
        Expr::Var(i)
    } else if kind == 1 {
        Expr::Next(i)
    } else {
        Expr::Arg(i)
    }
}

/// 下ろしの各関数が意味の保存を示す式の範囲。すべての式を含む（[`lemma_frag_total`]）。
pub open spec fn frag(e: TExpr) -> bool
    decreases e, 0nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_)
        | TExpr::Const(_) => true,
        TExpr::Bin(_, a, b) => frag(*a) && frag(*b),
        TExpr::Eq(_, a, b) => frag(*a) && frag(*b),
        TExpr::Not(a) => frag(*a),
        TExpr::Fold(_, es) => frag_seq(es@),
        TExpr::Implies(a, b) => frag(*a) && frag(*b),
        TExpr::Ite(p, a, b) => frag(*p) && frag(*a) && frag(*b),
        TExpr::Let(a, b) => frag(*a) && frag(*b),
        TExpr::Get(_, a, x) => frag(*a) && frag(*x),
        TExpr::SetBin(_, a, b) => frag(*a) && frag(*b),
        TExpr::SetLit(_, es) => frag_seq(es@),
        TExpr::ListLit(_, _, es) => frag_seq(es@),
        TExpr::At(a, i) => frag(*a) && frag(*i),
        TExpr::First(a) => frag(*a),
        TExpr::Last(a) => frag(*a),
        TExpr::Push(_, _, a, x) => frag(*a) && frag(*x),
        TExpr::Pop(a) => frag(*a),
        TExpr::Shift(a) => frag(*a),
        TExpr::ListContains(a, x) => frag(*a) && frag(*x),
        TExpr::MapLit(_, _, items) => frag_items(items@),
        TExpr::Put(_, _, a, x, y) => frag(*a) && frag(*x) && frag(*y),
        TExpr::HasKey(_, a, x) => frag(*a) && frag(*x),
        TExpr::Delete(_, a, x) => frag(*a) && frag(*x),
        TExpr::Keys(a) => frag(*a),
        TExpr::SetContains(_, a, x) => frag(*a) && frag(*x),
        TExpr::Insert(_, a, x) => frag(*a) && frag(*x),
        TExpr::Remove(_, a, x) => frag(*a) && frag(*x),
        TExpr::Size(a) => frag(*a),
        TExpr::IsEmpty(a) => frag(*a),
        TExpr::Tuple(es) => frag_seq(es@),
        TExpr::Record(_, es) => frag_seq(es@),
        TExpr::Nth(a, _) => frag(*a),
        TExpr::Field(a, _, _) => frag(*a),
        TExpr::None(_) => true,
        TExpr::Some(a) => frag(*a),
        TExpr::IsSome(a) => frag(*a),
        TExpr::IsNone(a) => frag(*a),
        TExpr::Unwrap(a) => frag(*a),
        TExpr::Quant(_, over, body) => frag(*body) && match over {
            Over::Type(_) => true,
            Over::Set(_, s) => frag(*s),
            Over::Map(_, m) => frag(*m),
            Over::List(l) => frag(*l),
        },
    }
}

/// すべての式は [`frag`] に含まれる。
pub proof fn lemma_frag_total(e: TExpr)
    ensures
        frag(e),
    decreases e, 0nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_)
        | TExpr::Const(_) | TExpr::None(_) => {},
        TExpr::Bin(_, a, b) | TExpr::Eq(_, a, b) | TExpr::Implies(a, b) | TExpr::Let(a, b) | TExpr::Get(_, a, b)
        | TExpr::SetBin(_, a, b) | TExpr::At(a, b) | TExpr::Push(_, _, a, b) | TExpr::ListContains(a, b)
        | TExpr::HasKey(_, a, b) | TExpr::Delete(_, a, b) | TExpr::SetContains(_, a, b) | TExpr::Insert(_, a, b)
        | TExpr::Remove(_, a, b) => {
            lemma_frag_total(*a);
            lemma_frag_total(*b);
        },
        TExpr::Ite(p, a, b) | TExpr::Put(_, _, p, a, b) => {
            lemma_frag_total(*p);
            lemma_frag_total(*a);
            lemma_frag_total(*b);
        },
        TExpr::Not(a) | TExpr::First(a) | TExpr::Last(a) | TExpr::Pop(a) | TExpr::Shift(a) | TExpr::Keys(a)
        | TExpr::Size(a) | TExpr::IsEmpty(a) | TExpr::Nth(a, _) | TExpr::Field(a, _, _) | TExpr::Some(a)
        | TExpr::IsSome(a) | TExpr::IsNone(a) | TExpr::Unwrap(a) => {
            lemma_frag_total(*a);
        },
        TExpr::Fold(_, es) | TExpr::SetLit(_, es) | TExpr::ListLit(_, _, es) | TExpr::Tuple(es)
        | TExpr::Record(_, es) => {
            lemma_frag_seq_total(es@);
        },
        TExpr::MapLit(_, _, items) => {
            lemma_frag_items_total(items@);
        },
        TExpr::Quant(_, over, body) => {
            lemma_frag_total(*body);
            match over {
                Over::Type(_) => {},
                Over::Set(_, s) => lemma_frag_total(*s),
                Over::Map(_, m) => lemma_frag_total(*m),
                Over::List(l) => lemma_frag_total(*l),
            }
        },
    }
}

pub proof fn lemma_frag_seq_total(es: Seq<TExpr>)
    ensures
        frag_seq(es),
    decreases es, 1nat,
{
    if es.len() > 0 {
        lemma_frag_seq_total(es.drop_last());
        lemma_frag_total(es.last());
    }
}

pub proof fn lemma_frag_items_total(items: Seq<Item>)
    ensures
        frag_items(items),
    decreases items, 1nat,
{
    if items.len() > 0 {
        lemma_frag_items_total(items.drop_last());
        lemma_frag_total(items.last().key);
        lemma_frag_total(items.last().value);
    }
}

pub open spec fn frag_seq(es: Seq<TExpr>) -> bool
    decreases es, 1nat,
{
    if es.len() == 0 {
        true
    } else {
        frag_seq(es.drop_last()) && frag(es.last())
    }
}

pub open spec fn frag_items(items: Seq<Item>) -> bool
    decreases items, 1nat,
{
    if items.len() == 0 {
        true
    } else {
        frag_items(items.drop_last()) && frag(items.last().key) && frag(items.last().value)
    }
}

pub proof fn lemma_frag_items(items: Seq<Item>, i: int)
    requires
        frag_items(items),
        0 <= i < items.len(),
    ensures
        frag(items[i].key),
        frag(items[i].value),
    decreases items.len(),
{
    if i < items.len() - 1 {
        assert(items.drop_last()[i] == items[i]);
        lemma_frag_items(items.drop_last(), i);
    }
}

pub proof fn lemma_frag_seq(es: Seq<TExpr>, i: int)
    requires
        frag_seq(es),
        0 <= i < es.len(),
    ensures
        frag(es[i]),
    decreases es.len(),
{
    if i < es.len() - 1 {
        assert(es.drop_last()[i] == es[i]);
        lemma_frag_seq(es.drop_last(), i);
    }
}

// ---- 短絡する演算 ----

/// 中核の式の列を左から短絡して評価する。`all` なら論理積、そうでなければ論理和。
pub open spec fn sc_fold(all: bool, xs: Seq<Expr>, env: Env, ls: Seq<Value>) -> Result<bool, ErrKind>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Ok(all)
    } else {
        match sc_fold(all, xs.drop_last(), env, ls) {
            Err(k) => Err(k),
            Ok(b) => if b != all {
                Ok(b)
            } else {
                as_bool(eval_l(xs.last(), env, ls))
            },
        }
    }
}

pub open spec fn raw_join(all: bool) -> Join {
    if all {
        Join::RawAnd
    } else {
        Join::RawOr
    }
}

pub open spec fn lift_bool(r: Result<bool, ErrKind>) -> Result<Value, ErrKind> {
    match r {
        Ok(b) => Ok(Value::Bool(b)),
        Err(k) => Err(k),
    }
}

/// 各項の値は、Boolか失敗である。
pub open spec fn bool_or_err(xs: Seq<Expr>, env: Env, ls: Seq<Value>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> lift_bool(as_bool(#[trigger] eval_l(xs[i], env, ls))) == eval_l(xs[i], env, ls)
}

pub proof fn lemma_sc_fold_append(all: bool, a: Seq<Expr>, b: Seq<Expr>, env: Env, ls: Seq<Value>)
    ensures
        sc_fold(all, a + b, env, ls) == match sc_fold(all, a, env, ls) {
            Err(k) => Err(k),
            Ok(x) => if x != all {
                Ok(x)
            } else {
                sc_fold(all, b, env, ls)
            },
        },
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sc_fold_append(all, a, b.drop_last(), env, ls);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// 平衡した木にたたんだ論理積（論理和）は、左から短絡して評価した値になる。
pub proof fn lemma_tree_sc(all: bool, xs: Seq<Expr>, env: Env, ls: Seq<Value>)
    requires
        bool_or_err(xs, env, ls),
    ensures
        eval_l(tree_s(xs, bool_lit(all), raw_join(all)), env, ls) == lift_bool(sc_fold(all, xs, env, ls)),
    decreases xs.len(),
{
    let k = raw_join(all);
    if xs.len() == 0 {
        assert(tree_s(xs, bool_lit(all), k) == bool_lit(all));
    } else if xs.len() == 1 {
        assert(xs.drop_last() =~= Seq::<Expr>::empty());
        assert(sc_fold(all, xs.drop_last(), env, ls) == Ok::<bool, ErrKind>(all));
        assert(xs.last() == xs[0]);
        assert(lift_bool(as_bool(eval_l(xs[0], env, ls))) == eval_l(xs[0], env, ls));
        assert(tree_s(xs, bool_lit(all), k) == xs[0]);
    } else {
        let m = (xs.len() / 2) as int;
        let a = xs.take(m);
        let b = xs.skip(m);
        assert forall|i: int| 0 <= i < a.len() implies lift_bool(as_bool(#[trigger] eval_l(a[i], env, ls))) == eval_l(
            a[i],
            env,
            ls,
        ) by {
            assert(a[i] == xs[i]);
        }
        assert forall|i: int| 0 <= i < b.len() implies lift_bool(as_bool(#[trigger] eval_l(b[i], env, ls))) == eval_l(
            b[i],
            env,
            ls,
        ) by {
            assert(b[i] == xs[i + m]);
        }
        lemma_tree_sc(all, a, env, ls);
        lemma_tree_sc(all, b, env, ls);
        lemma_sc_fold_append(all, a, b, env, ls);
        assert(a + b =~= xs);
        let ta = tree_s(a, bool_lit(all), k);
        let tb = tree_s(b, bool_lit(all), k);
        assert(tree_s(xs, bool_lit(all), k) == join_s(k, ta, tb));
        assert(as_bool(eval_l(ta, env, ls)) == sc_fold(all, a, env, ls));
        assert(as_bool(eval_l(tb, env, ls)) == sc_fold(all, b, env, ls));
        if all {
            assert(join_s(k, ta, tb) == Expr::And(Box::new(ta), Box::new(tb)));
        } else {
            assert(join_s(k, ta, tb) == Expr::Or(Box::new(ta), Box::new(tb)));
        }
    }
}

/// 各項の真偽が値の意味論と一致すれば、短絡した評価も `eval_fold` と一致する。
pub proof fn lemma_fold_eq(all: bool, es: Seq<TExpr>, xs: Seq<Expr>, se: SEnv, sls: Seq<SVal>, env: Env, ls: Seq<Value>)
    requires
        es.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] as_bool(eval_l(xs[i], env, ls)) == src_bool(eval_src(es[i], se, sls)),
    ensures
        sc_fold(all, xs, env, ls) == eval_fold(all, es, se, sls),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let n = xs.len() - 1;
        assert forall|i: int| 0 <= i < xs.drop_last().len() implies #[trigger] as_bool(
            eval_l(xs.drop_last()[i], env, ls),
        ) == src_bool(eval_src(es.drop_last()[i], se, sls)) by {
            assert(as_bool(eval_l(xs[i], env, ls)) == src_bool(eval_src(es[i], se, sls)));
        }
        lemma_fold_eq(all, es.drop_last(), xs.drop_last(), se, sls, env, ls);
        assert(as_bool(eval_l(xs[n], env, ls)) == src_bool(eval_src(es[n], se, sls)));
    }
}

/// 最初の項が失敗すれば、`eval_fold` は同じ失敗になる。
pub proof fn lemma_fold_first_err(all: bool, es: Seq<TExpr>, se: SEnv, sls: Seq<SVal>, k: ErrKind)
    requires
        es.len() >= 1,
        eval_src(es[0], se, sls) == Err::<SVal, ErrKind>(k),
    ensures
        eval_fold(all, es, se, sls) == Err::<bool, ErrKind>(k),
    decreases es.len(),
{
    if es.len() == 1 {
        assert(es.drop_last() =~= Seq::<TExpr>::empty());
    } else {
        assert(es.drop_last()[0] == es[0]);
        lemma_fold_first_err(all, es.drop_last(), se, sls, k);
    }
}

// ---- 下ろしの合成 ----

/// 束縛の列を評価できれば、局所変数の列は伸びて、その長さは `b1` の深さになる。
pub proof fn lemma_run_fresh_ok(b0: Block, b1: Block, env: Env, ls: Seq<Value>)
    requires
        extends(b0, b1),
        ls.len() == b0.depth_s(),
    ensures
        run(fresh(b0, b1), env, ls) matches Ok(l) ==> l.len() == b1.depth_s() && prefix(ls, l),
{
    lemma_run_len(fresh(b0, b1), env, ls);
}

/// 部分式を1つ下ろした結果を、環境ごとに取り出す。
pub proof fn lemma_one(
    a: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    t: XTy,
    xs: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        extends(b0, b1),
        lowers(a, cx, sc, b0, b1, t, xs),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(v) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && denotes(
                xs,
                env,
                l,
                v,
                t,
                se.enums,
            ) && ctx_ok(cx, sc, env, se, l, sls),
        },
{
    lemma_run_fresh_ok(b0, b1, env, ls);
    if let Ok(l) = run(fresh(b0, b1), env, ls) {
        lemma_ctx_weaken(cx, sc, env, se, ls, l, sls);
    }
}

/// 部分式を2つ順に下ろした結果を、環境ごとに取り出す。
pub proof fn lemma_pair(
    a: TExpr,
    b: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    ta: XTy,
    xa: Seq<Expr>,
    tb: XTy,
    xb: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        extends(b0, b1),
        extends(b1, b2),
        lowers(a, cx, sc, b0, b1, ta, xa),
        lowers(b, cx, sc, b1, b2, tb, xb),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        match eval_src(a, se, sls) {
            Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(va) => match eval_src(b, se, sls) {
                Err(k) => run(fresh(b0, b2), env, ls) == Err::<Seq<Value>, ErrKind>(k),
                Ok(vb) => run(fresh(b0, b2), env, ls) matches Ok(l) && l.len() == b2.depth_s() && prefix(ls, l)
                    && denotes(xa, env, l, va, ta, se.enums) && denotes(xb, env, l, vb, tb, se.enums) && ctx_ok(
                    cx,
                    sc,
                    env,
                    se,
                    l,
                    sls,
                ),
            },
        },
{
    lemma_run_fresh(b0, b1, b2, env, ls);
    lemma_one(a, cx, sc, b0, b1, ta, xa, env, se, ls, sls);
    if let Ok(va) = eval_src(a, se, sls) {
        let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
        lemma_one(b, cx, sc, b1, b2, tb, xb, env, se, l1, sls);
        if let Ok(vb) = eval_src(b, se, sls) {
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_denotes_weaken(xa, env, l1, l2, va, ta, se.enums);
            lemma_prefix_trans(ls, l1, l2);
        }
    }
}

/// スカラーの1つのスロットが表す値。
pub proof fn lemma_denotes_one(x: Expr, env: Env, l: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        denotes(seq![x], env, l, v, t, enums),
        t == XTy::Int || t == XTy::Bool,
    ensures
        pure_below(x, l.len()),
        to_value(v) is Some,
        eval_l(x, env, l) == Ok::<Value, ErrKind>(to_value(v)->Some_0),
        t == XTy::Int ==> v is Int,
        t == XTy::Bool ==> v is Bool,
{
    assert(seq![x][0] == x);
    assert(slot_vals(seq![x], env, l)[0] == eval_l(x, env, l)->Ok_0);
}

/// 純粋で評価できるスカラーの式は、その値を表す1つのスロットになる。
pub proof fn lemma_one_denotes(x: Expr, env: Env, l: Seq<Value>, val: Value, t: XTy, enums: Seq<i64>)
    requires
        pure_below(x, l.len()),
        eval_l(x, env, l) == Ok::<Value, ErrKind>(val),
        (t == XTy::Int && val is Int) || (t == XTy::Bool && val is Bool),
    ensures
        denotes(seq![x], env, l, of_value(val), t, enums),
{
    assert(seq![x][0] == x);
    assert(slot_vals(seq![x], env, l) =~= seq![val]);
}

/// 1つの束縛を加えた束縛の列の評価。
pub proof fn lemma_run_one(b0: Block, b1: Block, e: Expr, env: Env, l: Seq<Value>)
    requires
        b1.binds@ == b0.binds@.push(e),
    ensures
        run(fresh(b0, b1), env, l) == match eval_l(e, env, l) {
            Err(k) => Err(k),
            Ok(v) => Ok::<Seq<Value>, ErrKind>(l.push(v)),
        },
{
    lemma_fresh_push(b0, b1, e);
    assert(seq![e] =~= Seq::<Expr>::empty().push(e));
    lemma_run_push(Seq::empty(), e, env, l);
}

/// 単独に評価するBoolの式の真偽は、値の意味論の真偽と一致する。
pub proof fn lemma_scalar_bool(src: Result<SVal, ErrKind>, core: Result<Value, ErrKind>, enums: Seq<i64>)
    requires
        scalar_result(src, core, XTy::Bool, enums),
    ensures
        as_bool(core) == src_bool(src),
        lift_bool(as_bool(core)) == core,
{
    if let Ok(v) = src {
        assert(seq![core->Ok_0][0] == core->Ok_0);
    }
}

/// 束縛したスロットの列 `out` は、元のスロットの列 `xs` と同じ値を表す。
pub open spec fn atoms_ok(xs: Seq<Expr>, out: Seq<Expr>, b0: Block, b1: Block) -> bool {
    &&& out.len() == xs.len()
    &&& forall|env: Env, l: Seq<Value>|
        l.len() == b0.depth_s() && #[trigger] clean(xs, env, l) ==> atoms_run(xs, out, b0, b1, env, l)
}

pub open spec fn atoms_run(xs: Seq<Expr>, out: Seq<Expr>, b0: Block, b1: Block, env: Env, l: Seq<Value>) -> bool {
    match run(fresh(b0, b1), env, l) {
        Ok(l2) => prefix(l, l2) && l2.len() == b1.depth_s() && clean(out, env, l2) && slot_vals(out, env, l2)
            == slot_vals(xs, env, l),
        Err(_) => false,
    }
}

pub proof fn lemma_atoms_empty(b: Block)
    ensures
        atoms_ok(Seq::empty(), Seq::empty(), b, b),
{
    lemma_fresh_refl(b);
    assert forall|env: Env, l: Seq<Value>| l.len() == b.depth_s() && #[trigger] clean(Seq::empty(), env, l) implies atoms_run(Seq::empty(), Seq::empty(), b, b, env, l) by {
        assert(fresh(b, b) =~= Seq::<Expr>::empty());
        lemma_prefix_refl(l);
        assert(slot_vals(Seq::empty(), env, l) =~= slot_vals(Seq::empty(), env, l));
    }
}

pub proof fn lemma_atoms_step(xs: Seq<Expr>, x: Expr, out: Seq<Expr>, y: Expr, b0: Block, b1: Block, b2: Block)
    requires
        atoms_ok(xs, out, b0, b1),
        extends(b0, b1),
        extends(b1, b2),
        added(b1, b2, x, y),
    ensures
        atoms_ok(xs.push(x), out.push(y), b0, b2),
{
    assert forall|env: Env, l: Seq<Value>| l.len() == b0.depth_s() && #[trigger] clean(xs.push(x), env, l) implies atoms_run(xs.push(x), out.push(y), b0, b2, env, l) by {
        lemma_clean_sub(xs.push(x), env, l, 0, xs.len() as int);
        assert(xs.push(x).subrange(0, xs.len() as int) =~= xs);
        let l1 = run(fresh(b0, b1), env, l)->Ok_0;
        assert(xs.push(x)[xs.len() as int] == x);
        let val = eval_l(x, env, l)->Ok_0;
        lemma_weaken(x, env, l, l1);
        lemma_pure_mono(x, l.len(), l1.len());
        lemma_added(b1, b2, x, y, env, l1, val);
        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
        lemma_run_fresh(b0, b1, b2, env, l);
        lemma_clean_weaken(out, env, l1, l2);
        lemma_prefix_trans(l, l1, l2);
        assert forall|j: int| 0 <= j < out.len() + 1 implies pure_below(#[trigger] out.push(y)[j], l2.len()) && eval_l(
            out.push(y)[j],
            env,
            l2,
        ) is Ok by {
            if j < out.len() {
                assert(out.push(y)[j] == out[j]);
            }
        }
        assert(slot_vals(out.push(y), env, l2) =~= slot_vals(xs.push(x), env, l)) by {
            assert forall|j: int| 0 <= j < out.len() + 1 implies #[trigger] slot_vals(out.push(y), env, l2)[j]
                == slot_vals(xs.push(x), env, l)[j] by {
                if j < out.len() {
                    assert(out.push(y)[j] == out[j]);
                    assert(xs.push(x)[j] == xs[j]);
                    assert(slot_vals(out, env, l2)[j] == slot_vals(xs, env, l)[j]);
                }
            }
        }
    }
}


pub proof fn lemma_extends_trans(a: Block, b: Block, c: Block)
    requires
        extends(a, b),
        extends(b, c),
    ensures
        extends(a, c),
{
    assert forall|i: int| 0 <= i < a.binds@.len() implies #[trigger] c.binds@[i] == a.binds@[i] by {
        assert(c.binds@[i] == b.binds@[i]);
    }
}

/// 式 `e` は、局所変数 `n` 個のもとで純粋である（[`pure_below`]）。
pub fn pure_exec(e: &Expr, n: usize) -> (r: bool)
    ensures
        r == pure_below(*e, n as nat),
    decreases e,
{
    match e {
        Expr::Local(i) => *i < n,
        Expr::Bin(_, a, b) => pure_exec(a, n) && pure_exec(b, n),
        Expr::And(a, b) => pure_exec(a, n) && pure_exec(b, n),
        Expr::Or(a, b) => pure_exec(a, n) && pure_exec(b, n),
        Expr::Implies(a, b) => pure_exec(a, n) && pure_exec(b, n),
        Expr::Not(a) => pure_exec(a, n),
        Expr::Code(a) => pure_exec(a, n),
        Expr::Ite(c, a, b) => pure_exec(c, n) && pure_exec(a, n) && pure_exec(b, n),
        Expr::Let(_, _) => false,
        Expr::Forall(_, _, _, _) => false,
        Expr::Exists(_, _, _, _) => false,
        _ => true,
    }
}


// ---- 値の表現の混合 ----

/// `m` が真の位置は `a`、偽の位置は `b` からとった列。
pub open spec fn mix2(a: Seq<Value>, b: Seq<Value>, m: Seq<bool>) -> Seq<Value> {
    Seq::new(
        a.len(),
        |j: int|
            if m[j] {
                a[j]
            } else {
                b[j]
            },
    )
}

/// 同じ値を表す2つのスロットの値の列を、位置ごとに混ぜても、同じ値を表す。
/// Optionの空の中身のように、値が決めないスロットがあるので、2つの列は等しいとは限らない。
pub proof fn lemma_models_mix(a: Seq<Value>, b: Seq<Value>, m: Seq<bool>, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        models(a, v, t, enums),
        models(b, v, t, enums),
        m.len() == a.len(),
    ensures
        models(mix2(a, b, m), v, t, enums),
    decreases t, 1nat,
{
    lemma_models_len(a, v, t, enums);
    lemma_models_len(b, v, t, enums);
    let s = mix2(a, b, m);
    match t {
        XTy::Tuple(ts) => lemma_models_seq_mix(a, b, m, v->Tuple_0, ts, enums),
        XTy::Record(_, ts) => lemma_models_seq_mix(a, b, m, v->Tuple_0, ts, enums),
        XTy::Option(x) => {
            assert(s[0] == a[0]);
            if let SVal::Some(w) = v {
                assert(s.drop_first() =~= mix2(a.drop_first(), b.drop_first(), m.drop_first()));
                lemma_models_mix(a.drop_first(), b.drop_first(), m.drop_first(), *w, *x, enums);
            }
        },
        _ => {
            assert(s =~= a);
        },
    }
}

proof fn lemma_models_seq_mix(a: Seq<Value>, b: Seq<Value>, m: Seq<bool>, vs: Seq<SVal>, ts: Seq<XTy>, enums: Seq<i64>)
    requires
        models_seq(a, vs, ts, enums),
        models_seq(b, vs, ts, enums),
        m.len() == a.len(),
    ensures
        models_seq(mix2(a, b, m), vs, ts, enums),
    decreases ts, 0nat,
{
    lemma_models_seq_len(a, vs, ts, enums);
    lemma_models_seq_len(b, vs, ts, enums);
    let s = mix2(a, b, m);
    if ts.len() > 0 {
        let cut = a.len() - xwidth(ts.last(), enums);
        assert(s.take(cut) =~= mix2(a.take(cut), b.take(cut), m.take(cut)));
        assert(s.skip(cut) =~= mix2(a.skip(cut), b.skip(cut), m.skip(cut)));
        lemma_models_seq_mix(a.take(cut), b.take(cut), m.take(cut), vs.drop_last(), ts.drop_last(), enums);
        lemma_models_mix(a.skip(cut), b.skip(cut), m.skip(cut), vs.last(), ts.last(), enums);
    }
}

/// 対角に混ぜた列。先頭 `k + 1` 個の位置は `vs[j][j]`、残りは `vs[0][j]`。
pub open spec fn diag(vs: Seq<Seq<Value>>, k: int, n: nat) -> Seq<Value> {
    Seq::new(
        n,
        |j: int|
            if j <= k {
                vs[j][j]
            } else {
                vs[0][j]
            },
    )
}

proof fn lemma_models_diag_k(vs: Seq<Seq<Value>>, k: int, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        0 <= k < vs.len(),
        forall|j: int| 0 <= j < vs.len() ==> #[trigger] models(vs[j], v, t, enums) && vs[j].len() == vs.len(),
    ensures
        models(diag(vs, k, vs.len()), v, t, enums),
    decreases k,
{
    let n = vs.len();
    assert(models(vs[0], v, t, enums) && vs[0].len() == n);
    if k == 0 {
        assert(diag(vs, 0, n) =~= vs[0]);
    } else {
        lemma_models_diag_k(vs, k - 1, v, t, enums);
        assert(models(vs[k], v, t, enums) && vs[k].len() == n);
        let m = Seq::new(n, |j: int| j == k);
        assert(diag(vs, k, n) =~= mix2(vs[k], diag(vs, k - 1, n), m));
        lemma_models_mix(vs[k], diag(vs, k - 1, n), m, v, t, enums);
    }
}

/// 各 `vs[j]` が同じ値を表すなら、`j` 番目の位置を `vs[j]` からとった列も、その値を表す。
pub proof fn lemma_models_diag(vs: Seq<Seq<Value>>, r: Seq<Value>, v: SVal, t: XTy, enums: Seq<i64>)
    requires
        vs.len() > 0,
        r.len() == vs.len(),
        forall|j: int| 0 <= j < vs.len() ==> #[trigger] models(vs[j], v, t, enums) && vs[j].len() == vs.len(),
        forall|j: int| 0 <= j < r.len() ==> #[trigger] r[j] == vs[j][j],
    ensures
        models(r, v, t, enums),
{
    lemma_models_diag_k(vs, vs.len() - 1, v, t, enums);
    assert(diag(vs, vs.len() - 1, vs.len()) =~= r);
}

// ---- 単独に評価するスロット ----

/// 単独に評価する式の列 `xs` の結果が、値の意味論の結果 `src` と対応する。
pub open spec fn slots_result(src: Result<SVal, ErrKind>, xs: Seq<Expr>, env: Env, ls: Seq<Value>, t: XTy, enums: Seq<i64>) -> bool {
    match src {
        Err(k) => forall|j: int| 0 <= j < xs.len() ==> #[trigger] eval_l(xs[j], env, ls) == Err::<Value, ErrKind>(k),
        Ok(v) => (forall|j: int| 0 <= j < xs.len() ==> #[trigger] eval_l(xs[j], env, ls) is Ok) && models(
            slot_vals(xs, env, ls),
            v,
            t,
            enums,
        ),
    }
}

/// 深さ `d` で単独に評価する式の列 `xs` が、`e` の値を表す。
pub open spec fn closed_slots(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, d: nat, t: XTy, xs: Seq<Expr>) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == d ==> slots_result(
            eval_src(e, se, sls),
            xs,
            env,
            ls,
            t,
            se.enums,
        )
}

} // verus!
