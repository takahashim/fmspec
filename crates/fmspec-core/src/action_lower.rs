//! 操作の下ろし。名前を解決したIRの操作（`SAction`）を、中核の操作に下ろす。

use crate::canon::{canonical, slot_types_list};
#[cfg(verus_keep_ghost)]
use crate::canon::{lemma_member_in, lemma_wf_index};
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, lemma_enc_len, lemma_width_pos, member, sty, stys, to_xty, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{wf_stype, wf_stypes, width};
use crate::encoding::{STy, SType};
use crate::eval::ErrKind;
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, code_of, decode, eval_l, eval_spec, lookup, prop_spec, Env};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::{lim_s, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layout_at, layouts_at};
use crate::lower_ctx::{Fail, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{has_ty, in_slot, in_slots, layout_tys, lemma_slot_tys_len};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_slot_tys_seq_len, lemma_slot_tys_seq_sub, slot_tys, slot_tys_seq};
use crate::lowering::{lower_prop, lower_stored};
use crate::model::{Action, Expr, Output, Type, Update};
#[cfg(verus_keep_ghost)]
use crate::model::{RawModel, Value};
#[cfg(verus_keep_ghost)]
use crate::model_total::sa_typed;
#[cfg(verus_keep_ghost)]
use crate::preserve::{env_rel, layout_ok, prop_result, stored_result, top_ok};
use crate::smodel::SAction;
#[cfg(verus_keep_ghost)]
use crate::smodel::{s_apply, s_env, s_output, s_state_tys, s_step, s_write, SModel, SOutput, SStep};
#[cfg(verus_keep_ghost)]
use crate::smodel::{styped, SUpdate};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, src_bool, SEnv};
#[cfg(verus_keep_ghost)]
use crate::srel::{arg_slots, c_apply, c_write, canon_at, canon_from, codes, dom_ok, fold_ok};
#[cfg(verus_keep_ghost)]
use crate::srel::{lemma_c_apply_concat, lemma_c_apply_first, lemma_canon_eval, lemma_code_in};
#[cfg(verus_keep_ghost)]
use crate::srel::{lemma_rel_canon, lemma_width_take, rel};
#[cfg(verus_keep_ghost)]
use crate::state_enc::{encode_spec, in_type, vals_ok};
#[cfg(verus_keep_ghost)]
use crate::step::{act_env, apply_updates, output_spec, step_spec, Step};
use crate::stype_exec::stype_width;
#[cfg(verus_keep_ghost)]
use crate::total::{cx_wf, layout_wf, sctx};
#[cfg(verus_keep_ghost)]
use crate::typing::{ETy, TyEnv};
use vstd::prelude::*;

verus! {

/// 型の付く操作の代入 `u` の代入先は状態変数で、式は代入先の型を持つ。
pub(crate) proof fn lemma_upd_pre(sa: SAction, cx: LowerCtx, u: int)
    requires
        cx_wf(cx),
        sa_typed(sa, sctx(cx)),
        cx.states is Some,
        0 <= u < sa.updates@.len(),
    ensures
        ({
            let st = cx.states->Some_0@;
            let su = sa.updates@[u];
            &&& su.var < st.len()
            &&& styped(su.expr, sctx(cx), to_xty(sty(st[su.var as int].ty)))
            &&& crate::total::ok_s(sty(st[su.var as int].ty), cx.enums@)
            &&& width(sty(st[su.var as int].ty), cx.enums@) >= 1
            &&& st[su.var as int].offset + width(sty(st[su.var as int].ty), cx.enums@) <= usize::MAX
        }),
{
    let st = cx.states->Some_0@;
    let su = sa.updates@[u];
    assert(layout_tys(st).len() == st.len());
    assert(layout_tys(st)[su.var as int] == sty(st[su.var as int].ty));
    assert(layout_wf(st[su.var as int], cx.enums@));
    lemma_width_pos(sty(st[su.var as int].ty), cx.enums@);
}

/// 操作を下ろす。guardの前に引数の正規形の判定を置き、代入は値のスロットごとの更新にする。
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn lower_action(sa: &SAction, cx: &LowerCtx, a: usize) -> (r: Result<Action, LowerError>)
    requires
        cx.states is Some,
        !cx.next,
        cx.out is None,
        layouts_at(cx.args@, stys(sa.args@), cx.enums@),
        wf_stypes(stys(sa.args@), cx.enums@),
        smalls(stys(sa.args@)),
    ensures
        r matches Ok(m) ==> act_ok(*sa, *cx, m),
        cx_wf(*cx) && sa_typed(*sa, sctx(*cx)) ==> (r matches Err(e) ==> e == LowerError::Depth),
        cx_wf(*cx) && sa_typed(*sa, sctx(*cx)) && crate::lower_types::cx_tok(*cx) ==> (r matches Ok(m) ==> act_typed(
            m,
            crate::lower_types::lenv(*cx),
        )),
{
    let ghost enums = cx.enums@;
    let ghost doms = slot_tys_seq(stys(sa.args@), enums);
    let ghost pre = cx_wf(*cx) && sa_typed(*sa, sctx(*cx));
    let ghost tq = pre && crate::lower_types::cx_tok(*cx);
    let ghost tv = crate::lower_types::lenv(*cx);
    proof {
        assert(layout_tys(cx.args@) =~= stys(sa.args@)) by {
            assert forall|i: int| 0 <= i < stys(sa.args@).len() implies layout_tys(cx.args@)[i] == stys(sa.args@)[i] by {
                assert(layout_at(cx.args@[i], stys(sa.args@), i, enums));
            }
        }
        assert(tv.arg_tys == doms);
    }
    let body = match lower_prop(&sa.guard, cx) {
        Ok(g) => g,
        Err(Fail::Depth) => return Err(LowerError::Depth),
        Err(Fail::Type) => return Err(LowerError::Guard(a)),
    };
    proof {
        if pre {
            assert forall|i: int| 0 <= i < stys(sa.args@).len() implies lim_s(#[trigger] stys(sa.args@)[i], enums) by {
                assert(crate::total::ok_s(stys(sa.args@)[i], enums));
            }
        }
    }
    let ghost b = body;
    let guard = match guard_fold(Ghost(stys(sa.args@)), &cx.args, body, &cx.enums) {
        Ok(g) => g,
        Err(i) => return Err(LowerError::Args(a, i)),
    };
    proof {
        assert forall|env: Env, se: SEnv| #[trigger] env_rel(*cx, env, se) && dom_ok(env, doms, enums) implies prop_spec(
            guard,
            env,
        ) == src_bool(eval_src(sa.guard, se, Seq::empty())) by {
            lemma_rel_canon(cx.args@, se.args, env, enums);
            assert(eval_spec(guard, env) == eval_spec(guard, env));
            assert(prop_result(eval_src(sa.guard, se, Seq::empty()), eval_l(b, env, Seq::empty())));
        }
    }
    proof {
        if tq {
            assert(has_ty(b, tv, Seq::empty(), ETy::Bool));
            assert(has_ty(guard, tv, Seq::empty(), ETy::Bool));
        }
    }
    let domains = slot_types_list(&sa.args, &cx.enums);
    let st = match &cx.states {
        Some(st) => st,
        None => return Err(LowerError::Update(a, 0)),
    };
    let ghost c = sctx(*cx);
    let mut ups: Vec<Update> = Vec::new();
    let ghost mut bs: Seq<Seq<Update>> = Seq::empty();
    proof {
        reveal(ups_typed);
    }
    let mut u = 0;
    while u < sa.updates.len()
        invariant
            u <= sa.updates@.len(),
            cx.states == Some(*st),
            bs.len() == u,
            ups@ == flat_ups(bs),
            forall|k: int| 0 <= k < u ==> #[trigger] block_ok(sa.updates@[k], *cx, bs[k]),
            pre == (cx_wf(*cx) && sa_typed(*sa, sctx(*cx))),
            c == sctx(*cx),
            tq == (pre && crate::lower_types::cx_tok(*cx)),
            tv == crate::lower_types::lenv(*cx),
            tq ==> ups_typed(ups@, tv),
            enums == cx.enums@,
        decreases sa.updates@.len() - u,
    {
        let su = &sa.updates[u];
        proof {
            if pre {
                lemma_upd_pre(*sa, *cx, u as int);
            }
        }
        if su.var >= st.len() {
            return Err(LowerError::Update(a, u));
        }
        let l = &st[su.var];
        let out = match lower_stored(&su.expr, cx, &l.ty, 0) {
            Ok(o) => o,
            Err(Fail::Depth) => return Err(LowerError::Depth),
            Err(Fail::Type) => return Err(LowerError::Update(a, u)),
        };
        if out.len() == 0 {
            return Err(LowerError::Update(a, u));
        }
        match stype_width(&l.ty, &cx.enums) {
            Some(w) => if w != out.len() {
                return Err(LowerError::Update(a, u));
            },
            None => return Err(LowerError::Update(a, u)),
        }
        let ghost before = ups@;
        if !push_block(&mut ups, l.offset, &out) {
            return Err(LowerError::Update(a, u));
        }
        let ghost blk = ups@.subrange(before.len() as int, ups@.len() as int);
        proof {
            let bs0 = bs;
            bs = bs.push(blk);
            assert(bs.drop_last() =~= bs0);
            assert(ups@ =~= before + blk);
            assert forall|k: int| 0 <= k < blk.len() implies #[trigger] upd_exprs(blk)[k] == out@[k] by {
                assert(blk[k] == ups@[before.len() + k]);
                assert(ups@[before.len() + k].target == l.offset + k);
            }
            assert(upd_exprs(blk) =~= out@);
            assert forall|k: int| 0 <= k < blk.len() implies #[trigger] blk[k].target == l.offset + k by {
                assert(blk[k] == ups@[before.len() + k]);
            }
            assert forall|k: int| 0 <= k <= u implies #[trigger] block_ok(sa.updates@[k], *cx, bs[k]) by {
                if k < u {
                    assert(bs[k] == bs0[k]);
                }
            }
            if tq {
                assert(cx.states->Some_0@[su.var as int] == *l);
                lemma_ups_typed(before, ups@, out@, cx.states->Some_0@, su.var as int, tv, enums);
            }
        }
        u += 1;
    }
    let output = match &sa.output {
        None => None,
        Some(so) => {
            let ty = match &so.ty {
                SType::Bool => Type::Bool,
                SType::Int(lo, hi) => Type::Int(*lo, *hi),
                SType::Enum(id) => Type::Enum(*id),
                _ => return Err(LowerError::Output(a)),
            };
            let mut out = match lower_stored(&so.expr, cx, &so.ty, 0) {
                Ok(o) => o,
                Err(Fail::Depth) => return Err(LowerError::Depth),
                Err(Fail::Type) => return Err(LowerError::Output(a)),
            };
            if out.len() != 1 {
                return Err(LowerError::Output(a));
            }
            let ghost out0 = out@;
            let expr = match out.pop() {
                Some(e) => e,
                None => return Err(LowerError::Output(a)),
            };
            proof {
                assert(out0 =~= seq![expr]);
                if tq {
                    assert(crate::lower_types::typed(out0, crate::lower_types::etys(slot_tys(sty(so.ty), enums)), tv, Seq::empty()));
                    assert(has_ty(out0[0], tv, Seq::empty(), crate::lower_types::etys(slot_tys(sty(so.ty), enums))[0]));
                    assert(ty == slot_tys(sty(so.ty), enums)[0]);
                    assert(has_ty(expr, tv, Seq::empty(), crate::typing::ety_of(ty)));
                }
            }
            Some(Output { ty, expr })
        },
    };
    let m = Action { n_params: sa.n_params, domains, guard, updates: ups, output };
    proof {
        assert(upds_ok(sa.updates@, *cx, bs, m.updates@));
        if tq {
            reveal(ups_typed);
            assert(act_typed(m, tv));
        }
    }
    Ok(m)
}

/// 引数 `l` のスロットの式を作る。
pub(crate) fn arg_exprs(l: &Layout, enums: &Vec<i64>) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(xs) ==> xs@ == arg_slots(*l, enums@),
        lim_s(sty(l.ty), enums@) && l.offset + width(sty(l.ty), enums@) <= usize::MAX ==> r is Some,
{
    let w = stype_width(&l.ty, enums)?;
    let _ = l.offset.checked_add(w)?;
    let mut xs: Vec<Expr> = Vec::new();
    let mut j: usize = 0;
    while j < w
        invariant
            j <= w,
            w == width(sty(l.ty), enums@),
            l.offset + w <= usize::MAX,
            xs@ == arg_slots(*l, enums@).take(j as int),
        decreases w - j,
    {
        xs.push(Expr::Arg(l.offset + j));
        j += 1;
        proof {
            assert(xs@ =~= arg_slots(*l, enums@).take(j as int));
        }
    }
    proof {
        assert(arg_slots(*l, enums@).take(w as int) =~= arg_slots(*l, enums@));
    }
    Some(xs)
}

/// guard の前に、引数ごとの正規形の判定を `&&` でつなぐ。
pub(crate) fn guard_fold(Ghost(ts): Ghost<Seq<STy>>, la: &Vec<Layout>, body: Expr, enums: &Vec<i64>) -> (r: Result<Expr, usize>)
    requires
        layouts_at(la@, ts, enums@),
        wf_stypes(ts, enums@),
        smalls(ts),
    ensures
        r matches Ok(g) ==> fold_ok(g, body, la@, 0, slot_tys_seq(ts, enums@), enums@),
        (forall|i: int| 0 <= i < ts.len() ==> lim_s(#[trigger] ts[i], enums@)) ==> r is Ok,
        r matches Ok(g) ==> forall|tv: TyEnv|
            tv.enums == enums@ && tv.arg_tys == slot_tys_seq(ts, enums@) && #[trigger] has_ty(body, tv, Seq::empty(), ETy::Bool)
                ==> has_ty(g, tv, Seq::empty(), ETy::Bool),
{
    let ghost lims = forall|i: int| 0 <= i < ts.len() ==> lim_s(#[trigger] ts[i], enums@);
    let ghost doms = slot_tys_seq(ts, enums@);
    let ghost b = body;
    let mut g = body;
    let mut k = la.len();
    while k > 0
        invariant
            k <= la@.len(),
            doms == slot_tys_seq(ts, enums@),
            layouts_at(la@, ts, enums@),
            wf_stypes(ts, enums@),
            smalls(ts),
            fold_ok(g, b, la@, k as int, doms, enums@),
            lims == forall|i: int| 0 <= i < ts.len() ==> lim_s(#[trigger] ts[i], enums@),
            forall|tv: TyEnv|
                tv.enums == enums@ && tv.arg_tys == slot_tys_seq(ts, enums@) && #[trigger] has_ty(b, tv, Seq::empty(), ETy::Bool)
                    ==> has_ty(g, tv, Seq::empty(), ETy::Bool),
        decreases k,
    {
        k -= 1;
        proof {
            if lims {
                crate::smodel::lemma_layout_end(la@, ts, enums@, k as int);
                assert(layout_at(la@[k as int], ts, k as int, enums@));
                assert(lim_s(ts[k as int], enums@));
            }
        }
        let slots = match arg_exprs(&la[k], enums) {
            Some(s) => s,
            None => return Err(k),
        };
        let c = match canonical(&la[k].ty, &slots, enums) {
            Some(c) => c,
            None => return Err(k),
        };
        let ghost g0 = g;
        g = Expr::And(Box::new(c), Box::new(g));
        proof {
            assert(layout_tys(la@) =~= ts) by {
                assert forall|i: int| 0 <= i < ts.len() implies layout_tys(la@)[i] == ts[i] by {
                    assert(layout_at(la@[i], ts, i, enums@));
                }
            }
            assert forall|tv: TyEnv|
                tv.enums == enums@ && tv.arg_tys == slot_tys_seq(ts, enums@) && #[trigger] has_ty(b, tv, Seq::empty(), ETy::Bool)
                    implies has_ty(g, tv, Seq::empty(), ETy::Bool) by {
                let ki = k as int;
                lemma_wf_index(ts, ki, enums@);
                assert(layout_at(la@[ki], ts, ki, enums@));
                assert forall|j: int| 0 <= j < slots@.len() implies #[trigger] slots@[j] == crate::expr_build::kind_expr(2, (la@[ki].offset + j) as usize) by {
                }
                crate::lower_types::lemma_kind_typed(la@, ki, 2, slots@, tv, Seq::empty());
                crate::lower_types::lemma_xetys_of(ts[ki], enums@);
                assert(has_ty(c, tv, Seq::empty(), ETy::Bool));
                assert(has_ty(g0, tv, Seq::empty(), ETy::Bool));
            }
        }
        proof {
            assert forall|env: Env| dom_ok(env, doms, enums@) implies if canon_from(la@, k as int, env, enums@) {
                as_bool(#[trigger] eval_spec(g, env)) == as_bool(eval_spec(b, env))
            } else {
                eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false))
            } by {
                lemma_canon_eval(la@, k as int, env, ts, enums@, c);
                assert(eval_spec(g0, env) == eval_spec(g0, env));
                assert(as_bool(eval_l(c, env, Seq::empty())) == Ok::<bool, ErrKind>(canon_at(la@, k as int, env, enums@)));
                if canon_at(la@, k as int, env, enums@) {
                    assert(eval_spec(g, env) == match as_bool(eval_l(g0, env, Seq::empty())) {
                        Err(e) => Err(e),
                        Ok(y) => Ok::<Value, ErrKind>(Value::Bool(y)),
                    });
                    if canon_from(la@, (k + 1) as int, env, enums@) {
                        assert(canon_from(la@, k as int, env, enums@));
                        assert(as_bool(eval_spec(g, env)) == as_bool(eval_spec(g0, env)));
                    } else {
                        let i = choose|i: int| k + 1 <= i < la@.len() && !#[trigger] canon_at(la@, i, env, enums@);
                        assert(!canon_from(la@, k as int, env, enums@));
                    }
                } else {
                    assert(!canon_from(la@, k as int, env, enums@));
                    assert(eval_spec(g, env) == Ok::<Value, ErrKind>(Value::Bool(false)));
                }
            }
        }
    }
    Ok(g)
}

/// 中核の更新の列の式。
pub open spec fn upd_exprs(blk: Seq<Update>) -> Seq<Expr> {
    Seq::new(blk.len(), |j: int| blk[j].expr)
}

/// 中核の更新の列 `blk` は、代入 `su` の値の各スロットを、状態変数のスロットに書く。
pub open spec fn block_ok(su: SUpdate, cx: LowerCtx, blk: Seq<Update>) -> bool {
    let st = cx.states->Some_0@;
    &&& cx.states is Some
    &&& su.var < st.len()
    &&& blk.len() >= 1
    &&& blk.len() == width(sty(st[su.var as int].ty), cx.enums@)
    &&& forall|j: int| 0 <= j < blk.len() ==> #[trigger] blk[j].target == st[su.var as int].offset + j
    &&& forall|env: Env, se: SEnv|
        #[trigger] top_ok(cx, env, se, Seq::empty(), 0) ==> stored_result(
            eval_src(su.expr, se, Seq::empty()),
            upd_exprs(blk),
            env,
            Seq::empty(),
            sty(st[su.var as int].ty),
            cx.enums@,
        )
}

/// 更新の列をつなげた列。
pub open spec fn flat_ups(bs: Seq<Seq<Update>>) -> Seq<Update>
    decreases bs.len(),
{
    if bs.len() == 0 {
        Seq::empty()
    } else {
        flat_ups(bs.drop_last()) + bs.last()
    }
}

/// 中核の更新の列 `ups` は、代入ごとの更新の列 `bs` をつなげたものである。
pub open spec fn upds_ok(sups: Seq<SUpdate>, cx: LowerCtx, bs: Seq<Seq<Update>>, ups: Seq<Update>) -> bool {
    &&& bs.len() == sups.len()
    &&& ups == flat_ups(bs)
    &&& forall|u: int| 0 <= u < sups.len() ==> #[trigger] block_ok(sups[u], cx, bs[u])
}

/// `acc` の `off` 番目からを `cs` で置き換える。
pub open spec fn put(acc: Seq<i64>, off: int, cs: Seq<i64>) -> Seq<i64> {
    Seq::new(acc.len(), |q: int| if off <= q < off + cs.len() { cs[q - off] } else { acc[q] })
}

/// 符号に変換できる値は、スロットの型の値である。
pub proof fn lemma_encode_in(ty: Type, x: Value, enums: Seq<i64>)
    requires
        encode_spec(enums, ty, x) is Ok,
    ensures
        in_slot(ty, x, enums),
{
}

/// どの列にも適用できない更新があれば、更新の列の適用は失敗する。
pub(crate) proof fn lemma_c_apply_none(ups: Seq<Update>, i: int, env: Env, enums: Seq<i64>, acc: Seq<i64>)
    requires
        0 <= i < ups.len(),
        forall|acc2: Seq<i64>| #[trigger] c_write(ups[i], env, enums, acc2) is None,
    ensures
        c_apply(ups, env, enums, acc) is None,
    decreases ups.len(),
{
    if i < ups.len() - 1 {
        assert(ups.drop_last()[i] == ups[i]);
        lemma_c_apply_none(ups.drop_last(), i, env, enums, acc);
    } else {
        if c_apply(ups.drop_last(), env, enums, acc) is Some {
            assert(c_write(ups.last(), env, enums, c_apply(ups.drop_last(), env, enums, acc)->Some_0) is None);
        }
    }
}

/// 連続するスロットへの更新がどれも成功すれば、その範囲が値の符号で置き換わる。
pub(crate) proof fn lemma_c_apply_put(ups: Seq<Update>, env: Env, enums: Seq<i64>, acc: Seq<i64>, off: int, xs: Seq<Value>)
    requires
        xs.len() == ups.len(),
        0 <= off,
        off + ups.len() <= acc.len(),
        off + ups.len() <= env.st_tys.len(),
        forall|j: int|
            0 <= j < ups.len() ==> #[trigger] ups[j].target == off + j && eval_spec(ups[j].expr, env) == Ok::<
                Value,
                ErrKind,
            >(xs[j]) && encode_spec(enums, env.st_tys[off + j], xs[j]) == Ok::<i64, ErrKind>(code_of(xs[j])),
    ensures
        c_apply(ups, env, enums, acc) == Some(put(acc, off, codes(xs))),
    decreases ups.len(),
{
    if ups.len() == 0 {
        assert(put(acc, off, codes(xs)) =~= acc);
    } else {
        let n = ups.len() - 1;
        let a = ups.drop_last();
        let b = xs.drop_last();
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] a[j].target == off + j && eval_spec(a[j].expr, env)
            == Ok::<Value, ErrKind>(b[j]) && encode_spec(enums, env.st_tys[off + j], b[j]) == Ok::<i64, ErrKind>(
            code_of(b[j]),
        ) by {
            assert(a[j] == ups[j]);
        }
        lemma_c_apply_put(a, env, enums, acc, off, b);
        let t = put(acc, off, codes(b));
        assert(ups.last() == ups[n]);
        assert(c_write(ups[n], env, enums, t) == Some(t.update(off + n, code_of(xs[n]))));
        assert(t.update(off + n, code_of(xs[n])) =~= put(acc, off, codes(xs)));
    }
}

/// 別々の状態変数のスロットは重ならない。
pub(crate) proof fn lemma_disjoint(st: Seq<Layout>, ts: Seq<STy>, i: int, x: int, enums: Seq<i64>)
    requires
        layouts_at(st, ts, enums),
        0 <= i < st.len(),
        0 <= x < st.len(),
        i != x,
    ensures
        st[i].offset + width(ts[i], enums) <= st[x].offset || st[x].offset + width(ts[x], enums) <= st[i].offset,
{
    assert(layout_at(st[i], ts, i, enums));
    assert(layout_at(st[x], ts, x, enums));
    if i < x {
        lemma_width_take(ts, i, i + 1, enums);
        lemma_width_take(ts, i + 1, x, enums);
    } else {
        lemma_width_take(ts, x, x + 1, enums);
        lemma_width_take(ts, x + 1, i, enums);
    }
}

/// 状態変数 `x` のスロットを型に属する値 `v` の符号で置き換えると、値の列の `x` 番目を `v` にした列を表す。
pub(crate) proof fn lemma_rel_put(
    st: Seq<Layout>,
    vs: Seq<SVal>,
    tys: Seq<Type>,
    xs: Seq<i64>,
    ts: Seq<STy>,
    enums: Seq<i64>,
    x: int,
    v: SVal,
)
    requires
        rel(st, vs, tys, xs, enums),
        layouts_at(st, ts, enums),
        tys == slot_tys_seq(ts, enums),
        wf_stypes(ts, enums),
        smalls(ts),
        0 <= x < ts.len(),
        member(v, ts[x], enums),
    ensures
        rel(st, vs.update(x, v), tys, put(xs, st[x].offset as int, codes(enc(v, ts[x], enums))), enums),
{
    let t = ts[x];
    let off = st[x].offset as int;
    let e = enc(v, t, enums);
    let cs = codes(e);
    let w = width(t, enums) as int;
    let ys = put(xs, off, cs);
    let ws = vs.update(x, v);
    assert(layout_at(st[x], ts, x, enums));
    lemma_wf_index(ts, x, enums);
    lemma_member_in(v, t, enums);
    lemma_enc_len(v, t, enums);
    lemma_slot_tys_len(t, enums);
    lemma_slot_tys_seq_sub(ts, x, enums);
    lemma_slot_tys_seq_len(ts, enums);
    assert(tys.len() == xs.len());
    assert forall|q: int| off <= q < off + w implies tys[q] == #[trigger] slot_tys(t, enums)[q - off] && in_slot(
        tys[q],
        e[q - off],
        enums,
    ) && in_type(enums, tys[q], ys[q]) && decode(tys[q], ys[q]) == e[q - off] by {
        assert(tys.subrange(off, off + w)[q - off] == tys[q]);
        assert(in_slot(slot_tys(t, enums)[q - off], e[q - off], enums));
        lemma_code_in(tys[q], e[q - off], enums);
    }
    assert forall|q: int| 0 <= q < tys.len() implies in_type(enums, #[trigger] tys[q], ys[q]) by {
        if off <= q < off + w {
            assert(slot_tys(t, enums)[q - off] == tys[q]);
        }
    }
    assert forall|i: int| 0 <= i < st.len() implies #[trigger] layout_ok(st[i], ws[i], tys, ys, enums) by {
        if i == x {
            assert forall|j: int| 0 <= j < w implies #[trigger] lookup(tys, ys, (st[i].offset + j) as usize) == Ok::<
                Value,
                ErrKind,
            >(e[j]) by {
                assert(slot_tys(t, enums)[(off + j) - off] == tys[off + j]);
            }
        } else {
            assert(layout_ok(st[i], vs[i], tys, xs, enums));
            assert(layout_at(st[i], ts, i, enums));
            lemma_disjoint(st, ts, i, x, enums);
            let ti = sty(st[i].ty);
            assert forall|j: int| 0 <= j < width(ti, enums) implies #[trigger] lookup(
                tys,
                ys,
                (st[i].offset + j) as usize,
            ) == Ok::<Value, ErrKind>(enc(ws[i], ti, enums)[j]) by {
                assert(lookup(tys, xs, (st[i].offset + j) as usize) == Ok::<Value, ErrKind>(enc(vs[i], ti, enums)[j]));
            }
        }
    }
}

/// 1つの代入と、その下ろしの更新の列の対応。
pub(crate) proof fn lemma_block(
    su: SUpdate,
    cx: LowerCtx,
    blk: Seq<Update>,
    env: Env,
    se: SEnv,
    acc_s: Seq<SVal>,
    acc_c: Seq<i64>,
    ts: Seq<STy>,
)
    requires
        block_ok(su, cx, blk),
        top_ok(cx, env, se, Seq::empty(), 0),
        layouts_at(cx.states->Some_0@, ts, cx.enums@),
        env.st_tys == slot_tys_seq(ts, cx.enums@),
        wf_stypes(ts, cx.enums@),
        smalls(ts),
        rel(cx.states->Some_0@, acc_s, env.st_tys, acc_c, cx.enums@),
    ensures
        match (s_write(su, se, ts, acc_s), c_apply(blk, env, cx.enums@, acc_c)) {
            (None, None) => true,
            (Some(t), Some(y)) => rel(cx.states->Some_0@, t, env.st_tys, y, cx.enums@),
            _ => false,
        },
{
    let enums = cx.enums@;
    let st = cx.states->Some_0@;
    let x = su.var as int;
    let l = st[x];
    let t = ts[x];
    let off = l.offset as int;
    assert(layout_at(l, ts, x, enums));
    lemma_wf_index(ts, x, enums);
    lemma_slot_tys_len(t, enums);
    lemma_slot_tys_seq_sub(ts, x, enums);
    lemma_slot_tys_seq_len(ts, enums);
    let w = width(t, enums) as int;
    let tys = env.st_tys;
    let out = upd_exprs(blk);
    let r = eval_src(su.expr, se, Seq::empty());
    assert(stored_result(r, out, env, Seq::empty(), t, enums));
    assert(se.enums == enums);
    match r {
        Err(k) => {
            assert(eval_l(out[0], env, Seq::empty()) == Err::<Value, ErrKind>(k));
            assert forall|acc2: Seq<i64>| #[trigger] c_write(blk[0], env, enums, acc2) is None by {
                assert(eval_spec(blk[0].expr, env) == Err::<Value, ErrKind>(k));
            }
            lemma_c_apply_none(blk, 0, env, enums, acc_c);
        },
        Ok(v) => {
            let e = enc(v, t, enums);
            assert(out.len() == w);
            if member(v, t, enums) {
                lemma_member_in(v, t, enums);
                assert forall|j: int| 0 <= j < blk.len() implies #[trigger] blk[j].target == off + j && eval_spec(
                    blk[j].expr,
                    env,
                ) == Ok::<Value, ErrKind>(e[j]) && encode_spec(enums, tys[off + j], e[j]) == Ok::<i64, ErrKind>(
                    code_of(e[j]),
                ) by {
                    assert(eval_l(out[j], env, Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                    assert(tys.subrange(off, off + w)[j] == tys[off + j]);
                    assert(in_slot(slot_tys(t, enums)[j], e[j], enums));
                    lemma_code_in(tys[off + j], e[j], enums);
                }
                assert(acc_c.len() == tys.len());
                lemma_c_apply_put(blk, env, enums, acc_c, off, e);
                lemma_rel_put(st, acc_s, tys, acc_c, ts, enums, x, v);
            } else {
                assert(!in_slots(e, slot_tys(t, enums), enums));
                let j = choose|j: int| 0 <= j < e.len() && !#[trigger] in_slot(slot_tys(t, enums)[j], e[j], enums);
                assert forall|acc2: Seq<i64>| #[trigger] c_write(blk[j], env, enums, acc2) is None by {
                    assert(eval_l(out[j], env, Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                    assert(tys.subrange(off, off + w)[j] == tys[off + j]);
                    if encode_spec(enums, tys[off + j], e[j]) is Ok {
                        lemma_encode_in(tys[off + j], e[j], enums);
                    }
                }
                lemma_c_apply_none(blk, j, env, enums, acc_c);
            }
        },
    }
}

/// 代入の列と、その下ろしの更新の列の対応。
pub(crate) proof fn lemma_upds(
    sups: Seq<SUpdate>,
    cx: LowerCtx,
    bs: Seq<Seq<Update>>,
    env: Env,
    se: SEnv,
    acc_s: Seq<SVal>,
    acc_c: Seq<i64>,
    ts: Seq<STy>,
)
    requires
        bs.len() == sups.len(),
        forall|u: int| 0 <= u < sups.len() ==> #[trigger] block_ok(sups[u], cx, bs[u]),
        top_ok(cx, env, se, Seq::empty(), 0),
        layouts_at(cx.states->Some_0@, ts, cx.enums@),
        env.st_tys == slot_tys_seq(ts, cx.enums@),
        wf_stypes(ts, cx.enums@),
        smalls(ts),
        rel(cx.states->Some_0@, acc_s, env.st_tys, acc_c, cx.enums@),
    ensures
        match (s_apply(sups, se, ts, acc_s), c_apply(flat_ups(bs), env, cx.enums@, acc_c)) {
            (None, None) => true,
            (Some(t), Some(y)) => rel(cx.states->Some_0@, t, env.st_tys, y, cx.enums@),
            _ => false,
        },
    decreases sups.len(),
{
    let enums = cx.enums@;
    if sups.len() > 0 {
        let a = sups.drop_last();
        let b = bs.drop_last();
        assert forall|u: int| 0 <= u < a.len() implies #[trigger] block_ok(a[u], cx, b[u]) by {
            assert(a[u] == sups[u]);
            assert(b[u] == bs[u]);
        }
        lemma_upds(a, cx, b, env, se, acc_s, acc_c, ts);
        lemma_c_apply_concat(flat_ups(b), bs.last(), env, enums, acc_c);
        match s_apply(a, se, ts, acc_s) {
            None => {},
            Some(t) => {
                let y = c_apply(flat_ups(b), env, enums, acc_c)->Some_0;
                assert(block_ok(sups[sups.len() - 1], cx, bs[bs.len() - 1]));
                lemma_block(sups.last(), cx, bs.last(), env, se, t, y, ts);
            },
        }
    }
}

/// 中核の更新の適用（前からの再帰）は、[`c_apply`] と同じ結果になる。
pub(crate) proof fn lemma_apply_c(m: RawModel, a: int, env: Env, k: nat, acc: Seq<i64>)
    requires
        0 <= a < m.actions@.len(),
        env.st_tys == m.state_types@,
        k <= m.actions@[a].updates@.len(),
    ensures
        match apply_updates(m, a, env, k, acc) {
            Ok(t) => c_apply(
                m.actions@[a].updates@.subrange(k as int, m.actions@[a].updates@.len() as int),
                env,
                m.enums@,
                acc,
            ) == Some(t),
            Err(_) => c_apply(
                m.actions@[a].updates@.subrange(k as int, m.actions@[a].updates@.len() as int),
                env,
                m.enums@,
                acc,
            ) is None,
        },
    decreases m.actions@[a].updates@.len() - k,
{
    let ups = m.actions@[a].updates@;
    let n = ups.len() as int;
    if k == n {
        assert(ups.subrange(k as int, n) =~= Seq::<Update>::empty());
    } else {
        let u = ups[k as int];
        assert(ups.subrange(k as int, n) =~= seq![u] + ups.subrange(k + 1 as int, n));
        lemma_c_apply_first(u, ups.subrange(k + 1 as int, n), env, m.enums@, acc);
        match c_write(u, env, m.enums@, acc) {
            None => {},
            Some(t) => {
                lemma_apply_c(m, a, env, k + 1, t);
            },
        }
    }
}

/// 出力の下ろし。出力の型はBool、Int、Enumのどれかで、中核の出力の型はそのスロットの型である。
pub open spec fn out_ok(so: Option<SOutput>, cx: LowerCtx, mo: Option<Output>) -> bool {
    match (so, mo) {
        (None, None) => true,
        (Some(s), Some(o)) => {
            &&& (sty(s.ty) is Bool || sty(s.ty) is Int || sty(s.ty) is Enum)
            &&& o.ty == slot_tys(sty(s.ty), cx.enums@)[0]
            &&& forall|env: Env, se: SEnv|
                #[trigger] top_ok(cx, env, se, Seq::empty(), 0) ==> stored_result(
                    eval_src(s.expr, se, Seq::empty()),
                    seq![o.expr],
                    env,
                    Seq::empty(),
                    sty(s.ty),
                    cx.enums@,
                )
        },
        _ => false,
    }
}

/// 値の上の出力と、中核の出力の符号の対応。
pub open spec fn out_rel(so: Option<SOutput>, o: Option<SVal>, y: Option<i64>, enums: Seq<i64>) -> bool {
    match (o, y) {
        (None, None) => so is None,
        (Some(v), Some(c)) => so matches Some(s) && member(v, sty(s.ty), enums) && c == code_of(
            enc(v, sty(s.ty), enums)[0],
        ),
        _ => false,
    }
}

pub(crate) proof fn lemma_out(so: Option<SOutput>, cx: LowerCtx, m: RawModel, a: int, env: Env, se: SEnv)
    requires
        0 <= a < m.actions@.len(),
        out_ok(so, cx, m.actions@[a].output),
        top_ok(cx, env, se, Seq::empty(), 0),
        m.enums@ == cx.enums@,
    ensures
        match (s_output(so, se), output_spec(m, a, env)) {
            (None, Err(_)) => true,
            (Some(o), Ok(y)) => out_rel(so, o, y, cx.enums@),
            _ => false,
        },
{
    let enums = cx.enums@;
    assert(se.enums == enums);
    match so {
        None => {},
        Some(s) => {
            let o = m.actions@[a].output->Some_0;
            let t = sty(s.ty);
            let r = eval_src(s.expr, se, Seq::empty());
            assert(stored_result(r, seq![o.expr], env, Seq::empty(), t, enums));
            match r {
                Err(k) => {
                    assert(seq![o.expr][0] == o.expr);
                },
                Ok(v) => {
                    assert(seq![o.expr][0] == o.expr);
                    let e = enc(v, t, enums);
                    assert(eval_l(o.expr, env, Seq::empty()) == Ok::<Value, ErrKind>(e[0]));
                    if member(v, t, enums) {
                        assert(wf_stype(t, enums)) by {
                            lemma_enc_len(v, t, enums);
                        }
                        lemma_member_in(v, t, enums);
                        lemma_code_in(o.ty, e[0], enums);
                    } else {
                        if encode_spec(enums, o.ty, e[0]) is Ok {
                            lemma_encode_in(o.ty, e[0], enums);
                            lemma_slot_tys_len(t, enums);
                            assert(in_slots(e, slot_tys(t, enums), enums));
                        }
                    }
                },
            }
        },
    }
}

/// 下ろしの失敗の理由。
pub enum Fault {
    /// 式を下ろせない（型が合わない、または参照が未定義）。
    Lower,
    /// 式の評価に失敗した。範囲外の値は `OutOfRange` である。
    Eval(ErrKind),
    /// 局所変数の束縛の深さが上限に達した（式が大きすぎる）。
    Depth,
}

/// 下ろしの失敗の場所。
pub enum LowerError {
    /// 状態変数の型が整形式でないか、符号化が大きすぎる。
    State(usize),
    /// 定数。
    Const(usize, Fault),
    /// 状態変数 `.0` の `.1` 番目の初期値の候補。
    Init(usize, usize, Fault),
    /// 初期値の候補の列の数が状態変数の数と違うか、候補の組み合わせが多すぎる。
    InitCount,
    /// 初期条件。
    Constraint(Fault),
    /// 初期条件を満たす初期状態がない。
    NoInit,
    /// 操作 `.0` の `.1` 番目の引数の型。
    Args(usize, usize),
    /// 操作のguard。
    Guard(usize),
    /// 操作 `.0` の `.1` 番目の代入。
    Update(usize, usize),
    /// 操作の出力。
    Output(usize),
    /// 不変条件。
    Invariant(usize),
    /// 遷移契約。
    Contract(usize),
    /// 終端条件。
    Terminal,
    /// モデルの式が型を持たないか、大きさの条件を満たさない（[`crate::model_total::model_typed`] が偽）。
    Type,
    /// 局所変数の束縛の深さが上限に達した（式が大きすぎる）。
    Depth,
    /// 詳細化の検査の写像の式（添字）が、置く場所の型を持たない。
    Mapping(usize),
}

/// 型の誤り。`fmspec-ir` の型検査を通ったモデルでは起きない。
pub open spec fn type_err(e: LowerError) -> bool {
    e is Type || e is State || e is Args
}

/// 利用者の誤り（値の評価の失敗、初期状態の数、式の大きさ）。これ以外は内部の誤りである。
pub open spec fn user_err(e: LowerError) -> bool {
    match e {
        LowerError::Const(_, f) => !(f is Lower),
        LowerError::Init(_, _, f) => !(f is Lower),
        LowerError::Constraint(f) => !(f is Lower),
        LowerError::InitCount => true,
        LowerError::NoInit => true,
        LowerError::Depth => true,
        _ => false,
    }
}

/// 中核のguard `g` は、引数が正規形でなければ偽で、正規形なら値の上のguardと同じ真偽になる。
pub open spec fn guard_ok(sa: SAction, cx: LowerCtx, g: Expr) -> bool {
    let doms = slot_tys_seq(stys(sa.args@), cx.enums@);
    &&& forall|env: Env|
        dom_ok(env, doms, cx.enums@) && !canon_from(cx.args@, 0, env, cx.enums@) ==> #[trigger] eval_spec(g, env)
            == Ok::<Value, ErrKind>(Value::Bool(false))
    &&& forall|env: Env, se: SEnv|
        #[trigger] env_rel(cx, env, se) && dom_ok(env, doms, cx.enums@) ==> prop_spec(g, env) == src_bool(
            eval_src(sa.guard, se, Seq::empty()),
        )
}

/// 中核の操作 `m` は、操作 `sa` を文脈 `cx` で下ろしたものである。
pub open spec fn act_ok(sa: SAction, cx: LowerCtx, m: Action) -> bool {
    &&& m.n_params == sa.n_params
    &&& m.domains@ == slot_tys_seq(stys(sa.args@), cx.enums@)
    &&& guard_ok(sa, cx, m.guard)
    &&& exists|bs: Seq<Seq<Update>>| #[trigger] upds_ok(sa.updates@, cx, bs, m.updates@)
    &&& out_ok(sa.output, cx, m.output)
}

/// 各更新式は、対象の状態変数のスロットの型を持つ。
#[verifier::opaque]
pub open spec fn ups_typed(ups: Seq<Update>, tv: TyEnv) -> bool {
    forall|k: int|
        0 <= k < ups.len() ==> (#[trigger] ups[k]).target < tv.st_tys.len() && has_ty(
            ups[k].expr,
            tv,
            Seq::empty(),
            crate::typing::ety_of(tv.st_tys[ups[k].target as int]),
        )
}

/// 更新の列に、型の付く式で状態変数 `vi` のスロットへの更新を加えても、各更新式は対象の型を持つ。
pub(crate) proof fn lemma_ups_typed(
    before: Seq<Update>,
    ups: Seq<Update>,
    out: Seq<Expr>,
    sts: Seq<Layout>,
    vi: int,
    tv: TyEnv,
    enums: Seq<i64>,
)
    requires
        layouts_at(sts, layout_tys(sts), enums),
        tv.st_tys == slot_tys_seq(layout_tys(sts), enums),
        0 <= vi < sts.len(),
        out.len() == width(sty(sts[vi].ty), enums),
        crate::lower_types::typed(out, crate::lower_types::etys(slot_tys(sty(sts[vi].ty), enums)), tv, Seq::empty()),
        ups.len() == before.len() + out.len(),
        ups.subrange(0, before.len() as int) == before,
        forall|k: int| 0 <= k < out.len() ==> #[trigger] ups[before.len() + k].target == sts[vi].offset + k && ups[before.len() + k].expr == out[k],
        ups_typed(before, tv),
    ensures
        ups_typed(ups, tv),
{
    reveal(ups_typed);
    let ys = crate::lower_types::etys(slot_tys(sty(sts[vi].ty), enums));
    assert forall|k: int| 0 <= k < ups.len() implies (#[trigger] ups[k]).target < tv.st_tys.len() && has_ty(
        ups[k].expr,
        tv,
        Seq::empty(),
        crate::typing::ety_of(tv.st_tys[ups[k].target as int]),
    ) by {
        if k < before.len() {
            assert(ups[k] == ups.subrange(0, before.len() as int)[k]);
            assert(ups[k] == before[k]);
        } else {
            let j = k - before.len();
            assert(ups[before.len() + j].target == sts[vi].offset + j);
            assert(ups[before.len() + j].expr == out[j]);
            crate::lower_types::lemma_layout_slot(sts, vi, j, enums);
            assert(has_ty(out[j], tv, Seq::empty(), ys[j]));
        }
    }
}

/// 中核の操作 `m` の guard、更新式、出力式は、文脈 `t` で型が付く。
pub open spec fn act_typed(m: Action, t: TyEnv) -> bool {
    &&& has_ty(m.guard, t, Seq::empty(), ETy::Bool)
    &&& forall|u: int|
        0 <= u < m.updates@.len() ==> (#[trigger] m.updates@[u]).target < t.st_tys.len() && has_ty(
            m.updates@[u].expr,
            t,
            Seq::empty(),
            crate::typing::ety_of(t.st_tys[m.updates@[u].target as int]),
        )
    &&& m.output matches Some(o) ==> has_ty(o.expr, t, Seq::empty(), crate::typing::ety_of(o.ty))
}

/// 位置 `off` からのスロットへの更新を、`ups` の後ろに加える。
pub(crate) fn push_block(ups: &mut Vec<Update>, off: usize, out: &Vec<Expr>) -> (r: bool)
    ensures
        off + out@.len() <= usize::MAX ==> r,
        r ==> final(ups)@.len() == old(ups)@.len() + out@.len(),
        r ==> final(ups)@.subrange(0, old(ups)@.len() as int) == old(ups)@,
        r ==> forall|k: int|
            0 <= k < out@.len() ==> #[trigger] final(ups)@[old(ups)@.len() + k].target == off + k && final(ups)@[old(
                ups,
            )@.len() + k].expr == out@[k],
{
    let ghost before = ups@;
    let mut j = 0;
    while j < out.len()
        invariant
            j <= out@.len(),
            ups@.len() == before.len() + j,
            ups@.subrange(0, before.len() as int) == before,
            forall|k: int|
                0 <= k < j ==> #[trigger] ups@[before.len() + k].target == off + k && ups@[before.len() + k].expr
                    == out@[k],
        decreases out@.len() - j,
    {
        let target = match off.checked_add(j) {
            Some(t) => t,
            None => return false,
        };
        ups.push(Update { target, expr: copy_expr(&out[j]) });
        proof {
            assert(ups@.subrange(0, before.len() as int) =~= before);
        }
        j += 1;
    }
    true
}

/// 値の上の遷移の結果と、中核の遷移の結果の対応。
pub open spec fn step_rel(
    ss: SStep,
    cs: Step,
    st: Seq<Layout>,
    tys: Seq<Type>,
    so: Option<SOutput>,
    enums: Seq<i64>,
) -> bool {
    match (ss, cs) {
        (SStep::Disabled, Step::Disabled) => true,
        (SStep::Fail, Step::Fail(_, _)) => true,
        (SStep::To(t, o), Step::To(y, x)) => rel(st, t, tys, y, enums) && out_rel(so, o, x, enums),
        _ => false,
    }
}

/// 正規形でない引数では、下ろした操作は無効である。
pub proof fn lemma_step_off(sa: SAction, m: RawModel, a: int, cx: LowerCtx, ps: Seq<i64>, xs: Seq<i64>)
    requires
        0 <= a < m.actions@.len(),
        act_ok(sa, cx, m.actions@[a]),
        vals_ok(cx.enums@, m.actions@[a].domains@, xs),
        !canon_from(cx.args@, 0, act_env(m, a, xs, ps), cx.enums@),
    ensures
        step_spec(m, a, xs, ps) == Step::Disabled,
{
    let env = act_env(m, a, xs, ps);
    assert(dom_ok(env, slot_tys_seq(stys(sa.args@), cx.enums@), cx.enums@));
    assert(eval_spec(m.actions@[a].guard, env) == Ok::<Value, ErrKind>(Value::Bool(false)));
}

/// 値の列を表す状態と引数での遷移は、値の上の遷移に対応する。
pub proof fn lemma_step(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    a: int,
    cx: LowerCtx,
    p: Seq<SVal>,
    ps: Seq<i64>,
    vs: Seq<SVal>,
    xs: Seq<i64>,
)
    requires
        0 <= a < sm.actions@.len(),
        0 <= a < m.actions@.len(),
        act_ok(sm.actions@[a], cx, m.actions@[a]),
        cx.states is Some,
        layouts_at(cx.states->Some_0@, s_state_tys(sm), sm.enums@),
        wf_stypes(s_state_tys(sm), sm.enums@),
        smalls(s_state_tys(sm)),
        m.state_types@ == slot_tys_seq(s_state_tys(sm), sm.enums@),
        m.enums@ == sm.enums@,
        cx.enums@ == sm.enums@,
        env_rel(cx, act_env(m, a, xs, ps), s_env(sm, cv, p, vs, Seq::empty(), None)),
        vals_ok(sm.enums@, m.state_types@, ps),
        vals_ok(sm.enums@, m.actions@[a].domains@, xs),
    ensures
        step_rel(
            s_step(sm, cv, a, vs, p),
            step_spec(m, a, xs, ps),
            cx.states->Some_0@,
            m.state_types@,
            sm.actions@[a].output,
            sm.enums@,
        ),
{
    let sa = sm.actions@[a];
    let enums = sm.enums@;
    let ts = s_state_tys(sm);
    let env = act_env(m, a, xs, ps);
    let se = s_env(sm, cv, p, vs, Seq::empty(), None);
    assert(dom_ok(env, slot_tys_seq(stys(sa.args@), enums), enums));
    assert(prop_spec(m.actions@[a].guard, env) == src_bool(eval_src(sa.guard, se, Seq::empty())));
    assert(top_ok(cx, env, se, Seq::empty(), 0));
    let ups = m.actions@[a].updates@;
    lemma_apply_c(m, a, env, 0, ps);
    assert(ups.subrange(0, ups.len() as int) =~= ups);
    let bs = choose|bs: Seq<Seq<Update>>| #[trigger] upds_ok(sa.updates@, cx, bs, ups);
    lemma_upds(sa.updates@, cx, bs, env, se, p, ps, ts);
    lemma_out(sa.output, cx, m, a, env, se);
}

} // verus!
