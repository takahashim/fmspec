//! 操作の下ろし。名前を解決したIRの操作（`SAction`）を、中核の操作に下ろす。

use crate::canon::slot_types_list;
use crate::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_width_pos, sty, stys, to_xty, wf_stypes, width};
#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, eval_spec, prop_spec, Env};
#[cfg(verus_keep_ghost)]
use crate::limits::{lim_s, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layout_at, layouts_at};
use crate::lower_ctx::{Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{has_ty, layout_tys, slot_tys, slot_tys_seq};
use crate::lowering::{lower_prop, lower_stored};
use crate::model::{Action, Output, Type, Update};
#[cfg(verus_keep_ghost)]
use crate::model_total::sa_typed;
#[cfg(verus_keep_ghost)]
use crate::preserve::{env_rel, prop_result};
#[cfg(verus_keep_ghost)]
use crate::smodel::{act_ok, act_typed, block_ok, dom_ok, flat_ups, lemma_rel_canon};
use crate::smodel::{guard_fold, push_block, LowerError, SAction};
#[cfg(verus_keep_ghost)]
use crate::smodel::{lemma_ups_typed, styped, upd_exprs, upds_ok, ups_typed};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, src_bool, SEnv};
use crate::stype_exec::stype_width;
#[cfg(verus_keep_ghost)]
use crate::total::{cx_wf, layout_wf, sctx};
#[cfg(verus_keep_ghost)]
use crate::typing::ETy;
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

} // verus!
