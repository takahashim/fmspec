//! 下ろしたモデルの整形式性（計画書 docs/plans/lowering_totality.md の手順6）。
//!
//! 手順6a：`wf` のうち式の型以外（スロットの型、初期状態、引数の数、代入先、出力の型）。
//! 名前を解決したモデルが [`sm_wf`]（ラベルのない列挙型がなく、同じ操作の代入先が重ならず、
//! 公開引数のスロットの数が引数のスロットの数以下）を満たすことを前提にする。

#[cfg(verus_keep_ghost)]
use crate::action_lower::{act_ok, block_ok, flat_ups, upds_ok};
#[cfg(verus_keep_ghost)]
use crate::encoding::{sty, stys, wf_stype, wf_stypes, width, width_sum, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::limits::{small, smalls};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layout_at, layouts_at, Layout, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_slot_tys_seq_len, slot_tys, slot_tys_seq, ty_repeat};
#[cfg(verus_keep_ghost)]
use crate::model::{Action, Contract, RawModel, Type, Update};
#[cfg(verus_keep_ghost)]
use crate::model_safe::{ctx_is, init_ok, init_src, prop_low};
#[cfg(verus_keep_ghost)]
use crate::model_total::{action_typed, model_typed};
#[cfg(verus_keep_ghost)]
use crate::smodel::{s_arg_tys, SModel};
#[cfg(verus_keep_ghost)]
use crate::state_enc::state_ok;
#[cfg(verus_keep_ghost)]
use crate::typing::{type_ok, types_ok, update_fresh};
use vstd::prelude::*;

verus! {

/// 名前を解決したモデルの条件のうち、`model_typed` に含まれず、IR検証が利用者の誤りとして報告するもの。
pub open spec fn sm_wf(sm: SModel) -> bool {
    &&& forall|i: int| 0 <= i < sm.enums@.len() ==> 1 <= #[trigger] sm.enums@[i]
    &&& forall|a: int|
        0 <= a < sm.actions@.len() ==> (#[trigger] sm.actions@[a]).n_params <= width_sum(
            stys(sm.actions@[a].args@),
            sm.enums@,
        )
    &&& forall|a: int, u: int, w: int|
        0 <= a < sm.actions@.len() && 0 <= w < u < sm.actions@[a].updates@.len() ==> (
        #[trigger] sm.actions@[a].updates@[u]).var != (#[trigger] sm.actions@[a].updates@[w]).var
}

// ---- スロットの型 ----

pub proof fn lemma_types_ok_concat(enums: Seq<i64>, a: Seq<Type>, b: Seq<Type>)
    requires
        types_ok(enums, a),
        types_ok(enums, b),
    ensures
        types_ok(enums, a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies type_ok(enums, #[trigger] (a + b)[i]) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

pub proof fn lemma_types_ok_repeat(enums: Seq<i64>, xs: Seq<Type>, n: nat)
    requires
        types_ok(enums, xs),
    ensures
        types_ok(enums, ty_repeat(xs, n)),
    decreases n,
{
    if n > 0 {
        lemma_types_ok_repeat(enums, xs, (n - 1) as nat);
        lemma_types_ok_concat(enums, ty_repeat(xs, (n - 1) as nat), xs);
    }
}

/// 整形式な格納の型のスロットの型は、整形式である。
pub proof fn lemma_slot_tys_ok(t: STy, enums: Seq<i64>)
    requires
        wf_stype(t, enums),
        small(t),
    ensures
        types_ok(enums, slot_tys(t, enums)),
    decreases t, 1nat,
{
    match t {
        STy::Tuple(ts) => lemma_slot_tys_seq_ok(ts, enums),
        STy::Record(_, ts) => lemma_slot_tys_seq_ok(ts, enums),
        STy::Option(x) => {
            lemma_slot_tys_ok(*x, enums);
            lemma_types_ok_concat(enums, seq![Type::Bool], slot_tys(*x, enums));
        },
        STy::Set(e) => {
            lemma_types_ok_repeat(enums, seq![Type::Bool], crate::encoding::keys_or_zero(*e, enums));
        },
        STy::Map(k, v) => {
            lemma_slot_tys_ok(*v, enums);
            lemma_types_ok_concat(enums, seq![Type::Bool], slot_tys(*v, enums));
            lemma_types_ok_repeat(
                enums,
                seq![Type::Bool] + slot_tys(*v, enums),
                crate::encoding::keys_or_zero(*k, enums),
            );
        },
        STy::List(e, max) => {
            lemma_slot_tys_ok(*e, enums);
            lemma_types_ok_repeat(enums, slot_tys(*e, enums), max as nat);
            lemma_types_ok_concat(
                enums,
                seq![Type::Int(0, max as i64)],
                ty_repeat(slot_tys(*e, enums), max as nat),
            );
        },
        _ => {},
    }
}

pub proof fn lemma_slot_tys_seq_ok(ts: Seq<STy>, enums: Seq<i64>)
    requires
        wf_stypes(ts, enums),
        smalls(ts),
    ensures
        types_ok(enums, slot_tys_seq(ts, enums)),
    decreases ts, 0nat,
{
    if ts.len() > 0 {
        let a = ts.drop_last();
        assert(wf_stypes(a, enums) && wf_stype(ts.last(), enums));
        assert(smalls(a) && small(ts.last()));
        lemma_slot_tys_seq_ok(a, enums);
        lemma_slot_tys_ok(ts.last(), enums);
        lemma_types_ok_concat(enums, slot_tys_seq(a, enums), slot_tys(ts.last(), enums));
    }
}

// ---- 位置 ----

/// 位置の列で、`i < j` の型の位置の範囲は重ならない。
pub proof fn lemma_layouts_disjoint(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>, i: int, j: int)
    requires
        layouts_at(ls, ts, enums),
        0 <= i < j < ls.len(),
    ensures
        ls[i].offset + width(ts[i], enums) <= ls[j].offset,
    decreases j - i,
{
    assert(layout_at(ls[i], ts, i, enums));
    assert(layout_at(ls[j], ts, j, enums));
    assert(ts.take(i + 1).drop_last() =~= ts.take(i));
    assert(ts.take(i + 1).last() == ts[i]);
    crate::limits::lemma_width_sum_prefix(ts.take(j), enums, i + 1);
    assert(ts.take(j).take(i + 1) =~= ts.take(i + 1));
}


// ---- 代入先 ----

/// つなげた更新の列の `k` 番目は、`u` 番目の列の `j` 番目である。
pub proof fn lemma_flat_at(bs: Seq<Seq<Update>>, k: int) -> (r: (int, int))
    requires
        0 <= k < flat_ups(bs).len(),
    ensures
        0 <= r.0 < bs.len(),
        0 <= r.1 < bs[r.0].len(),
        flat_ups(bs)[k] == bs[r.0][r.1],
        k == flat_ups(bs.take(r.0)).len() + r.1,
    decreases bs.len(),
{
    let a = bs.drop_last();
    let n = flat_ups(a).len() as int;
    if k < n {
        let (u, j) = lemma_flat_at(a, k);
        assert(a.take(u) =~= bs.take(u));
        assert(a[u] == bs[u]);
        (u, j)
    } else {
        let u = bs.len() - 1;
        assert(bs.take(u) =~= a);
        (u, k - n)
    }
}

/// 操作 `a` の、式の型以外の整形式性。
pub open spec fn action_frame(m: RawModel, a: int) -> bool {
    let act = m.actions@[a];
    &&& act.n_params <= act.domains@.len()
    &&& types_ok(m.enums@, act.domains@)
    &&& forall|u: int| 0 <= u < act.updates@.len() ==> (#[trigger] act.updates@[u]).target < m.state_types@.len()
    &&& forall|u: int| 0 <= u < act.updates@.len() ==> #[trigger] update_fresh(m, a, u)
    &&& match act.output {
        None => true,
        Some(o) => type_ok(m.enums@, o.ty),
    }
}

/// 下ろした操作は、式の型以外で整形式である。
pub proof fn lemma_action_frame(sm: SModel, m: RawModel, a: int, cx: LowerCtx)
    requires
        sm_wf(sm),
        0 <= a < sm.actions@.len(),
        a < m.actions@.len(),
        act_ok(sm.actions@[a], cx, m.actions@[a]),
        cx.states is Some,
        layouts_at(cx.states->Some_0@, stys(sm.states@), sm.enums@),
        cx.enums@ == sm.enums@,
        m.enums@ == sm.enums@,
        m.state_types@.len() == width_sum(stys(sm.states@), sm.enums@),
        wf_stypes(stys(sm.actions@[a].args@), sm.enums@),
        smalls(stys(sm.actions@[a].args@)),
        sm.actions@[a].output matches Some(o) ==> wf_stype(sty(o.ty), sm.enums@) && small(sty(o.ty)),
    ensures
        action_frame(m, a),
{
    let sa = sm.actions@[a];
    let act = m.actions@[a];
    let enums = sm.enums@;
    let st = cx.states->Some_0@;
    let ts = stys(sm.states@);
    lemma_slot_tys_seq_ok(stys(sa.args@), enums);
    lemma_slot_tys_seq_len(stys(sa.args@), enums);
    crate::encoding::lemma_stys(sm.states@);
    let bs = choose|bs: Seq<Seq<Update>>| #[trigger] upds_ok(sa.updates@, cx, bs, act.updates@);
    assert(upds_ok(sa.updates@, cx, bs, act.updates@));
    assert forall|k: int| 0 <= k < act.updates@.len() implies (#[trigger] act.updates@[k]).target
        < m.state_types@.len() by {
        let (u, j) = lemma_flat_at(bs, k);
        assert(block_ok(sa.updates@[u], cx, bs[u]));
        let v = sa.updates@[u].var as int;
        assert(layout_at(st[v], ts, v, enums));
        crate::smodel::lemma_layout_end(st, ts, enums, v);
    }
    assert forall|k: int| 0 <= k < act.updates@.len() implies #[trigger] update_fresh(m, a, k) by {
        assert forall|w: int| 0 <= w < k implies (#[trigger] m.actions@[a].updates@[w]).target
            != m.actions@[a].updates@[k].target by {
            let (u1, j1) = lemma_flat_at(bs, w);
            let (u2, j2) = lemma_flat_at(bs, k);
            assert(block_ok(sa.updates@[u1], cx, bs[u1]));
            assert(block_ok(sa.updates@[u2], cx, bs[u2]));
            let v1 = sa.updates@[u1].var as int;
            let v2 = sa.updates@[u2].var as int;
            assert(layout_at(st[v1], ts, v1, enums));
            assert(layout_at(st[v2], ts, v2, enums));
            if u1 != u2 {
                if u1 < u2 {
                    assert(sm.actions@[a].updates@[u2].var != sm.actions@[a].updates@[u1].var);
                } else {
                    assert(sm.actions@[a].updates@[u1].var != sm.actions@[a].updates@[u2].var);
                }
                if v1 < v2 {
                    lemma_layouts_disjoint(st, ts, enums, v1, v2);
                } else {
                    lemma_layouts_disjoint(st, ts, enums, v2, v1);
                }
            }
        }
    }
    match sa.output {
        Some(o) => {
            lemma_slot_tys_ok(sty(o.ty), enums);
        },
        None => {},
    }
}


// ---- モデル ----

/// `wf` のうち、式の型以外。
pub open spec fn wf_frame(m: RawModel) -> bool {
    &&& forall|i: int| 0 <= i < m.enums@.len() ==> 1 <= #[trigger] m.enums@[i]
    &&& types_ok(m.enums@, m.state_types@)
    &&& m.inits@.len() >= 1
    &&& forall|i: int| 0 <= i < m.inits@.len() ==> state_ok(m, (#[trigger] m.inits@[i])@)
    &&& forall|a: int| 0 <= a < m.actions@.len() ==> #[trigger] action_frame(m, a)
    &&& forall|c: int| 0 <= c < m.contracts@.len() ==> (#[trigger] m.contracts@[c]).action < m.actions@.len()
}

/// [`crate::model_lower::lower_model`] が組み立てたモデルは、式の型以外で整形式である。
pub proof fn lemma_model_frame(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    cs: Seq<LowerCtx>,
    ks: Seq<LowerCtx>,
)
    requires
        sm_wf(sm),
        model_typed(sm),
        m.enums@ == sm.enums@,
        m.state_types@ == slot_tys_seq(stys(sm.states@), sm.enums@),
        wf_stypes(stys(sm.states@), sm.enums@),
        smalls(stys(sm.states@)),
        m.inits@.len() >= 1,
        init_ok(sm, cv, m, st),
        layouts_at(st, stys(sm.states@), sm.enums@),
        m.actions@.len() == sm.actions@.len(),
        cs.len() == sm.actions@.len(),
        forall|a: int| 0 <= a < cs.len() ==> #[trigger] action_at(sm, cv, st, cs[a], a, m.actions@[a]),
        m.contracts@.len() == sm.contracts@.len(),
        ks.len() == sm.contracts@.len(),
        forall|k: int| 0 <= k < ks.len() ==> #[trigger] contract_at(sm, cv, st, ks[k], k, m.contracts@[k]),
    ensures
        wf_frame(m),
{
    let enums = sm.enums@;
    lemma_slot_tys_seq_ok(stys(sm.states@), enums);
    lemma_slot_tys_seq_len(stys(sm.states@), enums);
    assert forall|i: int| 0 <= i < m.inits@.len() implies state_ok(m, (#[trigger] m.inits@[i])@) by {
        assert(init_src(sm, cv, st, m.state_types@, m.inits@[i]@));
    }
    assert forall|a: int| 0 <= a < m.actions@.len() implies #[trigger] action_frame(m, a) by {
        assert(action_at(sm, cv, st, cs[a], a, m.actions@[a]));
        assert(action_typed(sm, a));
        match sm.actions@[a].output {
            Some(o) => {
                crate::limits::lemma_lim_small(sty(o.ty), enums);
            },
            None => {},
        }
        lemma_action_frame(sm, m, a, cs[a]);
    }
    assert forall|c: int| 0 <= c < m.contracts@.len() implies (#[trigger] m.contracts@[c]).action
        < m.actions@.len() by {
        assert(contract_at(sm, cv, st, ks[c], c, m.contracts@[c]));
    }
}

// ---- 式の型 ----

/// 位置の列が型の列の位置なら、型の列は位置の型の列である。
pub proof fn lemma_layout_tys_eq(ls: Seq<Layout>, ts: Seq<STy>, enums: Seq<i64>)
    requires
        layouts_at(ls, ts, enums),
    ensures
        crate::lower_types::layout_tys(ls) == ts,
        layouts_at(ls, crate::lower_types::layout_tys(ls), enums),
{
    assert(crate::lower_types::layout_tys(ls) =~= ts) by {
        assert forall|i: int| 0 <= i < ts.len() implies crate::lower_types::layout_tys(ls)[i] == ts[i] by {
            assert(layout_at(ls[i], ts, i, enums));
        }
    }
}

/// 状態と引数が型の列の位置で、定数が値の符号化なら、下ろしの文脈は型についての前提を満たす。
pub proof fn lemma_cx_tok(cx: LowerCtx, cv: Seq<SVal>, ts: Seq<STy>, ats: Seq<STy>)
    requires
        crate::total::cx_wf(cx),
        cx.states is Some,
        layouts_at(cx.states->Some_0@, ts, cx.enums@),
        layouts_at(cx.args@, ats, cx.enums@),
        crate::srel::consts_rel(cx.consts@, cv, cx.enums@),
    ensures
        crate::lower_types::cx_tok(cx),
{
    let enums = cx.enums@;
    lemma_layout_tys_eq(cx.states->Some_0@, ts, enums);
    lemma_layout_tys_eq(cx.args@, ats, enums);
    assert forall|i: int| 0 <= i < cx.consts@.len() implies #[trigger] crate::lower_types::in_slots(
        cx.consts@[i].slots@,
        slot_tys(sty(cx.consts@[i].ty), enums),
        enums,
    ) by {
        let t = sty(cx.consts@[i].ty);
        assert(crate::total::ok_s(t, enums));
        crate::limits::lemma_lim_small(t, enums);
        crate::canon::lemma_member_in(cv[i], t, enums);
    }
}

/// 型検査の文脈が等しければ、式の型は等しい。
pub open spec fn same_env(a: crate::typing::TyEnv, b: crate::typing::TyEnv) -> bool {
    &&& a.enums == b.enums
    &&& a.st_tys == b.st_tys
    &&& a.arg_tys == b.arg_tys
    &&& a.next == b.next
    &&& a.out == b.out
}

pub proof fn lemma_same_env(a: crate::typing::TyEnv, b: crate::typing::TyEnv)
    requires
        same_env(a, b),
    ensures
        a == b,
{
}

/// 型の枠が整形式で、各式が型を持てば、モデルは整形式である。
pub proof fn lemma_model_wf(m: RawModel)
    requires
        wf_frame(m),
        forall|a: int|
            0 <= a < m.actions@.len() ==> #[trigger] crate::action_lower::act_typed(m.actions@[a], crate::typing::act_tyenv(m, a)),
        forall|i: int|
            0 <= i < m.invariants@.len() ==> #[trigger] crate::lower_types::has_ty(
                m.invariants@[i],
                crate::typing::inv_tyenv(m),
                Seq::empty(),
                crate::typing::ETy::Bool,
            ),
        forall|c: int|
            0 <= c < m.contracts@.len() ==> #[trigger] crate::lower_types::has_ty(
                m.contracts@[c].expr,
                crate::typing::con_tyenv(m, m.contracts@[c].action as int),
                Seq::empty(),
                crate::typing::ETy::Bool,
            ),
        m.terminal matches Some(e) ==> crate::lower_types::has_ty(
            e,
            crate::typing::inv_tyenv(m),
            Seq::empty(),
            crate::typing::ETy::Bool,
        ),
    ensures
        crate::typing::wf(m),
{
    assert forall|a: int| 0 <= a < m.actions@.len() implies #[trigger] crate::typing::action_wf(m, a) by {
        assert(action_frame(m, a));
        assert(crate::action_lower::act_typed(m.actions@[a], crate::typing::act_tyenv(m, a)));
        assert forall|u: int| 0 <= u < m.actions@[a].updates@.len() implies #[trigger] crate::typing::update_wf(m, a, u) by {
            assert(m.actions@[a].updates@[u].target < m.state_types@.len());
        }
    }
    assert forall|c: int| 0 <= c < m.contracts@.len() implies #[trigger] crate::typing::contract_wf(m, c) by {
        assert(m.contracts@[c].action < m.actions@.len());
        assert(crate::lower_types::has_ty(
            m.contracts@[c].expr,
            crate::typing::con_tyenv(m, m.contracts@[c].action as int),
            Seq::empty(),
            crate::typing::ETy::Bool,
        ));
    }
    assert forall|i: int| 0 <= i < m.invariants@.len() implies #[trigger] crate::typing::invariant_wf(m, i) by {
        assert(crate::lower_types::has_ty(m.invariants@[i], crate::typing::inv_tyenv(m), Seq::empty(), crate::typing::ETy::Bool));
    }
}

/// 状態変数だけを参照できる文脈の型検査の文脈は、不変条件の文脈である。
pub proof fn lemma_inv_env(sm: SModel, cv: Seq<SVal>, stg: Seq<Layout>, sx: LowerCtx, m: RawModel)
    requires
        crate::model_safe::ctx_is(sx, sm.enums@, cv, stg, Seq::empty(), false, None),
        layouts_at(stg, stys(sm.states@), sm.enums@),
        m.enums@ == sm.enums@,
        m.state_types@ == slot_tys_seq(stys(sm.states@), sm.enums@),
    ensures
        crate::lower_types::lenv(sx) == crate::typing::inv_tyenv(m),
{
    lemma_layout_tys_eq(stg, stys(sm.states@), sm.enums@);
    assert(crate::lower_types::layout_tys(sx.args@) =~= Seq::<STy>::empty());
    assert(slot_tys_seq(Seq::<STy>::empty(), sm.enums@) =~= Seq::<Type>::empty());
    lemma_same_env(crate::lower_types::lenv(sx), crate::typing::inv_tyenv(m));
}

/// 操作の文脈の型検査の文脈は、下ろした操作の文脈である。
pub proof fn lemma_act_env(sm: SModel, cv: Seq<SVal>, stg: Seq<Layout>, cx: LowerCtx, a: int, m: RawModel)
    requires
        0 <= a < m.actions@.len(),
        action_at(sm, cv, stg, cx, a, m.actions@[a]),
        layouts_at(stg, stys(sm.states@), sm.enums@),
        m.enums@ == sm.enums@,
        m.state_types@ == slot_tys_seq(stys(sm.states@), sm.enums@),
    ensures
        crate::lower_types::lenv(cx) == crate::typing::act_tyenv(m, a),
{
    lemma_layout_tys_eq(stg, stys(sm.states@), sm.enums@);
    lemma_layout_tys_eq(cx.args@, crate::smodel::s_arg_tys(sm, a), sm.enums@);
    lemma_same_env(crate::lower_types::lenv(cx), crate::typing::act_tyenv(m, a));
}

/// 遷移契約の文脈の型検査の文脈は、下ろした遷移契約の文脈である。
pub proof fn lemma_con_env(
    sm: SModel,
    cv: Seq<SVal>,
    stg: Seq<Layout>,
    cx: LowerCtx,
    kx: LowerCtx,
    k: int,
    m: RawModel,
)
    requires
        0 <= k < sm.contracts@.len(),
        k < m.contracts@.len(),
        m.contracts@[k].action == sm.contracts@[k].action,
        (sm.contracts@[k].action as int) < m.actions@.len(),
        contract_at(sm, cv, stg, kx, k, m.contracts@[k]),
        action_at(sm, cv, stg, cx, sm.contracts@[k].action as int, m.actions@[sm.contracts@[k].action as int]),
        layouts_at(stg, stys(sm.states@), sm.enums@),
        m.enums@ == sm.enums@,
        m.state_types@ == slot_tys_seq(stys(sm.states@), sm.enums@),
    ensures
        crate::lower_types::lenv(kx) == crate::typing::con_tyenv(m, m.contracts@[k].action as int),
{
    let a = sm.contracts@[k].action as int;
    lemma_layout_tys_eq(stg, stys(sm.states@), sm.enums@);
    lemma_layout_tys_eq(kx.args@, crate::smodel::s_arg_tys(sm, a), sm.enums@);
    assert(crate::action_lower::out_ok(sm.actions@[a].output, cx, m.actions@[a].output));
    lemma_same_env(crate::lower_types::lenv(kx), crate::typing::con_tyenv(m, a));
}

/// 操作 `a` を文脈 `cx` で下ろした結果 `act` の性質。
pub open spec fn action_at(sm: SModel, cv: Seq<SVal>, st: Seq<Layout>, cx: LowerCtx, a: int, act: Action) -> bool {
    let ts = s_arg_tys(sm, a);
    &&& ctx_is(cx, sm.enums@, cv, st, cx.args@, false, None)
    &&& layouts_at(cx.args@, ts, sm.enums@)
    &&& wf_stypes(ts, sm.enums@)
    &&& smalls(ts)
    &&& act_ok(sm.actions@[a], cx, act)
}

/// 遷移契約 `k` を文脈 `kx` で下ろした結果 `con` の性質。
pub open spec fn contract_at(sm: SModel, cv: Seq<SVal>, st: Seq<Layout>, kx: LowerCtx, k: int, con: Contract) -> bool {
    let a = sm.contracts@[k].action as int;
    &&& con.action == sm.contracts@[k].action
    &&& a < sm.actions@.len()
    &&& ctx_is(kx, sm.enums@, cv, st, kx.args@, true, sm.actions@[a].output)
    &&& layouts_at(kx.args@, s_arg_tys(sm, a), sm.enums@)
    &&& prop_low(sm.contracts@[k].expr, kx, con.expr)
}

} // verus!
