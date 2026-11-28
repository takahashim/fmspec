//! モデルの初期状態の計算。定数と初期値の式を評価し、状態変数ごとの初期値の候補と、その直積、初期条件で絞った初期状態を作る。

#[cfg(verus_keep_ghost)]
use crate::action_lower::lemma_encode_in;
#[cfg(verus_keep_ghost)]
use crate::encoding::{enc, enc_seq, lemma_stys, lemma_width_pos, member, members, sty, stys, STy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, wf_stypes};
use crate::encoding::{SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::eval::{code_of, eval_l, eval_spec, prop_spec, Env, ErrKind};
use crate::eval::{eval, eval_prop, Ctx};
#[cfg(verus_keep_ghost)]
use crate::limits::smalls;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{layouts_at, Layout};
use crate::lower_ctx::{Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_error::{type_err, user_err};
use crate::lower_error::{Fault, LowerError};
#[cfg(verus_keep_ghost)]
use crate::lower_spec::{ctx_is, init_ok, init_src, prop_low};
use crate::lowering::lower_stored;
#[cfg(verus_keep_ghost)]
use crate::model::RawModel;
use crate::model::{Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::model_safe::lemma_prop;
#[cfg(verus_keep_ghost)]
use crate::model_total::{const_ctx, consts_match, lemma_const_ctx, model_typed, styped};
#[cfg(verus_keep_ghost)]
use crate::preserve::{layouts_ok, lemma_members, stored_result, top_ok};
#[cfg(verus_keep_ghost)]
use crate::semantics::inv_env;
use crate::slot_types::slot_types;
#[cfg(verus_keep_ghost)]
use crate::slot_types::{lemma_slot_tys_len, slot_tys, slot_tys_seq};
use crate::smodel::SModel;
#[cfg(verus_keep_ghost)]
use crate::smodel::{s_cand, s_env, s_init, s_init_var, s_prop, s_state_tys};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, SEnv};
#[cfg(verus_keep_ghost)]
use crate::srel::{codes, consts_rel, lemma_code_in, lemma_rel_codes, rel};
#[cfg(verus_keep_ghost)]
use crate::state_enc::encode_spec;
use crate::state_enc::{copy_vec, encode, vec_eq};
use crate::state_set::cmp_state;
#[cfg(verus_keep_ghost)]
use crate::state_set::in_cert;
#[cfg(verus_keep_ghost)]
use crate::total::{cx_wf, ok_s, sctx};
use vstd::prelude::*;

verus! {

/// 状態も引数もない環境。
pub open spec fn empty_env() -> Env {
    Env {
        st_tys: Seq::empty(),
        arg_tys: Seq::empty(),
        pre: Seq::empty(),
        args: Seq::empty(),
        post: Seq::empty(),
        out: None,
    }
}

/// スロットの式 `out` の値は `vals` で、スロットの型 `tys` の符号は `cs` である。
pub open spec fn slots_eval(out: Seq<Expr>, tys: Seq<Type>, enums: Seq<i64>, vals: Seq<Value>, cs: Seq<i64>) -> bool {
    &&& out.len() == tys.len()
    &&& vals.len() == out.len()
    &&& cs.len() == out.len()
    &&& forall|j: int|
        0 <= j < out.len() ==> #[trigger] eval_spec(out[j], empty_env()) == Ok::<Value, ErrKind>(vals[j]) && encode_spec(
            enums,
            tys[j],
            vals[j],
        ) == Ok::<i64, ErrKind>(cs[j])
}

/// スロットの式を空の環境で評価し、スロットの型の符号にする。
pub(crate) fn eval_slots(out: &Vec<Expr>, tys: &Vec<Type>, enums: &Vec<i64>) -> (r: Result<(Vec<Value>, Vec<i64>), Fault>)
    ensures
        r matches Ok((vals, cs)) ==> slots_eval(out@, tys@, enums@, vals@, cs@),
        out@.len() == tys@.len() ==> !(r matches Err(Fault::Lower)),
{
    if out.len() != tys.len() {
        return Err(Fault::Lower);
    }
    let none_t: Vec<Type> = Vec::new();
    let none_v: Vec<i64> = Vec::new();
    let ctx = Ctx { st_tys: &none_t, arg_tys: &none_t, pre: &none_v, args: &none_v, post: &none_v, out: None };
    proof {
        assert(ctx@ =~= empty_env());
    }
    let mut vals: Vec<Value> = Vec::new();
    let mut cs: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < out.len()
        invariant
            j <= out@.len(),
            out@.len() == tys@.len(),
            ctx@ == empty_env(),
            vals@.len() == j,
            cs@.len() == j,
            forall|k: int|
                0 <= k < j ==> #[trigger] eval_spec(out@[k], empty_env()) == Ok::<Value, ErrKind>(vals@[k]) && encode_spec(
                    enums@,
                    tys@[k],
                    vals@[k],
                ) == Ok::<i64, ErrKind>(cs@[k]),
        decreases out@.len() - j,
    {
        let v = match eval(&out[j], &ctx) {
            Ok(v) => v,
            Err(k) => return Err(Fault::Eval(k)),
        };
        let c = match encode(enums, &tys[j], &v) {
            Ok(c) => c,
            Err(k) => return Err(Fault::Eval(k)),
        };
        vals.push(v);
        cs.push(c);
        j += 1;
    }
    Ok((vals, cs))
}

/// 評価したスロットがどれもスロットの型の値なら、値の上の評価は型に属する値で、スロットはその符号化である。
pub(crate) proof fn lemma_stored_val(
    src: Result<SVal, ErrKind>,
    out: Seq<Expr>,
    t: STy,
    enums: Seq<i64>,
    vals: Seq<Value>,
    cs: Seq<i64>,
)
    requires
        stored_result(src, out, empty_env(), Seq::empty(), t, enums),
        slots_eval(out, slot_tys(t, enums), enums, vals, cs),
        out.len() >= 1,
    ensures
        src is Ok,
        member(src->Ok_0, t, enums),
        enc(src->Ok_0, t, enums) == vals,
        cs == codes(vals),
{
    match src {
        Err(k) => {
            assert(eval_l(out[0], empty_env(), Seq::empty()) == Err::<Value, ErrKind>(k));
            assert(eval_spec(out[0], empty_env()) == Ok::<Value, ErrKind>(vals[0]));
        },
        Ok(v) => {
            let e = enc(v, t, enums);
            let tys = slot_tys(t, enums);
            lemma_slot_tys_len(t, enums);
            assert forall|j: int| 0 <= j < out.len() implies #[trigger] e[j] == vals[j] && in_slot_at(tys, vals, j, enums)
                && cs[j] == code_of(vals[j]) by {
                assert(eval_l(out[j], empty_env(), Seq::empty()) == Ok::<Value, ErrKind>(e[j]));
                assert(eval_spec(out[j], empty_env()) == Ok::<Value, ErrKind>(vals[j]));
                lemma_encode_in(tys[j], vals[j], enums);
                lemma_code_in(tys[j], vals[j], enums);
            }
            assert(e =~= vals);
            assert(cs =~= codes(vals));
            assert(crate::slot_types::in_slots(e, tys, enums));
        },
    }
}

pub(crate) open spec fn in_slot_at(tys: Seq<Type>, vals: Seq<Value>, j: int, enums: Seq<i64>) -> bool {
    crate::slot_types::in_slot(tys[j], vals[j], enums)
}

/// 型 `t` の式を空の環境で評価する。値を `(slots, codes)` で返す。
pub(crate) fn eval_stored(e: &crate::source::TExpr, cx: &LowerCtx, t: &SType) -> (r: Result<(Vec<Value>, Vec<i64>), Fault>)
    ensures
        r matches Ok((vals, cs)) ==> forall|se: SEnv| #[trigger]
            top_ok(*cx, empty_env(), se, Seq::empty(), 0) ==> {
                let src = eval_src(*e, se, Seq::empty());
                &&& src is Ok
                &&& member(src->Ok_0, sty(*t), cx.enums@)
                &&& enc(src->Ok_0, sty(*t), cx.enums@) == vals@
                &&& cs@ == codes(vals@)
            },
        cx_wf(*cx) && styped(*e, sctx(*cx), to_xty(sty(*t))) && ok_s(sty(*t), cx.enums@) ==> !(r matches Err(
            Fault::Lower,
        )),
{
    let ghost pre = cx_wf(*cx) && styped(*e, sctx(*cx), to_xty(sty(*t))) && ok_s(sty(*t), cx.enums@);
    let out = match lower_stored(e, cx, t, 0) {
        Ok(o) => o,
        Err(Fail::Depth) => return Err(Fault::Depth),
        Err(Fail::Type) => return Err(Fault::Lower),
    };
    proof {
        if pre {
            lemma_width_pos(sty(*t), cx.enums@);
            lemma_slot_tys_len(sty(*t), cx.enums@);
        }
    }
    if out.len() == 0 {
        return Err(Fault::Lower);
    }
    let mut tys: Vec<Type> = Vec::new();
    slot_types(t, &cx.enums, &mut tys);
    proof {
        assert(tys@ =~= slot_tys(sty(*t), cx.enums@));
    }
    let (vals, cs) = eval_slots(&out, &tys, &cx.enums)?;
    proof {
        assert forall|se: SEnv| #[trigger] top_ok(*cx, empty_env(), se, Seq::empty(), 0) implies {
            let src = eval_src(*e, se, Seq::empty());
            &&& src is Ok
            &&& member(src->Ok_0, sty(*t), cx.enums@)
            &&& enc(src->Ok_0, sty(*t), cx.enums@) == vals@
            &&& cs@ == codes(vals@)
        } by {
            assert(se.enums == cx.enums@);
            lemma_stored_val(eval_src(*e, se, Seq::empty()), out@, sty(*t), cx.enums@, vals@, cs@);
        }
    }
    Ok((vals, cs))
}

/// 辞書順に整列した列 `out` に `x` を加える。同じ列がすでにあれば加えない。
pub(crate) fn insert_sorted(out: &mut Vec<Vec<i64>>, x: Vec<i64>)
    ensures
        forall|y: Seq<i64>| #[trigger] in_cert(final(out)@, y) <==> (in_cert(old(out)@, y) || y == x@),
{
    let ghost o = out@;
    let mut k = 0;
    loop
        invariant
            k <= out@.len(),
            out@ == o,
        decreases out@.len() - k,
    {
        if k >= out.len() || !(cmp_state(&out[k], &x) < 0) {
            break;
        }
        k += 1;
    }
    if k < out.len() && vec_eq(&out[k], &x) {
        proof {
            assert forall|y: Seq<i64>| #[trigger] in_cert(out@, y) <==> (in_cert(o, y) || y == x@) by {
                if y == x@ {
                    assert(out@[k as int]@ == y);
                }
            }
        }
        return;
    }
    let ghost xv = x@;
    out.insert(k, x);
    proof {
        assert(out@ == o.insert(k as int, out@[k as int]));
        assert(out@[k as int]@ == xv);
        assert forall|y: Seq<i64>| #[trigger] in_cert(out@, y) <==> (in_cert(o, y) || y == xv) by {
            if in_cert(out@, y) {
                let q = choose|q: int| 0 <= q < out@.len() && #[trigger] out@[q]@ == y;
                if q < k {
                    assert(o[q]@ == y);
                } else if q > k {
                    assert(o[q - 1]@ == y);
                }
            }
            if in_cert(o, y) {
                let q = choose|q: int| 0 <= q < o.len() && #[trigger] o[q]@ == y;
                if q < k {
                    assert(out@[q]@ == y);
                } else {
                    assert(out@[q + 1]@ == y);
                }
            }
            if y == xv {
                assert(out@[k as int]@ == y);
            }
        }
    }
}

/// 定数と初期値の候補を下ろす文脈。状態と引数を参照できない。
pub open spec fn init_cx(sm: SModel, cv: Seq<SVal>, cx: LowerCtx) -> bool {
    &&& cx.enums@ == sm.enums@
    &&& cx.states is None
    &&& cx.args@ == Seq::<Layout>::empty()
    &&& !cx.next
    &&& cx.out is None
    &&& consts_rel(cx.consts@, cv, sm.enums@)
}

pub(crate) proof fn lemma_init_top(sm: SModel, cv: Seq<SVal>, cx: LowerCtx)
    requires
        init_cx(sm, cv, cx),
    ensures
        top_ok(cx, empty_env(), s_env(sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None), Seq::empty(), 0),
{
    assert(layouts_ok(cx.args@, Seq::<SVal>::empty(), Seq::<Type>::empty(), Seq::<i64>::empty(), sm.enums@));
}

/// `y` は、状態変数 `i` の初期値の候補の値 `w` の符号である。
pub open spec fn cand_codes(sm: SModel, cv: Seq<SVal>, i: int, w: SVal, y: Seq<i64>) -> bool {
    let t = s_state_tys(sm)[i];
    s_init_var(sm, cv, i, w) && member(w, t, sm.enums@) && y == codes(enc(w, t, sm.enums@))
}

/// 列 `cs` は、状態変数 `i` の初期値の候補の値の符号を過不足なく含む。
pub open spec fn cands_ok(sm: SModel, cv: Seq<SVal>, i: int, cs: Seq<Vec<i64>>) -> bool {
    let t = s_state_tys(sm)[i];
    &&& forall|y: Seq<i64>| #[trigger] in_cert(cs, y) ==> exists|w: SVal| #[trigger] cand_codes(sm, cv, i, w, y)
    &&& forall|w: SVal|
        #[trigger] s_init_var(sm, cv, i, w) ==> member(w, t, sm.enums@) && in_cert(cs, codes(enc(w, t, sm.enums@)))
}

/// 状態変数 `i` の初期値の候補の符号を、辞書順に整列して重複を除いた列。
pub(crate) fn var_cands(sm: &SModel, cx: &LowerCtx, i: usize, Ghost(cv): Ghost<Seq<SVal>>) -> (r: Result<Vec<Vec<i64>>, LowerError>)
    requires
        i < sm.states@.len(),
        i < sm.inits@.len(),
        init_cx(*sm, cv, *cx),
    ensures
        r matches Ok(cs) ==> cands_ok(*sm, cv, i as int, cs@),
        model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len() ==> (r matches Err(
            e,
        ) ==> user_err(e)),
{
    let ghost se = s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None);
    let ghost t = s_state_tys(*sm)[i as int];
    let ghost pre = model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len();
    proof {
        lemma_stys(sm.states@);
        lemma_init_top(*sm, cv, *cx);
        if pre {
            lemma_const_ctx(*sm, cv, *cx);
            assert(ok_s(stys(sm.states@)[i as int], sm.enums@));
        }
    }
    let es = &sm.inits[i];
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut j = 0;
    while j < es.len()
        invariant
            j <= es@.len(),
            i < sm.states@.len(),
            i < sm.inits@.len(),
            *es == sm.inits@[i as int],
            t == sty(sm.states@[i as int]),
            t == s_state_tys(*sm)[i as int],
            top_ok(*cx, empty_env(), se, Seq::empty(), 0),
            se == s_env(*sm, cv, Seq::empty(), Seq::empty(), Seq::empty(), None),
            cx.enums@ == sm.enums@,
            forall|y: Seq<i64>| #[trigger] in_cert(out@, y) ==> exists|w: SVal| #[trigger] cand_codes(*sm, cv, i as int, w, y),
            forall|q: int|
                0 <= q < j ==> {
                    let r = #[trigger] s_cand(*sm, cv, es@[q]);
                    &&& r is Ok
                    &&& member(r->Ok_0, t, sm.enums@)
                    &&& in_cert(out@, codes(enc(r->Ok_0, t, sm.enums@)))
                },
            pre ==> cx_wf(*cx) && sctx(*cx) == const_ctx(*sm, sm.consts@.len() as int) && ok_s(t, sm.enums@),
            pre == (model_typed(*sm) && consts_match(*sm, cx.consts@) && cx.consts@.len() == sm.consts@.len()),
        decreases es@.len() - j,
    {
        proof {
            if pre {
                assert(styped(sm.inits@[i as int]@[j as int], const_ctx(*sm, sm.consts@.len() as int), to_xty(t)));
            }
        }
        let (_vals, cs) = match eval_stored(&es[j], cx, &sm.states[i]) {
            Ok(r) => r,
            Err(f) => return Err(LowerError::Init(i, j, f)),
        };
        let ghost w = s_cand(*sm, cv, es@[j as int])->Ok_0;
        proof {
            assert(s_cand(*sm, cv, es@[j as int]) == eval_src(es@[j as int], se, Seq::empty()));
            assert(s_init_var(*sm, cv, i as int, w));
            assert(cand_codes(*sm, cv, i as int, w, cs@));
        }
        let ghost cv0 = cs@;
        let ghost o = out@;
        insert_sorted(&mut out, cs);
        proof {
            assert(in_cert(out@, cv0));
            assert forall|q: int| 0 <= q < j + 1 implies {
                let r = #[trigger] s_cand(*sm, cv, es@[q]);
                &&& r is Ok
                &&& member(r->Ok_0, t, sm.enums@)
                &&& in_cert(out@, codes(enc(r->Ok_0, t, sm.enums@)))
            } by {
                if q < j {
                    assert(in_cert(o, codes(enc(s_cand(*sm, cv, es@[q])->Ok_0, t, sm.enums@))));
                }
            }
            assert forall|y: Seq<i64>| #[trigger] in_cert(out@, y) implies exists|w: SVal| #[trigger] cand_codes(
                *sm,
                cv,
                i as int,
                w,
                y,
            ) by {
                if in_cert(o, y) {
                } else {
                    assert(cand_codes(*sm, cv, i as int, w, y));
                }
            }
        }
        j += 1;
    }
    proof {
        assert forall|w: SVal| #[trigger] s_init_var(*sm, cv, i as int, w) implies member(w, t, sm.enums@) && in_cert(
            out@,
            codes(enc(w, t, sm.enums@)),
        ) by {
            let q = choose|q: int| 0 <= q < sm.inits@[i as int].len() && #[trigger] s_cand(*sm, cv, sm.inits@[i as int][q])
                == Ok::<SVal, ErrKind>(w);
            assert(s_cand(*sm, cv, es@[q]) is Ok);
        }
    }
    Ok(out)
}

/// `ws` は、先頭の `k` 個の状態変数の初期値の候補の値の組である。
pub open spec fn combo(sm: SModel, cv: Seq<SVal>, k: int, ws: Seq<SVal>) -> bool {
    &&& ws.len() == k
    &&& forall|i: int|
        0 <= i < k ==> #[trigger] s_init_var(sm, cv, i, ws[i]) && member(ws[i], s_state_tys(sm)[i], sm.enums@)
}

/// 列 `ps` は、先頭の `k` 個の状態変数の初期値の候補の組の符号を過不足なく含む。
pub open spec fn prod_ok(sm: SModel, cv: Seq<SVal>, k: int, ps: Seq<Vec<i64>>) -> bool {
    let ts = s_state_tys(sm).take(k);
    &&& forall|y: Seq<i64>|
        #[trigger] in_cert(ps, y) ==> exists|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) && y == codes(enc_seq(ws, ts, sm.enums@))
    &&& forall|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) ==> in_cert(ps, codes(enc_seq(ws, ts, sm.enums@)))
}

/// 2つの符号の列をつなげる。
pub open spec fn cat(ps: Seq<Vec<i64>>, cs: Seq<Vec<i64>>, p: int, q: int) -> Seq<i64> {
    ps[p]@ + cs[q]@
}

pub(crate) fn concat_codes(a: &Vec<i64>, b: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        r@ == a@ + b@,
{
    let mut r = copy_vec(a);
    let mut j = 0;
    while j < b.len()
        invariant
            j <= b@.len(),
            r@ == a@ + b@.take(j as int),
        decreases b@.len() - j,
    {
        r.push(b[j]);
        j += 1;
        proof {
            assert(r@ =~= a@ + b@.take(j as int));
        }
    }
    proof {
        assert(b@.take(j as int) =~= b@);
    }
    r
}

/// `ps` の各列と `cs` の各列をつなげた列を、`ps` の順、`cs` の順に並べる。
pub(crate) fn product_step(ps: &Vec<Vec<i64>>, cs: &Vec<Vec<i64>>) -> (r: Vec<Vec<i64>>)
    ensures
        forall|y: Seq<i64>|
            #[trigger] in_cert(r@, y) ==> exists|p: int, q: int|
                0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
        forall|p: int, q: int| 0 <= p < ps@.len() && 0 <= q < cs@.len() ==> in_cert(r@, #[trigger] cat(ps@, cs@, p, q)),
{
    let mut r: Vec<Vec<i64>> = Vec::new();
    let mut p = 0;
    while p < ps.len()
        invariant
            p <= ps@.len(),
            forall|y: Seq<i64>|
                #[trigger] in_cert(r@, y) ==> exists|p: int, q: int|
                    0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
            forall|p0: int, q: int| 0 <= p0 < p && 0 <= q < cs@.len() ==> in_cert(r@, #[trigger] cat(ps@, cs@, p0, q)),
        decreases ps@.len() - p,
    {
        let mut q = 0;
        while q < cs.len()
            invariant
                p < ps@.len(),
                q <= cs@.len(),
                forall|y: Seq<i64>|
                    #[trigger] in_cert(r@, y) ==> exists|p: int, q: int|
                        0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q),
                forall|p0: int, q0: int|
                    0 <= p0 < p && 0 <= q0 < cs@.len() ==> in_cert(r@, #[trigger] cat(ps@, cs@, p0, q0)),
                forall|q0: int| 0 <= q0 < q ==> in_cert(r@, #[trigger] cat(ps@, cs@, p as int, q0)),
            decreases cs@.len() - q,
        {
            let x = concat_codes(&ps[p], &cs[q]);
            let ghost o = r@;
            r.push(x);
            proof {
                assert(r@[o.len() as int]@ == cat(ps@, cs@, p as int, q as int));
                assert forall|y: Seq<i64>| in_cert(o, y) implies #[trigger] in_cert(r@, y) by {
                    let k = choose|k: int| 0 <= k < o.len() && #[trigger] o[k]@ == y;
                    assert(r@[k]@ == y);
                }
                assert forall|y: Seq<i64>| #[trigger] in_cert(r@, y) implies exists|p: int, q: int|
                    0 <= p < ps@.len() && 0 <= q < cs@.len() && y == #[trigger] cat(ps@, cs@, p, q) by {
                    let k = choose|k: int| 0 <= k < r@.len() && #[trigger] r@[k]@ == y;
                    if k < o.len() {
                        assert(o[k]@ == y);
                        assert(in_cert(o, y));
                    }
                }
            }
            q += 1;
        }
        p += 1;
    }
    r
}

pub proof fn lemma_codes_concat(a: Seq<Value>, b: Seq<Value>)
    ensures
        codes(a + b) == codes(a) + codes(b),
{
    assert(codes(a + b) =~= codes(a) + codes(b));
}

/// 候補の組の直積を1つの状態変数だけ延ばす。
pub(crate) proof fn lemma_prod_step(
    sm: SModel,
    cv: Seq<SVal>,
    k: int,
    ps: Seq<Vec<i64>>,
    cs: Seq<Vec<i64>>,
    r: Seq<Vec<i64>>,
)
    requires
        0 <= k < s_state_tys(sm).len(),
        prod_ok(sm, cv, k, ps),
        cands_ok(sm, cv, k, cs),
        forall|y: Seq<i64>|
            #[trigger] in_cert(r, y) ==> exists|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() && y == #[trigger] cat(ps, cs, p, q),
        forall|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() ==> in_cert(r, #[trigger] cat(ps, cs, p, q)),
    ensures
        prod_ok(sm, cv, k + 1, r),
{
    let enums = sm.enums@;
    let all = s_state_tys(sm);
    let ts = all.take(k);
    let ts1 = all.take(k + 1);
    assert(ts1.drop_last() =~= ts);
    assert(ts1.last() == all[k]);
    assert forall|ws: Seq<SVal>| ws.len() == k + 1 implies #[trigger] enc_seq(ws, ts1, enums) == enc_seq(
        ws.drop_last(),
        ts,
        enums,
    ) + enc(ws[k], all[k], enums) by {
        assert(ws.last() == ws[k]);
    }
    assert forall|y: Seq<i64>| #[trigger] in_cert(r, y) implies exists|ws: Seq<SVal>| #[trigger] combo(sm, cv, k + 1, ws) && y
        == codes(enc_seq(ws, ts1, enums)) by {
        let (p, q) = choose|p: int, q: int| 0 <= p < ps.len() && 0 <= q < cs.len() && y == #[trigger] cat(ps, cs, p, q);
        assert(in_cert(ps, ps[p]@));
        let ws0 = choose|ws: Seq<SVal>| #[trigger] combo(sm, cv, k, ws) && ps[p]@ == codes(enc_seq(ws, ts, enums));
        assert(in_cert(cs, cs[q]@));
        let w = choose|w: SVal| #[trigger] cand_codes(sm, cv, k, w, cs[q]@);
        let ws = ws0.push(w);
        assert(ws.drop_last() =~= ws0);
        assert forall|i: int| 0 <= i < k + 1 implies #[trigger] s_init_var(sm, cv, i, ws[i]) && member(
            ws[i],
            all[i],
            enums,
        ) by {
            if i < k {
                assert(ws[i] == ws0[i]);
                assert(s_init_var(sm, cv, i, ws0[i]));
            }
        }
        assert(combo(sm, cv, k + 1, ws));
        lemma_codes_concat(enc_seq(ws0, ts, enums), enc(w, all[k], enums));
    }
    assert forall|ws: Seq<SVal>| #[trigger] combo(sm, cv, k + 1, ws) implies in_cert(r, codes(enc_seq(ws, ts1, enums))) by {
        let ws0 = ws.drop_last();
        assert forall|i: int| 0 <= i < k implies #[trigger] s_init_var(sm, cv, i, ws0[i]) && member(ws0[i], all[i], enums) by {
            assert(ws0[i] == ws[i]);
            assert(s_init_var(sm, cv, i, ws[i]));
        }
        assert(combo(sm, cv, k, ws0));
        let p = choose|p: int| 0 <= p < ps.len() && #[trigger] ps[p]@ == codes(enc_seq(ws0, ts, enums));
        assert(s_init_var(sm, cv, k, ws[k]));
        let q = choose|q: int| 0 <= q < cs.len() && #[trigger] cs[q]@ == codes(enc(ws[k], all[k], enums));
        lemma_codes_concat(enc_seq(ws0, ts, enums), enc(ws[k], all[k], enums));
        assert(cat(ps, cs, p, q) == codes(enc_seq(ws, ts1, enums)));
    }
}

/// 状態 `y` の環境。
pub open spec fn st_env(tys: Seq<Type>, y: Seq<i64>) -> Env {
    Env { st_tys: tys, arg_tys: Seq::empty(), pre: y, args: Seq::empty(), post: Seq::empty(), out: None }
}

/// 状態 `y` は初期条件 `cc` を満たす。
pub open spec fn keep(cc: Option<Expr>, tys: Seq<Type>, y: Seq<i64>) -> bool {
    match cc {
        None => true,
        Some(c) => prop_spec(c, st_env(tys, y)) == Ok::<bool, ErrKind>(true),
    }
}

/// 初期条件を満たす状態だけを、順に残す。評価に失敗すれば、その理由を返す。
pub(crate) fn filter_inits(ps: Vec<Vec<i64>>, cc: &Option<Expr>, tys: &Vec<Type>) -> (r: Result<Vec<Vec<i64>>, Fault>)
    ensures
        r matches Ok(f) ==> forall|y: Seq<i64>| #[trigger] in_cert(f@, y) <==> in_cert(ps@, y) && keep(*cc, tys@, y),
        r matches Err(f) ==> f is Eval,
{
    let c = match cc {
        None => {
            proof {
                assert forall|y: Seq<i64>| #[trigger] in_cert(ps@, y) <==> in_cert(ps@, y) && keep(*cc, tys@, y) by {}
            }
            return Ok(ps);
        },
        Some(c) => c,
    };
    let none_t: Vec<Type> = Vec::new();
    let none_v: Vec<i64> = Vec::new();
    let mut f: Vec<Vec<i64>> = Vec::new();
    let mut p = 0;
    while p < ps.len()
        invariant
            p <= ps@.len(),
            *cc == Some(*c),
            none_t@ == Seq::<Type>::empty(),
            none_v@ == Seq::<i64>::empty(),
            forall|y: Seq<i64>| #[trigger] in_cert(f@, y) ==> in_cert(ps@, y) && keep(*cc, tys@, y),
            forall|p0: int| 0 <= p0 < p && keep(*cc, tys@, ps@[p0]@) ==> in_cert(f@, #[trigger] ps@[p0]@),
        decreases ps@.len() - p,
    {
        let ctx = Ctx { st_tys: tys, arg_tys: &none_t, pre: &ps[p], args: &none_v, post: &none_v, out: None };
        proof {
            assert(ctx@ =~= st_env(tys@, ps@[p as int]@));
        }
        match eval_prop(c, &ctx) {
            Err(k) => return Err(Fault::Eval(k)),
            Ok(false) => {},
            Ok(true) => {
                let ghost o = f@;
                f.push(copy_vec(&ps[p]));
                proof {
                    assert(f@[o.len() as int]@ == ps@[p as int]@);
                    assert(in_cert(ps@, ps@[p as int]@));
                    assert forall|y: Seq<i64>| in_cert(o, y) implies #[trigger] in_cert(f@, y) by {
                        let k = choose|k: int| 0 <= k < o.len() && #[trigger] o[k]@ == y;
                        assert(f@[k]@ == y);
                    }
                    assert forall|y: Seq<i64>| #[trigger] in_cert(f@, y) implies in_cert(ps@, y) && keep(*cc, tys@, y) by {
                        let k = choose|k: int| 0 <= k < f@.len() && #[trigger] f@[k]@ == y;
                        if k < o.len() {
                            assert(o[k]@ == y);
                            assert(in_cert(o, y));
                        }
                    }
                }
            },
        }
        p += 1;
    }
    proof {
        assert forall|y: Seq<i64>| #[trigger] in_cert(f@, y) <==> in_cert(ps@, y) && keep(*cc, tys@, y) by {
            if in_cert(ps@, y) && keep(*cc, tys@, y) {
                let k = choose|k: int| 0 <= k < ps@.len() && #[trigger] ps@[k]@ == y;
            }
        }
    }
    Ok(f)
}

/// 初期条件の下ろし。
pub open spec fn constraint_low(sm: SModel, sx: LowerCtx, cc: Option<Expr>) -> bool {
    match (sm.constraint, cc) {
        (None, None) => true,
        (Some(e), Some(c)) => prop_low(e, sx, c),
        _ => false,
    }
}

/// 候補の組の直積から初期条件で選んだ中核の初期状態は、値の上の初期状態と対応する。
pub(crate) proof fn lemma_init_ok(
    sm: SModel,
    cv: Seq<SVal>,
    m: RawModel,
    st: Seq<Layout>,
    sx: LowerCtx,
    ps: Seq<Vec<i64>>,
    cc: Option<Expr>,
)
    requires
        sm.inits@.len() == sm.states@.len(),
        prod_ok(sm, cv, sm.states@.len() as int, ps),
        forall|y: Seq<i64>| #[trigger] in_cert(m.inits@, y) <==> in_cert(ps, y) && keep(cc, m.state_types@, y),
        constraint_low(sm, sx, cc),
        ctx_is(sx, sm.enums@, cv, st, Seq::empty(), false, None),
        layouts_at(st, s_state_tys(sm), sm.enums@),
        wf_stypes(s_state_tys(sm), sm.enums@),
        smalls(s_state_tys(sm)),
        m.state_types@ == slot_tys_seq(s_state_tys(sm), sm.enums@),
        m.enums@ == sm.enums@,
    ensures
        init_ok(sm, cv, m, st),
{
    let enums = sm.enums@;
    let ts = s_state_tys(sm);
    let n = sm.states@.len() as int;
    lemma_stys(sm.states@);
    assert(ts.take(n) =~= ts);
    assert forall|s: Seq<SVal>, y: Seq<i64>| combo(sm, cv, n, s) && y == codes(enc_seq(s, ts, enums)) implies {
        &&& #[trigger] rel(st, s, m.state_types@, y, enums)
        &&& members(s, ts, enums)
        &&& (keep(cc, m.state_types@, y) <==> match sm.constraint {
            None => true,
            Some(e) => s_prop(sm, cv, e, s) == Ok::<bool, ErrKind>(true),
        })
    } by {
        assert forall|i: int| 0 <= i < ts.len() implies member(#[trigger] s[i], ts[i], enums) by {
            assert(s_init_var(sm, cv, i, s[i]));
        }
        lemma_members(s, ts, enums);
        lemma_rel_codes(st, s, ts, enums);
        match (sm.constraint, cc) {
            (Some(e), Some(c)) => {
                lemma_prop(sm, cv, m, st, sx, e, c, s, y);
                assert(inv_env(m, y) == st_env(m.state_types@, y));
            },
            _ => {},
        }
    }
    assert forall|k: int| 0 <= k < m.inits@.len() implies #[trigger] init_src(sm, cv, st, m.state_types@, m.inits@[k]@) by {
        let y = m.inits@[k]@;
        assert(in_cert(m.inits@, y));
        let ws = choose|ws: Seq<SVal>| #[trigger] combo(sm, cv, n, ws) && y == codes(enc_seq(ws, ts.take(n), enums));
        assert(rel(st, ws, m.state_types@, y, enums));
        assert forall|i: int| 0 <= i < ws.len() implies #[trigger] s_init_var(sm, cv, i, ws[i]) by {}
        assert(s_init(sm, cv, ws));
    }
    assert forall|s: Seq<SVal>| #[trigger] s_init(sm, cv, s) implies exists|k: int|
        0 <= k < m.inits@.len() && #[trigger] rel(st, s, m.state_types@, m.inits@[k]@, enums) by {
        lemma_members(s, ts, enums);
        assert forall|i: int| 0 <= i < n implies #[trigger] s_init_var(sm, cv, i, s[i]) && member(s[i], ts[i], enums) by {
            assert(s_init_var(sm, cv, i, s[i]));
        }
        assert(combo(sm, cv, n, s));
        let y = codes(enc_seq(s, ts, enums));
        assert(rel(st, s, m.state_types@, y, enums));
        assert(in_cert(ps, y));
        assert(in_cert(m.inits@, y));
        let k = choose|k: int| 0 <= k < m.inits@.len() && #[trigger] m.inits@[k]@ == y;
    }
}

/// 初期値の候補を状態変数ごとに求め、その直積（`prod_ok`）を作る。
pub(crate) fn init_products(sm: &SModel, cx: &LowerCtx, Ghost(cv): Ghost<Seq<SVal>>) -> (r: Result<Vec<Vec<i64>>, LowerError>)
    requires
        init_cx(*sm, cv, *cx),
        model_typed(*sm),
        consts_match(*sm, cx.consts@),
        cx.consts@.len() == sm.consts@.len(),
    ensures
        r matches Ok(ps) ==> sm.inits@.len() == sm.states@.len() && prod_ok(*sm, cv, sm.states@.len() as int, ps@),
        r matches Err(e) ==> user_err(e) || (type_err(e) && !model_typed(*sm)),
{
    if sm.inits.len() != sm.states.len() {
        return Err(LowerError::InitCount);
    }
    let mut cands: Vec<Vec<Vec<i64>>> = Vec::new();
    let mut total: usize = 1;
    let mut i = 0;
    while i < sm.states.len()
        invariant
            i <= sm.states@.len(),
            sm.inits@.len() == sm.states@.len(),
            init_cx(*sm, cv, *cx),
            cands@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] cands_ok(*sm, cv, q, cands@[q]@),
            model_typed(*sm),
            consts_match(*sm, cx.consts@),
            cx.consts@.len() == sm.consts@.len(),
        decreases sm.states@.len() - i,
    {
        let c = var_cands(sm, cx, i, Ghost(cv))?;
        total = match total.checked_mul(c.len()) {
            Some(t) => t,
            None => return Err(LowerError::InitCount),
        };
        if total > MAX_INITIAL_CANDIDATES {
            return Err(LowerError::InitCount);
        }
        cands.push(c);
        i += 1;
    }
    // 候補の直積
    let mut ps: Vec<Vec<i64>> = Vec::new();
    ps.push(Vec::new());
    proof {
        let enums = sm.enums@;
        let ts0 = s_state_tys(*sm).take(0);
        assert(ts0 =~= Seq::<STy>::empty());
        assert forall|y: Seq<i64>| #[trigger] in_cert(ps@, y) implies exists|ws: Seq<SVal>| #[trigger] combo(*sm, cv, 0, ws) && y
            == codes(enc_seq(ws, ts0, enums)) by {
            assert(combo(*sm, cv, 0, Seq::<SVal>::empty()));
            assert(codes(enc_seq(Seq::<SVal>::empty(), ts0, enums)) =~= Seq::<i64>::empty());
        }
        assert forall|ws: Seq<SVal>| #[trigger] combo(*sm, cv, 0, ws) implies in_cert(ps@, codes(enc_seq(ws, ts0, enums))) by {
            assert(codes(enc_seq(ws, ts0, enums)) =~= Seq::<i64>::empty());
            assert(ps@[0]@ =~= Seq::<i64>::empty());
        }
        lemma_stys(sm.states@);
    }
    let mut k = 0;
    while k < cands.len()
        invariant
            k <= cands@.len(),
            cands@.len() == sm.states@.len(),
            s_state_tys(*sm).len() == sm.states@.len(),
            forall|q: int| 0 <= q < cands@.len() ==> #[trigger] cands_ok(*sm, cv, q, cands@[q]@),
            prod_ok(*sm, cv, k as int, ps@),
        decreases cands@.len() - k,
    {
        let next = product_step(&ps, &cands[k]);
        proof {
            assert(cands_ok(*sm, cv, k as int, cands@[k as int]@));
            lemma_prod_step(*sm, cv, k as int, ps@, cands@[k as int]@, next@);
        }
        ps = next;
        k += 1;
    }
    Ok(ps)
}

/// 初期値の候補の組み合わせのうち、調べる数の上限。
pub const MAX_INITIAL_CANDIDATES: usize = 1 << 20;

} // verus!
