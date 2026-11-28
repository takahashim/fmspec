//! 量化（`forall` と `exists`）の下ろしが意味を保存することの仕様と補題。
//!
//! 下ろしの実装は [`crate::lowering`] の `quant_over` と `low_quant`（`crate::lower_quant`）にある。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_items, enc_repeat, enc_rows, keys, lemma_default_len};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_items_len, lemma_enc_len, lemma_items_index, lemma_items_member};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_models_enc, lemma_repeat_len, member, sty, to_xty, STy, SType, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{width, xty, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, decode, eval_l, quant_l, Env, ErrKind};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, bool_lit, lemma_pure_mono, pure_below};
#[cfg(verus_keep_ghost)]
use crate::keys::{domain, lemma_domain_len, lemma_domain_rank};
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{extends, Block, Bound, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::pick::{at_rank, lemma_vals_weaken, picks, vals_at};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::quant::unrank_ok;
#[cfg(verus_keep_ghost)]
use crate::rows::{lemma_enc_rows_index, row_slots};
#[cfg(verus_keep_ghost)]
use crate::source::{eval_qstate, eval_quant, eval_src, qresult, select_bits, Over, QState, SEnv};
#[cfg(verus_keep_ghost)]
use crate::source::{src_bool, TExpr};
use vstd::prelude::*;

verus! {

/// `qb` は、ガード `g` が真なら本体 `b` の真偽、偽なら `all` になる。
pub open spec fn combine_ok(all: bool, g: Expr, b: Expr, qb: Expr) -> bool {
    forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(qb, env, l)) == match as_bool(eval_l(g, env, l)) {
        Err(k) => Err(k),
        Ok(true) => as_bool(eval_l(b, env, l)),
        Ok(false) => Ok::<bool, ErrKind>(all),
    }
}

pub open spec fn quant_s(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> Expr {
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

/// 量化でたどる値の列。値の意味論の `Quant` がたどる列である。
pub open spec fn src_items(over: Over, se: SEnv, sls: Seq<SVal>) -> Result<Seq<SVal>, ErrKind> {
    let enums = se.enums;
    match over {
        Over::Type(t) => Ok(domain(sty(t), enums)),
        Over::Set(t, s) => match eval_src(*s, se, sls) {
            Ok(SVal::Set(bits)) => Ok(select_bits(domain(sty(t), enums), bits)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::Map(t, m) => match eval_src(*m, se, sls) {
            Ok(SVal::Map(rows)) => Ok(
                select_bits(domain(sty(t), enums), Seq::new(rows.len(), |i: int| rows[i] is Some)),
            ),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => Ok(items),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
    }
}

/// 局所変数 `l` に位置 `x` を加えると、ガード `g` は `bits[x]` になる。
pub open spec fn guard_at(g: Expr, bits: Seq<bool>, env: Env, l: Seq<Value>) -> bool {
    forall|x: int|
        0 <= x < bits.len() ==> #[trigger] eval_l(g, env, l.push(Value::Int(x as i64))) == Ok::<Value, ErrKind>(
            Value::Bool(bits[x]),
        )
}

/// 局所変数 `l` に選ぶ位置 `x` を加えると、スロット `us` は `dom[x]` を表す。
pub open spec fn bound_at(us: Seq<Expr>, xt: XTy, dom: Seq<SVal>, bits: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>) -> bool {
    forall|x: int|
        0 <= x < bits.len() && bits[x] ==> #[trigger] denotes(us, env, l.push(Value::Int(x as i64)), dom[x], xt, enums)
}

/// 位置の列 `dom` から `bits` で選ぶと、たどる値の列 `xs` になる。ガードと束縛する値のスロットは、位置ごとにそれを表す。
pub open spec fn sel_ok(
    xs: Seq<SVal>,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    n: nat,
    g: Expr,
    us: Seq<Expr>,
    xt: XTy,
    env: Env,
    l: Seq<Value>,
    enums: Seq<i64>,
) -> bool {
    &&& bits.len() == n
    &&& dom.len() == n
    &&& select_bits(dom, bits) == xs
    &&& guard_at(g, bits, env, l)
    &&& bound_at(us, xt, dom, bits, env, l, enums)
}

/// 位置の列。型の全体、Set、Mapでは型の正規順の列、ListではListの要素を長さ `n` に埋めた列。
pub open spec fn over_dom(over: Over, se: SEnv, sls: Seq<SVal>, n: nat) -> Seq<SVal> {
    match over {
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => list_dom(items, n),
            _ => Seq::empty(),
        },
        _ => domain(over_sty(over), se.enums),
    }
}

/// 選ぶ位置。
pub open spec fn over_sel(over: Over, se: SEnv, sls: Seq<SVal>, n: nat) -> Seq<bool> {
    match over {
        Over::Type(_) => Seq::new(n, |i: int| true),
        Over::Set(_, s) => match eval_src(*s, se, sls) {
            Ok(SVal::Set(bits)) => bits,
            _ => Seq::empty(),
        },
        Over::Map(_, m) => match eval_src(*m, se, sls) {
            Ok(SVal::Map(rows)) => Seq::new(rows.len(), |i: int| rows[i] is Some),
            _ => Seq::empty(),
        },
        Over::List(l) => match eval_src(*l, se, sls) {
            Ok(SVal::List(items)) => Seq::new(n, |i: int| i < items.len()),
            _ => Seq::empty(),
        },
    }
}

pub open spec fn over_sty(over: Over) -> STy {
    match over {
        Over::Type(t) => sty(t),
        Over::Set(t, _) => sty(t),
        Over::Map(t, _) => sty(t),
        Over::List(_) => STy::Bool,
    }
}

/// 対象を `b0` から `b1` までに下ろした結果。成功すれば、位置の列と選ぶ位置が [`sel_ok`] を満たす。
pub open spec fn over_at(
    over: Over,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    xt: XTy,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
) -> bool {
    match src_items(over, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(xs) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && sel_ok(xs, over_dom(over, se, sls, n), over_sel(over, se, sls, n), n, g, us, xt, env, l, se.enums),
    }
}

pub open spec fn over_ok(over: Over, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, g: Expr, n: nat, us: Seq<Expr>, xt: XTy) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> over_at(
            over,
            cx,
            sc,
            b0,
            b1,
            g,
            n,
            us,
            xt,
            env,
            se,
            ls,
            sls,
        )
}

/// 番号から作ったスロットは、正規順でその番号の値を表す。
pub proof fn lemma_unrank_bound(st: STy, n: nat, us: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>, enums: Seq<i64>)
    requires
        unrank_ok(st, Expr::Local(l.len() as usize), us, enums),
        keys(st, enums) == Some(n),
        n <= 0x7fff_ffff,
        l.len() < usize::MAX,
        bits.len() == n,
    ensures
        bound_at(us, to_xty(st), domain(st, enums), bits, env, l, enums),
{
    assert forall|x: int| 0 <= x < bits.len() && bits[x] implies #[trigger] denotes(
        us,
        env,
        l.push(Value::Int(x as i64)),
        domain(st, enums)[x],
        to_xty(st),
        enums,
    ) by {
        let lx = l.push(Value::Int(x as i64));
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
        lemma_domain_rank(st, enums, x);
        lemma_models_enc(domain(st, enums)[x], st, enums);
    }
}

/// 型の全体をたどる量化のガードは、つねに真である。
pub proof fn lemma_over_type(over: Over, cx: LowerCtx, sc: Seq<Bound>, b: Block, n: nat, us: Seq<Expr>)
    requires
        over is Type,
        keys(sty(over->Type_0), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        b.depth_s() < usize::MAX,
        unrank_ok(sty(over->Type_0), Expr::Local(b.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b, b, bool_lit(true), n, us, to_xty(sty(over->Type_0))),
{
    let st = sty(over->Type_0);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies over_at(
        over,
        cx,
        sc,
        b,
        b,
        bool_lit(true),
        n,
        us,
        to_xty(st),
        env,
        se,
        ls,
        sls,
    ) by {
        let enums = se.enums;
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        let bits = Seq::new(n, |i: int| true);
        lemma_select_all(dom, n);
        assert(dom.take(n as int) =~= dom);
        assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(
            bool_lit(true),
            env,
            ls.push(Value::Int(x as i64)),
        ) == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {}
        lemma_unrank_bound(st, n, us, bits, env, ls, enums);
        assert(sel_ok(dom, dom, bits, n, bool_lit(true), us, to_xty(st), env, ls, enums));
    }
}

/// 下ろした式の列 `fs` が印 `bits` を表すなら、位置を選ぶ式 `g` は位置ごとのガードになる。
pub proof fn lemma_guard_pick(g: Expr, fs: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        picks(g, fs, Expr::Local(l.len() as usize)),
        vals_at(fs, Seq::new(bits.len(), |j: int| Value::Bool(bits[j])), env, l),
        l.len() < usize::MAX,
        bits.len() <= 0x7fff_ffff,
    ensures
        guard_at(g, bits, env, l),
{
    let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
    assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(g, env, l.push(Value::Int(x as i64)))
        == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {
        let lx = l.push(Value::Int(x as i64));
        assert(prefix(l, lx));
        lemma_vals_weaken(fs, vals, env, l, lx);
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
    }
}

/// Setの要素をたどる量化のガード。
pub proof fn lemma_over_set(
    over: Over,
    t: SType,
    s: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    cs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
)
    requires
        over == Over::Set(t, Box::new(s)),
        lowers(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        cs.len() == n,
        picks(g, cs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t))),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        n,
        us,
        to_xty(sty(t)),
        env,
        se,
        ls,
        sls,
    ) by {
        lemma_over_set_at(over, t, s, cx, sc, b0, b1, cs, g, n, us, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_over_set_at(
    over: Over,
    t: SType,
    s: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    cs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        over == Over::Set(t, Box::new(s)),
        lowers(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        cs.len() == n,
        picks(g, cs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        over_at(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t)), env, se, ls, sls),
{
    let st = sty(t);
    lemma_one(s, cx, sc, b0, b1, XTy::Set(Box::new(st)), cs, env, se, ls, sls);
    if let Ok(v) = eval_src(s, se, sls) {
        let enums = se.enums;
        let l = run(fresh(b0, b1), env, ls)->Ok_0;
        let bits = v->Set_0;
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        assert(slot_vals(cs, env, l) == enc(v, STy::Set(Box::new(st)), enums));
        let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
        assert forall|j: int| 0 <= j < cs.len() implies pure_below(#[trigger] cs[j], l.len()) && eval_l(cs[j], env, l)
            == Ok::<Value, ErrKind>(vals[j]) by {
            assert(slot_vals(cs, env, l)[j] == eval_l(cs[j], env, l)->Ok_0);
        }
        assert(vals_at(cs, vals, env, l));
        lemma_guard_pick(g, cs, bits, env, l);
        lemma_unrank_bound(st, n, us, bits, env, l, enums);
        assert(sel_ok(select_bits(dom, bits), dom, bits, n, g, us, to_xty(st), env, l, enums));
    }
}

/// Mapのキーをたどる量化のガード。`fs` は各行の有無のスロットである。
pub proof fn lemma_over_map(
    over: Over,
    t: SType,
    m: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
)
    requires
        over == Over::Map(t, Box::new(m)),
        lowers(m, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(sv)), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
        picks(g, fs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t))),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        n,
        us,
        to_xty(sty(t)),
        env,
        se,
        ls,
        sls,
    ) by {
        lemma_over_map_at(over, t, m, cx, sc, b0, b1, sv, stride, cs, fs, g, n, us, env, se, ls, sls);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_over_map_at(
    over: Over,
    t: SType,
    m: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    sv: STy,
    stride: int,
    cs: Seq<Expr>,
    fs: Seq<Expr>,
    g: Expr,
    n: nat,
    us: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        over == Over::Map(t, Box::new(m)),
        lowers(m, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(sv)), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
        picks(g, fs, Expr::Local(b1.depth_s() as usize)),
        unrank_ok(sty(t), Expr::Local(b1.depth_s() as usize), us, cx.enums@),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        over_at(over, cx, sc, b0, b1, g, n, us, to_xty(sty(t)), env, se, ls, sls),
{
    let st = sty(t);
    let xt = XTy::Map(Box::new(st), Box::new(sv));
    lemma_one(m, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
    if let Ok(v) = eval_src(m, se, sls) {
        let enums = se.enums;
        let l = run(fresh(b0, b1), env, ls)->Ok_0;
        let rows = v->Map_0;
        let bits = Seq::new(rows.len(), |i: int| rows[i] is Some);
        let dom = domain(st, enums);
        lemma_domain_len(st, enums);
        assert(slot_vals(cs, env, l) == enc_rows(rows, sv, enums));
        let vals = Seq::new(bits.len(), |j: int| Value::Bool(bits[j]));
        assert forall|q: int| 0 <= q < fs.len() implies pure_below(#[trigger] fs[q], l.len()) && eval_l(fs[q], env, l)
            == Ok::<Value, ErrKind>(vals[q]) by {
            lemma_enc_rows_index(rows, sv, enums, q, 0);
            let at = q * stride;
            assert(slot_vals(cs, env, l)[at] == eval_l(cs[at], env, l)->Ok_0);
            assert(row_slots(rows[q], sv, enums)[0] == Value::Bool(rows[q] is Some));
        }
        assert(vals_at(fs, vals, env, l));
        lemma_guard_pick(g, fs, bits, env, l);
        lemma_unrank_bound(st, n, us, bits, env, l, enums);
        assert(sel_ok(select_bits(dom, bits), dom, bits, n, g, us, to_xty(st), env, l, enums));
    }
}

/// Listの要素のスロットの列のうち、各要素の `j` 番目のスロット。
pub open spec fn list_col(cs: Seq<Expr>, w: int, max: nat, j: int) -> Seq<Expr> {
    Seq::new(max, |k: int| cs[1 + k * w + j])
}

/// Listの要素の位置の列。長さ `max` に足りない分は使わない値で埋める。
pub open spec fn list_dom(items: Seq<SVal>, max: nat) -> Seq<SVal> {
    Seq::new(max, |i: int| if i < items.len() { items[i] } else { SVal::Bool(false) })
}

/// Listの要素をたどる量化。位置は添字で、ガードは添字が長さより小さいことである。
pub proof fn lemma_over_list(
    over: Over,
    li: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    st: STy,
    max: nat,
    w: int,
    cs: Seq<Expr>,
    us: Seq<Expr>,
    g: Expr,
)
    requires
        over == Over::List(Box::new(li)),
        lowers(li, cx, sc, b0, b1, XTy::List(Box::new(st), max as usize), cs),
        extends(b0, b1),
        b1.depth_s() < usize::MAX,
        max <= 0x7fff_ffff,
        w == width(st, cx.enums@),
        cs.len() > 0,
        us.len() == w,
        forall|j: int| 0 <= j < w ==> #[trigger] picks(us[j], list_col(cs, w, max, j), Expr::Local(b1.depth_s() as usize)),
        g == Expr::Bin(BinOp::Lt, Box::new(Expr::Local(b1.depth_s() as usize)), Box::new(cs[0])),
    ensures
        over_ok(over, cx, sc, b0, b1, g, max, us, to_xty(st)),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies over_at(
        over,
        cx,
        sc,
        b0,
        b1,
        g,
        max,
        us,
        to_xty(st),
        env,
        se,
        ls,
        sls,
    ) by {
        let xt = XTy::List(Box::new(st), max as usize);
        lemma_one(li, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
        if let Ok(v) = eval_src(li, se, sls) {
            let enums = se.enums;
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let items = v->List_0;
            let len = items.len();
            let dom = list_dom(items, max);
            let bits = Seq::new(max, |i: int| i < len);
            lemma_list_quant_at(st, max, w, cs, us, g, items, env, l, enums);
            lemma_select_prefix(dom, max, len);
            assert(dom.take(len as int) =~= items);
            assert(sel_ok(items, dom, bits, max, g, us, to_xty(st), env, l, enums));
        }
    }
}

/// Listの値を表すスロットから選んだガードと要素のスロット。
pub proof fn lemma_list_quant_at(
    st: STy,
    max: nat,
    w: int,
    cs: Seq<Expr>,
    us: Seq<Expr>,
    g: Expr,
    items: Seq<SVal>,
    env: Env,
    l: Seq<Value>,
    enums: Seq<i64>,
)
    requires
        denotes(cs, env, l, SVal::List(items), XTy::List(Box::new(st), max as usize), enums),
        l.len() < usize::MAX,
        max <= 0x7fff_ffff,
        w == width(st, enums),
        us.len() == w,
        forall|j: int| 0 <= j < w ==> #[trigger] picks(us[j], list_col(cs, w, max, j), Expr::Local(l.len() as usize)),
        g == Expr::Bin(BinOp::Lt, Box::new(Expr::Local(l.len() as usize)), Box::new(cs[0])),
    ensures
        items.len() <= max,
        guard_at(g, Seq::new(max, |i: int| i < items.len()), env, l),
        bound_at(us, to_xty(st), list_dom(items, max), Seq::new(max, |i: int| i < items.len()), env, l, enums),
{
    let lt = STy::List(Box::new(st), max as usize);
    let len = items.len();
    let bits = Seq::new(max, |i: int| i < len);
    let dom = list_dom(items, max);
    let sv = slot_vals(cs, env, l);
    let ei = enc_items(items, st, enums);
    let pad = enc_repeat(enc(default_val(st, enums), st, enums), (max - len) as nat);
    assert(member(SVal::List(items), lt, enums));
    assert(sv == seq![Value::Int(len as i64)] + ei + pad);
    lemma_enc_items_len(items, st, enums);
    lemma_default_len(st, enums);
    lemma_repeat_len(enc(default_val(st, enums), st, enums), (max - len) as nat);
    assert(sv.len() == 1 + max * w) by (nonlinear_arith)
        requires
            sv.len() == 1 + len * w + (max - len) * w,
            len <= max,
    ;
    assert(sv[0] == Value::Int(len as i64));
    assert(eval_l(cs[0], env, l) == Ok::<Value, ErrKind>(Value::Int(len as i64)));
    assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(g, env, l.push(Value::Int(x as i64)))
        == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {
        let lx = l.push(Value::Int(x as i64));
        lemma_weaken(cs[0], env, l, lx);
        assert(eval_l(Expr::Local(l.len() as usize), env, lx) == Ok::<Value, ErrKind>(Value::Int(x as i64)));
    }
    assert forall|x: int| 0 <= x < bits.len() && bits[x] implies #[trigger] denotes(
        us,
        env,
        l.push(Value::Int(x as i64)),
        dom[x],
        to_xty(st),
        enums,
    ) by {
        let lx = l.push(Value::Int(x as i64));
        assert(prefix(l, lx));
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
        let item = items[x];
        assert(dom[x] == item);
        assert forall|j: int| 0 <= j < us.len() implies pure_below(#[trigger] us[j], lx.len()) && eval_l(us[j], env, lx)
            == Ok::<Value, ErrKind>(enc(item, st, enums)[j]) by {
            let col = list_col(cs, w, max, j);
            let vals = Seq::new(max, |k: int| sv[1 + k * w + j]);
            assert forall|k: int| 0 <= k < col.len() implies pure_below(#[trigger] col[k], l.len()) && eval_l(col[k], env, l)
                == Ok::<Value, ErrKind>(vals[k]) by {
                assert(0 <= 1 + k * w + j < 1 + max * w) by (nonlinear_arith)
                    requires
                        0 <= k < max,
                        0 <= j < w,
                ;
                assert(sv[1 + k * w + j] == eval_l(cs[1 + k * w + j], env, l)->Ok_0);
            }
            assert(vals_at(col, vals, env, l));
            lemma_vals_weaken(col, vals, env, l, lx);
            lemma_items_index(items, st, enums, x, j);
            assert(sv[1 + x * w + j] == ei[x * w + j]);
            assert forall|k: int| 0 <= k < col.len() implies pure_below(#[trigger] col[k], lx.len()) by {
                lemma_pure_mono(col[k], l.len(), lx.len());
            }
            assert(all_pure(col, lx.len()));
            let r = Expr::Local(l.len() as usize);
            assert(pure_below(r, lx.len()));
            assert(picks(us[j], col, r));
            assert(pure_below(us[j], lx.len()));
            assert(at_rank(r, env, lx, x as i64));
            assert(eval_l(us[j], env, lx) == Ok::<Value, ErrKind>(vals[x]));
            assert(vals[x] == sv[1 + x * w + j]);
        }
        lemma_items_member(items, st, enums, x);
        lemma_enc_len(item, st, enums);
        assert(slot_vals(us, env, lx) =~= enc(item, st, enums));
        lemma_models_enc(item, st, enums);
    }
}

/// 量化の値の意味論を、たどる値の列で書き直す。
pub proof fn lemma_quant_src(e: TExpr, all: bool, over: Over, body: TExpr, se: SEnv, sls: Seq<SVal>)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
    ensures
        eval_src(e, se, sls) == match src_items(over, se, sls) {
            Err(k) => Err(k),
            Ok(xs) => match eval_quant(all, xs, body, se, sls) {
                Err(k) => Err(k),
                Ok(b) => Ok(SVal::Bool(b)),
            },
        },
{
}

/// 位置 `x` を束縛した文脈。
pub proof fn lemma_quant_ctx(cx: LowerCtx, sc: Seq<Bound>, bd: Bound, env: Env, se: SEnv, l: Seq<Value>, sls: Seq<SVal>, x: int, v: SVal)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        denotes(bd.slots@, env, l.push(Value::Int(x as i64)), v, xty(bd.ty), se.enums),
    ensures
        ctx_ok(cx, sc.push(bd), env, se, l.push(Value::Int(x as i64)), sls.push(v)),
{
    let lx = l.push(Value::Int(x as i64));
    let enums = se.enums;
    assert(prefix(l, lx));
    lemma_ctx_weaken(cx, sc, env, se, l, lx, sls);
    let sc2 = sc.push(bd);
    let sls2 = sls.push(v);
    assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(sc2[i].slots@, env, lx, sls2[i], xty(sc2[i].ty), enums) by {
        if i < sc.len() {
            assert(sc2[i] == sc[i] && sls2[i] == sls[i]);
        }
    }
}

/// 位置 `x` での量化の本体の真偽。
pub proof fn lemma_quant_step(
    all: bool,
    g: Expr,
    b: Expr,
    qb: Expr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    bd: Bound,
    body: TExpr,
    env: Env,
    se: SEnv,
    l: Seq<Value>,
    sls: Seq<SVal>,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    x: int,
)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        guard_at(g, bits, env, l),
        bound_at(bd.slots@, xty(bd.ty), dom, bits, env, l, se.enums),
        combine_ok(all, g, b, qb),
        closed_lowers(body, cx, sc.push(bd), l.len() + 1, XTy::Bool, b),
        0 <= x < bits.len(),
    ensures
        as_bool(eval_l(qb, env, l.push(Value::Int(x as i64)))) == if bits[x] {
            src_bool(eval_src(body, se, sls.push(dom[x])))
        } else {
            Ok::<bool, ErrKind>(all)
        },
{
    let lx = l.push(Value::Int(x as i64));
    assert(eval_l(g, env, lx) == Ok::<Value, ErrKind>(Value::Bool(bits[x])));
    assert(as_bool(eval_l(qb, env, lx)) == match as_bool(eval_l(g, env, lx)) {
        Err(k) => Err(k),
        Ok(true) => as_bool(eval_l(b, env, lx)),
        Ok(false) => Ok::<bool, ErrKind>(all),
    });
    if bits[x] {
        let sls2 = sls.push(dom[x]);
        assert(denotes(bd.slots@, env, lx, dom[x], xty(bd.ty), se.enums));
        lemma_quant_ctx(cx, sc, bd, env, se, l, sls, x, dom[x]);
        assert(ctx_ok(cx, sc.push(bd), env, se, lx, sls2));
        lemma_scalar_bool(eval_src(body, se, sls2), eval_l(b, env, lx), se.enums);
    }
}

/// 量化の下ろし。対象を下ろし、位置を1つの整数でたどる量化を束縛する。
pub proof fn lemma_quant(
    e: TExpr,
    all: bool,
    over: Over,
    body: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    n: nat,
    g: Expr,
    bd: Bound,
    b: Expr,
    qb: Expr,
    q: Expr,
)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
        over_ok(over, cx, sc, b0, b1, g, n, bd.slots@, xty(bd.ty)),
        n <= 0x7fff_ffff,
        closed_lowers(body, cx, sc.push(bd), b1.depth_s() + 1, XTy::Bool, b),
        combine_ok(all, g, b, qb),
        q == quant_s(all, Type::Int(0, if n == 0 { 0i64 } else { (n - 1) as i64 }), 0, (n - 1) as i64, qb),
        b2.binds@ == b1.binds@.push(q),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let z = Expr::Local(b1.depth_s() as usize);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![z],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_quant_src(e, all, over, body, se, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(xs) = src_items(over, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let dom = over_dom(over, se, sls, n);
            let bits = over_sel(over, se, sls, n);
            assert forall|x: int| 0 <= x < bits.len() implies #[trigger] as_bool(
                eval_l(qb, env, l.push(Value::Int(x as i64))),
            ) == if bits[x] {
                src_bool(eval_src(body, se, sls.push(dom[x])))
            } else {
                Ok::<bool, ErrKind>(all)
            } by {
                lemma_quant_step(all, g, b, qb, cx, sc, bd, body, env, se, l, sls, dom, bits, x);
            }
            assert(q_step_ok(all, qb, env, l, bits, dom, body, se, sls));
            let ty = Type::Int(0, if n == 0 { 0 } else { (n - 1) as i64 });
            assert(bits.take(0) =~= Seq::<bool>::empty());
            assert(qprefix(all, dom, bits, 0, body, se, sls) == QState::Open);
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, 0);
            assert(bits.take(bits.len() as int) =~= bits);
            let res = eval_quant(all, xs, body, se, sls);
            assert(eval_l(q, env, l) == lift_bool(res));
            lemma_run_one(b1, b2, q, env, l);
            if let Ok(bv) = res {
                lemma_one_denotes(z, env, l.push(Value::Bool(bv)), Value::Bool(bv), XTy::Bool, se.enums);
            }
        }
    }
}

/// 正規順の列 `dom` のうち、`bits` の先頭 `n` 個で選んだ値をたどった量化の状態。
pub open spec fn qprefix(all: bool, dom: Seq<SVal>, bits: Seq<bool>, n: int, body: TExpr, se: SEnv, sls: Seq<SVal>) -> QState {
    eval_qstate(all, select_bits(dom, bits.take(n)), body, se, sls)
}

/// 状態に、本体を1つ評価した結果を加える。
pub open spec fn qstep(all: bool, st: QState, r: Result<bool, ErrKind>) -> QState {
    match st {
        QState::Decided(b) => QState::Decided(b),
        _ => match r {
            Ok(b) => if b != all {
                QState::Decided(b)
            } else {
                st
            },
            Err(k) => match st {
                QState::Open => QState::Pending(k),
                _ => st,
            },
        },
    }
}

/// 値の決まっていない状態が保留している失敗。
pub open spec fn qpend(st: QState) -> Option<ErrKind> {
    match st {
        QState::Pending(k) => Some(k),
        _ => None,
    }
}

/// 1つ先の位置までの量化の状態。選ばない位置では変わらず、選ぶ位置ではその値で本体を評価した結果を加える。
pub(crate) proof fn lemma_qprefix_next(all: bool, dom: Seq<SVal>, bits: Seq<bool>, n: int, body: TExpr, se: SEnv, sls: Seq<SVal>)
    requires
        0 <= n < bits.len(),
    ensures
        qprefix(all, dom, bits, n + 1, body, se, sls) == if bits[n] {
            qstep(all, qprefix(all, dom, bits, n, body, se, sls), src_bool(eval_src(body, se, sls.push(dom[n]))))
        } else {
            qprefix(all, dom, bits, n, body, se, sls)
        },
{
    let t = bits.take(n + 1);
    assert(t.drop_last() =~= bits.take(n));
    assert(t.last() == bits[n]);
    let pre = select_bits(dom, bits.take(n));
    if bits[n] {
        assert(select_bits(dom, t) == pre.push(dom[n]));
        assert(pre.push(dom[n]).drop_last() =~= pre);
    } else {
        assert(select_bits(dom, t) == pre);
    }
}

/// 量化の値が決まったら、先をたどっても変わらない。
pub(crate) proof fn lemma_qprefix_stuck(
    all: bool,
    dom: Seq<SVal>,
    bits: Seq<bool>,
    n: int,
    m: int,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
)
    requires
        0 <= n <= m <= bits.len(),
        qprefix(all, dom, bits, n, body, se, sls) is Decided,
    ensures
        qprefix(all, dom, bits, m, body, se, sls) == qprefix(all, dom, bits, n, body, se, sls),
    decreases m - n,
{
    if m > n {
        lemma_qprefix_stuck(all, dom, bits, n, m - 1, body, se, sls);
        lemma_qprefix_next(all, dom, bits, m - 1, body, se, sls);
    }
}

/// 番号 `x` で本体を評価した真偽は、選ぶ位置では値の意味論の本体の真偽になり、選ばない位置では `all` になる。
pub open spec fn q_step_ok(
    all: bool,
    qb: Expr,
    env: Env,
    l: Seq<Value>,
    bits: Seq<bool>,
    dom: Seq<SVal>,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
) -> bool {
    forall|x: int|
        0 <= x < bits.len() ==> #[trigger] as_bool(eval_l(qb, env, l.push(Value::Int(x as i64)))) == if bits[x] {
            src_bool(eval_src(body, se, sls.push(dom[x])))
        } else {
            Ok::<bool, ErrKind>(all)
        }
}

/// 番号 `n..` をたどる量化の値は、先頭から選んだ値をたどる量化の値になる。
/// 番号の量化が保留している失敗は、値の量化の状態が保留している失敗と同じである。
pub proof fn lemma_qscan(
    all: bool,
    ty: Type,
    qb: Expr,
    env: Env,
    l: Seq<Value>,
    bits: Seq<bool>,
    dom: Seq<SVal>,
    body: TExpr,
    se: SEnv,
    sls: Seq<SVal>,
    n: int,
)
    requires
        ty is Int,
        0 <= n <= bits.len() <= 0x7fff_ffff,
        q_step_ok(all, qb, env, l, bits, dom, body, se, sls),
        !(qprefix(all, dom, bits, n, body, se, sls) is Decided),
    ensures
        quant_l(all, ty, qb, env, l, n, bits.len() - 1, qpend(qprefix(all, dom, bits, n, body, se, sls)))
            == lift_bool(qresult(all, qprefix(all, dom, bits, bits.len() as int, body, se, sls))),
    decreases bits.len() - n,
{
    let st = qprefix(all, dom, bits, n, body, se, sls);
    if n < bits.len() {
        assert(decode(ty, n as i64) == Value::Int(n as i64));
        let s = as_bool(eval_l(qb, env, l.push(Value::Int(n as i64))));
        assert(s == if bits[n] {
            src_bool(eval_src(body, se, sls.push(dom[n])))
        } else {
            Ok::<bool, ErrKind>(all)
        });
        lemma_qprefix_next(all, dom, bits, n, body, se, sls);
        assert(qprefix(all, dom, bits, n + 1, body, se, sls) == qstep(all, st, s));
        if s == Ok::<bool, ErrKind>(all) {
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, n + 1);
        } else if s is Err {
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, n + 1);
        } else {
            lemma_qprefix_stuck(all, dom, bits, n + 1, bits.len() as int, body, se, sls);
        }
    } else {
        assert(bits.take(n) =~= bits.take(bits.len() as int));
    }
}

/// すべての位置を選ぶと、列そのものになる。
pub proof fn lemma_select_all(dom: Seq<SVal>, n: nat)
    requires
        n <= dom.len(),
    ensures
        select_bits(dom, Seq::new(n, |i: int| true)) == dom.take(n as int),
    decreases n,
{
    if n > 0 {
        let bits = Seq::new(n, |i: int| true);
        assert(bits.drop_last() =~= Seq::new((n - 1) as nat, |i: int| true));
        lemma_select_all(dom, (n - 1) as nat);
        assert(dom.take(n - 1).push(dom[n - 1]) =~= dom.take(n as int));
    } else {
        assert(dom.take(0) =~= Seq::<SVal>::empty());
    }
}

/// 先頭の `len` 個の位置を選ぶと、列の先頭になる。
pub proof fn lemma_select_prefix(dom: Seq<SVal>, m: nat, len: nat)
    requires
        m <= dom.len(),
    ensures
        select_bits(dom, Seq::new(m, |i: int| i < len)) == dom.take(if m <= len { m as int } else { len as int }),
    decreases m,
{
    if m > 0 {
        let bits = Seq::new(m, |i: int| i < len);
        assert(bits.drop_last() =~= Seq::new((m - 1) as nat, |i: int| i < len));
        lemma_select_prefix(dom, (m - 1) as nat, len);
        if m <= len {
            assert(dom.take(m - 1).push(dom[m - 1]) =~= dom.take(m as int));
        }
    } else {
        assert(dom.take(0) =~= Seq::<SVal>::empty());
    }
}

} // verus!
