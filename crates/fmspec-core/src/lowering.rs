//! IRの型付き構文木を、中核の式に下ろす。
//!
//! 複合型の値は、[`crate::encoding`] の配置に従ってスロットの列で表す。式は、スロットごとの中核の式に下ろす。
//!
//! 部分式の評価の順序と打ち切りは、値の上の意味論（[`crate::source::eval_src`]）と一致させる。
//! そのために、下ろした式は「束縛の列」（[`Block`]）と「スロットの式」の組で表す。
//! 束縛は、評価の順に `let` で局所変数に束縛する式で、失敗しうる計算はすべてここに置く。
//! スロットの式は失敗せず、束縛子（`let`、量化）も含まないので、どの深さで評価しても同じ値になる。
//! 短絡する演算（`all`、`any`、`implies`、`ite`）と量化の本体は、評価する位置の深さで
//! 独立に下ろし、外側の束縛の列には混ぜない。
//!
//! 局所変数は外側から数えた添字で指すので、下ろした式は評価する深さに依存する。
//! 束縛子を含む式は、作った深さでただちに束縛する。
//!
//! 下ろしは、型の合わない式や、長さの合わないスロットの列に対して `None` を返す。

#[cfg(verus_keep_ghost)]
use crate::bindings::eval_bound_body;
use crate::encoding::{copy_stype, copy_xtype, keys_exec, stype_eq, to_xtype, usizes_eq, xtype_eq, SType, XType};
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, enc_rows, keys, keys_or_zero, member, sty, stys, width, STy, SVal};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_enc_len, lemma_models_enc, lemma_stys, lemma_xtys, models};
#[cfg(verus_keep_ghost)]
use crate::encoding::{to_xty, xty, xtys, xwidth, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, lookup, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::keys::{domain, lemma_domain_len, lemma_domain_rank, lemma_rank_in_domain, rank};
#[cfg(verus_keep_ghost)]
use crate::map_lookup::{flat_slot, flat_slot_int, key_rank, MISSING_KEY};
use crate::map_lookup::{put_map_rows_exec, select_flat_map_lookup};
use crate::model::{BinOp, Expr, Type, Value};
use crate::preserve::pure_exec;
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
#[cfg(verus_keep_ghost)]
use crate::quant::unrank_ok;
#[cfg(verus_keep_ghost)]
use crate::quant::{at_rank, flags_at, lemma_flags_weaken, lemma_qscan, lemma_select_all, picks, q_step_ok, qprefix};
use crate::quant::{pick_flag, unrank};
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_fold, eval_quant, eval_src, select_bits, src_bool, SEnv};
use crate::source::{Over, SetOp, TExpr, FAIL_EMPTY, FAIL_FULL, FAIL_INDEX, FAIL_NONE, FAIL_NOT_IN_DOMAIN};
use vstd::prelude::*;

verus! {

/// 状態変数や引数の、スロットの列での位置。
pub struct Layout {
    pub ty: SType,
    pub offset: usize,
}

/// 名前付きの定数。値はスロットごとの中核の値。
pub struct Constant {
    pub ty: SType,
    pub slots: Vec<Value>,
}

/// 下ろしの文脈。
pub struct LowerCtx {
    /// 各列挙型のラベルの数。
    pub enums: Vec<i64>,
    /// 状態変数。`None` なら状態を参照できない（初期値と定数）。
    pub states: Option<Vec<Layout>>,
    /// 公開引数に続けて内部選択。
    pub args: Vec<Layout>,
    /// 遷移後の状態と出力を参照できる（遷移契約）。
    pub next: bool,
    pub out: Option<SType>,
    pub consts: Vec<Constant>,
}

/// 局所変数（`let` と量化の束縛）。
pub struct Bound {
    pub ty: XType,
    pub slots: Vec<Expr>,
}

/// 値を型 `st` の場所に置けるか。整数の範囲は問わない（値ごとに検査する）。
pub fn fits(t: &XType, st: &SType) -> (r: bool)
    ensures
        r ==> fits_s(xty(*t), sty(*st)),
    decreases t, 1nat,
{
    match (t, st) {
        (XType::Bool, SType::Bool) => true,
        (XType::Int, SType::Int(_, _)) => true,
        (XType::Enum(a), SType::Enum(b)) => *a == *b,
        (XType::Tuple(xs), SType::Tuple(ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            fits_all(t, xs, ts)
        },
        (XType::Record(a, xs), SType::Record(b, ts)) => {
            proof {
                assert(decreases_to!(*t => *xs));
            }
            usizes_eq(a, b) && fits_all(t, xs, ts)
        },
        (XType::Option(x), SType::Option(u)) => fits(x, u),
        (XType::Set(a), SType::Set(b)) => stype_eq(a, b),
        (XType::Map(ka, va), SType::Map(kb, vb)) => stype_eq(ka, kb) && stype_eq(va, vb),
        (XType::List(a, n), SType::List(b, m)) => *n == *m && stype_eq(a, b),
        _ => false,
    }
}

fn fits_all(_parent: &XType, xs: &Vec<XType>, ts: &Vec<SType>) -> (r: bool)
    requires
        decreases_to!(*_parent => *xs),
    ensures
        r ==> fits_all_s(xtys(xs@), stys(ts@)),
    decreases _parent, 0nat,
{
    if xs.len() != ts.len() {
        return false;
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            decreases_to!(*_parent => *xs),
            xs.len() == ts.len(),
            i <= xs.len(),
            forall|j: int| 0 <= j < i ==> fits_s(#[trigger] xty(xs@[j]), sty(ts@[j])),
        decreases xs.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*xs, i as int);
        }
        if !fits(&xs[i], &ts[i]) {
            return false;
        }
        i += 1;
    }
    proof {
        lemma_xtys(xs@);
        lemma_stys(ts@);
        lemma_fits_all(xtys(xs@), stys(ts@));
        assert forall|j: int| 0 <= j < xs@.len() implies #[trigger] fits_s(xtys(xs@)[j], stys(ts@)[j]) by {
            assert(fits_s(xty(xs@[j]), sty(ts@[j])));
        }
    }
    true
}

/// 状態変数や引数のスロット。`kind` は 0 が遷移前の状態変数、1 が遷移後の状態変数、2 が引数。
fn layout_slots(l: &Layout, kind: u8, enums: &Vec<i64>) -> (r: Option<(XType, Vec<Expr>)>)
    ensures
        r matches Some((t, out)) ==> xty(t) == to_xty(sty(l.ty)) && out@.len() == width(sty(l.ty), enums@) && forall|j: int|
            0 <= j < out@.len() ==> #[trigger] out@[j] == kind_expr(kind, (l.offset + j) as usize),
{
    let w = stype_width(&l.ty, enums)?;
    let end = l.offset.checked_add(w)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = l.offset;
    while i < end
        invariant
            l.offset <= i <= end,
            end == l.offset + w,
            out@.len() == i - l.offset,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] == kind_expr(kind, (l.offset + j) as usize),
        decreases end - i,
    {
        out.push(
            if kind == 0 {
                Expr::Var(i)
            } else if kind == 1 {
                Expr::Next(i)
            } else {
                Expr::Arg(i)
            },
        );
        i += 1;
    }
    Some((to_xtype(&l.ty), out))
}

fn lit_type(v: &Value) -> (r: XType)
    ensures
        xty(r) == match *v {
            Value::Bool(_) => XTy::Bool,
            Value::Int(_) => XTy::Int,
            Value::Enum(id, _) => XTy::Enum(id),
        },
{
    match v {
        Value::Bool(_) => XType::Bool,
        Value::Int(_) => XType::Int,
        Value::Enum(id, _) => XType::Enum(*id),
    }
}

/// `xs` の各スロットを、何度も参照できるように束縛する。
fn atoms(xs: Vec<Expr>, blk: &mut Block) -> (r: Option<Vec<Expr>>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r matches Some(out) ==> atoms_ok(xs@, out@, *old(blk), *final(blk)),
{
    let ghost b0 = *blk;
    let mut out: Vec<Expr> = Vec::new();
    proof {
        lemma_extends_refl(*blk);
        lemma_atoms_empty(*blk);
        assert(xs@.take(0) =~= Seq::<Expr>::empty());
    }
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            extends(b0, *blk),
            atoms_ok(xs@.take(i as int), out@, b0, *blk),
            b0 == *old(blk),
        decreases xs.len() - i,
    {
        let ghost b1 = *blk;
        let ghost o1 = out@;
        let x = copy_expr(&xs[i]);
        let y = atom(blk, x)?;
        out.push(y);
        proof {
            lemma_atoms_step(xs@.take(i as int), x, o1, y, b0, b1, *blk);
            assert(xs@.take(i as int).push(x) =~= xs@.take(i + 1));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs.len() as int) =~= xs@);
    }
    Some(out)
}

/// 局所変数 `lo..hi` のスロット。
fn locals(lo: usize, hi: usize) -> (r: Vec<Expr>) {
    let mut out: Vec<Expr> = Vec::new();
    let mut i = lo;
    while i < hi
        decreases hi - i,
    {
        out.push(Expr::Local(i));
        i += 1;
    }
    out
}

fn append(out: &mut Vec<Expr>, xs: &Vec<Expr>) {
    let mut i = 0;
    while i < xs.len()
        decreases xs.len() - i,
    {
        out.push(copy_expr(&xs[i]));
        i += 1;
    }
}

/// 長さ `n` の、一つの式を並べた行の列。
fn singletons(xs: &Vec<Expr>) -> (r: Vec<Vec<Expr>>) {
    let mut rows: Vec<Vec<Expr>> = Vec::new();
    let mut i = 0;
    while i < xs.len()
        decreases xs.len() - i,
    {
        let mut row: Vec<Expr> = Vec::new();
        row.push(copy_expr(&xs[i]));
        rows.push(row);
        i += 1;
    }
    rows
}

/// 行を選び、その唯一のスロットを返す。行がなければ偽。
fn select_one(rows: &Vec<Vec<Expr>>, idx: &Expr) -> (r: Option<Expr>) {
    let mut fallback: Vec<Expr> = Vec::new();
    fallback.push(cb(false));
    let mut picked = select(rows, idx, &fallback)?;
    match picked.pop() {
        Some(x) => Some(x),
        None => Some(cb(false)),
    }
}

/// 式を `blk` の中に下ろす。部分式の束縛は評価の順に `blk` に追加し、失敗しないスロットの式を返す。
fn low(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 2nat,
{
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_)
        | TExpr::Bin(_, _, _) | TExpr::Eq(_, _, _) | TExpr::Not(_) | TExpr::Fold(_, _) | TExpr::Implies(_, _)
        | TExpr::Ite(_, _, _) | TExpr::Let(_, _) => low_core(e, cx, sc, blk),
        TExpr::Quant(_, _, _) | TExpr::Tuple(_) | TExpr::Record(_, _) | TExpr::Nth(_, _) | TExpr::Field(_, _, _)
        | TExpr::None(_) | TExpr::Some(_) | TExpr::IsSome(_) | TExpr::IsNone(_) | TExpr::Unwrap(_) => low_struct(
            e,
            cx,
            sc,
            blk,
        ),
        TExpr::SetLit(_, _) | TExpr::MapLit(_, _, _) | TExpr::ListLit(_, _, _) | TExpr::SetContains(_, _, _)
        | TExpr::ListContains(_, _) | TExpr::Insert(_, _, _) | TExpr::Remove(_, _, _) | TExpr::SetBin(_, _, _)
        | TExpr::Size(_) | TExpr::IsEmpty(_) => low_coll(e, cx, sc, blk),
        _ => low_access(e, cx, sc, blk),
    }
}

/// 型 `want` のスカラーの式として下ろす。
fn sub_scalar(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, want: &XType) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some(x) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(*want), seq![x]),
    decreases e, 3nat,
{
    let (t, slots) = low(e, cx, sc, blk)?;
    if !xtype_eq(&t, want) || slots.len() != 1 {
        return None;
    }
    let x = copy_expr(&slots[0]);
    proof {
        assert(slots@ =~= seq![x]);
    }
    Some(x)
}

/// 深さ `depth` で単独に評価できるように下ろす。スロットごとに、束縛を含む式を返す。
fn closed_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Option<(XType, Vec<Expr>)>)
    ensures
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, xs)) ==> frag(*e) ==> closed_slots(*e, *cx, old(sc)@, depth as nat, xty(t), xs@),
    decreases e, 4nat,
{
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < slots.len()
        invariant
            i <= slots@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, slots@[j]),
        decreases slots.len() - i,
    {
        let x = wrap(&blk.binds, copy_expr(&slots[i]));
        out.push(x);
        proof {
            assert(wraps(out@[i as int], blk.binds@, slots@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        if frag(*e) {
            assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == depth as nat implies slots_result(
                eval_src(*e, se, sls),
                out@,
                env,
                ls,
                xty(t),
                se.enums,
            ) by {
                match eval_src(*e, se, sls) {
                    Ok(v) => {
                        let l = run(blk.binds@, env, ls)->Ok_0;
                        assert(denotes(slots@, env, l, v, xty(t), se.enums));
                        lemma_models_len(slot_vals(slots@, env, l), v, xty(t), se.enums);
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Ok::<
                            Value,
                            ErrKind,
                        >(slot_vals(slots@, env, l)[j]) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                        assert(slot_vals(out@, env, ls) =~= slot_vals(slots@, env, l));
                    },
                    Err(_) => {
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Err::<
                            Value,
                            ErrKind,
                        >(eval_src(*e, se, sls)->Err_0) by {
                            assert(wraps(out@[j], blk.binds@, slots@[j]));
                        }
                    },
                }
            }
        }
    }
    Some((t, out))
}

/// スカラー型の式として、深さ `depth` で単独に評価できるように下ろす。
fn scalar_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Option<(XType, Expr)>)
    ensures
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, x)) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, xty(t), x),
    decreases e, 5nat,
{
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    if !is_scalar(&t) || slots.len() != 1 {
        return None;
    }
    let x = wrap(&blk.binds, copy_expr(&slots[0]));
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
            #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == depth as nat && frag(*e) implies scalar_result(
            eval_src(*e, se, sls),
            eval_l(x, env, ls),
            xty(t),
            se.enums,
        ) by {
            match eval_src(*e, se, sls) {
                Ok(v) => {
                    let l = run(blk.binds@, env, ls)->Ok_0;
                    assert(denotes(slots@, env, l, v, xty(t), se.enums));
                    assert(slot_vals(slots@, env, l) =~= seq![eval_l(slots@[0], env, l)->Ok_0]);
                },
                Err(_) => {},
            }
        }
    }
    Some((t, x))
}

/// 述語として、深さ `depth` で単独に評価できるように下ろす。
fn bool_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Option<Expr>)
    ensures
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some(x) ==> frag(*e) ==> closed_lowers(*e, *cx, old(sc)@, depth as nat, XTy::Bool, x),
    decreases e, 6nat,
{
    let (t, x) = scalar_in(e, cx, sc, depth)?;
    match t {
        XType::Bool => Some(x),
        _ => None,
    }
}

/// 要素を集合の型に合わせて評価し、属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。正規形のスロットを返す。
fn element(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Option<Vec<Expr>>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
    decreases e, 3nat,
{
    let (t, slots) = low(e, cx, sc, blk)?;
    if !fits(&t, st) {
        return None;
    }
    let (cond, slots) = store(&t, &slots, st, &cx.enums)?;
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    atoms(slots, blk)
}

/// 要素の番号。属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
fn element_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
    decreases e, 3nat,
{
    let (t, slots) = low(e, cx, sc, blk)?;
    if !fits(&t, st) {
        return None;
    }
    let (cond, _) = store(&t, &slots, st, &cx.enums)?;
    check(blk, cond, FAIL_NOT_IN_DOMAIN)?;
    let r = rank_expr(&t, &slots, st, &cx.enums)?;
    atom(blk, r)
}

/// 要素の番号。属さなければ -1。
fn lookup_rank(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block, st: &SType) -> (r: Option<Expr>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some(x) ==> frag(*e) ==> rank_lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), sty(*st), x),
    decreases e, 3nat,
{
    if keys_exec(st, &cx.enums).is_none() {
        proof {
            lemma_extends_refl(*blk);
        }
        return None;
    }
    let ghost b0 = *blk;
    let (t, slots) = low(e, cx, sc, blk)?;
    let ghost b1 = *blk;
    if !fits(&t, st) {
        return None;
    }
    let r = rank_or_neg(&t, &slots, st, &cx.enums)?;
    let ghost rr = r;
    let x = atom(blk, r)?;
    proof {
        let enums = cx.enums@;
        assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
            #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == b0.depth_s() && frag(*e) implies rank_result(
            eval_src(*e, se, sls),
            run(fresh(b0, *blk), env, ls),
            x,
            env,
            sty(*st),
            se.enums,
        ) by {
            lemma_run_fresh(b0, b1, *blk, env, ls);
            lemma_run_len(fresh(b0, b1), env, ls);
            match eval_src(*e, se, sls) {
                Ok(v) => {
                    let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                    assert(denotes(slots@, env, l1, v, xty(t), enums));
                    lemma_clean_pure(slots@, env, l1);
                    assert(eval_l(rr, env, l1) == Ok::<Value, ErrKind>(Value::Int(if member(v, sty(*st), enums) {
                        rank(v, sty(*st), enums) as i64
                    } else {
                        -1i64
                    })));
                    lemma_added(b1, *blk, rr, x, env, l1, Value::Int(if member(v, sty(*st), enums) {
                        rank(v, sty(*st), enums) as i64
                    } else {
                        -1i64
                    }));
                },
                Err(_) => {},
            }
        }
    }
    Some(x)
}

/// Mapのスロット `ms` のキー `key` に値 `value` を置く。キーと値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
fn put(
    _parent: &TExpr,
    ms: &Vec<Expr>,
    k: &SType,
    v: &SType,
    key: &TExpr,
    value: &TExpr,
    cx: &LowerCtx,
    sc: &mut Vec<Bound>,
    blk: &mut Block,
) -> (r: Option<Vec<Expr>>)
    requires
        old(blk).wf(),
        decreases_to!(*_parent => *key),
        decreases_to!(*_parent => *value),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
    decreases _parent, 0nat,
{
    let r = element_rank(key, cx, sc, blk, k)?;
    let x = element(value, cx, sc, blk, v)?;
    let rank_local = match bind(blk, r)? {
        Expr::Local(i) => i,
        _ => return None,
    };
    let rows = keys_or_zero_exec(k, &cx.enums);
    let width = stype_width(v, &cx.enums)?;
    put_map_rows_exec(ms, rows, width, rank_local, &x)
}

/// リテラルと参照。束縛を加えない。
fn low_leaf(e: &TExpr, cx: &LowerCtx, sc: &Vec<Bound>, _blk: &Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        _blk.wf(),
    ensures
        r matches Some((t, slots)) ==> lowers(*e, *cx, sc@, *_blk, *_blk, xty(t), slots@),
{
    let enums = &cx.enums;
    match e {
        TExpr::Lit(v) => {
            match v {
                Value::Enum(id, k) => {
                    if !(*id < enums.len() && 0 <= *k && *k < enums[*id]) {
                        return None;
                    }
                },
                _ => {},
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Const(*v));
            let t = lit_type(v);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(slot_vals(out@, env, ls) =~= seq![*v]);
                }
            }
            Some((t, out))
        },
        TExpr::Var(i) | TExpr::Next(i) => {
            let states = match &cx.states {
                Some(s) => s,
                None => return None,
            };
            let is_next = match e {
                TExpr::Next(_) => true,
                _ => false,
            };
            if is_next && !cx.next {
                return None;
            }
            if *i >= states.len() {
                return None;
            }
            let kind: u8 = if is_next {
                1
            } else {
                0
            };
            let (t, out) = layout_slots(&states[*i], kind, enums)?;
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = states@[*i as int];
                    let xs = if is_next {
                        env.post
                    } else {
                        env.pre
                    };
                    let vs = if is_next {
                        se.post
                    } else {
                        se.pre
                    };
                    assert(layouts_ok(states@, vs, env.st_tys, xs, enums@));
                    let v = vs[*i as int];
                    assert(layout_ok(l, v, env.st_tys, xs, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(kind, (l.offset + j) as usize));
                        assert(lookup(env.st_tys, xs, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Some((t, out))
        },
        TExpr::Arg(i) => {
            if *i >= cx.args.len() {
                return None;
            }
            let (t, out) = layout_slots(&cx.args[*i], 2, enums)?;
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let l = cx.args@[*i as int];
                    let v = se.args[*i as int];
                    assert(layout_ok(l, v, env.arg_tys, env.args, enums@));
                    lemma_enc_len(v, sty(l.ty), enums@);
                    lemma_models_enc(v, sty(l.ty), enums@);
                    assert forall|j: int| 0 <= j < out@.len() implies pure_below(#[trigger] out@[j], ls.len()) && eval_l(
                        out@[j],
                        env,
                        ls,
                    ) == Ok::<Value, ErrKind>(enc(v, sty(l.ty), enums@)[j]) by {
                        assert(out@[j] == kind_expr(2, (l.offset + j) as usize));
                        assert(lookup(env.arg_tys, env.args, (l.offset + j) as usize) == Ok::<Value, ErrKind>(
                            enc(v, sty(l.ty), enums@)[j],
                        ));
                    }
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(l.ty), enums@));
                }
            }
            Some((t, out))
        },
        TExpr::Out => {
            let st = match &cx.out {
                Some(t) => t,
                None => return None,
            };
            if !cx.next {
                return None;
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(Expr::Out);
            let t = to_xtype(st);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.out->Some_0;
                    lemma_enc_len(v, sty(*st), enums@);
                    lemma_models_enc(v, sty(*st), enums@);
                    assert(slot_vals(out@, env, ls) =~= enc(v, sty(*st), enums@));
                }
            }
            Some((t, out))
        },
        TExpr::Local(i) => {
            if *i >= sc.len() {
                return None;
            }
            let t = copy_xtype(&sc[*i].ty);
            let out = copy_exprs(&sc[*i].slots);
            proof {
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    assert(denotes(sc@[*i as int].slots@, env, ls, sls[*i as int], xty(sc@[*i as int].ty), se.enums));
                }
            }
            Some((t, out))
        },
        TExpr::Const(i) => {
            if *i >= cx.consts.len() {
                return None;
            }
            let c = &cx.consts[*i];
            let mut out: Vec<Expr> = Vec::new();
            let mut j = 0;
            while j < c.slots.len()
                invariant
                    j <= c.slots@.len(),
                    out@ == lits(c.slots@.take(j as int)),
                decreases c.slots.len() - j,
            {
                out.push(Expr::Const(c.slots[j]));
                proof {
                    assert(out@ =~= lits(c.slots@.take(j + 1)));
                }
                j += 1;
            }
            let t = to_xtype(&c.ty);
            proof {
                assert(c.slots@.take(c.slots@.len() as int) =~= c.slots@);
                assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
                    #[trigger] ctx_ok(*cx, sc@, env, se, ls, sls) && ls.len() == _blk.depth_s() implies result_ok(
                    eval_src(*e, se, sls),
                    run(fresh(*_blk, *_blk), env, ls),
                    out@,
                    env,
                    xty(t),
                    se.enums,
                ) by {
                    lemma_fresh_refl(*_blk);
                    let v = se.consts[*i as int];
                    assert(member(v, sty(c.ty), enums@) && c.slots@ == enc(v, sty(c.ty), enums@));
                    lemma_lits(c.slots@, env, ls);
                    lemma_models_enc(v, sty(c.ty), enums@);
                }
            }
            Some((t, out))
        },
        _ => None,
    }
}

/// リテラル、参照、スカラーの演算、短絡する演算、`let`。
fn low_core(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    match e {
        TExpr::Lit(_) | TExpr::Var(_) | TExpr::Next(_) | TExpr::Arg(_) | TExpr::Out | TExpr::Local(_) | TExpr::Const(_) => {
            proof {
                lemma_extends_refl(*blk);
            }
            low_leaf(e, cx, sc, blk)
        },
        TExpr::Bin(op, a, b) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Int)?;
            let ghost b1 = *blk;
            let y = sub_scalar(b, cx, sc, blk, &XType::Int)?;
            let ghost b2 = *blk;
            let ghost z = Expr::Bin(*op, Box::new(x), Box::new(y));
            let mut out: Vec<Expr> = Vec::new();
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    out.push(bind(blk, bin(*op, x, y))?);
                    proof {
                        if frag(*e) {
                            lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Int, out@);
                        }
                    }
                    Some((XType::Int, out))
                },
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    out.push(bin(*op, x, y));
                    proof {
                        lemma_extends_refl(*blk);
                        if frag(*e) {
                            lemma_bin(*e, *cx, sc@, b0, b1, b2, *blk, x, y, XTy::Bool, out@);
                        }
                    }
                    Some((XType::Bool, out))
                },
                _ => None,
            }
        },
        TExpr::Eq(positive, a, b) => {
            let (tx, x) = low(a, cx, sc, blk)?;
            let (ty, y) = low(b, cx, sc, blk)?;
            if !xtype_eq(&ty, &tx) {
                return None;
            }
            let c = eq_slots(&tx, &x, &y, enums)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(
                if *positive {
                    c
                } else {
                    not(c)
                },
            );
            Some((XType::Bool, out))
        },
        TExpr::Not(a) => {
            let ghost b0 = *blk;
            let x = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(not(x));
            proof {
                if frag(*e) {
                    lemma_not(*e, *cx, sc@, b0, *blk, x);
                }
            }
            Some((XType::Bool, out))
        },
        TExpr::Fold(_, _) => low_fold(e, cx, sc, blk),
        TExpr::Implies(a, b) => {
            let ghost b0 = *blk;
            let p = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let ghost b1 = *blk;
            let q = bool_in(b, cx, sc, depth(blk))?;
            let mut out: Vec<Expr> = Vec::new();
            let ghost z = Expr::Implies(Box::new(p), Box::new(q));
            out.push(bind(blk, Expr::Implies(Box::new(p), Box::new(q)))?);
            proof {
                if frag(*e) {
                    lemma_implies(*e, *cx, sc@, b0, b1, *blk, p, q);
                }
            }
            Some((XType::Bool, out))
        },
        TExpr::Ite(_, _, _) => low_ite(e, cx, sc, blk),
        TExpr::Let(a, b) => {
            let ghost b0 = *blk;
            let (t, slots) = low(a, cx, sc, blk)?;
            let ghost b1 = *blk;
            let ghost s0 = slots@;
            let slots = atoms(slots, blk)?;
            let ghost b2 = *blk;
            let ghost before = sc@;
            let ghost bound = Bound { ty: t, slots };
            sc.push(Bound { ty: t, slots });
            let ghost sc1 = sc@;
            let r = low(b, cx, sc, blk);
            if r.is_none() {
                return None;
            }
            sc.pop();
            proof {
                assert(sc@ =~= before);
                assert(sc1 == before.push(bound));
                if frag(*e) {
                    let (tb, out) = r->Some_0;
                    lemma_let(*e, *cx, before, b0, b1, b2, *blk, s0, bound, xty(tb), out@);
                }
            }
            r
        },
        _ => None,
    }
}

/// `all` と `any`。先頭の項はスロットにし、残りの項は単独に評価する式にして、短絡する木にたたむ。
fn low_fold(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let (all, es) = match e {
        TExpr::Fold(all, es) => (*all, es),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return None;
        },
    };
    proof {
        assert(decreases_to!(*e => *es));
    }
    let ghost b0 = *blk;
    let mut out: Vec<Expr> = Vec::new();
    if es.len() == 0 {
        proof {
            lemma_extends_refl(*blk);
        }
        out.push(cb(all));
        proof {
            if frag(*e) {
                lemma_fold_empty(*e, *cx, sc@, *blk, out@);
            }
        }
        return Some((XType::Bool, out));
    }
    proof {
        vstd::std_specs::vec::axiom_vec_index_decreases(*es, 0);
    }
    let x = sub_scalar(&es[0], cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let d = depth(blk);
    let mut terms: Vec<Expr> = Vec::new();
    terms.push(x);
    let ghost sc0 = sc@;
    let mut i = 1;
    while i < es.len()
        invariant
            decreases_to!(*e => *es),
            *e == TExpr::Fold(all, *es),
            1 <= i <= es@.len(),
            sc@ == sc0,
            *blk == b1,
            b0 == *old(blk),
            extends(b0, b1),
            d == b1.depth_s(),
            frag(es@[0]) ==> lowers(es@[0], *cx, sc0, b0, b1, XTy::Bool, seq![x]),
            terms@.len() == i,
            terms@[0] == x,
            frag(*e) ==> forall|j: int|
                1 <= j < i ==> #[trigger] closed_lowers(es@[j], *cx, sc0, d as nat, XTy::Bool, terms@[j]),
        decreases es.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
        }
        let q = bool_in(&es[i], cx, sc, d)?;
        let ghost t0 = terms@;
        terms.push(q);
        proof {
            if frag(*e) {
                lemma_frag_seq(es@, i as int);
                assert forall|j: int| 1 <= j < i + 1 implies #[trigger] closed_lowers(
                    es@[j],
                    *cx,
                    sc0,
                    d as nat,
                    XTy::Bool,
                    terms@[j],
                ) by {
                    if j < i {
                        assert(terms@[j] == t0[j]);
                    }
                }
            }
        }
        i += 1;
    }
    let joined = tree(&terms, cb(all), if all { Join::RawAnd } else { Join::RawOr });
    out.push(bind(blk, joined)?);
    proof {
        if frag(*e) {
            lemma_frag_seq(es@, 0);
            lemma_fold(*e, *cx, sc0, b0, b1, *blk, terms@);
        }
    }
    Some((XType::Bool, out))
}

/// 条件式のスロット。枝のスロットが局所変数 `n` 個のもとで純粋でなければ `None`。
fn ite_slots(c: &Expr, xs: &Vec<Expr>, ys: &Vec<Expr>, n: usize) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(out) ==> xs@.len() == ys@.len() && out@.len() == xs@.len() && (forall|i: int|
            0 <= i < out@.len() ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i])) && (forall|i: int|
            0 <= i < xs@.len() ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat)),
{
    if xs.len() != ys.len() {
        return None;
    }
    let mut out: Vec<Expr> = Vec::new();
    let mut j = 0;
    while j < xs.len()
        invariant
            xs@.len() == ys@.len(),
            j <= xs@.len(),
            out@.len() == j,
            forall|i: int| 0 <= i < j ==> #[trigger] out@[i] == ite_s(*c, xs@[i], ys@[i]),
            forall|i: int| 0 <= i < j ==> pure_below(#[trigger] xs@[i], n as nat) && pure_below(ys@[i], n as nat),
        decreases xs.len() - j,
    {
        if !pure_exec(&xs[j], n) || !pure_exec(&ys[j], n) {
            return None;
        }
        let ghost px = pure_below(xs@[j as int], n as nat) && pure_below(ys@[j as int], n as nat);
        out.push(ite(copy_expr(c), copy_expr(&xs[j]), copy_expr(&ys[j])));
        proof {
            assert(px);
            assert forall|i: int| 0 <= i < j + 1 implies pure_below(#[trigger] xs@[i], n as nat) && pure_below(
                ys@[i],
                n as nat,
            ) by {}
        }
        j += 1;
    }
    Some(out)
}

/// 条件式。条件を束縛する。枝が束縛を持たなければ、スロットごとに `ite` で選ぶ。
/// 束縛を持つなら、スロットごとに、その位置の深さで枝を単独に評価する式に下ろし直して束縛する。
/// 中核の `ite` は2つの枝が同じ型でなければならないので、枝の束縛を条件で守って並べることはしない。
fn low_ite(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let (p, a, b) = match e {
        TExpr::Ite(p, a, b) => (p, a, b),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return None;
        },
    };
    let ghost b0 = *blk;
    let c0 = sub_scalar(p, cx, sc, blk, &XType::Bool)?;
    let ghost b1 = *blk;
    let c = atom(blk, c0)?;
    let ghost b2 = *blk;
    let d = depth(blk);
    let mut ba = new_block(d)?;
    let ghost ba0 = ba;
    let (tx, xs) = low(a, cx, sc, &mut ba)?;
    let mut bb = new_block(d)?;
    let ghost bb0 = bb;
    let (ty, ys) = low(b, cx, sc, &mut bb)?;
    if !xtype_eq(&ty, &tx) {
        return None;
    }
    if ba.binds.len() == 0 && bb.binds.len() == 0 {
        let out = ite_slots(&c, &xs, &ys, d)?;
        proof {
            lemma_extends_refl(*blk);
            if frag(*e) {
                lemma_ite_simple(*e, *cx, sc@, b0, b1, b2, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, out@);
            }
        }
        return Some((tx, out));
    }
    if xs.len() == 0 || xs.len() != ys.len() {
        return None;
    }
    let w = xs.len();
    let ghost sc0 = sc@;
    let ghost mut fa: Seq<Seq<Expr>> = Seq::empty();
    let ghost mut fb: Seq<Seq<Expr>> = Seq::empty();
    let mut out: Vec<Expr> = Vec::new();
    proof {
        lemma_extends_refl(*blk);
        lemma_extends_trans(b0, b1, b2);
        assert(decreases_to!(*e => **a));
        assert(decreases_to!(*e => **b));
    }
    let mut j = 0;
    while j < w
        invariant
            decreases_to!(*e => **a),
            decreases_to!(*e => **b),
            sc@ == sc0,
            j <= w,
            b2.wf(),
            d == b2.depth_s(),
            b0 == *old(blk),
            extends(b0, *blk),
            extends(b2, *blk),
            blk.base == b2.base,
            blk.binds@ == b2.binds@ + ite_binds(c, fa, fb, j as nat),
            fa.len() == j,
            fb.len() == j,
            out@ == Seq::new(j as nat, |i: int| Expr::Local((d + i) as usize)),
            frag(**a) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(**a, *cx, sc0, (d + i) as nat, xty(tx), fa[i]),
            frag(**b) ==> forall|i: int|
                0 <= i < j ==> #[trigger] closed_slots(**b, *cx, sc0, (d + i) as nat, xty(tx), fb[i]),
            forall|i: int| 0 <= i < j ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        decreases w - j,
    {
        let dj = depth(blk);
        let (ta, xa) = closed_in(a, cx, sc, dj)?;
        let (tb, yb) = closed_in(b, cx, sc, dj)?;
        if !xtype_eq(&ta, &tx) || !xtype_eq(&tb, &tx) || j >= xa.len() || j >= yb.len() {
            return None;
        }
        let ghost bj = *blk;
        let o = bind(blk, ite(copy_expr(&c), copy_expr(&xa[j]), copy_expr(&yb[j])))?;
        out.push(o);
        proof {
            lemma_extends_trans(b0, bj, *blk);
            lemma_extends_trans(b2, bj, *blk);
            let fa0 = fa;
            let fb0 = fb;
            fa = fa.push(xa@);
            fb = fb.push(yb@);
            lemma_ite_binds_push(c, fa0, fb0, xa@, yb@, j as nat);
            assert(blk.binds@ == b2.binds@ + ite_binds(c, fa, fb, (j + 1) as nat));
            assert(out@ =~= Seq::new((j + 1) as nat, |i: int| Expr::Local((d + i) as usize)));
            assert(fa[j as int] == xa@ && fb[j as int] == yb@);
            assert(j < xa@.len() && j < yb@.len());
            assert forall|i: int| 0 <= i < j + 1 implies i < (#[trigger] fa[i]).len() && i < fb[i].len() by {
                if i < j {
                    assert(fa[i] == fa0[i] && fb[i] == fb0[i]);
                }
            }
            if frag(**a) {
                assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                    **a,
                    *cx,
                    sc0,
                    (d + i) as nat,
                    xty(tx),
                    fa[i],
                ) by {
                    if i < j {
                        assert(fa[i] == fa0[i]);
                    }
                }
            }
            if frag(**b) {
                assert forall|i: int| 0 <= i < j + 1 implies #[trigger] closed_slots(
                    **b,
                    *cx,
                    sc0,
                    (d + i) as nat,
                    xty(tx),
                    fb[i],
                ) by {
                    if i < j {
                        assert(fb[i] == fb0[i]);
                    }
                }
            }
        }
        j += 1;
    }
    proof {
        if frag(*e) {
            lemma_ite_bound(*e, *cx, sc0, b0, b1, b2, *blk, c0, c, ba0, ba, bb0, bb, xty(tx), xs@, ys@, fa, fb, out@);
        }
    }
    Some((tx, out))
}

/// 空の `all` と `any` は、単位元になる。
proof fn lemma_fold_empty(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b: Block, out: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() == 0 && out == seq![bool_lit(all)],
    ensures
        lowers(e, cx, sc, b, b, XTy::Bool, out),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b, b), env, ls),
        out,
        env,
        XTy::Bool,
        se.enums,
    ) by {
        assert(fresh(b, b) =~= Seq::<Expr>::empty());
        assert(eval_fold(all, es@, se, sls) == Ok::<bool, ErrKind>(all));
        assert(eval_l(bool_lit(all), env, ls) == Ok::<Value, ErrKind>(Value::Bool(all)));
        lemma_one_denotes(bool_lit(all), env, ls, Value::Bool(all), XTy::Bool, se.enums);
    }
}

/// `let` の下ろし。束縛する値のスロットを局所変数の対応に加えて、本体を下ろす。
proof fn lemma_let(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    s0: Seq<Expr>,
    bound: Bound,
    tb: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Let(a, b) && lowers(*a, cx, sc, b0, b1, xty(bound.ty), s0) && lowers(
            *b,
            cx,
            sc.push(bound),
            b2,
            b3,
            tb,
            out,
        ),
        atoms_ok(s0, bound.slots@, b1, b2),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, tb, out),
{
    let a = e->Let_0;
    let b = e->Let_1;
    lemma_extends_trans(b1, b2, b3);
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        tb,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, xty(bound.ty), s0, env, se, ls, sls);
        lemma_run_fresh(b0, b1, b3, env, ls);
        lemma_run_fresh(b1, b2, b3, env, run(fresh(b0, b1), env, ls)->Ok_0);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            assert(clean(s0, env, l1));
            assert(atoms_run(s0, bound.slots@, b1, b2, env, l1));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            let sc2 = sc.push(bound);
            let sls2 = sls.push(v);
            assert(denotes(bound.slots@, env, l2, v, xty(bound.ty), se.enums));
            assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(
                sc2[i].slots@,
                env,
                l2,
                sls2[i],
                xty(sc2[i].ty),
                se.enums,
            ) by {
                if i < sc.len() {
                    assert(sc2[i] == sc[i]);
                    assert(sls2[i] == sls[i]);
                }
            }
            assert(ctx_ok(cx, sc2, env, se, l2, sls2));
        }
    }
}

/// `all` と `any` の下ろし。先頭の項はスロットで、残りの項は単独に評価する式である。
proof fn lemma_fold(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, terms: Seq<Expr>)
    requires
        e matches TExpr::Fold(all, es) && es@.len() >= 1 && terms.len() == es@.len() && lowers(
            es@[0],
            cx,
            sc,
            b0,
            b1,
            XTy::Bool,
            seq![terms[0]],
        ) && (forall|j: int|
            1 <= j < es@.len() ==> #[trigger] closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]))
            && b2.binds@ == b1.binds@.push(tree_s(terms, bool_lit(all), raw_join(all))),
        extends(b0, b1),
        extends(b1, b2),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let all = e->Fold_0;
    let es = e->Fold_1;
    let joined = tree_s(terms, bool_lit(all), raw_join(all));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(es@[0], cx, sc, b0, b1, XTy::Bool, seq![terms[0]], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        match eval_src(es@[0], se, sls) {
            Err(k) => {
                lemma_fold_first_err(all, es@, se, sls, k);
            },
            Ok(v0) => {
                let l = run(fresh(b0, b1), env, ls)->Ok_0;
                lemma_denotes_one(terms[0], env, l, v0, XTy::Bool, se.enums);
                assert forall|j: int| 0 <= j < terms.len() implies #[trigger] as_bool(eval_l(terms[j], env, l)) == src_bool(
                    eval_src(es@[j], se, sls),
                ) && lift_bool(as_bool(eval_l(terms[j], env, l))) == eval_l(terms[j], env, l) by {
                    if j > 0 {
                        assert(closed_lowers(es@[j], cx, sc, b1.depth_s(), XTy::Bool, terms[j]));
                        lemma_scalar_bool(eval_src(es@[j], se, sls), eval_l(terms[j], env, l), se.enums);
                    }
                }
                assert(bool_or_err(terms, env, l));
                lemma_fold_eq(all, es@, terms, se, sls, env, l);
                lemma_tree_sc(all, terms, env, l);
                lemma_run_one(b1, b2, joined, env, l);
                if let Ok(r) = eval_l(joined, env, l) {
                    lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
                }
            },
        }
    }
}

/// 条件式のスロットは、条件の真偽に応じて、片方の枝のスロットの値になる。
proof fn lemma_ite_slots(c: Expr, xs: Seq<Expr>, ys: Seq<Expr>, out: Seq<Expr>, env: Env, l: Seq<Value>, pos: bool)
    requires
        pure_below(c, l.len()),
        eval_l(c, env, l) == Ok::<Value, ErrKind>(Value::Bool(pos)),
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] out[j] == ite_s(c, xs[j], ys[j]),
        forall|j: int| 0 <= j < xs.len() ==> pure_below(#[trigger] xs[j], l.len()) && pure_below(ys[j], l.len()),
        pos ==> clean(xs, env, l),
        !pos ==> clean(ys, env, l),
    ensures
        clean(out, env, l),
        slot_vals(out, env, l) == if pos {
            slot_vals(xs, env, l)
        } else {
            slot_vals(ys, env, l)
        },
{
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], l.len()) && eval_l(out[j], env, l)
        == if pos {
        eval_l(xs[j], env, l)
    } else {
        eval_l(ys[j], env, l)
    } by {
        assert(pure_below(xs[j], l.len()));
    }
    if pos {
        assert(slot_vals(out, env, l) =~= slot_vals(xs, env, l));
    } else {
        assert(slot_vals(out, env, l) =~= slot_vals(ys, env, l));
    }
}

/// 条件式のスロットごとの束縛。`i` 番目は、条件で枝の `i` 番目のスロットを選ぶ。
spec fn ite_binds(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, n: nat) -> Seq<Expr> {
    Seq::new(n, |i: int| ite_s(c, fa[i][i], fb[i][i]))
}

proof fn lemma_ite_binds_push(c: Expr, fa: Seq<Seq<Expr>>, fb: Seq<Seq<Expr>>, xa: Seq<Expr>, yb: Seq<Expr>, j: nat)
    requires
        fa.len() == j,
        fb.len() == j,
    ensures
        ite_binds(c, fa.push(xa), fb.push(yb), j + 1) =~= ite_binds(c, fa, fb, j).push(ite_s(c, xa[j as int], yb[j as int])),
{
    assert forall|i: int| 0 <= i < j implies #[trigger] fa.push(xa)[i] == fa[i] && fb.push(yb)[i] == fb[i] by {}
}

/// 枝が束縛を持たない条件式の下ろし。
proof fn lemma_ite_simple(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys),
        extends(b0, b1),
        extends(b1, b2),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        ba1.binds@.len() == 0,
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        bb1.binds@.len() == 0,
        xs.len() == ys.len(),
        out.len() == xs.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == ite_s(c, xs[i], ys[i]),
        forall|i: int|
            0 <= i < xs.len() ==> pure_below(#[trigger] xs[i], b2.depth_s()) && pure_below(ys[i], b2.depth_s()),
    ensures
        lowers(e, cx, sc, b0, b2, t, out),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*p, se, sls) {
            let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
            let bv = v->Bool_0;
            lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
            let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
            lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
            assert(fresh(ba0, ba1) =~= Seq::<Expr>::empty());
            assert(fresh(bb0, bb1) =~= Seq::<Expr>::empty());
            assert(run(Seq::<Expr>::empty(), env, l2) == Ok::<Seq<Value>, ErrKind>(l2));
            if bv {
                lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
                if let Ok(va) = eval_src(*a, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, true);
                }
            } else {
                lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
                if let Ok(vb) = eval_src(*b, se, sls) {
                    lemma_ite_slots(c, xs, ys, out, env, l2, false);
                }
            }
        }
    }
}

/// スロットごとの束縛の、先頭 `k` 個の評価。
proof fn lemma_ite_prefix(
    br: TExpr,
    f: Seq<Seq<Expr>>,
    c: Expr,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    bv: bool,
    d: nat,
    w: nat,
    k: nat,
    cx: LowerCtx,
    sc: Seq<Bound>,
    t: XTy,
    env: Env,
    se: SEnv,
    l2: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        ctx_ok(cx, sc, env, se, l2, sls),
        l2.len() == d,
        pure_below(c, d),
        eval_l(c, env, l2) == Ok::<Value, ErrKind>(Value::Bool(bv)),
        f == if bv {
            fa
        } else {
            fb
        },
        fa.len() == w,
        fb.len() == w,
        k <= w,
        forall|i: int| 0 <= i < w ==> #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]),
        forall|i: int| 0 <= i < w ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
    ensures
        match eval_src(br, se, sls) {
            Err(kk) => k > 0 ==> run(ite_binds(c, fa, fb, k), env, l2) == Err::<Seq<Value>, ErrKind>(kk),
            Ok(v) => run(ite_binds(c, fa, fb, k), env, l2) matches Ok(lk) && lk.len() == d + k && prefix(l2, lk)
                && forall|i: int|
                0 <= i < k ==> #[trigger] lk[d + i] == slot_vals(f[i], env, lk.take(d + i))[i] && models(
                    slot_vals(f[i], env, lk.take(d + i)),
                    v,
                    t,
                    se.enums,
                ),
        },
    decreases k,
{
    if k == 0 {
        assert(ite_binds(c, fa, fb, 0) =~= Seq::<Expr>::empty());
        lemma_prefix_refl(l2);
    } else {
        let j = (k - 1) as nat;
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, j, cx, sc, t, env, se, l2, sls);
        let x = ite_s(c, fa[j as int][j as int], fb[j as int][j as int]);
        assert(ite_binds(c, fa, fb, k) =~= ite_binds(c, fa, fb, j).push(x));
        lemma_run_push(ite_binds(c, fa, fb, j), x, env, l2);
        let r = run(ite_binds(c, fa, fb, j), env, l2);
        if r is Ok {
            let lj = r->Ok_0;
            lemma_run_len(ite_binds(c, fa, fb, j), env, l2);
            lemma_weaken(c, env, l2, lj);
            lemma_ctx_weaken(cx, sc, env, se, l2, lj, sls);
            assert(closed_slots(br, cx, sc, (d + j) as nat, t, f[j as int]));
            assert(ctx_ok(cx, sc, env, se, lj, sls));
            assert(j < f[j as int].len());
            match eval_src(br, se, sls) {
                Ok(v) => {
                    let val = eval_l(f[j as int][j as int], env, lj)->Ok_0;
                    let lk = lj.push(val);
                    assert(lk.take((d + j) as int) =~= lj);
                    assert forall|i: int| 0 <= i < k implies #[trigger] lk[d + i] == slot_vals(
                        f[i],
                        env,
                        lk.take(d + i),
                    )[i] && models(slot_vals(f[i], env, lk.take(d + i)), v, t, se.enums) by {
                        if i < j {
                            assert(lk.take((d + i) as int) =~= lj.take((d + i) as int));
                            assert(lk[d + i] == lj[d + i]);
                        }
                    }
                    lemma_prefix_trans(l2, lj, lk);
                },
                Err(_) => {},
            }
        }
    }
}

/// 枝が束縛を持つ条件式の、1つの環境での評価。
proof fn lemma_ite_bound_at(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    env: Env,
    se: SEnv,
    ls: Seq<Value>,
    sls: Seq<SVal>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
        ctx_ok(cx, sc, env, se, ls, sls),
        ls.len() == b0.depth_s(),
    ensures
        result_ok(eval_src(e, se, sls), run(fresh(b0, b3), env, ls), out, env, t, se.enums),
{
    let p = e->Ite_0;
    let a = e->Ite_1;
    let b = e->Ite_2;
    let d = b2.depth_s();
    let w = xs.len();
    lemma_one(*p, cx, sc, b0, b1, XTy::Bool, seq![c0], env, se, ls, sls);
    lemma_extends_trans(b1, b2, b3);
    lemma_run_fresh(b0, b1, b3, env, ls);
    if let Ok(v) = eval_src(*p, se, sls) {
        let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
        lemma_denotes_one(c0, env, l1, v, XTy::Bool, se.enums);
        let bv = v->Bool_0;
        lemma_added(b1, b2, c0, c, env, l1, Value::Bool(bv));
        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
        lemma_run_fresh(b1, b2, b3, env, l1);
        lemma_ctx_weaken(cx, sc, env, se, l1, l2, sls);
        assert(fresh(b2, b3) =~= ite_binds(c, fa, fb, w));
        let br = if bv {
            *a
        } else {
            *b
        };
        let f = if bv {
            fa
        } else {
            fb
        };
        assert forall|i: int| 0 <= i < w implies #[trigger] closed_slots(br, cx, sc, (d + i) as nat, t, f[i]) by {
            if bv {
                assert(closed_slots(*a, cx, sc, (d + i) as nat, t, fa[i]));
            } else {
                assert(closed_slots(*b, cx, sc, (d + i) as nat, t, fb[i]));
            }
        }
        lemma_ite_prefix(br, f, c, fa, fb, bv, d, w, w, cx, sc, t, env, se, l2, sls);
        if bv {
            lemma_one(*a, cx, sc, ba0, ba1, t, xs, env, se, l2, sls);
        } else {
            lemma_one(*b, cx, sc, bb0, bb1, t, ys, env, se, l2, sls);
        }
        if let Ok(vv) = eval_src(br, se, sls) {
            let lw = run(ite_binds(c, fa, fb, w), env, l2)->Ok_0;
            if bv {
                let la = run(fresh(ba0, ba1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(xs, env, la), vv, t, se.enums);
            } else {
                let lb = run(fresh(bb0, bb1), env, l2)->Ok_0;
                lemma_models_len(slot_vals(ys, env, lb), vv, t, se.enums);
            }
            assert(b3.wf());
            lemma_ite_out(f, out, d, w, vv, t, env, lw, se.enums);
        }
    }
}

/// スロットごとの束縛を評価し終えたときの、条件式のスロットの値。
proof fn lemma_ite_out(
    f: Seq<Seq<Expr>>,
    out: Seq<Expr>,
    d: nat,
    w: nat,
    vv: SVal,
    t: XTy,
    env: Env,
    lw: Seq<Value>,
    enums: Seq<i64>,
)
    requires
        w > 0,
        w == xwidth(t, enums),
        lw.len() == d + w,
        d + w < usize::MAX,
        out == Seq::new(w, |i: int| Expr::Local((d + i) as usize)),
        forall|i: int|
            0 <= i < w ==> #[trigger] lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i] && models(
                slot_vals(f[i], env, lw.take(d + i)),
                vv,
                t,
                enums,
            ),
    ensures
        denotes(out, env, lw, vv, t, enums),
{
    let vs = Seq::new(w, |i: int| slot_vals(f[i], env, lw.take(d + i)));
    let r = slot_vals(out, env, lw);
    assert forall|i: int| 0 <= i < w implies #[trigger] models(vs[i], vv, t, enums) && vs[i].len() == w by {
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
        lemma_models_len(vs[i], vv, t, enums);
    }
    assert forall|i: int| 0 <= i < w implies #[trigger] r[i] == vs[i][i] by {
        assert(out[i] == Expr::Local((d + i) as usize));
        assert(((d + i) as usize) as int == d + i);
        assert(lw[d + i] == slot_vals(f[i], env, lw.take(d + i))[i]);
    }
    lemma_models_diag(vs, r, vv, t, enums);
    assert forall|j: int| 0 <= j < out.len() implies pure_below(#[trigger] out[j], lw.len()) && eval_l(
        out[j],
        env,
        lw,
    ) is Ok by {
        assert(out[j] == Expr::Local((d + j) as usize));
    }
}

/// 枝が束縛を持つ条件式の下ろし。
proof fn lemma_ite_bound(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    c0: Expr,
    c: Expr,
    ba0: Block,
    ba1: Block,
    bb0: Block,
    bb1: Block,
    t: XTy,
    xs: Seq<Expr>,
    ys: Seq<Expr>,
    fa: Seq<Seq<Expr>>,
    fb: Seq<Seq<Expr>>,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Ite(p, a, b) && lowers(*p, cx, sc, b0, b1, XTy::Bool, seq![c0]) && lowers(
            *a,
            cx,
            sc,
            ba0,
            ba1,
            t,
            xs,
        ) && lowers(*b, cx, sc, bb0, bb1, t, ys) && (forall|i: int|
            0 <= i < xs.len() ==> #[trigger] closed_slots(*a, cx, sc, (b2.depth_s() + i) as nat, t, fa[i])) && (forall|
            i: int,
        | 0 <= i < xs.len() ==> #[trigger] closed_slots(*b, cx, sc, (b2.depth_s() + i) as nat, t, fb[i])),
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(ba0, ba1),
        extends(bb0, bb1),
        added(b1, b2, c0, c),
        ba0.binds@.len() == 0,
        ba0.base == b2.depth_s(),
        bb0.binds@.len() == 0,
        bb0.base == b2.depth_s(),
        xs.len() > 0,
        xs.len() == ys.len(),
        fa.len() == xs.len(),
        fb.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> i < (#[trigger] fa[i]).len() && i < fb[i].len(),
        b3.binds@ == b2.binds@ + ite_binds(c, fa, fb, xs.len()),
        out == Seq::new(xs.len(), |i: int| Expr::Local((b2.depth_s() + i) as usize)),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_ite_bound_at(e, cx, sc, b0, b1, b2, b3, c0, c, ba0, ba1, bb0, bb1, t, xs, ys, fa, fb, out, env, se, ls, sls);
    }
}

/// 整数の演算と比較の下ろし。算術は束縛し、比較はそのままスロットにする。
proof fn lemma_bin(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    x: Expr,
    y: Expr,
    t: XTy,
    out: Seq<Expr>,
)
    requires
        e matches TExpr::Bin(op, a, b) && lowers(*a, cx, sc, b0, b1, XTy::Int, seq![x]) && lowers(
            *b,
            cx,
            sc,
            b1,
            b2,
            XTy::Int,
            seq![y],
        ) && if op is Add || op is Sub || op is Mul || op is Div || op is Mod {
            t == XTy::Int && b3.binds@ == b2.binds@.push(Expr::Bin(op, Box::new(x), Box::new(y))) && out == seq![
                Expr::Local(b2.depth_s() as usize),
            ]
        } else {
            (op is Lt || op is Le || op is Gt || op is Ge) && t == XTy::Bool && b3 == b2 && out == seq![
                Expr::Bin(op, Box::new(x), Box::new(y)),
            ]
        },
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
    ensures
        lowers(e, cx, sc, b0, b3, t, out),
{
    let op = e->Bin_0;
    let a = e->Bin_1;
    let b = e->Bin_2;
    let z = Expr::Bin(op, Box::new(x), Box::new(y));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b3), env, ls),
        out,
        env,
        t,
        se.enums,
    ) by {
        lemma_pair(*a, *b, cx, sc, b0, b1, b2, XTy::Int, seq![x], XTy::Int, seq![y], env, se, ls, sls);
        lemma_run_fresh(b0, b2, b3, env, ls);
        if let Ok(va) = eval_src(*a, se, sls) {
            if let Ok(vb) = eval_src(*b, se, sls) {
                let l = run(fresh(b0, b2), env, ls)->Ok_0;
                lemma_denotes_one(x, env, l, va, XTy::Int, se.enums);
                lemma_denotes_one(y, env, l, vb, XTy::Int, se.enums);
                if t == XTy::Bool {
                    lemma_fresh_refl(b2);
                    assert(fresh(b2, b3) =~= Seq::<Expr>::empty());
                    lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
                } else {
                    lemma_run_one(b2, b3, z, env, l);
                    if let Ok(r) = eval_l(z, env, l) {
                        lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Int, se.enums);
                    }
                }
            }
        }
    }
}

/// 否定の下ろし。
proof fn lemma_not(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, x: Expr)
    requires
        e matches TExpr::Not(a) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![x]),
        extends(b0, b1),
    ensures
        lowers(e, cx, sc, b0, b1, XTy::Bool, seq![Expr::Not(Box::new(x))]),
{
    let a = e->Not_0;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b1), env, ls),
        seq![Expr::Not(Box::new(x))],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![x], env, se, ls, sls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(x, env, l, v, XTy::Bool, se.enums);
            let z = Expr::Not(Box::new(x));
            lemma_one_denotes(z, env, l, eval_l(z, env, l)->Ok_0, XTy::Bool, se.enums);
        }
    }
}

/// 含意の下ろし。前件はスロットにし、後件は単独に評価する式にして、全体を束縛する。
proof fn lemma_implies(e: TExpr, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, b2: Block, p: Expr, q: Expr)
    requires
        e matches TExpr::Implies(a, b) && lowers(*a, cx, sc, b0, b1, XTy::Bool, seq![p]) && closed_lowers(
            *b,
            cx,
            sc,
            b1.depth_s(),
            XTy::Bool,
            q,
        ),
        extends(b0, b1),
        extends(b1, b2),
        b2.binds@ == b1.binds@.push(Expr::Implies(Box::new(p), Box::new(q))),
    ensures
        lowers(e, cx, sc, b0, b2, XTy::Bool, seq![Expr::Local(b1.depth_s() as usize)]),
{
    let a = e->Implies_0;
    let b = e->Implies_1;
    let z = Expr::Implies(Box::new(p), Box::new(q));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b2), env, ls),
        seq![Expr::Local(b1.depth_s() as usize)],
        env,
        XTy::Bool,
        se.enums,
    ) by {
        lemma_one(*a, cx, sc, b0, b1, XTy::Bool, seq![p], env, se, ls, sls);
        lemma_run_fresh(b0, b1, b2, env, ls);
        if let Ok(v) = eval_src(*a, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            lemma_denotes_one(p, env, l, v, XTy::Bool, se.enums);
            lemma_run_one(b1, b2, z, env, l);
            assert(ctx_ok(cx, sc, env, se, l, sls));
            if let Ok(r) = eval_l(z, env, l) {
                lemma_one_denotes(Expr::Local(l.len() as usize), env, l.push(r), r, XTy::Bool, se.enums);
            }
        }
    }
}

/// 量化、Tuple、Record、Option。
fn low_struct(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    match e {
        TExpr::Quant(_, _, _) => low_quant(e, cx, sc, blk),
        TExpr::Tuple(es) | TExpr::Record(_, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            if es.len() == 0 {
                return None;
            }
            let ghost sc0 = sc@;
            proof {
                lemma_extends_refl(*blk);
            }
            let mut ts: Vec<XType> = Vec::new();
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    extends(*old(blk), *blk),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let (t, s) = low(&es[i], cx, sc, blk)?;
                ts.push(t);
                append(&mut out, &s);
                i += 1;
            }
            match e {
                TExpr::Record(names, _) => Some((XType::Record(names.clone(), ts), out)),
                _ => Some((XType::Tuple(ts), out)),
            }
        },
        TExpr::Nth(a, i) => {
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Tuple(ts) => {
                    let parts = split(&ts, &slots, enums)?;
                    if *i < ts.len() && *i < parts.len() {
                        Some((copy_xtype(&ts[*i]), copy_exprs(&parts[*i])))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        TExpr::Field(a, name, i) => {
            let (t, slots) = low(a, cx, sc, blk)?;
            match t {
                XType::Record(names, ts) => {
                    let parts = split(&ts, &slots, enums)?;
                    if *i < ts.len() && *i < parts.len() && *i < names.len() && names[*i] == *name {
                        Some((copy_xtype(&ts[*i]), copy_exprs(&parts[*i])))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        TExpr::None(t) => {
            proof {
                lemma_extends_refl(*blk);
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(false));
            append(&mut out, &defaults(t, enums));
            Some((XType::Option(Box::new(to_xtype(t))), out))
        },
        TExpr::Some(a) => {
            let (t, s) = low(a, cx, sc, blk)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(cb(true));
            append(&mut out, &s);
            Some((XType::Option(Box::new(t)), out))
        },
        TExpr::IsSome(a) | TExpr::IsNone(a) => {
            let (t, s) = low(a, cx, sc, blk)?;
            match t {
                XType::Option(_) => {},
                _ => return None,
            }
            if s.len() == 0 {
                return None;
            }
            let tag = copy_expr(&s[0]);
            let mut out: Vec<Expr> = Vec::new();
            match e {
                TExpr::IsSome(_) => out.push(tag),
                _ => out.push(not(tag)),
            }
            Some((XType::Bool, out))
        },
        TExpr::Unwrap(a) => {
            let (t, s) = low(a, cx, sc, blk)?;
            let inner = match t {
                XType::Option(x) => *x,
                _ => return None,
            };
            if s.len() == 0 {
                return None;
            }
            check(blk, copy_expr(&s[0]), FAIL_NONE)?;
            Some((inner, sub_exprs(&s, 1, s.len())))
        },
        _ => None,
    }
}

/// `forall` と `exists`。型の全体、Set の要素、Map のキー、List の要素をたどる。
///
/// List 以外は、値の正規順での番号を1つの整数の局所変数でたどる。束縛する値のスロットは
/// 番号から作り（[`unrank`]）、番号の位置が対象に含まれるかをガードで表す。
fn low_quant(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let (all, over, body) = match e {
        TExpr::Quant(all, over, body) => (*all, over, body),
        _ => return None,
    };
    let ghost b0 = *blk;
    let ghost before = sc@;
    if let Over::List(l) = over {
        let (ty, cs) = low(l, cx, sc, blk)?;
        let (st, max) = match ty {
            XType::List(u, max) => (*u, max),
            _ => return None,
        };
        let d = depth(blk);
        let q = {
            let (len, rows) = list_parts(&st, max, &cs, enums)?;
            let w = stype_width(&st, enums)?;
            let first = d.checked_add(1)?;
            let top = first.checked_add(w)?;
            let i = Expr::Local(d);
            let picked = select(&rows, &i, &defaults(&st, enums))?;
            let x = locals(first, top);
            sc.push(Bound { ty: to_xtype(&st), slots: x });
            let b = bool_in(body, cx, sc, top);
            if b.is_none() {
                return None;
            }
            sc.pop();
            let b = wrap(&picked, b.unwrap());
            let guard = bin(BinOp::Lt, i, len);
            if max > 0x7fff_ffffusize {
                return None;
            }
            let (lo, hi) = if max == 0 {
                (0i64, -1i64)
            } else {
                (0i64, max as i64 - 1)
            };
            let top_code = if max == 0 {
                0i64
            } else {
                max as i64 - 1
            };
            quant(all, Type::Int(0, top_code), lo, hi, combine(all, guard, b))
        };
        let mut out: Vec<Expr> = Vec::new();
        out.push(keep(blk, q)?);
        return Some((XType::Bool, out));
    }
    // たどる値の型、番号の位置が対象に含まれるかのガード、値の数。
    let (st, g, n): (SType, Expr, usize) = match over {
        Over::Type(t) => {
            let n = keys_exec(t, enums)?;
            if n > 0x7fff_ffff {
                return None;
            }
            proof {
                lemma_extends_refl(*blk);
                lemma_over_type(*over, *cx, sc@, *blk, n as nat);
            }
            (copy_stype(t), cb(true), n as usize)
        },
        Over::Set(t, s) => {
            let (ty, cs) = low(s, cx, sc, blk)?;
            let ghost xt = ty;
            let u = match ty {
                XType::Set(u) => u,
                _ => return None,
            };
            let n = keys_exec(t, enums)?;
            if !stype_eq(&u, t) || n > 0x7fff_ffff || cs.len() != n as usize {
                return None;
            }
            let d = depth(blk);
            let g = pick_flag(&cs, &Expr::Local(d));
            proof {
                if frag(*e) {
                    lemma_over_set(*over, *t, **s, *cx, sc@, b0, *blk, cs@, g, n as nat);
                }
            }
            (copy_stype(t), g, n as usize)
        },
        Over::Map(t, m) => {
            let (ty, cs) = low(m, cx, sc, blk)?;
            let (kt, vt) = match ty {
                XType::Map(k, v) => (k, v),
                _ => return None,
            };
            let n = keys_exec(t, enums)?;
            if !stype_eq(&kt, t) || n > 0x7fff_ffff {
                return None;
            }
            let w = stype_width(&vt, enums)?;
            let stride = w.checked_add(1)?;
            let ghost b1 = *blk;
            let mut fs: Vec<Expr> = Vec::new();
            let mut j: usize = 0;
            while j < n as usize
                invariant
                    n <= 0x7fff_ffff,
                    j <= n,
                    fs@.len() == j,
                    forall|q: int| 0 <= q < j ==> #[trigger] fs@[q] == cs@[q * stride],
                    extends(*old(blk), *blk),
                    *blk == b1,
                decreases n - j,
            {
                let at = j.checked_mul(stride)?;
                if at >= cs.len() {
                    return None;
                }
                fs.push(copy_expr(&cs[at]));
                j += 1;
            }
            let d = depth(blk);
            let g = pick_flag(&fs, &Expr::Local(d));
            proof {
                if frag(*e) {
                    lemma_over_map(*over, *t, **m, *cx, sc@, b0, *blk, sty(*vt), stride as int, cs@, fs@, g, n as nat);
                }
            }
            (copy_stype(t), g, n as usize)
        },
        Over::List(_) => return None,
    };
    let ghost b1 = *blk;
    let d = depth(blk);
    let top = d.checked_add(1)?;
    let us = unrank(&st, &Expr::Local(d), enums)?;
    let bd = Bound { ty: to_xtype(&st), slots: us };
    let ghost bg = bd;
    sc.push(bd);
    let b = bool_in(body, cx, sc, top)?;
    sc.pop();
    proof {
        assert(sc@ =~= before);
    }
    let qb = combine(all, g, b);
    let hi = n as i64 - 1;
    let top_code = if n == 0 {
        0i64
    } else {
        hi
    };
    let q = quant(all, Type::Int(0, top_code), 0, hi, qb);
    let z = bind(blk, q)?;
    let mut out: Vec<Expr> = Vec::new();
    out.push(z);
    proof {
        if frag(*e) {
            lemma_quant(*e, all, *over, **body, *cx, before, b0, b1, *blk, sty(st), n as nat, g, bg, b, qb, q);
        }
    }
    Some((XType::Bool, out))
}

/// 量化の本体と、値が対象に含まれる条件を組み合わせる。
fn combine(all: bool, guard: Expr, e: Expr) -> (r: Expr)
    ensures
        combine_ok(all, guard, e, r),
{
    if is_bool_lit(&guard, true) {
        proof {
            assert forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(e, env, l)) == match as_bool(eval_l(guard, env, l)) {
                Err(k) => Err(k),
                Ok(true) => as_bool(eval_l(e, env, l)),
                Ok(false) => Ok::<bool, ErrKind>(all),
            } by {
                assert(eval_l(guard, env, l) == Ok::<Value, ErrKind>(Value::Bool(true)));
            }
        }
        e
    } else if all {
        Expr::Implies(Box::new(guard), Box::new(e))
    } else {
        Expr::And(Box::new(guard), Box::new(e))
    }
}

/// `qb` は、ガード `g` が真なら本体 `b` の真偽、偽なら `all` になる。
pub open spec fn combine_ok(all: bool, g: Expr, b: Expr, qb: Expr) -> bool {
    forall|env: Env, l: Seq<Value>| #[trigger] as_bool(eval_l(qb, env, l)) == match as_bool(eval_l(g, env, l)) {
        Err(k) => Err(k),
        Ok(true) => as_bool(eval_l(b, env, l)),
        Ok(false) => Ok::<bool, ErrKind>(all),
    }
}

fn quant(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> (r: Expr)
    ensures
        r == quant_s(all, ty, lo, hi, e),
{
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

pub open spec fn quant_s(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> Expr {
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
    }
}

/// 量化でたどる値の型。
pub open spec fn over_sty(over: Over) -> STy {
    match over {
        Over::Type(t) => sty(t),
        Over::Set(t, _) => sty(t),
        Over::Map(t, _) => sty(t),
        Over::List(_) => STy::Bool,
    }
}

/// 量化でたどる値を、型の正規順の列のどの位置から選ぶか。
pub open spec fn over_bits(over: Over, se: SEnv, sls: Seq<SVal>) -> Result<Seq<bool>, ErrKind> {
    match over {
        Over::Type(t) => Ok(Seq::new(domain(sty(t), se.enums).len(), |i: int| true)),
        Over::Set(_, s) => match eval_src(*s, se, sls) {
            Ok(SVal::Set(bits)) => Ok(bits),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::Map(_, m) => match eval_src(*m, se, sls) {
            Ok(SVal::Map(rows)) => Ok(Seq::new(rows.len(), |i: int| rows[i] is Some)),
            Ok(_) => Err(ErrKind::TypeMismatch),
            Err(k) => Err(k),
        },
        Over::List(_) => Err(ErrKind::TypeMismatch),
    }
}

/// 局所変数 `l` に番号 `x` を加えると、ガード `g` は `bits[x]` になる。
pub open spec fn guard_at(g: Expr, bits: Seq<bool>, env: Env, l: Seq<Value>) -> bool {
    forall|x: int|
        0 <= x < bits.len() ==> #[trigger] eval_l(g, env, l.push(Value::Int(x as i64))) == Ok::<Value, ErrKind>(
            Value::Bool(bits[x]),
        )
}

/// 対象を `b0` から `b1` までに下ろすと、ガード `g` は、番号の位置がたどる値に含まれるかを表す。
pub open spec fn over_ok(over: Over, cx: LowerCtx, sc: Seq<Bound>, b0: Block, b1: Block, g: Expr, n: nat) -> bool {
    forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() ==> match over_bits(over, se, sls) {
            Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
            Ok(bits) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
                cx,
                sc,
                env,
                se,
                l,
                sls,
            ) && bits.len() == n && guard_at(g, bits, env, l),
        }
}

/// 型の全体をたどる量化のガードは、つねに真である。
proof fn lemma_over_type(over: Over, cx: LowerCtx, sc: Seq<Bound>, b: Block, n: nat)
    requires
        over is Type,
        keys(over_sty(over), cx.enums@) == Some(n),
    ensures
        over_ok(over, cx, sc, b, b, bool_lit(true), n),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b.depth_s() implies match over_bits(over, se, sls) {
        Err(k) => run(fresh(b, b), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(bits) => run(fresh(b, b), env, ls) matches Ok(l) && l.len() == b.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && bits.len() == n && guard_at(bool_lit(true), bits, env, l),
    } by {
        lemma_domain_len(over_sty(over), se.enums);
        lemma_fresh_refl(b);
        assert(run(Seq::<Expr>::empty(), env, ls) == Ok::<Seq<Value>, ErrKind>(ls));
        lemma_prefix_refl(ls);
        let bits = over_bits(over, se, sls)->Ok_0;
        assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(
            bool_lit(true),
            env,
            ls.push(Value::Int(x as i64)),
        ) == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {}
    }
}

/// 下ろした式の列 `fs` が印 `bits` を表すなら、番号の位置を選ぶ式 `g` は番号ごとのガードになる。
proof fn lemma_guard_pick(g: Expr, fs: Seq<Expr>, bits: Seq<bool>, env: Env, l: Seq<Value>)
    requires
        picks(g, fs, Expr::Local(l.len() as usize)),
        flags_at(fs, bits, env, l),
        l.len() < usize::MAX,
        bits.len() <= 0x7fff_ffff,
    ensures
        guard_at(g, bits, env, l),
{
    assert forall|x: int| 0 <= x < bits.len() implies #[trigger] eval_l(g, env, l.push(Value::Int(x as i64)))
        == Ok::<Value, ErrKind>(Value::Bool(bits[x])) by {
        let lx = l.push(Value::Int(x as i64));
        assert(prefix(l, lx));
        lemma_flags_weaken(fs, bits, env, l, lx);
        assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
    }
}

/// Setの要素をたどる量化のガード。
proof fn lemma_over_set(
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
)
    requires
        over == Over::Set(t, Box::new(s)),
        lowers(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs),
        extends(b0, b1),
        b1.wf(),
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        cs.len() == n,
        picks(g, cs, Expr::Local(b1.depth_s() as usize)),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n),
{
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match over_bits(over, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(bits) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && bits.len() == n && guard_at(g, bits, env, l),
    } by {
        lemma_one(s, cx, sc, b0, b1, XTy::Set(Box::new(sty(t))), cs, env, se, ls, sls);
        if let Ok(v) = eval_src(s, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let bits = v->Set_0;
            assert(slot_vals(cs, env, l) == enc(v, STy::Set(Box::new(sty(t))), se.enums));
            assert forall|j: int| 0 <= j < cs.len() implies pure_below(#[trigger] cs[j], l.len()) && eval_l(cs[j], env, l)
                == Ok::<Value, ErrKind>(Value::Bool(bits[j])) by {
                assert(slot_vals(cs, env, l)[j] == eval_l(cs[j], env, l)->Ok_0);
            }
            assert(flags_at(cs, bits, env, l));
            lemma_guard_pick(g, cs, bits, env, l);
        }
    }
}

/// Mapのキーをたどる量化のガード。`fs` は各行の有無のスロットである。
proof fn lemma_over_map(
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
)
    requires
        over == Over::Map(t, Box::new(m)),
        lowers(m, cx, sc, b0, b1, XTy::Map(Box::new(sty(t)), Box::new(sv)), cs),
        extends(b0, b1),
        b1.wf(),
        keys(sty(t), cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        stride == 1 + width(sv, cx.enums@),
        fs.len() == n,
        forall|q: int| 0 <= q < n ==> #[trigger] fs[q] == cs[q * stride],
        picks(g, fs, Expr::Local(b1.depth_s() as usize)),
    ensures
        over_ok(over, cx, sc, b0, b1, g, n),
{
    let xt = XTy::Map(Box::new(sty(t)), Box::new(sv));
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies match over_bits(over, se, sls) {
        Err(k) => run(fresh(b0, b1), env, ls) == Err::<Seq<Value>, ErrKind>(k),
        Ok(bits) => run(fresh(b0, b1), env, ls) matches Ok(l) && l.len() == b1.depth_s() && prefix(ls, l) && ctx_ok(
            cx,
            sc,
            env,
            se,
            l,
            sls,
        ) && bits.len() == n && guard_at(g, bits, env, l),
    } by {
        lemma_one(m, cx, sc, b0, b1, xt, cs, env, se, ls, sls);
        if let Ok(v) = eval_src(m, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let rows = v->Map_0;
            let bits = Seq::new(rows.len(), |i: int| rows[i] is Some);
            assert(slot_vals(cs, env, l) == enc_rows(rows, sv, se.enums));
            assert forall|q: int| 0 <= q < fs.len() implies pure_below(#[trigger] fs[q], l.len()) && eval_l(fs[q], env, l)
                == Ok::<Value, ErrKind>(Value::Bool(bits[q])) by {
                lemma_enc_rows_index(rows, sv, se.enums, q, 0);
                let at = q * stride;
                assert(slot_vals(cs, env, l)[at] == eval_l(cs[at], env, l)->Ok_0);
                assert(row_slots(rows[q], sv, se.enums)[0] == Value::Bool(rows[q] is Some));
            }
            assert(flags_at(fs, bits, env, l));
            lemma_guard_pick(g, fs, bits, env, l);
        }
    }
}

/// 量化の値の意味論を、たどる値の選び方で書き直す。
proof fn lemma_quant_src(e: TExpr, all: bool, over: Over, body: TExpr, se: SEnv, sls: Seq<SVal>)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
        !(over is List),
    ensures
        eval_src(e, se, sls) == match over_bits(over, se, sls) {
            Err(k) => Err(k),
            Ok(bits) => match eval_quant(all, select_bits(domain(over_sty(over), se.enums), bits), body, se, sls) {
                Err(k) => Err(k),
                Ok(b) => Ok(SVal::Bool(b)),
            },
        },
{
    if let Over::Type(t) = over {
        let dom = domain(sty(t), se.enums);
        lemma_select_all(dom, dom.len());
        assert(dom.take(dom.len() as int) =~= dom);
    }
}

/// 番号 `x` を束縛した文脈。束縛した値は、正規順で `x` 番目の値である。
proof fn lemma_quant_ctx(
    cx: LowerCtx,
    sc: Seq<Bound>,
    bd: Bound,
    st: STy,
    n: nat,
    env: Env,
    se: SEnv,
    l: Seq<Value>,
    sls: Seq<SVal>,
    x: int,
)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        l.len() < usize::MAX,
        unrank_ok(st, Expr::Local(l.len() as usize), bd.slots@, cx.enums@),
        xty(bd.ty) == to_xty(st),
        keys(st, cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        0 <= x < n,
    ensures
        ctx_ok(cx, sc.push(bd), env, se, l.push(Value::Int(x as i64)), sls.push(domain(st, se.enums)[x])),
{
    let lx = l.push(Value::Int(x as i64));
    let enums = se.enums;
    assert(prefix(l, lx));
    lemma_ctx_weaken(cx, sc, env, se, l, lx, sls);
    assert(at_rank(Expr::Local(l.len() as usize), env, lx, x as i64));
    let v = domain(st, enums)[x];
    lemma_domain_rank(st, enums, x);
    lemma_models_enc(v, st, enums);
    assert(denotes(bd.slots@, env, lx, v, xty(bd.ty), enums));
    let sc2 = sc.push(bd);
    let sls2 = sls.push(v);
    assert forall|i: int| 0 <= i < sc2.len() implies #[trigger] denotes(sc2[i].slots@, env, lx, sls2[i], xty(sc2[i].ty), enums) by {
        if i < sc.len() {
            assert(sc2[i] == sc[i] && sls2[i] == sls[i]);
        }
    }
}

/// 番号 `x` での量化の本体の真偽。
proof fn lemma_quant_step(
    all: bool,
    g: Expr,
    b: Expr,
    qb: Expr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    bd: Bound,
    st: STy,
    n: nat,
    body: TExpr,
    env: Env,
    se: SEnv,
    l: Seq<Value>,
    sls: Seq<SVal>,
    bits: Seq<bool>,
    x: int,
)
    requires
        ctx_ok(cx, sc, env, se, l, sls),
        l.len() < usize::MAX,
        unrank_ok(st, Expr::Local(l.len() as usize), bd.slots@, cx.enums@),
        xty(bd.ty) == to_xty(st),
        keys(st, cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        bits.len() == n,
        guard_at(g, bits, env, l),
        combine_ok(all, g, b, qb),
        closed_lowers(body, cx, sc.push(bd), l.len() + 1, XTy::Bool, b),
        0 <= x < n,
    ensures
        as_bool(eval_l(qb, env, l.push(Value::Int(x as i64)))) == if bits[x] {
            src_bool(eval_src(body, se, sls.push(domain(st, se.enums)[x])))
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
        let sls2 = sls.push(domain(st, se.enums)[x]);
        lemma_quant_ctx(cx, sc, bd, st, n, env, se, l, sls, x);
        assert(ctx_ok(cx, sc.push(bd), env, se, lx, sls2));
        lemma_scalar_bool(eval_src(body, se, sls2), eval_l(b, env, lx), se.enums);
    }
}

/// 量化の下ろし。対象を下ろし、番号を1つの整数でたどる量化を束縛する。
proof fn lemma_quant(
    e: TExpr,
    all: bool,
    over: Over,
    body: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    st: STy,
    n: nat,
    g: Expr,
    bd: Bound,
    b: Expr,
    qb: Expr,
    q: Expr,
)
    requires
        e == TExpr::Quant(all, over, Box::new(body)),
        !(over is List),
        over_sty(over) == st,
        over_ok(over, cx, sc, b0, b1, g, n),
        keys(st, cx.enums@) == Some(n),
        n <= 0x7fff_ffff,
        b1.depth_s() + 1 < usize::MAX,
        unrank_ok(st, Expr::Local(b1.depth_s() as usize), bd.slots@, cx.enums@),
        xty(bd.ty) == to_xty(st),
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
        if let Ok(bits) = over_bits(over, se, sls) {
            let l = run(fresh(b0, b1), env, ls)->Ok_0;
            let dom = domain(st, se.enums);
            lemma_domain_len(st, se.enums);
            assert forall|x: int| 0 <= x < bits.len() implies #[trigger] as_bool(
                eval_l(qb, env, l.push(Value::Int(x as i64))),
            ) == if bits[x] {
                src_bool(eval_src(body, se, sls.push(dom[x])))
            } else {
                Ok::<bool, ErrKind>(all)
            } by {
                lemma_quant_step(all, g, b, qb, cx, sc, bd, st, n, body, env, se, l, sls, bits, x);
            }
            assert(q_step_ok(all, qb, env, l, bits, dom, body, se, sls));
            let ty = Type::Int(0, if n == 0 { 0 } else { (n - 1) as i64 });
            assert(bits.take(0) =~= Seq::<bool>::empty());
            assert(qprefix(all, dom, bits, 0, body, se, sls) == Ok::<bool, ErrKind>(all));
            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, 0);
            assert(bits.take(bits.len() as int) =~= bits);
            let res = eval_quant(all, select_bits(dom, bits), body, se, sls);
            assert(eval_l(q, env, l) == lift_bool(res));
            lemma_run_one(b1, b2, q, env, l);
            if let Ok(bv) = res {
                lemma_one_denotes(z, env, l.push(Value::Bool(bv)), Value::Bool(bv), XTy::Bool, se.enums);
            }
        }
    }
}

/// Set、Map、Listのリテラルと、Setの演算と大きさ。
fn low_coll(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    match e {
        TExpr::SetLit(t, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            let n = keys_or_zero_exec(t, enums);
            if n > 0x7fff_ffffusize {
                return None;
            }
            let mut bits: Vec<Expr> = Vec::new();
            let mut k = 0;
            while k < n
                decreases n - k,
            {
                bits.push(cb(false));
                k += 1;
            }
            let ghost sc0 = sc@;
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    extends(*old(blk), *blk),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let r = element_rank(&es[i], cx, sc, blk, t)?;
                bits = mark(&bits, &r, true);
                i += 1;
            }
            Some((XType::Set(Box::new(copy_stype(t))), bits))
        },
        TExpr::MapLit(k, v, items) => {
            proof {
                assert(decreases_to!(*e => *items));
                lemma_extends_refl(*blk);
            }
            let map = SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v)));
            let mut slots = defaults(&map, enums);
            let ghost sc0 = sc@;
            let mut i = 0;
            while i < items.len()
                invariant
                    decreases_to!(*e => *items),
                    sc@ == sc0,
                    extends(*old(blk), *blk),
                decreases items.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*items, i as int);
                }
                let item = &items[i];
                proof {
                    assert(decreases_to!(*e => item.key));
                    assert(decreases_to!(*e => item.value));
                }
                slots = put(e, &slots, k, v, &item.key, &item.value, cx, sc, blk)?;
                i += 1;
            }
            Some((to_xtype(&map), slots))
        },
        TExpr::ListLit(t, max, es) => {
            proof {
                assert(decreases_to!(*e => *es));
                lemma_extends_refl(*blk);
            }
            if es.len() > *max || es.len() > 0x7fff_ffffusize {
                return None;
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(ci(es.len() as i64));
            let ghost sc0 = sc@;
            let mut i = 0;
            while i < es.len()
                invariant
                    decreases_to!(*e => *es),
                    sc@ == sc0,
                    extends(*old(blk), *blk),
                decreases es.len() - i,
            {
                proof {
                    vstd::std_specs::vec::axiom_vec_index_decreases(*es, i as int);
                }
                let x = element(&es[i], cx, sc, blk, t)?;
                append(&mut out, &x);
                i += 1;
            }
            let defs = defaults(t, enums);
            let mut p = es.len();
            while p < *max
                decreases *max - p,
            {
                append(&mut out, &defs);
                p += 1;
            }
            Some((XType::List(Box::new(copy_stype(t)), *max), out))
        },
        TExpr::SetContains(t, a, x) => {
            let (tc, cs) = low(a, cx, sc, blk)?;
            let elem = match tc {
                XType::Set(u) => *u,
                _ => return None,
            };
            if !stype_eq(&elem, t) {
                return None;
            }
            let r = lookup_rank(x, cx, sc, blk, &elem)?;
            let hit = select_one(&singletons(&cs), &r)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(and(bin(BinOp::Ge, r, ci(0)), hit));
            Some((XType::Bool, out))
        },
        TExpr::ListContains(a, x) => {
            let (tc, cs) = low(a, cx, sc, blk)?;
            let (elem, max) = match tc {
                XType::List(u, max) => (*u, max),
                _ => return None,
            };
            let (tx, xv) = low(x, cx, sc, blk)?;
            if !fits(&tx, &elem) {
                return None;
            }
            let (len, rows) = list_parts(&elem, max, &cs, enums)?;
            let et = to_xtype(&elem);
            if rows.len() > 0x7fff_ffffusize {
                return None;
            }
            let mut hits: Vec<Expr> = Vec::new();
            let mut p = 0;
            while p < rows.len()
                invariant
                    rows.len() <= 0x7fff_ffffusize,
                    extends(*old(blk), *blk),
                decreases rows.len() - p,
            {
                let same = eq_slots(&et, &rows[p], &xv, enums)?;
                hits.push(and(bin(BinOp::Lt, ci(p as i64), copy_expr(&len)), same));
                p += 1;
            }
            let mut out: Vec<Expr> = Vec::new();
            out.push(any_of(&hits));
            Some((XType::Bool, out))
        },
        TExpr::Insert(t, a, x) | TExpr::Remove(t, a, x) => {
            let (ts, bits) = low(a, cx, sc, blk)?;
            let elem = match &ts {
                XType::Set(u) => copy_stype(u),
                _ => return None,
            };
            if !stype_eq(&elem, t) {
                return None;
            }
            let slots = match e {
                TExpr::Insert(_, _, _) => {
                    let r = element_rank(x, cx, sc, blk, &elem)?;
                    mark(&bits, &r, true)
                },
                _ => {
                    let r = lookup_rank(x, cx, sc, blk, &elem)?;
                    mark(&bits, &r, false)
                },
            };
            Some((ts, slots))
        },
        TExpr::SetBin(op, a, b) => {
            let (ta, xs) = low(a, cx, sc, blk)?;
            let (tb, ys) = low(b, cx, sc, blk)?;
            match &ta {
                XType::Set(_) => {},
                _ => return None,
            }
            if !xtype_eq(&tb, &ta) {
                return None;
            }
            let n = if xs.len() < ys.len() {
                xs.len()
            } else {
                ys.len()
            };
            let mut out: Vec<Expr> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= xs.len(),
                    n <= ys.len(),
                decreases n - i,
            {
                let x = copy_expr(&xs[i]);
                let y = copy_expr(&ys[i]);
                out.push(
                    match op {
                        SetOp::Union => or(x, y),
                        SetOp::Intersection => and(x, y),
                        SetOp::Difference => and(x, not(y)),
                        SetOp::Subset => implies(x, y),
                    },
                );
                i += 1;
            }
            match op {
                SetOp::Subset => {
                    let mut r: Vec<Expr> = Vec::new();
                    r.push(all_of(&out));
                    Some((XType::Bool, r))
                },
                _ => Some((ta, out)),
            }
        },
        TExpr::Size(a) | TExpr::IsEmpty(a) => {
            let (t, s) = low(a, cx, sc, blk)?;
            let is_size = match e {
                TExpr::Size(_) => true,
                _ => false,
            };
            let flags: Vec<Expr> = match &t {
                XType::Set(_) => copy_exprs(&s),
                XType::Map(k, v) => {
                    let (present, _) = map_parts(k, v, &s, enums)?;
                    present
                },
                XType::List(_, _) => {
                    if s.len() == 0 {
                        return None;
                    }
                    let len = copy_expr(&s[0]);
                    let mut out: Vec<Expr> = Vec::new();
                    if is_size {
                        out.push(len);
                        return Some((XType::Int, out));
                    } else {
                        out.push(eq(len, ci(0)));
                        return Some((XType::Bool, out));
                    }
                },
                _ => return None,
            };
            let mut out: Vec<Expr> = Vec::new();
            if is_size {
                let mut codes: Vec<Expr> = Vec::new();
                let mut i = 0;
                while i < flags.len()
                    decreases flags.len() - i,
                {
                    codes.push(Expr::Code(Box::new(copy_expr(&flags[i]))));
                    i += 1;
                }
                out.push(keep(blk, sum(&codes))?);
                Some((XType::Int, out))
            } else {
                out.push(not(any_of(&flags)));
                Some((XType::Bool, out))
            }
        },
        _ => None,
    }
}

/// Setのスロット `bits` の、番号 `r` の位置を `on` にする。
fn mark(bits: &Vec<Expr>, r: &Expr, on: bool) -> (out: Vec<Expr>) {
    let mut out: Vec<Expr> = Vec::new();
    if bits.len() > 0x7fff_ffffusize {
        return out;
    }
    let mut k = 0;
    while k < bits.len()
        invariant
            bits.len() <= 0x7fff_ffffusize,
        decreases bits.len() - k,
    {
        let bit = copy_expr(&bits[k]);
        out.push(
            if on {
                or(bit, eq(copy_expr(r), ci(k as i64)))
            } else {
                and(bit, bin(BinOp::Ne, copy_expr(r), ci(k as i64)))
            },
        );
        k += 1;
    }
    out
}

/// `Map#get`。キーの番号を束縛し、キーがなければ失敗する検査を束縛してから、行の値を選ぶ。
fn low_get(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let (t, a, x) = match e {
        TExpr::Get(t, a, x) => (t, a, x),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return None;
        },
    };
    let ghost b0 = *blk;
    let (tm, ms) = low(a, cx, sc, blk)?;
    let ghost b1 = *blk;
    let ghost tmx = xty(tm);
    let (k, v) = match tm {
        XType::Map(k, v) => (*k, *v),
        _ => return None,
    };
    if !stype_eq(&k, t) {
        return None;
    }
    let r = lookup_rank(x, cx, sc, blk, &k)?;
    let ghost b2 = *blk;
    let ghost rr = r;
    let rank_local = match r {
        Expr::Local(index) => index,
        _ => {
            let index = depth(blk);
            bind(blk, r)?;
            index
        },
    };
    let ghost b3 = *blk;
    let rows = keys_or_zero_exec(&k, enums);
    let width = stype_width(&v, enums)?;
    let fallback = defaults(&v, enums);
    let (chk, slots) = select_flat_map_lookup(&ms, rows, width, rank_local, &fallback)?;
    let ghost c = chk;
    bind(blk, chk)?;
    let ty = to_xtype(&v);
    proof {
        assert(added(b2, b3, rr, Expr::Local(rank_local)));
        lemma_fresh_push(b3, *blk, c);
        if frag(*e) {
            lemma_get(
                *e, *cx, sc@, b0, b1, b2, b3, *blk, **a, **x, ms@, sty(k), sty(v), rr, rank_local, c, slots@,
                fallback@, rows, width,
            );
        }
    }
    Some((ty, slots))
}

/// `Map#get` の下ろしの正しさ（[`low_get`]）。
#[verifier::spinoff_prover]
proof fn lemma_get(
    e: TExpr,
    cx: LowerCtx,
    sc: Seq<Bound>,
    b0: Block,
    b1: Block,
    b2: Block,
    b3: Block,
    b4: Block,
    a: TExpr,
    x: TExpr,
    ms: Seq<Expr>,
    sk: STy,
    sv: STy,
    rr: Expr,
    rank_local: usize,
    c: Expr,
    slots: Seq<Expr>,
    fallback: Seq<Expr>,
    rows: usize,
    wd: usize,
)
    requires
        e matches TExpr::Get(t, ea, ex) && *ea == a && *ex == x && sty(t) == sk,
        extends(b0, b1),
        extends(b1, b2),
        extends(b2, b3),
        extends(b3, b4),
        lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), ms),
        rank_lowers(x, cx, sc, b1, b2, sk, rr),
        added(b2, b3, rr, Expr::Local(rank_local)),
        fresh(b3, b4) == seq![c],
        rows == keys_or_zero(sk, cx.enums@),
        wd == width(sv, cx.enums@),
        fallback == lits(enc(default_val(sv, cx.enums@), sv, cx.enums@)),
        slots.len() == wd,
        forall|n: nat| #[trigger] all_pure(ms, n) && rank_local < n && all_pure(fallback, n) ==> all_pure(slots, n),
        forall|env: Env, locals: Seq<Value>|
            rank_local < locals.len() && locals[rank_local as int] is Int && (key_rank(locals, rank_local) < 0
                || key_rank(locals, rank_local) < rows <= i64::MAX) ==> #[trigger] eval_l(c, env, locals) == if key_rank(
                locals,
                rank_local,
            ) < 0 {
                Err(ErrKind::Failed(MISSING_KEY))
            } else {
                match as_bool(flat_slot(ms, wd, 0, key_rank(locals, rank_local), env, locals)) {
                    Ok(true) => Ok(Value::Bool(true)),
                    Ok(false) => Err(ErrKind::Failed(MISSING_KEY)),
                    Err(error) => Err(error),
                }
            },
        forall|i: int, env: Env, locals: Seq<Value>|
            0 <= i < wd && rank_local < locals.len() && locals[rank_local as int] is Int && 0 <= key_rank(
                locals,
                rank_local,
            ) < rows <= i64::MAX ==> #[trigger] eval_l(slots[i], env, locals) == flat_slot_int(
                ms,
                wd,
                i + 1,
                key_rank(locals, rank_local),
                env,
                locals,
            ),
    ensures
        lowers(e, cx, sc, b0, b4, to_xty(sv), slots),
{
    let enums = cx.enums@;
    assert forall|env: Env, se: SEnv, ls: Seq<Value>, sls: Seq<SVal>|
        #[trigger] ctx_ok(cx, sc, env, se, ls, sls) && ls.len() == b0.depth_s() implies result_ok(
        eval_src(e, se, sls),
        run(fresh(b0, b4), env, ls),
        slots,
        env,
        to_xty(sv),
        se.enums,
    ) by {
        lemma_run_fresh(b0, b1, b4, env, ls);
        lemma_run_len(fresh(b0, b1), env, ls);
        match eval_src(a, se, sls) {
            Err(_) => {},
            Ok(m) => {
                let l1 = run(fresh(b0, b1), env, ls)->Ok_0;
                assert(denotes(ms, env, l1, m, XTy::Map(Box::new(sk), Box::new(sv)), enums));
                lemma_ctx_weaken(cx, sc, env, se, ls, l1, sls);
                assert(ctx_ok(cx, sc, env, se, l1, sls));
                lemma_run_fresh(b1, b2, b4, env, l1);
                lemma_run_len(fresh(b1, b2), env, l1);
                match eval_src(x, se, sls) {
                    Err(_) => {},
                    Ok(y) => {
                        let l2 = run(fresh(b1, b2), env, l1)->Ok_0;
                        let rows_v = m->Map_0;
                        let mem = member(y, sk, enums);
                        let rk: i64 = if mem {
                            rank(y, sk, enums) as i64
                        } else {
                            -1i64
                        };
                        assert(eval_l(rr, env, l2) == Ok::<Value, ErrKind>(Value::Int(rk)));
                        lemma_added(b2, b3, rr, Expr::Local(rank_local), env, l2, Value::Int(rk));
                        lemma_run_fresh(b2, b3, b4, env, l2);
                        let l3 = run(fresh(b2, b3), env, l2)->Ok_0;
                        assert(rank_local < l3.len() && l3[rank_local as int] == Value::Int(rk));
                        assert(key_rank(l3, rank_local) == rk as int);
                        lemma_run_push(Seq::empty(), c, env, l3);
                        assert(seq![c] =~= Seq::<Expr>::empty().push(c));
                        lemma_prefix_trans(ls, l1, l2);
                        lemma_prefix_trans(l1, l2, l3);
                        assert(keys(sk, enums) == Some(rows_v.len()));
                        if mem {
                            lemma_rank_in_domain(y, sk, enums);
                            let rkk = rank(y, sk, enums);
                            assert(0 <= rkk < rows);
                            let w1 = 1 + wd;
                            lemma_enc_rows_index(rows_v, sv, enums, rkk, 0);
                            let pos = rkk * w1;
                            assert(clean(ms, env, l1));
                            lemma_weaken(ms[pos], env, l1, l3);
                            assert(eval_l(ms[pos], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[pos]));
                            assert(slot_vals(ms, env, l1) == enc_rows(rows_v, sv, enums));
                            assert(flat_slot(ms, wd, 0, rkk, env, l3) == Ok::<Value, ErrKind>(
                                Value::Bool(rows_v[rkk] is Some),
                            ));
                            match rows_v[rkk] {
                                None => {},
                                Some(val) => {
                                    let l4 = l3.push(Value::Bool(true));
                                    lemma_prefix_trans(l3, l3, l4);
                                    lemma_prefix_trans(l1, l3, l4);
                                    assert(key_rank(l4, rank_local) == rkk);
                                    lemma_map_rows_member_index(rows_v, sv, enums, rkk);
                                    lemma_enc_len(val, sv, enums);
                                    lemma_models_enc(val, sv, enums);
                                    lemma_clean_pure(ms, env, l1);
                                    assert(all_pure(ms, l4.len())) by {
                                        assert forall|j: int| 0 <= j < ms.len() implies pure_below(#[trigger] ms[j], l4.len()) by {
                                            lemma_pure_mono(ms[j], l1.len(), l4.len());
                                        }
                                    }
                                    lemma_lits(enc(default_val(sv, enums), sv, enums), env, l4);
                                    assert(all_pure(fallback, l4.len()));
                                    assert(all_pure(slots, l4.len()));
                                    assert forall|i: int| 0 <= i < slots.len() implies pure_below(#[trigger] slots[i], l4.len())
                                        && eval_l(slots[i], env, l4) == Ok::<Value, ErrKind>(enc(val, sv, enums)[i]) by {
                                        lemma_enc_rows_index(rows_v, sv, enums, rkk, i + 1);
                                        let q = rkk * w1 + i + 1;
                                        lemma_weaken(ms[q], env, l1, l4);
                                        assert(eval_l(ms[q], env, l1) == Ok::<Value, ErrKind>(slot_vals(ms, env, l1)[q]));
                                        assert(eval_l(slots[i], env, l4) == flat_slot_int(ms, wd, i + 1, rkk, env, l4));
                                    }
                                    assert(slot_vals(slots, env, l4) =~= enc(val, sv, enums));
                                },
                            }
                        }
                    },
                }
            },
        }
    }
}

/// Mapの参照と更新、Listの参照と更新。
fn low_access(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Option<(XType, Vec<Expr>)>)
    requires
        old(blk).wf(),
    ensures
        extends(*old(blk), *final(blk)),
        r is Some ==> final(sc)@ == old(sc)@,
        r matches Some((t, slots)) ==> frag(*e) ==> lowers(*e, *cx, old(sc)@, *old(blk), *final(blk), xty(t), slots@),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    match e {
        TExpr::HasKey(t, a, x) => {
            let (tm, ms) = low(a, cx, sc, blk)?;
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return None,
            };
            if !stype_eq(&k, t) {
                return None;
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let mut out: Vec<Expr> = Vec::new();
            let (present, _) = map_parts(&k, &v, &ms, enums)?;
            let hit = select_one(&singletons(&present), &r)?;
            out.push(and(bin(BinOp::Ge, copy_expr(&r), ci(0)), hit));
            Some((XType::Bool, out))
        },
        TExpr::Get(_, _, _) => low_get(e, cx, sc, blk),
        TExpr::Put(kt, vt, a, x, y) => {
            let (tm, ms) = low(a, cx, sc, blk)?;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return None,
            };
            if !stype_eq(&k, kt) || !stype_eq(&v, vt) {
                return None;
            }
            let slots = put(e, &ms, &k, &v, x, y, cx, sc, blk)?;
            Some((tm, slots))
        },
        TExpr::Delete(t, a, x) => {
            let (tm, ms) = low(a, cx, sc, blk)?;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return None,
            };
            if !stype_eq(&k, t) {
                return None;
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let (present, values) = map_parts(&k, &v, &ms, enums)?;
            let defs = defaults(&v, enums);
            let n = if present.len() < values.len() {
                present.len()
            } else {
                values.len()
            };
            if n > 0x7fff_ffffusize {
                return None;
            }
            let mut p2: Vec<Expr> = Vec::new();
            let mut v2: Vec<Vec<Expr>> = Vec::new();
            let mut i = 0;
            while i < n
                invariant
                    n <= present.len(),
                    n <= values.len(),
                    n <= 0x7fff_ffffusize,
                decreases n - i,
            {
                p2.push(and(copy_expr(&present[i]), bin(BinOp::Ne, copy_expr(&r), ci(i as i64))));
                let row = &values[i];
                let m = if row.len() < defs.len() {
                    row.len()
                } else {
                    defs.len()
                };
                let mut vs: Vec<Expr> = Vec::new();
                let mut j = 0;
                while j < m
                    invariant
                        m <= row.len(),
                        m <= defs.len(),
                        i < 0x7fff_ffffusize,
                    decreases m - j,
                {
                    vs.push(ite(eq(copy_expr(&r), ci(i as i64)), copy_expr(&defs[j]), copy_expr(&row[j])));
                    j += 1;
                }
                v2.push(vs);
                i += 1;
            }
            Some((tm, map_join(&p2, &v2)))
        },
        TExpr::Keys(a) => {
            let (tm, ms) = low(a, cx, sc, blk)?;
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return None,
            };
            let (present, _) = map_parts(&k, &v, &ms, enums)?;
            Some((XType::Set(Box::new(k)), present))
        },
        TExpr::At(a, i) => {
            let (tl, ls) = low(a, cx, sc, blk)?;
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return None,
            };
            let i = sub_scalar(i, cx, sc, blk, &XType::Int)?;
            let i = atom(blk, i)?;
            let (len, rows) = list_parts(&t, max, &ls, enums)?;
            check(blk, and(bin(BinOp::Ge, copy_expr(&i), ci(0)), bin(BinOp::Lt, copy_expr(&i), len)), FAIL_INDEX)?;
            let slots = select(&rows, &i, &defaults(&t, enums))?;
            Some((to_xtype(&t), slots))
        },
        TExpr::First(a) | TExpr::Last(a) => {
            let (tl, ls) = low(a, cx, sc, blk)?;
            let (t, max) = match tl {
                XType::List(u, max) => (*u, max),
                _ => return None,
            };
            let (len, rows) = list_parts(&t, max, &ls, enums)?;
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            match e {
                TExpr::First(_) => {
                    let slots = if rows.len() > 0 {
                        copy_exprs(&rows[0])
                    } else {
                        defaults(&t, enums)
                    };
                    return Some((to_xtype(&t), slots));
                },
                _ => {},
            }
            let i = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            let slots = select(&rows, &i, &defaults(&t, enums))?;
            Some((to_xtype(&t), slots))
        },
        TExpr::Push(t, n, a, x) => {
            let (tl, ls) = low(a, cx, sc, blk)?;
            let (u, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return None,
            };
            if max != *n || !stype_eq(&u, t) || max > 0x7fff_ffffusize {
                return None;
            }
            let x = element(x, cx, sc, blk, &u)?;
            let (len, rows) = list_parts(&u, max, &ls, enums)?;
            check(blk, bin(BinOp::Lt, copy_expr(&len), ci(max as i64)), FAIL_FULL)?;
            let new_len = bind(blk, bin(BinOp::Add, copy_expr(&len), ci(1)))?;
            if rows.len() > 0x7fff_ffffusize {
                return None;
            }
            let mut out: Vec<Vec<Expr>> = Vec::new();
            let mut p = 0;
            while p < rows.len()
                invariant
                    rows.len() <= 0x7fff_ffffusize,
                decreases rows.len() - p,
            {
                let row = &rows[p];
                let m = if row.len() < x.len() {
                    row.len()
                } else {
                    x.len()
                };
                let mut vs: Vec<Expr> = Vec::new();
                let mut j = 0;
                while j < m
                    invariant
                        m <= row.len(),
                        m <= x.len(),
                        p < 0x7fff_ffffusize,
                    decreases m - j,
                {
                    vs.push(ite(eq(copy_expr(&len), ci(p as i64)), copy_expr(&x[j]), copy_expr(&row[j])));
                    j += 1;
                }
                out.push(vs);
                p += 1;
            }
            Some((tl, list_join(new_len, &out)))
        },
        TExpr::Pop(a) | TExpr::Shift(a) => {
            let (tl, ls) = low(a, cx, sc, blk)?;
            let (t, max) = match &tl {
                XType::List(u, max) => (copy_stype(u), *max),
                _ => return None,
            };
            let (len, rows) = list_parts(&t, max, &ls, enums)?;
            check(blk, bin(BinOp::Gt, copy_expr(&len), ci(0)), FAIL_EMPTY)?;
            let new_len = bind(blk, bin(BinOp::Sub, len, ci(1)))?;
            let defs = defaults(&t, enums);
            if rows.len() > 0x7fff_ffffusize {
                return None;
            }
            let mut out: Vec<Vec<Expr>> = Vec::new();
            match e {
                TExpr::Pop(_) => {
                    let mut p = 0;
                    while p < rows.len()
                        invariant
                            rows.len() <= 0x7fff_ffffusize,
                        decreases rows.len() - p,
                    {
                        let row = &rows[p];
                        let m = if row.len() < defs.len() {
                            row.len()
                        } else {
                            defs.len()
                        };
                        let mut vs: Vec<Expr> = Vec::new();
                        let mut j = 0;
                        while j < m
                            invariant
                                m <= row.len(),
                                m <= defs.len(),
                                p < 0x7fff_ffffusize,
                            decreases m - j,
                        {
                            vs.push(
                                ite(eq(copy_expr(&new_len), ci(p as i64)), copy_expr(&defs[j]), copy_expr(&row[j])),
                            );
                            j += 1;
                        }
                        out.push(vs);
                        p += 1;
                    }
                },
                _ => {
                    let mut p = 1;
                    while p < rows.len()
                        decreases rows.len() - p,
                    {
                        out.push(copy_exprs(&rows[p]));
                        p += 1;
                    }
                    out.push(defs);
                },
            }
            Some((tl, list_join(new_len, &out)))
        },
        _ => None,
    }
}

/// 述語（guard、不変条件、遷移契約、終端条件）として下ろす。
///
/// 環境が対応するとき、下ろした式の値は、値の上の意味論の値と一致する（失敗するなら同じ失敗）。
pub fn lower_prop(e: &TExpr, cx: &LowerCtx) -> (r: Option<Expr>)
    ensures
        r matches Some(c) ==> frag(*e) ==> forall|env: Env, se: SEnv|
            #[trigger] env_rel(*cx, env, se) ==> prop_result(
                eval_src(*e, se, Seq::empty()),
                eval_l(c, env, Seq::empty()),
            ),
{
    let mut sc: Vec<Bound> = Vec::new();
    let r = bool_in(e, cx, &mut sc, 0);
    proof {
        if r is Some {
            let c = r->Some_0;
            if frag(*e) {
                assert forall|env: Env, se: SEnv| #[trigger] env_rel(*cx, env, se) implies prop_result(
                    eval_src(*e, se, Seq::empty()),
                    eval_l(c, env, Seq::empty()),
                ) by {
                    assert(ctx_ok(*cx, Seq::empty(), env, se, Seq::empty(), Seq::empty()));
                    assert(sc@ =~= Seq::<Bound>::empty());
                }
            }
        }
    }
    r
}

/// 値を型 `st` の場所に置くスロット（正規形）。整数の範囲は検査しない（中核の範囲外更新で検出する）。
///
/// 環境が対応し、局所変数の数が `depth` のとき、値が型に属するなら、各スロットの値はその正規形の符号化になる。
/// 失敗するなら、各スロットは同じ失敗になる。
pub fn lower_stored(e: &TExpr, cx: &LowerCtx, st: &SType, depth: usize) -> (r: Option<Vec<Expr>>)
    ensures
        r matches Some(out) ==> frag(*e) ==> forall|env: Env, se: SEnv, ls: Seq<Value>|
            #[trigger] top_ok(*cx, env, se, ls, depth as nat) ==> stored_result(
                eval_src(*e, se, Seq::empty()),
                out@,
                env,
                ls,
                sty(*st),
                se.enums,
            ),
{
    let mut sc: Vec<Bound> = Vec::new();
    let mut blk = new_block(depth)?;
    let ghost b0 = blk;
    let (t, slots) = low(e, cx, &mut sc, &mut blk)?;
    if !fits(&t, st) {
        return None;
    }
    let (_c, stored) = store(&t, &slots, st, &cx.enums)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < stored.len()
        invariant
            i <= stored@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] wraps(out@[j], blk.binds@, stored@[j]),
        decreases stored.len() - i,
    {
        let x = wrap(&blk.binds, copy_expr(&stored[i]));
        out.push(x);
        proof {
            assert(wraps(out@[i as int], blk.binds@, stored@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(fresh(b0, blk) =~= blk.binds@);
        if frag(*e) {
            assert forall|env: Env, se: SEnv, ls: Seq<Value>| #[trigger] top_ok(*cx, env, se, ls, depth as nat) implies stored_result(
                eval_src(*e, se, Seq::empty()),
                out@,
                env,
                ls,
                sty(*st),
                se.enums,
            ) by {
                assert(sc@ =~= Seq::<Bound>::empty());
                assert(ctx_ok(*cx, sc@, env, se, ls, Seq::empty()));
                match eval_src(*e, se, Seq::empty()) {
                    Ok(v) => {
                        let l = run(blk.binds@, env, ls)->Ok_0;
                        assert(denotes(slots@, env, l, v, xty(t), se.enums));
                        assert(store_ok(_c, stored@, env, l, v, sty(*st), se.enums));
                        if member(v, sty(*st), se.enums) {
                            lemma_enc_len(v, sty(*st), se.enums);
                            assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Ok::<
                                Value,
                                ErrKind,
                            >(enc(v, sty(*st), se.enums)[j]) by {
                                assert(wraps(out@[j], blk.binds@, stored@[j]));
                                assert(eval_l(stored@[j], env, l) == Ok::<Value, ErrKind>(slot_vals(stored@, env, l)[j]));
                            }
                        }
                    },
                    Err(_) => {
                        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] eval_l(out@[j], env, ls) == Err::<
                            Value,
                            ErrKind,
                        >(eval_src(*e, se, Seq::empty())->Err_0) by {
                            assert(wraps(out@[j], blk.binds@, stored@[j]));
                        }
                    },
                }
            }
        }
    }
    Some(out)
}

} // verus!
