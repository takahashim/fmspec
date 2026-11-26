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
use crate::encoding::{lemma_enc_len, lemma_models_enc, lemma_stys, lemma_xtys, to_xty, xty, xtys, XTy};
#[cfg(verus_keep_ghost)]
use crate::eval::{as_bool, eval_l, lookup, Env, ErrKind};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::keys::{lemma_rank_in_domain, rank};
#[cfg(verus_keep_ghost)]
use crate::map_lookup::{flat_slot, flat_slot_int, key_rank, MISSING_KEY};
use crate::map_lookup::{put_map_rows_exec, select_flat_map_lookup};
use crate::model::{BinOp, Expr, Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::*;
use crate::slots::*;
#[cfg(verus_keep_ghost)]
use crate::source::{eval_src, SEnv};
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
{
    let mut xs = xs;
    let mut rev: Vec<Expr> = Vec::new();
    while xs.len() > 0
        decreases xs.len(),
    {
        rev.push(xs.pop().unwrap());
    }
    let mut out: Vec<Expr> = Vec::new();
    proof {
        lemma_extends_refl(*blk);
    }
    while rev.len() > 0
        invariant
            extends(*old(blk), *blk),
        decreases rev.len(),
    {
        let x = rev.pop().unwrap();
        out.push(atom(blk, x)?);
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
    decreases e, 3nat,
{
    let (t, mut slots) = low(e, cx, sc, blk)?;
    if !xtype_eq(&t, want) {
        return None;
    }
    match slots.pop() {
        Some(x) => Some(x),
        None => Some(cb(false)),
    }
}

/// 深さ `depth` で単独に評価できるように下ろす。スロットごとに、束縛を含む式を返す。
fn closed_in(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, depth: usize) -> (r: Option<(XType, Vec<Expr>)>)
    ensures
        r is Some ==> final(sc)@ == old(sc)@,
    decreases e, 4nat,
{
    let mut blk = new_block(depth)?;
    let (t, slots) = low(e, cx, sc, &mut blk)?;
    let mut out: Vec<Expr> = Vec::new();
    let mut i = 0;
    while i < slots.len()
        decreases slots.len() - i,
    {
        out.push(wrap(&blk.binds, copy_expr(&slots[i])));
        i += 1;
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
            let x = sub_scalar(a, cx, sc, blk, &XType::Int)?;
            let y = sub_scalar(b, cx, sc, blk, &XType::Int)?;
            let mut out: Vec<Expr> = Vec::new();
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    out.push(keep(blk, bin(*op, x, y))?);
                    Some((XType::Int, out))
                },
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    out.push(bin(*op, x, y));
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
            let x = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(not(x));
            Some((XType::Bool, out))
        },
        TExpr::Fold(all, es) => {
            proof {
                assert(decreases_to!(*e => *es));
            }
            let mut out: Vec<Expr> = Vec::new();
            if es.len() == 0 {
                proof {
                    lemma_extends_refl(*blk);
                }
                out.push(cb(*all));
                return Some((XType::Bool, out));
            }
            proof {
                vstd::std_specs::vec::axiom_vec_index_decreases(*es, 0);
            }
            let x = sub_scalar(&es[0], cx, sc, blk, &XType::Bool)?;
            let d = depth(blk);
            let mut terms: Vec<Expr> = Vec::new();
            terms.push(x);
            let ghost sc0 = sc@;
            let mut i = 1;
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
                terms.push(bool_in(&es[i], cx, sc, d)?);
                i += 1;
            }
            let joined = tree(
                &terms,
                cb(*all),
                if *all {
                    Join::RawAnd
                } else {
                    Join::RawOr
                },
            );
            out.push(keep(blk, joined)?);
            Some((XType::Bool, out))
        },
        TExpr::Implies(a, b) => {
            let p = sub_scalar(a, cx, sc, blk, &XType::Bool)?;
            let q = bool_in(b, cx, sc, depth(blk))?;
            let mut out: Vec<Expr> = Vec::new();
            out.push(keep(blk, Expr::Implies(Box::new(p), Box::new(q)))?);
            Some((XType::Bool, out))
        },
        TExpr::Ite(p, a, b) => {
            let c = sub_scalar(p, cx, sc, blk, &XType::Bool)?;
            let d = depth(blk);
            let (tx, xs) = closed_in(a, cx, sc, d)?;
            let (ty, ys) = closed_in(b, cx, sc, d)?;
            if !xtype_eq(&ty, &tx) {
                return None;
            }
            if is_scalar(&tx) {
                if xs.len() == 0 || ys.len() == 0 {
                    return None;
                }
                let mut out: Vec<Expr> = Vec::new();
                out.push(keep(blk, ite(c, copy_expr(&xs[0]), copy_expr(&ys[0])))?);
                return Some((tx, out));
            }
            let mut simple = true;
            let mut i = 0;
            while i < xs.len()
                decreases xs.len() - i,
            {
                if may_fail(&xs[i]) || binds(&xs[i]) {
                    simple = false;
                }
                i += 1;
            }
            let mut i = 0;
            while i < ys.len()
                decreases ys.len() - i,
            {
                if may_fail(&ys[i]) || binds(&ys[i]) {
                    simple = false;
                }
                i += 1;
            }
            let c = atom(blk, c)?;
            let mut out: Vec<Expr> = Vec::new();
            if simple {
                let n = if xs.len() < ys.len() {
                    xs.len()
                } else {
                    ys.len()
                };
                let mut j = 0;
                while j < n
                    invariant
                        n <= xs.len(),
                        n <= ys.len(),
                    decreases n - j,
                {
                    out.push(ite(copy_expr(&c), copy_expr(&xs[j]), copy_expr(&ys[j])));
                    j += 1;
                }
                return Some((tx, out));
            }
            // 枝が失敗しうるなら、スロットごとに、その位置の深さで枝を下ろし直して束縛する。
            // 式は純粋なので、同じ枝を何度評価しても結果は同じで、最初の失敗も同じになる。
            let w = xtype_width(&tx, enums)?;
            let ghost sc0 = sc@;
            let mut j = 0;
            proof {
                assert(decreases_to!(*e => **a));
                assert(decreases_to!(*e => **b));
            }
            while j < w
                invariant
                    sc@ == sc0,
                    extends(*old(blk), *blk),
                    decreases_to!(*e => **a),
                    decreases_to!(*e => **b),
                decreases w - j,
            {
                let d = depth(blk);
                let (_, xs) = closed_in(a, cx, sc, d)?;
                let (_, ys) = closed_in(b, cx, sc, d)?;
                if j >= xs.len() || j >= ys.len() {
                    return None;
                }
                out.push(keep(blk, ite(copy_expr(&c), copy_expr(&xs[j]), copy_expr(&ys[j])))?);
                j += 1;
            }
            Some((tx, out))
        },
        TExpr::Let(a, b) => {
            let (t, slots) = low(a, cx, sc, blk)?;
            let slots = atoms(slots, blk)?;
            let ghost before = sc@;
            sc.push(Bound { ty: t, slots });
            let r = low(b, cx, sc, blk);
            if r.is_none() {
                return None;
            }
            sc.pop();
            proof {
                assert(sc@ =~= before);
            }
            r
        },
        _ => None,
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

/// `forall` と `exists`。集合（Set の要素、Map のキー、List の要素）か、型の全体をたどる。
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
    // 束縛する値の型と、その値が対象に含まれる条件の元（Setの要素の有無、Mapのキーの有無）。
    // List なら、要素の型、長さの上限、Listのスロット。
    let mut flags: Option<Vec<Expr>> = None;
    let mut list: Option<(usize, Vec<Expr>)> = None;
    let st: SType = match over {
        Over::Type(t) => {
            proof {
                lemma_extends_refl(*blk);
            }
            if keys_exec(t, enums).is_none() {
                return None;
            }
            copy_stype(t)
        },
        Over::Set(t, s) => {
            let (ty, cs) = low(s, cx, sc, blk)?;
            match ty {
                XType::Set(u) => {
                    if !stype_eq(&u, t) {
                        return None;
                    }
                    flags = Some(cs);
                    *u
                },
                _ => return None,
            }
        },
        Over::Map(t, m) => {
            let (ty, cs) = low(m, cx, sc, blk)?;
            match ty {
                XType::Map(k, v) => {
                    if !stype_eq(&k, t) {
                        return None;
                    }
                    let (present, _) = map_parts(&k, &v, &cs, enums)?;
                    flags = Some(present);
                    *k
                },
                _ => return None,
            }
        },
        Over::List(l) => {
            let (ty, cs) = low(l, cx, sc, blk)?;
            match ty {
                XType::List(u, max) => {
                    list = Some((max, cs));
                    *u
                },
                _ => return None,
            }
        },
    };
    let d = depth(blk);
    let ghost before = sc@;
    let q = match list {
        None => {
            let ranges = quant_ranges(&st, enums);
            let k = ranges.len();
            let top = d.checked_add(k)?;
            let x = locals(d, top);
            let mut guard = canonical(&st, &x, enums)?;
            match flags {
                Some(fs) => {
                    let r = rank_expr(&to_xtype(&st), &x, &st, enums)?;
                    let hit = select_one(&singletons(&fs), &r)?;
                    guard = and(guard, hit);
                },
                None => {},
            }
            sc.push(Bound { ty: to_xtype(&st), slots: x });
            let b = bool_in(body, cx, sc, top);
            if b.is_none() {
                return None;
            }
            sc.pop();
            let mut q = combine(all, guard, b.unwrap());
            let mut i = ranges.len();
            while i > 0
                invariant
                    i <= ranges.len(),
                decreases i,
            {
                i -= 1;
                let (ty, lo, hi) = ranges[i];
                q = quant(all, ty, lo, hi, q);
            }
            q
        },
        Some((max, cs)) => {
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
        },
    };
    proof {
        assert(sc@ =~= before);
    }
    let mut out: Vec<Expr> = Vec::new();
    out.push(keep(blk, q)?);
    Some((XType::Bool, out))
}

/// 量化の本体と、値が対象に含まれる条件を組み合わせる。
fn combine(all: bool, guard: Expr, e: Expr) -> (r: Expr) {
    if is_bool_lit(&guard, true) {
        e
    } else if all {
        Expr::Implies(Box::new(guard), Box::new(e))
    } else {
        Expr::And(Box::new(guard), Box::new(e))
    }
}

fn quant(all: bool, ty: Type, lo: i64, hi: i64, e: Expr) -> (r: Expr) {
    if all {
        Expr::Forall(ty, lo, hi, Box::new(e))
    } else {
        Expr::Exists(ty, lo, hi, Box::new(e))
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
        lemma_get(
            *e, *cx, sc@, b0, b1, b2, b3, *blk, **a, **x, ms@, sty(k), sty(v), rr, rank_local, c, slots@, fallback@,
            rows, width,
        );
    }
    Some((ty, slots))
}

/// `Map#get` の下ろしの正しさ（[`low_get`]）。
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
        frag(e) ==> lowers(a, cx, sc, b0, b1, XTy::Map(Box::new(sk), Box::new(sv)), ms),
        frag(e) ==> rank_lowers(x, cx, sc, b1, b2, sk, rr),
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
        frag(e) ==> lowers(e, cx, sc, b0, b4, to_xty(sv), slots),
{
    if frag(e) {
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
