//! 中核の式の組み立て。spec の構築子（`ite_s`、`and_s` など）と、対応する exec の構築子。

#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq};
#[cfg(verus_keep_ghost)]
use crate::encoding::{lemma_default_vals_len, lemma_stys, lemma_xtys, sty, stys, STy, SVal, XTy};
#[cfg(verus_keep_ghost)]
use crate::encoding::{xty, xtys, xwidth, xwidth_sum};
use crate::encoding::{SType, XType};
use crate::expr_copy::copy_expr;
#[cfg(verus_keep_ghost)]
use crate::limits::{lemma_lim_xs_at, lemma_xwidth_sum_prefix, lim, lim_xs};
use crate::model::{BinOp, Expr, Value};
#[cfg(verus_keep_ghost)]
use crate::source::SetOp;
use crate::stype_exec::{keys_or_zero_exec, xtype_width};
use vstd::prelude::*;

verus! {

/// 列 `ts` の `i` 番目の要素のスロットの位置。
pub open spec fn xoff(ts: Seq<XTy>, i: int, enums: Seq<i64>) -> int {
    xwidth_sum(ts.take(i), enums) as int
}

pub proof fn lemma_xoff_step(ts: Seq<XTy>, i: int, enums: Seq<i64>)
    requires
        0 <= i < ts.len(),
    ensures
        xoff(ts, i + 1, enums) == xoff(ts, i, enums) + xwidth(ts[i], enums),
{
    assert(ts.take(i + 1).drop_last() =~= ts.take(i));
}

pub open spec fn bool_lit(b: bool) -> Expr {
    Expr::Const(Value::Bool(b))
}

pub open spec fn int_lit(x: i64) -> Expr {
    Expr::Const(Value::Int(x))
}

pub fn cb(x: bool) -> (r: Expr)
    ensures
        r == bool_lit(x),
{
    Expr::Const(Value::Bool(x))
}

pub fn ci(x: i64) -> (r: Expr)
    ensures
        r == int_lit(x),
{
    Expr::Const(Value::Int(x))
}

pub fn is_bool_lit(e: &Expr, b: bool) -> (r: bool)
    ensures
        r == (*e == bool_lit(b)),
{
    match e {
        Expr::Const(Value::Bool(x)) => *x == b,
        _ => false,
    }
}

pub open spec fn and_s(x: Expr, y: Expr) -> Expr {
    if x == bool_lit(true) {
        y
    } else if y == bool_lit(true) {
        x
    } else {
        Expr::And(Box::new(x), Box::new(y))
    }
}

pub open spec fn or_s(x: Expr, y: Expr) -> Expr {
    if x == bool_lit(false) {
        y
    } else if y == bool_lit(false) {
        x
    } else {
        Expr::Or(Box::new(x), Box::new(y))
    }
}

pub open spec fn implies_s(x: Expr, y: Expr) -> Expr {
    if y == bool_lit(true) {
        y
    } else {
        Expr::Implies(Box::new(x), Box::new(y))
    }
}

/// 一方が真のリテラルなら、もう一方にする。
pub fn and(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == and_s(x, y),
{
    if is_bool_lit(&x, true) {
        y
    } else if is_bool_lit(&y, true) {
        x
    } else {
        Expr::And(Box::new(x), Box::new(y))
    }
}

/// 一方が偽のリテラルなら、もう一方にする。
pub fn or(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == or_s(x, y),
{
    if is_bool_lit(&x, false) {
        y
    } else if is_bool_lit(&y, false) {
        x
    } else {
        Expr::Or(Box::new(x), Box::new(y))
    }
}

/// 後件が真のリテラルなら、真にする。
pub fn implies(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == implies_s(x, y),
{
    if is_bool_lit(&y, true) {
        y
    } else {
        Expr::Implies(Box::new(x), Box::new(y))
    }
}

pub open spec fn ite_s(c: Expr, x: Expr, y: Expr) -> Expr {
    Expr::Ite(Box::new(c), Box::new(x), Box::new(y))
}

pub fn ite(c: Expr, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == ite_s(c, x, y),
{
    Expr::Ite(Box::new(c), Box::new(x), Box::new(y))
}

pub fn bin(op: BinOp, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == Expr::Bin(op, Box::new(x), Box::new(y)),
{
    Expr::Bin(op, Box::new(x), Box::new(y))
}

pub fn eq(x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == Expr::Bin(BinOp::Eq, Box::new(x), Box::new(y)),
{
    Expr::Bin(BinOp::Eq, Box::new(x), Box::new(y))
}

/// 式の列の `lo..hi` の部分の複製。
pub fn sub_exprs(xs: &Vec<Expr>, lo: usize, hi: usize) -> (r: Vec<Expr>)
    ensures
        lo <= hi <= xs@.len() ==> r@ == xs@.subrange(lo as int, hi as int),
{
    let mut out: Vec<Expr> = Vec::new();
    if !(lo <= hi && hi <= xs.len()) {
        return out;
    }
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= xs@.len(),
            out@ == xs@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(copy_expr(&xs[i]));
        proof {
            assert(out@ =~= xs@.subrange(lo as int, i + 1));
        }
        i += 1;
    }
    out
}

/// 二分木の節の作り方。
#[derive(Clone, Copy)]
pub enum Join {
    /// [`and`]（真のリテラルを省く）。
    And,
    /// [`or`]（偽のリテラルを省く）。
    Or,
    /// `Expr::And`。
    RawAnd,
    /// `Expr::Or`。
    RawOr,
    /// 整数の和。
    Add,
}

pub open spec fn join_s(k: Join, x: Expr, y: Expr) -> Expr {
    match k {
        Join::And => and_s(x, y),
        Join::Or => or_s(x, y),
        Join::RawAnd => Expr::And(Box::new(x), Box::new(y)),
        Join::RawOr => Expr::Or(Box::new(x), Box::new(y)),
        Join::Add => Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)),
    }
}

pub(crate) fn join(k: Join, x: Expr, y: Expr) -> (r: Expr)
    ensures
        r == join_s(k, x, y),
{
    match k {
        Join::And => and(x, y),
        Join::Or => or(x, y),
        Join::RawAnd => Expr::And(Box::new(x), Box::new(y)),
        Join::RawOr => Expr::Or(Box::new(x), Box::new(y)),
        Join::Add => Expr::Bin(BinOp::Add, Box::new(x), Box::new(y)),
    }
}

/// 列を平衡した二分木にたたむ。前半は長さの半分（切り捨て）。空なら `unit`。
pub open spec fn tree_s(items: Seq<Expr>, unit: Expr, k: Join) -> Expr
    decreases items.len(),
{
    if items.len() == 0 {
        unit
    } else if items.len() == 1 {
        items[0]
    } else {
        let m = items.len() / 2;
        join_s(k, tree_s(items.take(m as int), unit, k), tree_s(items.skip(m as int), unit, k))
    }
}

pub(crate) fn tree_range(items: &Vec<Expr>, lo: usize, hi: usize, unit: &Expr, k: Join) -> (r: Expr)
    requires
        lo <= hi <= items@.len(),
    ensures
        r == tree_s(items@.subrange(lo as int, hi as int), *unit, k),
    decreases hi - lo,
{
    let ghost s = items@.subrange(lo as int, hi as int);
    if hi - lo == 0 {
        copy_expr(unit)
    } else if hi - lo == 1 {
        copy_expr(&items[lo])
    } else {
        let mid = lo + (hi - lo) / 2;
        proof {
            assert(s.take(((hi - lo) / 2) as int) =~= items@.subrange(lo as int, mid as int));
            assert(s.skip(((hi - lo) / 2) as int) =~= items@.subrange(mid as int, hi as int));
        }
        let l = tree_range(items, lo, mid, unit, k);
        let r = tree_range(items, mid, hi, unit, k);
        join(k, l, r)
    }
}

pub fn tree(items: &Vec<Expr>, unit: Expr, k: Join) -> (r: Expr)
    ensures
        r == tree_s(items@, unit, k),
{
    proof {
        assert(items@.subrange(0, items@.len() as int) =~= items@);
    }
    tree_range(items, 0, items.len(), &unit, k)
}

/// すべてが真。
pub fn all_of(items: &Vec<Expr>) -> (r: Expr)
    ensures
        r == tree_s(items@, bool_lit(true), Join::And),
{
    tree(items, cb(true), Join::And)
}

/// 値の列を、定数の式の列にする。
pub open spec fn lits(vs: Seq<Value>) -> Seq<Expr> {
    vs.map_values(|v: Value| Expr::Const(v))
}

/// `out` の後ろに `xs` の複製を加える。
pub fn extend(out: &mut Vec<Expr>, xs: &Vec<Expr>)
    ensures
        final(out)@ == old(out)@ + xs@,
{
    let ghost start = out@;
    let mut i = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            out@ == start + xs@.take(i as int),
        decreases xs.len() - i,
    {
        out.push(copy_expr(&xs[i]));
        proof {
            assert(xs@.take(i + 1) =~= xs@.take(i as int).push(xs@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs@.len() as int) =~= xs@);
    }
}

/// 型 `t` の既定値のスロット。
pub fn defaults(t: &SType, enums: &Vec<i64>) -> (r: Vec<Expr>)
    ensures
        r@ == lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)),
    decreases t, 1nat,
{
    let mut out: Vec<Expr> = Vec::new();
    match t {
        SType::Bool => {
            out.push(cb(false));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Int(lo, _) => {
            out.push(ci(*lo));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Enum(id) => {
            out.push(Expr::Const(Value::Enum(*id, 0)));
            proof {
                assert(out@ =~= lits(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = defaults_all(t, ts, enums);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = defaults_all(t, ts, enums);
        },
        SType::Option(x) => {
            out.push(cb(false));
            let d = defaults(x, enums);
            extend(&mut out, &d);
            proof {
                let dv = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                assert(out@ =~= lits(seq![Value::Bool(false)] + dv));
            }
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut i = 0;
            while i < n
                invariant
                    i <= n,
                    out@ == lits(Seq::new(i as nat, |_j: int| Value::Bool(false))),
                decreases n - i,
            {
                out.push(cb(false));
                proof {
                    assert(out@ =~= lits(Seq::new((i + 1) as nat, |_j: int| Value::Bool(false))));
                }
                i += 1;
            }
            proof {
                let bits = Seq::new(n as nat, |_i: int| false);
                assert(enc(default_val(sty(*t), enums@), sty(*t), enums@) =~= Seq::new(
                    n as nat,
                    |_j: int| Value::Bool(false),
                ));
            }
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let d = defaults(v, enums);
            let ghost dv = enc(default_val(sty(**v), enums@), sty(**v), enums@);
            let mut i = 0;
            proof {
                assert(enc_rows(Seq::new(0, |_j: int| None::<SVal>), sty(**v), enums@) =~= Seq::<Value>::empty());
                assert(out@ =~= lits(Seq::<Value>::empty()));
            }
            while i < n
                invariant
                    i <= n,
                    d@ == lits(dv),
                    dv == enc(default_val(sty(**v), enums@), sty(**v), enums@),
                    out@ == lits(enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@)),
                decreases n - i,
            {
                out.push(cb(false));
                extend(&mut out, &d);
                proof {
                    let rows = Seq::new((i + 1) as nat, |_j: int| None::<SVal>);
                    assert(rows.drop_last() =~= Seq::new(i as nat, |_j: int| None::<SVal>));
                    let prev = enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@);
                    assert(enc_rows(rows, sty(**v), enums@) == prev + (seq![Value::Bool(false)] + dv));
                    assert(out@ =~= lits(prev + (seq![Value::Bool(false)] + dv)));
                }
                i += 1;
            }
        },
        SType::List(e, max) => {
            out.push(ci(0));
            let d = defaults(e, enums);
            let ghost dv = enc(default_val(sty(**e), enums@), sty(**e), enums@);
            let mut i = 0;
            proof {
                assert(out@ =~= lits(seq![Value::Int(0)] + enc_repeat(dv, 0)));
            }
            while i < *max
                invariant
                    i <= *max,
                    d@ == lits(dv),
                    dv == enc(default_val(sty(**e), enums@), sty(**e), enums@),
                    out@ == lits(seq![Value::Int(0)] + enc_repeat(dv, i as nat)),
                decreases *max - i,
            {
                extend(&mut out, &d);
                proof {
                    assert(enc_repeat(dv, (i + 1) as nat) == enc_repeat(dv, i as nat) + dv);
                    assert(out@ =~= lits(seq![Value::Int(0)] + enc_repeat(dv, (i + 1) as nat)));
                }
                i += 1;
            }
            proof {
                let items = Seq::<SVal>::empty();
                assert(enc_items(items, sty(**e), enums@) =~= Seq::<Value>::empty());
                assert(enc(default_val(sty(*t), enums@), sty(*t), enums@) =~= seq![Value::Int(0)] + enc_repeat(
                    dv,
                    *max as nat,
                ));
            }
        },
    }
    out
}

pub(crate) fn defaults_all(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Vec<Expr>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r@ == lits(enc_seq(default_vals(stys(ts@), enums@), stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let mut out: Vec<Expr> = Vec::new();
    let ghost xs = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(xs.take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= lits(enc_seq(default_vals(xs.take(0), enums@), xs.take(0), enums@)));
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts@.len(),
            xs == stys(ts@),
            xs.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] xs[j] == sty(ts@[j]),
            out@ == lits(enc_seq(default_vals(xs.take(i as int), enums@), xs.take(i as int), enums@)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let d = defaults(&ts[i], enums);
        let ghost prev = out@;
        extend(&mut out, &d);
        proof {
            let p = xs.take(i + 1);
            assert(p.drop_last() =~= xs.take(i as int));
            assert(p.last() == xs[i as int]);
            let dvs = default_vals(p, enums@);
            assert(dvs.drop_last() == default_vals(xs.take(i as int), enums@));
            assert(dvs.last() == default_val(xs[i as int], enums@));
            lemma_default_vals_len(p, enums@);
            assert(enc_seq(dvs, p, enums@) == enc_seq(dvs.drop_last(), p.drop_last(), enums@) + enc(
                dvs.last(),
                p.last(),
                enums@,
            ));
            let a = enc_seq(default_vals(xs.take(i as int), enums@), xs.take(i as int), enums@);
            let b = enc(default_val(xs[i as int], enums@), xs[i as int], enums@);
            assert(out@ =~= lits(a + b));
        }
        i += 1;
    }
    proof {
        assert(xs.take(ts@.len() as int) =~= xs);
    }
    out
}

/// 要素の型ごとに、スロットの列を区切る。
pub fn split(tys: &Vec<XType>, slots: &Vec<Expr>, enums: &Vec<i64>) -> (r: Option<Vec<Vec<Expr>>>)
    ensures
        r matches Some(parts) ==> parts@.len() == tys@.len() && forall|i: int|
            0 <= i < tys@.len() ==> #[trigger] split_ok(parts@[i]@, slots@, xtys(tys@), i, enums@),
        lim_xs(xtys(tys@), enums@) && xwidth_sum(xtys(tys@), enums@) <= lim() && xwidth_sum(xtys(tys@), enums@)
            <= slots@.len() ==> r is Some,
{
    let ghost pre = lim_xs(xtys(tys@), enums@) && xwidth_sum(xtys(tys@), enums@) <= lim() && xwidth_sum(
        xtys(tys@),
        enums@,
    ) <= slots@.len();
    let mut out: Vec<Vec<Expr>> = Vec::new();
    let mut at: usize = 0;
    let mut i = 0;
    proof {
        lemma_xtys(tys@);
        assert(xtys(tys@).take(0) =~= Seq::<XTy>::empty());
    }
    while i < tys.len()
        invariant
            i <= tys@.len(),
            xtys(tys@).len() == tys@.len(),
            forall|j: int| 0 <= j < tys@.len() ==> #[trigger] xtys(tys@)[j] == xty(tys@[j]),
            at == xoff(xtys(tys@), i as int, enums@),
            at <= slots@.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] split_ok(out@[k]@, slots@, xtys(tys@), k, enums@),
            pre == (lim_xs(xtys(tys@), enums@) && xwidth_sum(xtys(tys@), enums@) <= lim() && xwidth_sum(
                xtys(tys@),
                enums@,
            ) <= slots@.len()),
        decreases tys.len() - i,
    {
        proof {
            lemma_xoff_step(xtys(tys@), i as int, enums@);
            if pre {
                lemma_lim_xs_at(xtys(tys@), enums@, i as int);
                lemma_xwidth_sum_prefix(xtys(tys@), enums@, i + 1);
                assert(usize::MAX >= 0xffff_ffff);
            }
        }
        let w = xtype_width(&tys[i], enums)?;
        let end = at.checked_add(w)?;
        if end > slots.len() {
            return None;
        }
        proof {
            lemma_xoff_step(xtys(tys@), i as int, enums@);
        }
        out.push(sub_exprs(slots, at, end));
        proof {
            assert(split_ok(out@[i as int]@, slots@, xtys(tys@), i as int, enums@));
        }
        at = end;
        i += 1;
    }
    Some(out)
}

/// `part` は、型の列 `ts` のスロットの列 `slots` の `i` 番目の部分である。
pub open spec fn split_ok(part: Seq<Expr>, slots: Seq<Expr>, ts: Seq<XTy>, i: int, enums: Seq<i64>) -> bool {
    &&& 0 <= xoff(ts, i, enums)
    &&& xoff(ts, i, enums) + xwidth(ts[i], enums) <= slots.len()
    &&& part == slots.subrange(xoff(ts, i, enums), xoff(ts, i, enums) + xwidth(ts[i], enums))
}

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

pub open spec fn all_pure(s: Seq<Expr>, n: nat) -> bool {
    forall|j: int| 0 <= j < s.len() ==> pure_below(#[trigger] s[j], n)
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

/// Setの演算の、要素ごとのスロットの式。
pub open spec fn setop_s(op: SetOp, x: Expr, y: Expr) -> Expr {
    match op {
        SetOp::Union => or_s(x, y),
        SetOp::Intersection => and_s(x, y),
        SetOp::Difference => and_s(x, Expr::Not(Box::new(y))),
        SetOp::Subset => implies_s(x, y),
    }
}

pub open spec fn mark_s(on: bool, bit: Expr, r: Expr, k: i64) -> Expr {
    if on {
        or_s(bit, Expr::Bin(BinOp::Eq, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    } else {
        and_s(bit, Expr::Bin(BinOp::Ne, Box::new(r), Box::new(Expr::Const(Value::Int(k)))))
    }
}

} // verus!
