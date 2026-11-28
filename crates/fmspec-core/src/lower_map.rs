//! Map のリテラル、参照、キーの有無、更新、削除、キーの集合の下ろし。意味の保存は `preserve_map` にある。

#[cfg(verus_keep_ghost)]
use crate::canon::lemma_defaults_typed;
#[cfg(verus_keep_ghost)]
use crate::encoding::{default_val, enc, keys, keys_or_zero, lemma_default_len, lemma_xwidth_of};
#[cfg(verus_keep_ghost)]
use crate::encoding::{sty, to_xty, wf_stype, width, xty, STy, XTy};
use crate::encoding::{SType, XType};
#[cfg(verus_keep_ghost)]
use crate::expr_build::{all_pure, pure_below};
use crate::expr_build::{and, bin, cb, ci, defaults, extend};
#[cfg(verus_keep_ghost)]
use crate::infer::ir_type_of;
#[cfg(verus_keep_ghost)]
use crate::limits::lemma_lim_small;
#[cfg(verus_keep_ghost)]
use crate::lists::rows_view;
#[cfg(verus_keep_ghost)]
use crate::lower_ctx::{added, extends};
use crate::lower_ctx::{Block, Bound, Fail, LowerCtx};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{all_ty, binds_typed, blt, etys, has_ty, lemma_and_typed, lemma_bind_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_bools_typed, lemma_cols_typed, lemma_etys_concat, lemma_flat_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_ge0_typed, lemma_has_ty_blk, lemma_ite_rows_typed};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_map_rows_typed, lemma_mrows_typed, lemma_tok_ext, lemma_typed_blk};
#[cfg(verus_keep_ghost)]
use crate::lower_types::{lemma_xetys_of, lenv, shaped, slot_tys, tok, typed, xetys};
#[cfg(verus_keep_ghost)]
use crate::lowering::low_ok;
use crate::lowering::{element, element_rank, lookup_rank, low};
use crate::map_lookup::select_flat_map_lookup;
use crate::maps::map_rows;
use crate::model::{BinOp, Expr};
#[cfg(verus_keep_ghost)]
use crate::model::{Type, Value};
#[cfg(verus_keep_ghost)]
use crate::preserve::{lemma_extends_trans, lemma_fresh_push, lemma_lits, lemma_pure_mono};
#[cfg(verus_keep_ghost)]
use crate::preserve_map::{lemma_delete, lemma_get, lemma_has_key, lemma_keys, lemma_maplit_base};
#[cfg(verus_keep_ghost)]
use crate::preserve_map::{lemma_maplit_step, lemma_put, lemma_put_expr, maplit_ok, put_lowers};
use crate::quant::pick_slot;
#[cfg(verus_keep_ghost)]
use crate::slots::lemma_extends_refl;
use crate::slots::{bind, depth, heads, ite_rows, join_rows, need};
#[cfg(verus_keep_ghost)]
use crate::source::Item;
use crate::source::TExpr;
use crate::stype_exec::{copy_stype, keys_exec, keys_or_zero_exec, stype_eq, stype_width, to_xtype};
#[cfg(verus_keep_ghost)]
use crate::total::{bound_tys, deep, here_ok, items_ok, lemma_all_pure_mono, lemma_flat_shape};
#[cfg(verus_keep_ghost)]
use crate::total::{lemma_heads_pure, lemma_ite_rows_shape, lemma_items_ok_at, lemma_items_ok_intro};
#[cfg(verus_keep_ghost)]
use crate::total::{lemma_mrows_shape, lemma_ok_map, lemma_put_pre, lemma_sc_wf_mono, lim_ok, ok_s};
#[cfg(verus_keep_ghost)]
use crate::total::{ok_s_o, put_pre, sctx, tpre};
#[cfg(verus_keep_ghost)]
use crate::typing::ETy;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

/// Mapのスロット `ms` のキー `key` に値 `value` を置く。キーと値が型に属さなければ `FAIL_NOT_IN_DOMAIN` で失敗する。
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub(crate) fn put(
    _parent: &TExpr,
    ms: &Vec<Expr>,
    k: &SType,
    v: &SType,
    key: &TExpr,
    value: &TExpr,
    cx: &LowerCtx,
    sc: &mut Vec<Bound>,
    blk: &mut Block,
) -> (r: Result<Vec<Expr>, Fail>)
    requires
        old(blk).wf(),
        decreases_to!(*_parent => *key),
        decreases_to!(*_parent => *value),
    ensures
        extends(*old(blk), *final(blk)),
        r is Ok ==> final(sc)@ == old(sc)@,
        r matches Ok(out) ==> put_lowers(
            *key,
            *value,
            *cx,
            old(sc)@,
            *old(blk),
            *final(blk),
            sty(*k),
            sty(*v),
            ms@,
            out@,
        ),
        put_pre(*key, *value, *cx, old(sc)@, old(blk).depth_s(), sty(*k), sty(*v), ms@) ==> deep(r) && (r matches Ok(
            out,
        ) ==> shaped(out@, XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), final(blk).depth_s(), cx.enums@)),
        put_pre(*key, *value, *cx, old(sc)@, old(blk).depth_s(), sty(*k), sty(*v), ms@) && tok(*cx, old(sc)@, *old(blk))
            && typed(ms@, xetys(XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), cx.enums@), lenv(*cx), blt(*old(blk), *cx)) ==> binds_typed(
            final(blk).outer@,
            final(blk).binds@,
            lenv(*cx),
        ) && (r matches Ok(out) ==> typed(out@, xetys(XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), cx.enums@), lenv(*cx), blt(*final(blk), *cx))),
    decreases _parent, 0nat,
{
    proof {
        lemma_extends_refl(*blk);
    }
    let ghost b0 = *blk;
    let ghost pre = put_pre(*key, *value, *cx, old(sc)@, old(blk).depth_s(), sty(*k), sty(*v), ms@);
    let ghost tq = pre && tok(*cx, old(sc)@, *old(blk)) && typed(ms@, xetys(XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), cx.enums@), lenv(*cx), blt(*old(blk), *cx));
    let ghost tv = lenv(*cx);
    let ghost rowt = seq![Type::Bool] + slot_tys(sty(*v), cx.enums@);
    let ghost nk = keys_or_zero(sty(*k), cx.enums@);
    proof {
        reveal(put_pre);
        if tq {
            crate::lower_types::lemma_slot_tys_len(sty(*v), cx.enums@);
            assert(xetys(XTy::Map(Box::new(sty(*k)), Box::new(sty(*v))), cx.enums@) == etys(crate::lower_types::ty_repeat(rowt, nk)));
            assert(wf_stype(sty(*k), cx.enums@) && wf_stype(sty(*v), cx.enums@));
            lemma_lim_small(sty(*k), cx.enums@);
            lemma_lim_small(sty(*v), cx.enums@);
        }
    }
    let ghost mt = STy::Map(Box::new(sty(*k)), Box::new(sty(*v)));
    let rows = need(map_rows(k, v, ms, &cx.enums))?;
    proof {
        if pre {
            assert(keys(sty(*k), cx.enums@) is Some);
            assert(rows@.len() <= crate::encoding::MAX_KEYS);
        }
    }
    if rows.len() > 0x7fff_ffffusize {
        return Err(Fail::Type);
    }
    proof {
        if tq {
            lemma_mrows_typed(ms@, rows_view(rows@), rowt, nk, tv, blt(b0, *cx));
        }
    }
    let r = element_rank(key, cx, sc, blk, k)?;
    let ghost b1 = *blk;
    proof {
        if pre {
            lemma_sc_wf_mono(sc@, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
        if tq {
            lemma_tok_ext(*cx, sc@, b0, b1);
        }
    }
    let xs = element(value, cx, sc, blk, v)?;
    let mut alt: Vec<Expr> = Vec::new();
    alt.push(cb(true));
    extend(&mut alt, &xs);
    proof {
        if pre {
            let w1 = (1 + width(sty(*v), cx.enums@)) as nat;
            lemma_all_pure_mono(ms@, b0.depth_s(), blk.depth_s());
            lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(*k), cx.enums@), blk.depth_s());
            assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == alt@.len() by {
                assert(rows_view(rows@)[q] == rows@[q]@);
            }
            assert(all_pure(alt@, blk.depth_s())) by {
                assert forall|j: int| 0 <= j < alt@.len() implies pure_below(#[trigger] alt@[j], blk.depth_s()) by {
                    if j > 0 {
                        assert(alt@[j] == xs@[j - 1]);
                    }
                }
            }
            lemma_pure_mono(r, b1.depth_s(), blk.depth_s());
        }
    }
    proof {
        if tq {
            let rv = rows_view(rows@);
            let ys = etys(slot_tys(sty(*v), cx.enums@));
            lemma_etys_concat(seq![Type::Bool], slot_tys(sty(*v), cx.enums@));
            assert(etys(seq![Type::Bool]) =~= seq![ETy::Bool]);
            assert forall|j: int| 0 <= j < alt@.len() implies #[trigger] has_ty(alt@[j], tv, blt(*blk, *cx), etys(rowt)[j]) by {
                if j > 0 {
                    assert(alt@[j] == xs@[j - 1]);
                    assert(has_ty(xs@[j - 1], tv, blt(*blk, *cx), ys[j - 1]));
                }
            }
            lemma_all_pure_mono(ms@, b0.depth_s(), b0.depth_s());
            let w1 = (1 + width(sty(*v), cx.enums@)) as nat;
            lemma_mrows_shape(ms@, rv, w1, nk, b0.depth_s());
            assert forall|q: int| 0 <= q < rv.len() implies #[trigger] typed(rv[q], etys(rowt), tv, blt(*blk, *cx)) by {
                assert(typed(rv[q], etys(rowt), tv, blt(b0, *cx)));
                lemma_typed_blk(rv[q], etys(rowt), *cx, b0, *blk);
            }
            lemma_has_ty_blk(r, ETy::Int, *cx, b1, *blk);
        }
    }
    let out = need(ite_rows(&rows, &r, &alt))?;
    let res = join_rows(&out);
    proof {
        if tq {
            let rv = rows_view(rows@);
            lemma_ite_rows_typed(rows_view(out@), rv, r, alt@, etys(rowt), tv, blt(*blk, *cx));
            lemma_flat_typed(rows_view(out@), rowt, tv, blt(*blk, *cx));
        }
    }
    proof {
        if pre {
            let w1 = (1 + width(sty(*v), cx.enums@)) as nat;
            lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), r, alt@, blk.depth_s());
            lemma_flat_shape(rows_view(out@), w1, blk.depth_s());
            assert(res@.len() == keys_or_zero(sty(*k), cx.enums@) * w1);
        }
    }
    proof {
        lemma_extends_trans(b0, b1, *blk);
        lemma_put(*key, *value, *cx, sc@, b0, b1, *blk, sty(*k), sty(*v), ms@, rows_view(rows@), r, xs@, alt@, rows_view(out@), res@);
    }
    Ok(res)
}

/// Mapのリテラル。
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
pub(crate) fn low_map_lit(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is MapLit,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::MapLit(k, v, items) => {
            proof {
                assert(decreases_to!(*e => *items));
                lemma_extends_refl(*blk);
            }
            if keys_exec(k, enums).is_none() {
                return Err(Fail::Type);
            }
            let map = SType::Map(Box::new(copy_stype(k)), Box::new(copy_stype(v)));
            let mut slots = defaults(&map, enums);
            let ghost sc0 = sc@;
            let ghost b0 = *blk;
            let ghost kt = sty(*k);
            let ghost vt = sty(*v);
            proof {
                lemma_default_len(sty(map), enums@);
                lemma_lits(enc(default_val(sty(map), enums@), sty(map), enums@), arbitrary(), Seq::empty());
                if pre {
                    lemma_items_ok_intro(items@, c, bt, kt, vt);
                    assert(here_ok(*e, c, bt));
                    assert(ir_type_of(*e, c, bt) == Some(XTy::Map(Box::new(kt), Box::new(vt))));
                    lemma_ok_map(kt, vt, enums@);
                    assert(ok_s_o(STy::Map(Box::new(kt), Box::new(vt)), enums@)) by {
                        reveal(ok_s_o);
                    }
                }
            }
            proof {
                lemma_maplit_base(*cx, sc0, b0, kt, vt, slots@);
                assert(items@.take(0) =~= Seq::<Item>::empty());
                if tp {
                    let mt = STy::Map(Box::new(kt), Box::new(vt));
                    assert(ok_s(mt, enums@)) by {
                        reveal(ok_s_o);
                    }
                    lemma_lim_small(mt, enums@);
                    lemma_defaults_typed(mt, tv, blt(b0, *cx));
                    assert(xetys(XTy::Map(Box::new(kt), Box::new(vt)), enums@) == etys(slot_tys(mt, enums@)));
                }
            }
            let mut i = 0;
            while i < items.len()
                invariant
                    decreases_to!(*e => *items),
                    sc@ == sc0,
                    b0 == *old(blk),
                    extends(*old(blk), *blk),
                    i <= items@.len(),
                    kt == sty(*k),
                    vt == sty(*v),
                    e is MapLit && e->MapLit_2 == *items,
                    maplit_ok(items@.take(i as int), *cx, sc0, b0, *blk, kt, vt, slots@),
                    pre == tpre(*e, *cx, sc0, b0.depth_s()),
                    sc0 == old(sc)@,
                    c == sctx(*cx),
                    bt == bound_tys(sc0),
                    pre ==> items_ok(items@, c, bt, kt, vt),
                    pre ==> ok_s_o(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
                    pre ==> slots@.len() == width(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@) && all_pure(
                        slots@,
                        blk.depth_s(),
                    ),
                    tp == (pre && tok(*cx, sc0, b0)),
                    tv == lenv(*cx),
                    tp ==> tok(*cx, sc0, *blk) && typed(
                        slots@,
                        xetys(XTy::Map(Box::new(kt), Box::new(vt)), cx.enums@),
                        tv,
                        blt(*blk, *cx),
                    ),
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
                let ghost b1 = *blk;
                let ghost s1 = slots@;
                proof {
                    if pre {
                        lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
                        lemma_items_ok_at(items@, c, bt, kt, vt, i as int);
                        assert(tpre(item.key, *cx, sc@, blk.depth_s()));
                        assert(tpre(item.value, *cx, sc@, blk.depth_s()));
                        assert(ir_type_of(item.key, sctx(*cx), bound_tys(sc@)) == Some(to_xty(kt)));
                        assert(ir_type_of(item.value, sctx(*cx), bound_tys(sc@)) == Some(to_xty(vt)));
                        assert(slots@.len() == width(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@));
                        assert(all_pure(slots@, blk.depth_s()));
                        lemma_put_pre(item.key, item.value, *cx, sc@, blk.depth_s(), kt, vt, slots@);
                    }
                }
                slots = put(e, &slots, k, v, &item.key, &item.value, cx, sc, blk)?;
                proof {
                    if tp {
                        lemma_tok_ext(*cx, sc0, b1, *blk);
                    }
                    lemma_extends_trans(*old(blk), b1, *blk);
                    assert(items@.take(i + 1).drop_last() =~= items@.take(i as int));
                    if pre {
                        lemma_xwidth_of(STy::Map(Box::new(kt), Box::new(vt)), cx.enums@);
                    }
                    lemma_maplit_step(items@.take(i + 1), *cx, sc0, b0, b1, *blk, kt, vt, s1, slots@);
                }
                i += 1;
            }
            proof {
                assert(items@.take(items@.len() as int) =~= items@);
            }
            Ok((to_xtype(&map), slots))
        },
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            Err(Fail::Type)
        },
    }
}

/// `Map#get`。キーの番号を束縛し、キーがなければ失敗する検査を束縛してから、行の値を選ぶ。
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub(crate) fn low_get(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Get,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let (t, a, x) = match e {
        TExpr::Get(t, a, x) => (t, a, x),
        _ => {
            proof {
                lemma_extends_refl(*blk);
            }
            return Err(Fail::Type);
        },
    };
    let ghost b0 = *blk;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    proof {
        if pre {
            assert(lim_ok(**a, c, bt) && lim_ok(**x, c, bt));
        }
    }
    let (tm, ms) = low(a, cx, sc, blk)?;
    let ghost b1 = *blk;
    proof {
        if pre {
            assert(here_ok(**a, c, bt));
            lemma_sc_wf_mono(sc0, b0.depth_s(), b1.depth_s(), cx.enums@);
        }
    }
    let ghost tmx = xty(tm);
    let (k, v) = match tm {
        XType::Map(k, v) => (*k, *v),
        _ => return Err(Fail::Type),
    };
    if !stype_eq(&k, t) {
        return Err(Fail::Type);
    }
    proof {
        if pre {
            lemma_ok_map(sty(k), sty(v), enums@);
        }
        if tp {
            lemma_tok_ext(*cx, sc0, b0, b1);
            lemma_lim_small(sty(k), cx.enums@);
            lemma_lim_small(sty(v), cx.enums@);
        }
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
    proof {
        if tp {
            if b3 == b2 {
                assert(has_ty(Expr::Local(rank_local), tv, blt(b3, *cx), ETy::Int));
            } else {
                lemma_bind_typed(b2, b3, rr, Expr::Local(rank_local), *cx, ETy::Int);
            }
        }
    }
    let rows = keys_or_zero_exec(&k, enums);
    let width = need(stype_width(&v, enums))?;
    let fallback = defaults(&v, enums);
    proof {
        lemma_default_len(sty(v), enums@);
        lemma_lits(enc(default_val(sty(v), enums@), sty(v), enums@), arbitrary(), Seq::empty());
        lemma_xwidth_of(sty(v), enums@);
        assert(usize::MAX >= 0xffff_ffff);
        if pre {
            assert(rank_local < b3.depth_s());
            lemma_all_pure_mono(ms@, b1.depth_s(), b3.depth_s());
        }
    }
    let ghost sv = sty(v);
    let ghost row = seq![Type::Bool] + slot_tys(sv, cx.enums@);
    let ghost ys = etys(row);
    proof {
        if tp {
            let mt = STy::Map(Box::new(sty(k)), Box::new(sv));
            lemma_xetys_of(mt, cx.enums@);
            assert(tmx == to_xty(mt));
            crate::lower_types::lemma_slot_tys_len(sv, cx.enums@);
            lemma_extends_trans(b1, b2, b3);
            lemma_typed_blk(ms@, xetys(tmx, cx.enums@), *cx, b1, b3);
            assert(slot_tys(mt, cx.enums@) == crate::lower_types::ty_repeat(row, rows as nat));
            lemma_cols_typed(ms@, row, rows, width, tv, blt(b3, *cx));
            lemma_defaults_typed(sv, tv, blt(b3, *cx));
            assert(ys.subrange(1, 1 + width as int) =~= etys(slot_tys(sv, cx.enums@)));
            assert(crate::map_lookup::rank_ty(blt(b3, *cx), rank_local));
        }
    }
    let (chk, slots) = need(select_flat_map_lookup(&ms, rows, width, rank_local, &fallback))?;
    let ghost c = chk;
    bind(blk, chk)?;
    proof {
        if pre {
            assert(all_pure(slots@, b3.depth_s()));
            lemma_all_pure_mono(slots@, b3.depth_s(), blk.depth_s());
        }
        if tp {
            assert(has_ty(c, tv, blt(b3, *cx), ETy::Bool));
            assert(typed(slots@, ys.subrange(1, 1 + width as int), tv, blt(b3, *cx)));
            lemma_bind_typed(b3, *blk, c, Expr::Local(b3.depth_s() as usize), *cx, ETy::Bool);
            lemma_typed_blk(slots@, etys(slot_tys(sv, cx.enums@)), *cx, b3, *blk);
            lemma_xetys_of(sv, cx.enums@);
        }
    }
    let ty = to_xtype(&v);
    proof {
        assert(added(b2, b3, rr, Expr::Local(rank_local)));
        lemma_fresh_push(b3, *blk, c);
        lemma_get(
            *e, *cx, sc@, b0, b1, b2, b3, *blk, **a, **x, ms@, sty(k), sty(v), rr, rank_local, c, slots@,
            fallback@, rows, width,
        );
    }
    Ok((ty, slots))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[allow(unused_variables)]
pub(crate) fn low_map_access(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is HasKey || e is Put || e is Delete || e is Keys,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 1nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::HasKey(_, _, _) => low_has_key(e, cx, sc, blk),
        TExpr::Put(kt, vt, a, x, y) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, *old(blk), *blk);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, kt) || !stype_eq(&v, vt) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt) && lim_ok(**y, c, bt));
                    assert(tpre(**x, *cx, sc@, blk.depth_s()));
                    assert(tpre(**y, *cx, sc@, blk.depth_s()));
                    lemma_put_pre(**x, **y, *cx, sc@, blk.depth_s(), sty(k), sty(v), ms@);
                }
            }
            let slots = put(e, &ms, &k, &v, x, y, cx, sc, blk)?;
            proof {
                lemma_put_expr(*e, *cx, sc@, b0, b1, *blk, sty(k), sty(v), ms@, slots@);
            }
            Ok((tm, slots))
        },
        TExpr::Delete(_, _, _) => low_delete(e, cx, sc, blk),
        _ => low_keys(e, cx, sc, blk),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
pub(crate) fn low_has_key(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is HasKey,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::HasKey(t, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, *old(blk), *blk);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, t) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt));
                }
                if tp {
                    lemma_lim_small(sty(k), cx.enums@);
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), b1.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() > 0 by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let present = need(heads(&rows))?;
            proof {
                if tp {
                    lemma_map_rows_typed(ms@, rows_view(rows@), sty(k), sty(v), tv, blt(b1, *cx));
                }
            }
            proof {
                if pre {
                    lemma_heads_pure(present@, rows_view(rows@), b1.depth_s());
                    assert(present@.len() <= crate::encoding::MAX_KEYS);
                }
            }
            if present.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let ghost rg = r;
            let hit = pick_slot(&present, &r);
            let ghost hg = hit;
            let known = bin(BinOp::Ge, r, ci(0));
            let mut out: Vec<Expr> = Vec::new();
            out.push(and(known, hit));
            proof {
                if pre {
                    lemma_all_pure_mono(present@, b1.depth_s(), blk.depth_s());
                    crate::quant::lemma_hit_pure(rg, present@, hg, blk.depth_s());
                    if tp {
                        assert(all_ty(present@, ETy::Bool, tv, blt(b1, *cx)));
                        assert forall|q: int| 0 <= q < present@.len() implies #[trigger] has_ty(present@[q], tv, blt(*blk, *cx), ETy::Bool) by {
                            assert(pure_below(present@[q], b1.depth_s()));
                            assert(has_ty(present@[q], tv, blt(b1, *cx), ETy::Bool));
                            lemma_has_ty_blk(present@[q], ETy::Bool, *cx, b1, *blk);
                        }
                        lemma_ge0_typed(rg, tv, blt(*blk, *cx));
                        if present@.len() > 0 {
                            assert(all_ty(present@, ETy::Bool, tv, blt(*blk, *cx)));
                        }
                        lemma_and_typed(
                            Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                            hg,
                            tv,
                            blt(*blk, *cx),
                        );
                    }
                    assert(out@[0] == crate::expr_build::and_s(
                        Expr::Bin(BinOp::Ge, Box::new(rg), Box::new(Expr::Const(Value::Int(0)))),
                        hg,
                    ));
                }
            }
            proof {
                lemma_has_key(*e, *cx, sc@, b0, b1, *blk, sty(v), ms@, rows_view(rows@), present@, rg, hg, out@);
            }
            Ok((XType::Bool, out))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_delete(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Delete,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Delete(t, a, x) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, *old(blk), *blk);
                }
            }
            let ghost b1 = *blk;
            let (k, v) = match &tm {
                XType::Map(k, v) => (copy_stype(k), copy_stype(v)),
                _ => return Err(Fail::Type),
            };
            if !stype_eq(&k, t) {
                return Err(Fail::Type);
            }
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                    assert(lim_ok(**x, c, bt));
                }
                if tp {
                    lemma_lim_small(sty(k), cx.enums@);
                    lemma_lim_small(sty(v), cx.enums@);
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    assert(rows@.len() <= crate::encoding::MAX_KEYS);
                }
            }
            if rows.len() > 0x7fff_ffffusize {
                return Err(Fail::Type);
            }
            let r = lookup_rank(x, cx, sc, blk, &k)?;
            let mut alt: Vec<Expr> = Vec::new();
            alt.push(cb(false));
            let dv = defaults(&v, enums);
            extend(&mut alt, &dv);
            proof {
                lemma_default_len(sty(v), enums@);
                lemma_lits(enc(default_val(sty(v), enums@), sty(v), enums@), arbitrary(), Seq::empty());
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_all_pure_mono(ms@, b1.depth_s(), blk.depth_s());
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() == alt@.len() by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                    assert(all_pure(alt@, blk.depth_s())) by {
                        assert forall|j: int| 0 <= j < alt@.len() implies pure_below(#[trigger] alt@[j], blk.depth_s()) by {
                            if j > 0 {
                                assert(alt@[j] == dv@[j - 1]);
                            }
                        }
                    }
                }
            }
            let out = need(ite_rows(&rows, &r, &alt))?;
            let res = join_rows(&out);
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_ite_rows_shape(rows_view(out@), rows_view(rows@), r, alt@, blk.depth_s());
                    lemma_flat_shape(rows_view(out@), w1, blk.depth_s());
                }
                if tp {
                    let sv = sty(v);
                    let row = seq![Type::Bool] + slot_tys(sv, cx.enums@);
                    let lt = blt(*blk, *cx);
                    lemma_all_pure_mono(ms@, b1.depth_s(), blk.depth_s());
                    lemma_typed_blk(ms@, xetys(xty(tm), cx.enums@), *cx, b1, *blk);
                    lemma_map_rows_typed(ms@, rows_view(rows@), sty(k), sv, tv, lt);
                    lemma_defaults_typed(sv, tv, lt);
                    assert(etys(row) =~= seq![ETy::Bool] + etys(slot_tys(sv, cx.enums@)));
                    assert forall|j: int| 0 <= j < alt@.len() implies #[trigger] has_ty(alt@[j], tv, lt, etys(row)[j]) by {
                        if j > 0 {
                            assert(alt@[j] == dv@[j - 1]);
                        }
                    }
                    lemma_ite_rows_typed(rows_view(out@), rows_view(rows@), r, alt@, etys(row), tv, lt);
                    lemma_flat_typed(rows_view(out@), row, tv, lt);
                    let mt = STy::Map(Box::new(sty(k)), Box::new(sv));
                    lemma_xetys_of(mt, cx.enums@);
                    assert(xty(tm) == to_xty(mt));
                    assert(slot_tys(mt, cx.enums@) == crate::lower_types::ty_repeat(row, keys_or_zero(sty(k), cx.enums@)));
                }
            }
            proof {
                lemma_delete(*e, *cx, sc@, b0, b1, *blk, sty(v), ms@, rows_view(rows@), r, alt@, rows_view(out@), res@);
            }
            Ok((tm, res))
        },
        _ => Err(Fail::Type),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub(crate) fn low_keys(e: &TExpr, cx: &LowerCtx, sc: &mut Vec<Bound>, blk: &mut Block) -> (r: Result<(XType, Vec<Expr>), Fail>)
    requires
        old(blk).wf(),
        e is Keys,
    ensures
        low_ok(*e, *cx, old(sc)@, final(sc)@, *old(blk), *final(blk), r),
    decreases e, 0nat,
{
    let enums = &cx.enums;
    let ghost pre = tpre(*e, *cx, old(sc)@, old(blk).depth_s());
    let ghost c = sctx(*cx);
    let ghost bt = bound_tys(old(sc)@);
    let ghost sc0 = sc@;
    let ghost tp = pre && tok(*cx, old(sc)@, *old(blk));
    let ghost tv = lenv(*cx);
    match e {
        TExpr::Keys(a) => {
            let ghost b0 = *blk;
            proof {
                if pre {
                    assert(lim_ok(**a, c, bt));
                }
            }
            let (tm, ms) = low(a, cx, sc, blk)?;
            proof {
                if pre {
                    assert(here_ok(**a, c, bt));
                    lemma_sc_wf_mono(sc0, old(blk).depth_s(), blk.depth_s(), cx.enums@);
                }
                if tp {
                    lemma_tok_ext(*cx, sc0, *old(blk), *blk);
                }
            }
            let (k, v) = match tm {
                XType::Map(k, v) => (*k, *v),
                _ => return Err(Fail::Type),
            };
            proof {
                if pre {
                    lemma_ok_map(sty(k), sty(v), enums@);
                }
            }
            let rows = need(map_rows(&k, &v, &ms, enums))?;
            proof {
                if pre {
                    let w1 = (1 + width(sty(v), enums@)) as nat;
                    lemma_mrows_shape(ms@, rows_view(rows@), w1, keys_or_zero(sty(k), enums@), blk.depth_s());
                    assert forall|q: int| 0 <= q < rows@.len() implies (#[trigger] rows@[q])@.len() > 0 by {
                        assert(rows_view(rows@)[q] == rows@[q]@);
                    }
                }
            }
            let present = need(heads(&rows))?;
            proof {
                if pre {
                    lemma_heads_pure(present@, rows_view(rows@), blk.depth_s());
                }
                if tp {
                    lemma_map_rows_typed(ms@, rows_view(rows@), sty(k), sty(v), tv, blt(*blk, *cx));
                    lemma_bools_typed(present@, keys_or_zero(sty(k), cx.enums@), tv, blt(*blk, *cx));
                }
            }
            proof {
                lemma_keys(*e, *cx, sc@, b0, *blk, sty(k), sty(v), ms@, rows_view(rows@), present@);
            }
            Ok((XType::Set(Box::new(k)), present))
        },
        _ => Err(Fail::Type),
    }
}

} // verus!
