//! 型の既定値の符号の列。

#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
use crate::value::encoding::SType;
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{codes, default_val, default_vals, enc, enc_items, enc_repeat, enc_rows, enc_seq};
#[cfg(verus_keep_ghost)]
use crate::value::encoding::{lemma_codes_concat, lemma_default_vals_len, lemma_stys, sty, stys, STy, SVal};
use crate::value::stype_exec::keys_or_zero_exec;
use vstd::prelude::*;

verus! {

/// 型 `t` の既定値の符号の列。
pub fn default_codes(t: &SType, enums: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        r@ == codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)),
    decreases t, 1nat,
{
    let mut out: Vec<i64> = Vec::new();
    match t {
        SType::Bool => {
            out.push(0);
            proof {
                assert(out@ =~= codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Int(lo, _) => {
            out.push(*lo);
            proof {
                assert(out@ =~= codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Enum(_) => {
            out.push(0);
            proof {
                assert(out@ =~= codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Tuple(ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = default_codes_seq(t, ts, enums);
        },
        SType::Record(_, ts) => {
            proof {
                assert(decreases_to!(*t => *ts));
            }
            out = default_codes_seq(t, ts, enums);
        },
        SType::Option(x) => {
            out.push(0);
            let d = default_codes(x, enums);
            append(&mut out, &d);
            proof {
                let dv = enc(default_val(sty(**x), enums@), sty(**x), enums@);
                lemma_codes_concat(seq![Value::Bool(false)], dv);
                assert(out@ =~= codes(seq![Value::Bool(false)] + dv));
            }
        },
        SType::Set(e) => {
            let n = keys_or_zero_exec(e, enums);
            let mut i = 0;
            while i < n
                invariant
                    i <= n,
                    out@ == Seq::new(i as nat, |_j: int| 0i64),
                decreases n - i,
            {
                out.push(0);
                proof {
                    assert(out@ =~= Seq::new((i + 1) as nat, |_j: int| 0i64));
                }
                i += 1;
            }
            proof {
                assert(out@ =~= codes(enc(default_val(sty(*t), enums@), sty(*t), enums@)));
            }
        },
        SType::Map(k, v) => {
            let n = keys_or_zero_exec(k, enums);
            let d = default_codes(v, enums);
            let ghost dv = enc(default_val(sty(**v), enums@), sty(**v), enums@);
            let mut i = 0;
            proof {
                assert(enc_rows(Seq::new(0, |_j: int| None::<SVal>), sty(**v), enums@) =~= Seq::<Value>::empty());
                assert(out@ =~= codes(Seq::<Value>::empty()));
            }
            while i < n
                invariant
                    i <= n,
                    d@ == codes(dv),
                    dv == enc(default_val(sty(**v), enums@), sty(**v), enums@),
                    out@ == codes(enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@)),
                decreases n - i,
            {
                let ghost before = out@;
                out.push(0);
                append(&mut out, &d);
                proof {
                    let rows = Seq::new((i + 1) as nat, |_j: int| None::<SVal>);
                    assert(rows.drop_last() =~= Seq::new(i as nat, |_j: int| None::<SVal>));
                    let prev = enc_rows(Seq::new(i as nat, |_j: int| None::<SVal>), sty(**v), enums@);
                    assert(enc_rows(rows, sty(**v), enums@) == prev + (seq![Value::Bool(false)] + dv));
                    lemma_codes_concat(prev, seq![Value::Bool(false)] + dv);
                    lemma_codes_concat(seq![Value::Bool(false)], dv);
                    assert(out@ =~= codes(prev + (seq![Value::Bool(false)] + dv)));
                }
                i += 1;
            }
            proof {
                let rows = default_val(sty(*t), enums@)->Map_0;
                assert(rows =~= Seq::new(n as nat, |_j: int| None::<SVal>));
            }
        },
        SType::List(e, max) => {
            out.push(0);
            let d = default_codes(e, enums);
            let ghost dv = enc(default_val(sty(**e), enums@), sty(**e), enums@);
            let mut i = 0;
            proof {
                assert(out@ =~= codes(seq![Value::Int(0)] + enc_repeat(dv, 0)));
            }
            while i < *max
                invariant
                    i <= *max,
                    d@ == codes(dv),
                    dv == enc(default_val(sty(**e), enums@), sty(**e), enums@),
                    out@ == codes(seq![Value::Int(0)] + enc_repeat(dv, i as nat)),
                decreases *max - i,
            {
                append(&mut out, &d);
                proof {
                    assert(enc_repeat(dv, (i + 1) as nat) == enc_repeat(dv, i as nat) + dv);
                    lemma_codes_concat(seq![Value::Int(0)] + enc_repeat(dv, i as nat), dv);
                    assert(seq![Value::Int(0)] + enc_repeat(dv, (i + 1) as nat) =~= (seq![Value::Int(0)]
                        + enc_repeat(dv, i as nat)) + dv);
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

fn default_codes_seq(_parent: &SType, ts: &Vec<SType>, enums: &Vec<i64>) -> (r: Vec<i64>)
    requires
        decreases_to!(*_parent => *ts),
    ensures
        r@ == codes(enc_seq(default_vals(stys(ts@), enums@), stys(ts@), enums@)),
    decreases _parent, 0nat,
{
    let mut out: Vec<i64> = Vec::new();
    let ghost all = stys(ts@);
    proof {
        lemma_stys(ts@);
        assert(all.take(0) =~= Seq::<STy>::empty());
        assert(out@ =~= codes(enc_seq(default_vals(all.take(0), enums@), all.take(0), enums@)));
    }
    let mut i = 0;
    while i < ts.len()
        invariant
            decreases_to!(*_parent => *ts),
            i <= ts.len(),
            all == stys(ts@),
            all.len() == ts@.len(),
            forall|j: int| 0 <= j < ts@.len() ==> #[trigger] all[j] == sty(ts@[j]),
            out@ == codes(enc_seq(default_vals(all.take(i as int), enums@), all.take(i as int), enums@)),
        decreases ts.len() - i,
    {
        proof {
            vstd::std_specs::vec::axiom_vec_index_decreases(*ts, i as int);
        }
        let d = default_codes(&ts[i], enums);
        let ghost before = out@;
        append(&mut out, &d);
        proof {
            let pre = all.take(i as int);
            let nx = all.take(i + 1);
            assert(nx.drop_last() =~= pre);
            assert(nx.last() == all[i as int]);
            lemma_default_vals_len(nx, enums@);
            let dv = default_vals(nx, enums@);
            assert(dv.drop_last() == default_vals(pre, enums@));
            assert(dv.last() == default_val(all[i as int], enums@));
            let a = enc_seq(default_vals(pre, enums@), pre, enums@);
            let b = enc(default_val(all[i as int], enums@), all[i as int], enums@);
            assert(enc_seq(dv, nx, enums@) == a + b);
            lemma_codes_concat(a, b);
        }
        i += 1;
    }
    proof {
        assert(all.take(i as int) =~= all);
    }
    out
}

/// `out` の後ろに `xs` を加える。
pub fn append(out: &mut Vec<i64>, xs: &Vec<i64>)
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
        out.push(xs[i]);
        proof {
            assert(xs@.take(i + 1) =~= xs@.take(i as int).push(xs@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(xs@.take(xs@.len() as int) =~= xs@);
    }
}

} // verus!
