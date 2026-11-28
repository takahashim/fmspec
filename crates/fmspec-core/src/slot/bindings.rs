//! 評価の順に並べた束縛の列を、中核の `let` の入れ子にする。

#[cfg(verus_keep_ghost)]
use crate::kernel::eval::{eval_l, Env};
use crate::kernel::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::kernel::model::Value;
#[cfg(verus_keep_ghost)]
use crate::kernel::typing::{type_l, ETy, TyEnv};
#[cfg(verus_keep_ghost)]
use crate::slot::lower_types::{binds_typed, lemma_lts_at, lemma_lts_len, lemma_lts_prefix, lts};
#[cfg(verus_keep_ghost)]
use crate::slot::preserve::{eval_bindings, eval_bound_body};
use vstd::prelude::*;

verus! {

/// 束縛を順に評価してから本体を評価する式を返す。
pub fn wrap_bindings(bindings: Vec<Expr>, body: Expr) -> (out: Expr)
    ensures
        forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) == eval_bound_body(bindings@, bindings@.len(), body, env, locals),
        forall|t: TyEnv, outer: Seq<ETy>|
            #[trigger] binds_typed(outer, bindings@, t) ==> type_l(out, t, outer) == type_l(body, t, lts(outer, bindings@, t)),
{
    let ghost original = bindings@;
    let mut pending = bindings;
    let mut out = body;
    proof {
        assert(original.take(original.len() as int) =~= original);
    }
    while pending.len() > 0
        invariant
            pending@.len() <= original.len(),
            pending@ == original.take(pending@.len() as int),
            forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_bound_body(original, pending@.len(), out, env, locals)
                    == eval_bound_body(original, original.len(), body, env, locals),
            forall|t: TyEnv, outer: Seq<ETy>|
                #[trigger] binds_typed(outer, original, t) ==> type_l(out, t, lts(outer, original.take(pending@.len() as int), t))
                    == type_l(body, t, lts(outer, original, t)),
        decreases pending@.len(),
    {
        let ghost n = pending@.len();
        let ghost previous = out;
        let binding = pending.pop().unwrap();
        out = Expr::Let(Box::new(binding), Box::new(out));
        proof {
            assert(pending@ =~= original.take((n - 1) as int));
            assert forall|t: TyEnv, outer: Seq<ETy>|
                #[trigger] binds_typed(outer, original, t) implies type_l(out, t, lts(outer, original.take((n - 1) as int), t))
                    == type_l(body, t, lts(outer, original, t)) by {
                let i = (n - 1) as int;
                lemma_lts_at(outer, original, t, i);
                lemma_lts_prefix(outer, original, t, i + 1);
                lemma_lts_prefix(outer, original, t, i);
                let pre = lts(outer, original.take(i), t);
                let y = lts(outer, original, t)[outer.len() + i];
                lemma_lts_len(outer, original, t);
                lemma_lts_len(outer, original.take(i), t);
                lemma_lts_len(outer, original.take(i + 1), t);
                assert(type_l(binding, t, pre) == Some(y));
                assert(lts(outer, original.take(i + 1), t) =~= pre.push(y));
                assert(type_l(previous, t, lts(outer, original.take(n as int), t)) == type_l(body, t, lts(outer, original, t)));
            }
            assert forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_bound_body(original, pending@.len(), out, env, locals)
                    == eval_bound_body(original, original.len(), body, env, locals) by {
                assert(eval_bound_body(original, n, previous, env, locals)
                    == eval_bound_body(original, original.len(), body, env, locals));
                reveal_with_fuel(eval_bindings, 2);
                reveal_with_fuel(eval_l, 2);
            }
        }
    }
    proof {
        assert forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) == eval_bound_body(original, original.len(), body, env, locals) by {
            assert(eval_bound_body(original, 0, out, env, locals) == eval_l(out, env, locals));
        }
        assert(original.take(0) =~= Seq::<Expr>::empty());
        assert(original.take(original.len() as int) =~= original);
    }
    out
}

} // verus!
