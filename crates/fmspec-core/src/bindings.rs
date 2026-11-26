//! 評価の順に並べた束縛の列を、中核の `let` の入れ子にする。

#[cfg(verus_keep_ghost)]
use crate::eval::{eval_l, Env, ErrKind};
use crate::model::Expr;
#[cfg(verus_keep_ghost)]
use crate::model::Value;
use vstd::prelude::*;

verus! {

/// 束縛の列を先頭から評価する。最初のエラーで止まる。
pub open spec fn eval_bindings(
    bindings: Seq<Expr>,
    n: nat,
    env: Env,
    locals: Seq<Value>,
) -> Result<Seq<Value>, ErrKind>
    recommends n <= bindings.len(),
    decreases n,
{
    if n == 0 {
        Ok(locals)
    } else {
        match eval_bindings(bindings, (n - 1) as nat, env, locals) {
            Err(error) => Err(error),
            Ok(prefix) => match eval_l(bindings[n - 1], env, prefix) {
                Err(error) => Err(error),
                Ok(value) => Ok(prefix.push(value)),
            },
        }
    }
}

pub open spec fn eval_bound_body(
    bindings: Seq<Expr>,
    n: nat,
    body: Expr,
    env: Env,
    locals: Seq<Value>,
) -> Result<Value, ErrKind> {
    match eval_bindings(bindings, n, env, locals) {
        Err(error) => Err(error),
        Ok(final_locals) => eval_l(body, env, final_locals),
    }
}

/// 束縛を順に評価してから本体を評価する式を返す。
pub fn wrap_bindings(bindings: Vec<Expr>, body: Expr) -> (out: Expr)
    ensures
        forall|env: Env, locals: Seq<Value>|
            #[trigger] eval_l(out, env, locals) == eval_bound_body(bindings@, bindings@.len(), body, env, locals),
{
    let ghost original = bindings@;
    let mut pending = bindings;
    let mut out = body;
    while pending.len() > 0
        invariant
            pending@.len() <= original.len(),
            pending@ == original.take(pending@.len() as int),
            forall|env: Env, locals: Seq<Value>|
                #[trigger] eval_bound_body(original, pending@.len(), out, env, locals)
                    == eval_bound_body(original, original.len(), body, env, locals),
        decreases pending@.len(),
    {
        let ghost n = pending@.len();
        let ghost previous = out;
        let binding = pending.pop().unwrap();
        out = Expr::Let(Box::new(binding), Box::new(out));
        proof {
            assert(pending@ =~= original.take((n - 1) as int));
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
    }
    out
}

} // verus!
