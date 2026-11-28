//! 未検証コード（探索器、直列化、テスト）が使う、標準トレイトの実装。
//!
//! Verus は再帰的な型や `Vec` を持つ型の `derive` に仕様を付けられないので、
//! `verus!` の外に手で書く。ここにあるコードは証明の対象ではなく、判定の経路からも呼ばれない。

use crate::evidence::{Certificate, Claim, Evidence, RefClaim, RefEvidence, TraceStep};
use crate::gate::Verdict;
use crate::model::{Action, Contract, Expr, Output, RawModel, Update};
use crate::refine::RefVerdict;
use crate::semantics::Conditions;
use crate::step::{Enumerated, Transition};
use core::fmt;

impl Clone for Expr {
    fn clone(&self) -> Self {
        crate::expr_copy::copy_expr(self)
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        use Expr::*;
        match (self, other) {
            (Const(a), Const(b)) => a == b,
            (Var(a), Var(b)) | (Arg(a), Arg(b)) | (Next(a), Next(b)) | (Local(a), Local(b)) => a == b,
            (Out, Out) => true,
            (Bin(o, a, b), Bin(p, c, d)) => o == p && a == c && b == d,
            (Not(a), Not(b)) | (Code(a), Code(b)) => a == b,
            (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Implies(a, b), Implies(c, d)) | (Let(a, b), Let(c, d)) => {
                a == c && b == d
            }
            (Ite(a, b, c), Ite(d, e, f)) => a == d && b == e && c == f,
            (Forall(t, l, h, a), Forall(u, m, i, b)) | (Exists(t, l, h, a), Exists(u, m, i, b)) => {
                t == u && l == m && h == i && a == b
            }
            (Fail(t, k), Fail(u, l)) => t == u && k == l,
            _ => false,
        }
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Expr::*;
        match self {
            Const(v) => write!(f, "Const({v:?})"),
            Var(i) => write!(f, "Var({i})"),
            Arg(i) => write!(f, "Arg({i})"),
            Next(i) => write!(f, "Next({i})"),
            Out => write!(f, "Out"),
            Bin(o, a, b) => write!(f, "Bin({o:?}, {a:?}, {b:?})"),
            Not(a) => write!(f, "Not({a:?})"),
            And(a, b) => write!(f, "And({a:?}, {b:?})"),
            Or(a, b) => write!(f, "Or({a:?}, {b:?})"),
            Implies(a, b) => write!(f, "Implies({a:?}, {b:?})"),
            Ite(c, a, b) => write!(f, "Ite({c:?}, {a:?}, {b:?})"),
            Local(i) => write!(f, "Local({i})"),
            Let(a, b) => write!(f, "Let({a:?}, {b:?})"),
            Forall(t, l, h, a) => write!(f, "Forall({t:?}, {l}, {h}, {a:?})"),
            Exists(t, l, h, a) => write!(f, "Exists({t:?}, {l}, {h}, {a:?})"),
            Code(a) => write!(f, "Code({a:?})"),
            Fail(t, k) => write!(f, "Fail({t:?}, {k})"),
        }
    }
}

impl Clone for Update {
    fn clone(&self) -> Self {
        Update {
            target: self.target,
            expr: self.expr.clone(),
        }
    }
}

impl Clone for Output {
    fn clone(&self) -> Self {
        Output {
            ty: self.ty,
            expr: self.expr.clone(),
        }
    }
}

impl Clone for Action {
    fn clone(&self) -> Self {
        Action {
            n_params: self.n_params,
            domains: self.domains.clone(),
            guard: self.guard.clone(),
            updates: self.updates.clone(),
            output: self.output.clone(),
        }
    }
}

impl Clone for Contract {
    fn clone(&self) -> Self {
        Contract {
            action: self.action,
            expr: self.expr.clone(),
        }
    }
}

impl Clone for RawModel {
    fn clone(&self) -> Self {
        RawModel {
            enums: self.enums.clone(),
            state_types: self.state_types.clone(),
            inits: self.inits.clone(),
            actions: self.actions.clone(),
            invariants: self.invariants.clone(),
            contracts: self.contracts.clone(),
            terminal: self.terminal.clone(),
        }
    }
}

impl Clone for Conditions {
    fn clone(&self) -> Self {
        Conditions {
            actions: self.actions.clone(),
            invariants: self.invariants.clone(),
            contracts: self.contracts.clone(),
            deadlock: self.deadlock,
        }
    }
}

impl PartialEq for Conditions {
    fn eq(&self, other: &Self) -> bool {
        self.actions == other.actions
            && self.invariants == other.invariants
            && self.contracts == other.contracts
            && self.deadlock == other.deadlock
    }
}

impl fmt::Debug for Conditions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Conditions")
            .field("actions", &self.actions)
            .field("invariants", &self.invariants)
            .field("contracts", &self.contracts)
            .field("deadlock", &self.deadlock)
            .finish()
    }
}

impl Clone for Transition {
    fn clone(&self) -> Self {
        Transition {
            args: self.args.clone(),
            output: self.output,
            state: self.state.clone(),
        }
    }
}

impl fmt::Debug for Transition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Transition")
            .field("args", &self.args)
            .field("output", &self.output)
            .field("state", &self.state)
            .finish()
    }
}

impl fmt::Debug for Enumerated {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Enumerated::Ok(ts) => f.debug_tuple("Ok").field(ts).finish(),
            Enumerated::Fail(args, site, kind) => f.debug_tuple("Fail").field(args).field(site).field(kind).finish(),
        }
    }
}

impl Clone for TraceStep {
    fn clone(&self) -> Self {
        TraceStep {
            action: self.action,
            args: self.args.clone(),
            output: self.output,
            state: self.state.clone(),
        }
    }
}

impl PartialEq for TraceStep {
    fn eq(&self, other: &Self) -> bool {
        self.action == other.action
            && self.args == other.args
            && self.output == other.output
            && self.state == other.state
    }
}

impl fmt::Debug for TraceStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TraceStep")
            .field("action", &self.action)
            .field("args", &self.args)
            .field("output", &self.output)
            .field("state", &self.state)
            .finish()
    }
}

impl Clone for Claim {
    fn clone(&self) -> Self {
        match self {
            Claim::Invariant(i) => Claim::Invariant(*i),
            Claim::Contract(k) => Claim::Contract(*k),
            Claim::Deadlock => Claim::Deadlock,
            Claim::InvariantError(i, e) => Claim::InvariantError(*i, *e),
            Claim::ContractError(k, e) => Claim::ContractError(*k, *e),
            Claim::TerminalError(e) => Claim::TerminalError(*e),
            Claim::StepError(a, args, site, e) => Claim::StepError(*a, args.clone(), *site, *e),
        }
    }
}

impl PartialEq for Claim {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Claim::Invariant(a), Claim::Invariant(b)) => a == b,
            (Claim::Contract(a), Claim::Contract(b)) => a == b,
            (Claim::Deadlock, Claim::Deadlock) => true,
            (Claim::InvariantError(a, e), Claim::InvariantError(b, f)) => a == b && e == f,
            (Claim::ContractError(a, e), Claim::ContractError(b, f)) => a == b && e == f,
            (Claim::TerminalError(e), Claim::TerminalError(f)) => e == f,
            (Claim::StepError(a, x, s, e), Claim::StepError(b, y, t, f)) => a == b && x == y && s == t && e == f,
            _ => false,
        }
    }
}

impl fmt::Debug for Claim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Claim::Invariant(i) => f.debug_tuple("Invariant").field(i).finish(),
            Claim::Contract(k) => f.debug_tuple("Contract").field(k).finish(),
            Claim::Deadlock => f.write_str("Deadlock"),
            Claim::InvariantError(i, e) => f.debug_tuple("InvariantError").field(i).field(e).finish(),
            Claim::ContractError(k, e) => f.debug_tuple("ContractError").field(k).field(e).finish(),
            Claim::TerminalError(e) => f.debug_tuple("TerminalError").field(e).finish(),
            Claim::StepError(a, args, site, e) => f
                .debug_tuple("StepError")
                .field(a)
                .field(args)
                .field(site)
                .field(e)
                .finish(),
        }
    }
}

impl Clone for Certificate {
    fn clone(&self) -> Self {
        Certificate {
            conditions: self.conditions.clone(),
            states: self.states.clone(),
        }
    }
}

impl fmt::Debug for Certificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Certificate")
            .field("conditions", &self.conditions)
            .field("states", &self.states)
            .finish()
    }
}

impl Clone for Evidence {
    fn clone(&self) -> Self {
        match self {
            Evidence::Certificate(c) => Evidence::Certificate(c.clone()),
            Evidence::Trace(start, steps, claim) => Evidence::Trace(start.clone(), steps.clone(), claim.clone()),
            Evidence::Unavailable(limit) => Evidence::Unavailable(*limit),
        }
    }
}

impl fmt::Debug for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Evidence::Certificate(c) => f.debug_tuple("Certificate").field(c).finish(),
            Evidence::Trace(start, steps, claim) => {
                f.debug_tuple("Trace").field(start).field(steps).field(claim).finish()
            }
            Evidence::Unavailable(limit) => f.debug_tuple("Unavailable").field(limit).finish(),
        }
    }
}

impl fmt::Debug for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Verdict")
            .field("kind", &self.kind())
            .field("reject", &self.reject())
            .field("invalid", &self.invalid())
            .field("limit", &self.limit())
            .finish()
    }
}

impl Clone for RefClaim {
    fn clone(&self) -> Self {
        match self {
            RefClaim::Init => RefClaim::Init,
            RefClaim::Step => RefClaim::Step,
            RefClaim::Map(slot, e) => RefClaim::Map(*slot, *e),
            RefClaim::Model(c) => RefClaim::Model(c.clone()),
        }
    }
}

impl PartialEq for RefClaim {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RefClaim::Init, RefClaim::Init) => true,
            (RefClaim::Step, RefClaim::Step) => true,
            (RefClaim::Map(a, e), RefClaim::Map(b, f)) => a == b && e == f,
            (RefClaim::Model(a), RefClaim::Model(b)) => a == b,
            _ => false,
        }
    }
}

impl fmt::Debug for RefClaim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefClaim::Init => f.write_str("Init"),
            RefClaim::Step => f.write_str("Step"),
            RefClaim::Map(slot, e) => f.debug_tuple("Map").field(slot).field(e).finish(),
            RefClaim::Model(c) => f.debug_tuple("Model").field(c).finish(),
        }
    }
}

impl Clone for RefEvidence {
    fn clone(&self) -> Self {
        match self {
            RefEvidence::Certificate(c) => RefEvidence::Certificate(c.clone()),
            RefEvidence::Trace(start, steps, claim) => RefEvidence::Trace(start.clone(), steps.clone(), claim.clone()),
            RefEvidence::Unavailable(limit) => RefEvidence::Unavailable(*limit),
        }
    }
}

impl fmt::Debug for RefEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefEvidence::Certificate(c) => f.debug_tuple("Certificate").field(c).finish(),
            RefEvidence::Trace(start, steps, claim) => {
                f.debug_tuple("Trace").field(start).field(steps).field(claim).finish()
            }
            RefEvidence::Unavailable(limit) => f.debug_tuple("Unavailable").field(limit).finish(),
        }
    }
}

impl fmt::Debug for RefVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RefVerdict")
            .field("kind", &self.kind())
            .field("reject", &self.reject())
            .field("limit", &self.limit())
            .finish()
    }
}
