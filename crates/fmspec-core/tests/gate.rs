//! IR検証と判定ゲートの頑健性。不正なモデルや不正な証拠を直接渡しても、panicせずに
//! `InvalidModel` または拒否を返す（仕様書 §17.1）。

use fmspec_core::eval::ErrKind;
use fmspec_core::evidence::{Certificate, Claim, Evidence, Limit, Reject, TraceStep};
use fmspec_core::gate::{decide, decide_raw, validate, CertCheck, CheckedModel, VerdictKind, VerdictOutcome};
use fmspec_core::model::{Action, BinOp, Contract, Expr, Output, RawModel, Type, Update, Value};
use fmspec_core::semantics::Conditions;
use fmspec_core::step::{Enumerated, Site, StepR};
use fmspec_core::typing::InvalidModel;

fn int(x: i64) -> Expr {
    Expr::Const(Value::Int(x))
}

fn bin(op: BinOp, a: Expr, b: Expr) -> Expr {
    Expr::Bin(op, Box::new(a), Box::new(b))
}

/// `x`（0..=3、初期値0）を、3未満のときに引数 `d`（1..=2）だけ増やすモデル。
/// 不変条件は `x <= 3`、出力は増やした後の値、契約は「出力は遷移後の `x` に等しい」。
fn base() -> RawModel {
    RawModel {
        enums: vec![2],
        state_types: vec![Type::Int(0, 3)],
        inits: vec![vec![0]],
        actions: vec![Action {
            n_params: 1,
            domains: vec![Type::Int(1, 2)],
            guard: bin(BinOp::Le, bin(BinOp::Add, Expr::Var(0), Expr::Arg(0)), int(3)),
            updates: vec![Update {
                target: 0,
                expr: bin(BinOp::Add, Expr::Var(0), Expr::Arg(0)),
            }],
            output: Some(Output {
                ty: Type::Int(0, 3),
                expr: bin(BinOp::Add, Expr::Var(0), Expr::Arg(0)),
            }),
        }],
        invariants: vec![bin(BinOp::Le, Expr::Var(0), int(3))],
        contracts: vec![Contract {
            action: 0,
            expr: bin(BinOp::Eq, Expr::Out, Expr::Next(0)),
        }],
        terminal: Some(bin(BinOp::Eq, Expr::Var(0), int(3))),
    }
}

fn checked() -> CheckedModel {
    validate(base()).expect("整形式のモデル")
}

fn all(deadlock: bool) -> Conditions {
    Conditions {
        actions: vec![true],
        invariants: vec![true],
        contracts: vec![true],
        deadlock,
    }
}

fn invalid(change: impl FnOnce(&mut RawModel)) -> InvalidModel {
    let mut raw = base();
    change(&mut raw);
    let reason = validate(raw.clone()).err().expect("拒否されるはずのモデル");
    // 検証を経ずに判定ゲートへ渡しても、同じ理由で InvalidModel になる。
    let cert = Evidence::Certificate(Certificate {
        conditions: all(false),
        states: vec![vec![0]],
    });
    let v = decide_raw(&raw, &all(false), &cert);
    assert_eq!((v.kind(), v.invalid()), (VerdictKind::InvalidModel, Some(reason)));
    reason
}

#[test]
fn validation_rejects_ill_formed_models() {
    assert_eq!(invalid(|m| m.enums[0] = 0), InvalidModel::EmptyEnum(0));
    assert_eq!(
        invalid(|m| m.state_types[0] = Type::Int(3, 0)),
        InvalidModel::StateType(0)
    );
    assert_eq!(
        invalid(|m| m.state_types[0] = Type::Enum(1)),
        InvalidModel::StateType(0)
    );
    assert_eq!(invalid(|m| m.inits[0][0] = 4), InvalidModel::Initial(0));
    assert_eq!(invalid(|m| m.inits[0].push(0)), InvalidModel::Initial(0));
    assert_eq!(invalid(|m| m.inits.push(vec![5])), InvalidModel::Initial(1));
    assert_eq!(invalid(|m| m.inits.clear()), InvalidModel::NoInitial);
    assert_eq!(invalid(|m| m.state_types.clear()), InvalidModel::Initial(0));
    assert_eq!(invalid(|m| m.actions[0].n_params = 2), InvalidModel::Params(0));
    assert_eq!(
        invalid(|m| m.actions[0].domains[0] = Type::Int(2, 1)),
        InvalidModel::Domain(0, 0)
    );
    assert_eq!(invalid(|m| m.actions[0].guard = int(1)), InvalidModel::Guard(0));
    assert_eq!(
        invalid(|m| m.actions[0].guard = bin(BinOp::Eq, Expr::Arg(1), int(1))),
        InvalidModel::Guard(0)
    );
    assert_eq!(
        invalid(|m| m.actions[0].guard = bin(BinOp::Eq, Expr::Next(0), int(1))),
        InvalidModel::Guard(0)
    );
    assert_eq!(
        invalid(|m| m.actions[0].updates[0].target = 1),
        InvalidModel::Update(0, 0)
    );
    assert_eq!(
        invalid(|m| m.actions[0].updates[0].expr = Expr::Const(Value::Bool(true))),
        InvalidModel::Update(0, 0)
    );
    assert_eq!(
        invalid(|m| m.actions[0].updates.push(Update {
            target: 0,
            expr: int(1)
        })),
        InvalidModel::DuplicateUpdate(0, 1)
    );
    assert_eq!(
        invalid(|m| m.actions[0].output.as_mut().unwrap().ty = Type::Bool),
        InvalidModel::Output(0)
    );
    assert_eq!(invalid(|m| m.invariants[0] = Expr::Var(0)), InvalidModel::Invariant(0));
    assert_eq!(
        invalid(|m| m.invariants[0] = bin(BinOp::Eq, Expr::Var(1), int(0))),
        InvalidModel::Invariant(0)
    );
    assert_eq!(
        invalid(|m| m.invariants[0] = bin(BinOp::Eq, Expr::Arg(0), int(0))),
        InvalidModel::Invariant(0)
    );
    assert_eq!(
        invalid(|m| m.invariants[0] = bin(
            BinOp::Eq,
            Expr::Const(Value::Enum(0, 2)),
            Expr::Const(Value::Enum(0, 0))
        )),
        InvalidModel::Invariant(0)
    );
    assert_eq!(invalid(|m| m.contracts[0].action = 1), InvalidModel::Contract(0));
    assert_eq!(invalid(|m| m.terminal = Some(Expr::Out)), InvalidModel::Terminal);
    // 出力を宣言しない操作の契約は、出力を参照できない。
    assert_eq!(invalid(|m| m.actions[0].output = None), InvalidModel::Contract(0));
    // すべての枝を型検査する。評価されない枝の型エラーも拒否する。
    let dead_branch = Expr::Ite(
        Box::new(Expr::Const(Value::Bool(true))),
        Box::new(Expr::Const(Value::Bool(true))),
        Box::new(int(1)),
    );
    assert_eq!(invalid(|m| m.invariants[0] = dead_branch), InvalidModel::Invariant(0));
}

fn decide_cert(states: Vec<Vec<i64>>) -> (VerdictKind, Option<Reject>) {
    let m = checked();
    let cert = Evidence::Certificate(Certificate {
        conditions: all(true),
        states,
    });
    let v = decide(&m, &all(true), &cert);
    (v.kind(), v.reject())
}

#[test]
fn certificates() {
    let full = vec![vec![0], vec![1], vec![2], vec![3]];
    assert_eq!(decide_cert(full.clone()), (VerdictKind::Verified, None));
    assert_eq!(
        decide_cert(vec![]),
        (VerdictKind::Rejected, Some(Reject::MissingInitial(0)))
    );
    assert_eq!(
        decide_cert(vec![vec![0], vec![1], vec![2]]),
        (VerdictKind::Rejected, Some(Reject::MissingSuccessor(1, 0)))
    );
    // 整列されていない証明書は、所属の判定に失敗して拒否されるだけで、誤って受理されることはない。
    let (kind, _) = decide_cert(vec![vec![3], vec![2], vec![1], vec![0]]);
    assert_eq!(kind, VerdictKind::Rejected);
    // 状態型に従わない状態、長さの違う状態。
    assert_eq!(
        decide_cert(vec![vec![0], vec![1], vec![2], vec![3], vec![4]]).1,
        Some(Reject::IllTypedState(4))
    );
    assert_eq!(
        decide_cert(vec![vec![], vec![0], vec![1], vec![2], vec![3]]).1,
        Some(Reject::IllTypedState(0))
    );
    assert_eq!(
        decide_cert(vec![vec![0], vec![0, 0], vec![1], vec![2], vec![3]]).1,
        Some(Reject::IllTypedState(1))
    );
    // 重複した状態は、健全性に影響しない。
    assert_eq!(
        decide_cert(vec![vec![0], vec![1], vec![1], vec![2], vec![3]]).0,
        VerdictKind::Verified
    );
}

#[test]
fn certificates_are_checked_against_every_property() {
    // 不変条件 x <= 2 に変えると、状態3で成立しない。
    let mut raw = base();
    raw.invariants[0] = bin(BinOp::Le, Expr::Var(0), int(2));
    let m = validate(raw).unwrap();
    let full = Certificate {
        conditions: all(false),
        states: vec![vec![0], vec![1], vec![2], vec![3]],
    };
    let v = decide(&m, &all(false), &Evidence::Certificate(full.clone()));
    assert_eq!(v.reject(), Some(Reject::InvariantNotHeld(3, 0)));
    // その不変条件を対象から外した検査条件では受理する。証明書の検査条件も同じでなければならない。
    let relaxed = Conditions {
        invariants: vec![false],
        ..all(false)
    };
    let v = decide(&m, &relaxed, &Evidence::Certificate(full.clone()));
    assert_eq!(v.reject(), Some(Reject::ConditionMismatch));
    let v = decide(
        &m,
        &relaxed,
        &Evidence::Certificate(Certificate {
            conditions: relaxed.clone(),
            ..full
        }),
    );
    assert_eq!(v.kind(), VerdictKind::Verified);

    // 終端条件を外すと、状態3は非終端のデッドロックになる。
    let mut raw = base();
    raw.terminal = None;
    let m = validate(raw).unwrap();
    let full = Certificate {
        conditions: all(true),
        states: vec![vec![0], vec![1], vec![2], vec![3]],
    };
    assert_eq!(
        decide(&m, &all(true), &Evidence::Certificate(full)).reject(),
        Some(Reject::Deadlock(3))
    );

    // 範囲外更新が起きる状態を含む証明書。
    let mut raw = base();
    raw.actions[0].guard = Expr::Const(Value::Bool(true));
    let m = validate(raw).unwrap();
    let full = Certificate {
        conditions: all(false),
        states: vec![vec![0], vec![1], vec![2], vec![3]],
    };
    assert_eq!(
        decide(&m, &all(false), &Evidence::Certificate(full)).reject(),
        Some(Reject::StepFailed(2, 0))
    );
}

fn step(d: i64, to: i64) -> TraceStep {
    TraceStep {
        action: 0,
        args: vec![d],
        output: Some(to),
        state: vec![to],
    }
}

fn decide_trace(steps: Vec<TraceStep>, claim: Claim) -> (VerdictKind, Option<Reject>) {
    let m = checked();
    let v = decide(&m, &all(true), &Evidence::Trace(vec![0], steps, claim));
    (v.kind(), v.reject())
}

#[test]
fn traces_must_match_the_model_step_by_step() {
    let rejected = |r| (VerdictKind::Rejected, Some(r));
    // 途中の状態が誤ったトレースは、末尾が正しくても拒否する。
    assert_eq!(
        decide_trace(vec![step(1, 2), step(1, 3)], Claim::Deadlock),
        rejected(Reject::StepMismatch(0))
    );
    // 出力が誤ったトレース。
    let wrong_output = TraceStep {
        action: 0,
        args: vec![1],
        output: Some(2),
        state: vec![1],
    };
    assert_eq!(
        decide_trace(vec![wrong_output], Claim::Deadlock),
        rejected(Reject::StepMismatch(0))
    );
    let no_output = TraceStep {
        action: 0,
        args: vec![1],
        output: None,
        state: vec![1],
    };
    assert_eq!(
        decide_trace(vec![no_output], Claim::Deadlock),
        rejected(Reject::StepMismatch(0))
    );
    // guard が偽の遷移。
    assert_eq!(
        decide_trace(vec![step(2, 2), step(2, 4)], Claim::Invariant(0)),
        rejected(Reject::StepMismatch(1))
    );
    // 未定義の操作、ドメイン外の引数、個数の合わない引数。
    let bad_action = TraceStep {
        action: 1,
        args: vec![1],
        output: Some(1),
        state: vec![1],
    };
    assert_eq!(
        decide_trace(vec![bad_action], Claim::Deadlock),
        rejected(Reject::BadStep(0))
    );
    assert_eq!(
        decide_trace(vec![step(3, 3)], Claim::Deadlock),
        rejected(Reject::BadStep(0))
    );
    let bad_arity = TraceStep {
        action: 0,
        args: vec![1, 1],
        output: Some(1),
        state: vec![1],
    };
    assert_eq!(
        decide_trace(vec![step(1, 1), bad_arity], Claim::Deadlock),
        rejected(Reject::BadStep(1))
    );
    let no_args = TraceStep {
        action: usize::MAX,
        args: vec![],
        output: None,
        state: vec![],
    };
    assert_eq!(
        decide_trace(vec![no_args], Claim::Deadlock),
        rejected(Reject::BadStep(0))
    );
}

#[test]
fn claims_must_hold_at_the_end_of_the_trace() {
    let rejected = (VerdictKind::Rejected, Some(Reject::ClaimNotReproduced));
    let to_three = || vec![step(2, 2), step(1, 3)];
    // 状態3は有効な遷移がないが、終端なのでデッドロックではない。
    assert_eq!(decide_trace(to_three(), Claim::Deadlock), rejected);
    // 成立している不変条件・契約の違反の主張、未定義の性質への主張。
    assert_eq!(decide_trace(to_three(), Claim::Invariant(0)), rejected);
    assert_eq!(decide_trace(to_three(), Claim::Invariant(1)), rejected);
    assert_eq!(decide_trace(to_three(), Claim::Invariant(usize::MAX)), rejected);
    assert_eq!(decide_trace(to_three(), Claim::Contract(0)), rejected);
    assert_eq!(decide_trace(to_three(), Claim::Contract(7)), rejected);
    // 遷移のないトレースに対する契約の主張。
    assert_eq!(decide_trace(vec![], Claim::Contract(0)), rejected);
    assert_eq!(
        decide_trace(vec![], Claim::ContractError(0, ErrKind::Overflow)),
        rejected
    );
    // 起きていない評価エラーの主張。
    assert_eq!(
        decide_trace(to_three(), Claim::InvariantError(0, ErrKind::Overflow)),
        rejected
    );
    assert_eq!(
        decide_trace(to_three(), Claim::TerminalError(ErrKind::Overflow)),
        rejected
    );
    let step_error = |a, args: Vec<i64>| Claim::StepError(a, args, Site::Update(0), ErrKind::OutOfRange(4));
    assert_eq!(decide_trace(to_three(), step_error(0, vec![1])), rejected);
    assert_eq!(decide_trace(to_three(), step_error(0, vec![9])), rejected);
    assert_eq!(decide_trace(to_three(), step_error(0, vec![])), rejected);
    assert_eq!(decide_trace(to_three(), step_error(5, vec![1])), rejected);
}

#[test]
fn accepted_traces() {
    // 終端条件を外したモデルでは、状態3はデッドロックである。
    let mut raw = base();
    raw.terminal = None;
    let m = validate(raw).unwrap();
    let steps = vec![step(2, 2), step(1, 3)];
    let v = decide(
        &m,
        &all(true),
        &Evidence::Trace(vec![0], steps.clone(), Claim::Deadlock),
    );
    assert_eq!(v.kind(), VerdictKind::Violated);
    // デッドロック検査が無効な検査条件では、デッドロックの主張を受理しない。
    let v = decide(
        &m,
        &all(false),
        &Evidence::Trace(vec![0], steps.clone(), Claim::Deadlock),
    );
    assert_eq!(v.reject(), Some(Reject::ClaimNotReproduced));
    // 対象外の操作を含むトレースは受理しない。
    let no_actions = Conditions {
        actions: vec![false],
        ..all(true)
    };
    let v = decide(&m, &no_actions, &Evidence::Trace(vec![0], steps, Claim::Deadlock));
    assert_eq!(v.reject(), Some(Reject::BadStep(0)));

    // guard を外したモデルでは、状態2から2を足す更新が範囲外になる。
    let mut raw = base();
    raw.actions[0].guard = Expr::Const(Value::Bool(true));
    let m = validate(raw).unwrap();
    let claim = |kind| Claim::StepError(0, vec![2], Site::Update(0), kind);
    let v = decide(
        &m,
        &all(false),
        &Evidence::Trace(vec![0], vec![step(2, 2)], claim(ErrKind::OutOfRange(4))),
    );
    assert_eq!(v.kind(), VerdictKind::Error);
    // 評価エラーの種類や箇所が違う主張は受理しない。
    let v = decide(
        &m,
        &all(false),
        &Evidence::Trace(vec![0], vec![step(2, 2)], claim(ErrKind::OutOfRange(5))),
    );
    assert_eq!(v.reject(), Some(Reject::ClaimNotReproduced));
    let v = decide(
        &m,
        &all(false),
        &Evidence::Trace(vec![0], vec![step(2, 2)], claim(ErrKind::Overflow)),
    );
    assert_eq!(v.reject(), Some(Reject::ClaimNotReproduced));
    let guard = Claim::StepError(0, vec![2], Site::Guard, ErrKind::OutOfRange(4));
    let v = decide(&m, &all(false), &Evidence::Trace(vec![0], vec![step(2, 2)], guard));
    assert_eq!(v.reject(), Some(Reject::ClaimNotReproduced));
}

#[test]
fn multiple_initial_states() {
    // 初期状態を 0 と 2 にしたモデル。
    let mut raw = base();
    raw.inits = vec![vec![0], vec![2]];
    raw.terminal = None;
    let m = validate(raw).unwrap();
    // 証明書は、初期状態をすべて含まなければならない。
    let cert = |states| {
        Evidence::Certificate(Certificate {
            conditions: all(false),
            states,
        })
    };
    assert_eq!(
        decide(&m, &all(false), &cert(vec![vec![0], vec![1], vec![2], vec![3]])).kind(),
        VerdictKind::Verified
    );
    assert_eq!(
        decide(&m, &all(false), &cert(vec![vec![0], vec![1], vec![3]])).reject(),
        Some(Reject::MissingInitial(1))
    );
    // トレースは、どの初期状態からでも始められる。初期状態でない状態からは始められない。
    let v = decide(
        &m,
        &all(true),
        &Evidence::Trace(vec![2], vec![step(1, 3)], Claim::Deadlock),
    );
    assert_eq!(v.kind(), VerdictKind::Violated);
    let v = decide(
        &m,
        &all(true),
        &Evidence::Trace(vec![1], vec![step(2, 3)], Claim::Deadlock),
    );
    assert_eq!(v.reject(), Some(Reject::BadStart));
    let v = decide(&m, &all(true), &Evidence::Trace(vec![3], vec![], Claim::Deadlock));
    assert_eq!(v.reject(), Some(Reject::BadStart));
    let v = decide(&m, &all(true), &Evidence::Trace(vec![], vec![], Claim::Deadlock));
    assert_eq!(v.reject(), Some(Reject::BadStart));
}

#[test]
fn unavailable_evidence_is_inconclusive() {
    let v = decide(&checked(), &all(false), &Evidence::Unavailable(Limit::MaxStates));
    assert_eq!(
        (v.kind(), v.limit()),
        (VerdictKind::Inconclusive, Some(Limit::MaxStates))
    );
}

#[test]
fn conditions_shorter_or_longer_than_the_model_are_tolerated() {
    let m = checked();
    // 列が短ければ、足りない添字は対象外として扱う。何も検査しないので、初期状態だけの証明書を受理する。
    let none = Conditions {
        actions: vec![],
        invariants: vec![],
        contracts: vec![],
        deadlock: false,
    };
    let cert = Evidence::Certificate(Certificate {
        conditions: none.clone(),
        states: vec![vec![0]],
    });
    assert_eq!(decide(&m, &none, &cert).kind(), VerdictKind::Verified);
    // 列が長くても panic しない。
    let long = Conditions {
        actions: vec![true; 5],
        invariants: vec![true; 5],
        contracts: vec![true; 5],
        deadlock: true,
    };
    let states = vec![vec![0], vec![1], vec![2], vec![3]];
    let cert = Evidence::Certificate(Certificate {
        conditions: long.clone(),
        states,
    });
    assert_eq!(decide(&m, &long, &cert).kind(), VerdictKind::Verified);
}

#[test]
fn certificate_conditions_are_compared_by_meaning() {
    let m = checked();
    let states = vec![vec![0], vec![1], vec![2], vec![3]];
    // 列より後ろは対象外なので、[true] と [true, false] は同じ検査条件である。
    // モデルにない添字（操作は1つ）も対象外なので、[true] と [true, true] も同じである。
    let padded = Conditions {
        actions: vec![true, true],
        invariants: vec![true, false],
        contracts: vec![true, false, false],
        deadlock: true,
    };
    let cert = Certificate {
        conditions: padded.clone(),
        states: states.clone(),
    };
    let v = decide(&m, &all(true), &Evidence::Certificate(cert.clone()));
    assert_eq!((v.kind(), v.reject()), (VerdictKind::Verified, None));
    let req = all(true);
    let mut chk = CertCheck::start(&m, &req, &cert).ok().expect("同じ検査条件の証明書");
    assert_eq!(chk.advance(usize::MAX).map(|v| v.kind()), Some(VerdictKind::Verified));
    // モデルにある添字で対象が違えば、拒否する。
    for other in [
        Conditions {
            invariants: vec![false],
            ..padded.clone()
        },
        Conditions {
            contracts: vec![],
            ..padded.clone()
        },
        Conditions {
            actions: vec![false, true],
            ..padded.clone()
        },
        Conditions {
            deadlock: false,
            ..padded.clone()
        },
    ] {
        let cert = Certificate {
            conditions: other,
            states: states.clone(),
        };
        assert_eq!(
            decide(&m, &all(true), &Evidence::Certificate(cert.clone())).reject(),
            Some(Reject::ConditionMismatch)
        );
        let v = CertCheck::start(&m, &all(true), &cert)
            .err()
            .expect("検査条件の違う証明書");
        assert_eq!(v.reject(), Some(Reject::ConditionMismatch));
    }
}

#[test]
fn every_verdict_carries_its_reason() {
    let m = checked();
    for limit in [
        Limit::MaxStates,
        Limit::Interrupted,
        Limit::CheckBudget,
        Limit::MaxDepth,
        Limit::MaxTime,
    ] {
        let v = decide(&m, &all(false), &Evidence::Unavailable(limit));
        assert_eq!(
            (v.kind(), v.limit(), v.reject(), v.invalid()),
            (VerdictKind::Inconclusive, Some(limit), None, None)
        );
        assert_eq!(v.outcome(), VerdictOutcome::Inconclusive(limit));
        let v = decide_raw(&base(), &all(false), &Evidence::Unavailable(limit));
        assert_eq!((v.kind(), v.limit()), (VerdictKind::Inconclusive, Some(limit)));
    }
    let v = decide(&m, &all(false), &Evidence::Trace(vec![], vec![], Claim::Deadlock));
    assert_eq!(
        (v.kind(), v.limit(), v.reject(), v.invalid()),
        (VerdictKind::Rejected, None, Some(Reject::BadStart), None)
    );
    assert_eq!(v.outcome(), VerdictOutcome::Rejected(Reject::BadStart));
    let cert = Evidence::Certificate(Certificate {
        conditions: all(false),
        states: vec![vec![0], vec![1], vec![2], vec![3]],
    });
    let v = decide(&m, &all(false), &cert);
    assert_eq!(
        (v.kind(), v.limit(), v.reject(), v.invalid()),
        (VerdictKind::Verified, None, None, None)
    );
    assert_eq!(v.outcome(), VerdictOutcome::Verified);
    let mut raw = base();
    raw.inits.clear();
    let v = decide_raw(&raw, &all(false), &Evidence::Unavailable(Limit::MaxStates));
    assert_eq!(
        (v.kind(), v.limit(), v.reject()),
        (VerdictKind::InvalidModel, None, None)
    );
    assert!(v.invalid().is_some());
    assert_eq!(v.outcome(), VerdictOutcome::InvalidModel(InvalidModel::NoInitial));
}

#[test]
fn cert_check_advances_in_chunks_and_records_why_it_stopped() {
    let m = checked();
    let c = all(true);
    let cert = Certificate {
        conditions: c.clone(),
        states: vec![vec![0], vec![1], vec![2], vec![3]],
    };
    let mut chk = CertCheck::start(&m, &c, &cert).ok().expect("初期状態を含む証明書");
    assert_eq!(chk.remaining(), 4);
    // 0個なら何も検査しない。区切りの途中では判定を返さない。
    assert!(chk.advance(0).is_none());
    assert_eq!(chk.remaining(), 4);
    assert!(chk.advance(3).is_none());
    assert_eq!(chk.remaining(), 1);
    let v = chk.advance(10).expect("検査し終えた");
    assert_eq!((v.kind(), v.reject(), v.limit()), (VerdictKind::Verified, None, None));

    // 打ち切った検査は Inconclusive で、渡した理由を記録する。
    for limit in [Limit::MaxTime, Limit::Interrupted, Limit::CheckBudget] {
        let mut chk = CertCheck::start(&m, &c, &cert).ok().unwrap();
        assert!(chk.advance(2).is_none());
        assert_eq!(chk.remaining(), 2);
        let v = chk.stop(limit);
        assert_eq!(
            (v.kind(), v.limit(), v.reject()),
            (VerdictKind::Inconclusive, Some(limit), None)
        );
    }

    // 区切って進めても、decide と同じ理由で拒否する。
    let short = Certificate {
        conditions: c.clone(),
        states: vec![vec![0], vec![1], vec![2]],
    };
    let mut chk = CertCheck::start(&m, &c, &short).ok().unwrap();
    assert!(chk.advance(1).is_none());
    let v = chk.advance(1).expect("状態1で拒否する");
    assert_eq!(
        (v.kind(), v.reject(), v.limit()),
        (VerdictKind::Rejected, Some(Reject::MissingSuccessor(1, 0)), None)
    );
    assert_eq!(
        decide(&m, &c, &Evidence::Certificate(short)).reject(),
        Some(Reject::MissingSuccessor(1, 0))
    );

    // 初期状態を含まない証明書は、始める時点で拒否する。
    let missing = Certificate {
        conditions: c.clone(),
        states: vec![vec![1]],
    };
    let v = CertCheck::start(&m, &c, &missing).err().expect("初期状態がない");
    assert_eq!(
        (v.kind(), v.reject()),
        (VerdictKind::Rejected, Some(Reject::MissingInitial(0)))
    );
}

#[test]
fn apply_returns_none_exactly_for_bad_input() {
    let m = checked();
    // 操作の添字が範囲外。
    assert!(m.apply(1, &vec![1], &vec![0]).is_none());
    assert!(m.apply(usize::MAX, &vec![1], &vec![0]).is_none());
    // 引数の長さが違う。
    assert!(m.apply(0, &vec![], &vec![0]).is_none());
    assert!(m.apply(0, &vec![1, 1], &vec![0]).is_none());
    // 引数がドメイン（1..=2）の外。
    assert!(m.apply(0, &vec![0], &vec![0]).is_none());
    assert!(m.apply(0, &vec![3], &vec![0]).is_none());
    // 状態が状態型に従わない。
    assert!(m.apply(0, &vec![1], &vec![4]).is_none());
    assert!(m.apply(0, &vec![1], &vec![]).is_none());
    assert!(m.apply(0, &vec![1], &vec![0, 0]).is_none());
    // それ以外は、guard が偽でも Some。
    assert!(matches!(m.apply(0, &vec![2], &vec![1]), Some(StepR::To(t, Some(3))) if t == vec![3]));
    assert!(matches!(m.apply(0, &vec![2], &vec![2]), Some(StepR::Disabled)));
    assert!(matches!(m.apply(0, &vec![1], &vec![3]), Some(StepR::Disabled)));
}

#[test]
fn apply_computes_one_transition_where_enumeration_fails() {
    // 引数 d（0..=2）で 3 / d >= 1 を guard にし、x を d にする。d = 0 で評価エラーになる。
    let raw = RawModel {
        enums: vec![],
        state_types: vec![Type::Int(0, 3)],
        inits: vec![vec![0]],
        actions: vec![Action {
            n_params: 1,
            domains: vec![Type::Int(0, 2)],
            guard: bin(BinOp::Ge, bin(BinOp::Div, int(3), Expr::Arg(0)), int(1)),
            updates: vec![Update {
                target: 0,
                expr: Expr::Arg(0),
            }],
            output: None,
        }],
        invariants: vec![],
        contracts: vec![],
        terminal: None,
    };
    let m = validate(raw).expect("整形式のモデル");
    // 列挙は最初の引数 d = 0 で評価エラーになる。
    assert!(matches!(
        m.successors(0, &vec![0]),
        Some(Enumerated::Fail(args, Site::Guard, ErrKind::DivByZero)) if args == vec![0]
    ));
    // 引数を1つ選んで適用すれば、他の引数の評価エラーに関係なく遷移を計算できる。
    assert!(matches!(
        m.apply(0, &vec![0], &vec![0]),
        Some(StepR::Fail(Site::Guard, ErrKind::DivByZero))
    ));
    assert!(matches!(m.apply(0, &vec![1], &vec![0]), Some(StepR::To(t, None)) if t == vec![1]));
    assert!(matches!(m.apply(0, &vec![2], &vec![0]), Some(StepR::To(t, None)) if t == vec![2]));
}

#[test]
fn the_search_api_rejects_bad_input_instead_of_panicking() {
    let m = checked();
    assert!(m.successors(1, &vec![0]).is_none());
    assert!(m.successors(0, &vec![4]).is_none());
    assert!(m.successors(0, &vec![]).is_none());
    assert!(m.successors(usize::MAX, &vec![0, 0]).is_none());
    match m.successors(0, &vec![1]) {
        Some(Enumerated::Ok(ts)) => {
            // 引数の辞書順に、有効な遷移をすべて返す。
            let got: Vec<_> = ts.iter().map(|t| (t.args.clone(), t.output, t.state.clone())).collect();
            assert_eq!(got, vec![(vec![1], Some(2), vec![2]), (vec![2], Some(3), vec![3])]);
        }
        other => panic!("{other:?}"),
    }
    assert!(!m.state_ok(&vec![-1]));
    assert_eq!(m.terminal(&vec![3]), Ok(true));
    assert_eq!(m.terminal(&vec![]), Err(ErrKind::Unbound));
    assert_eq!(m.invariants(&all(false), &vec![]), Some((0, Err(ErrKind::Unbound))));
    assert_eq!(m.contracts(&all(false), 9, &vec![0], &vec![], &vec![0], &None), None);
    assert_eq!(
        m.contracts(&all(false), 0, &vec![0], &vec![1], &vec![1], &Some(2)),
        Some((0, Ok(false)))
    );
}
