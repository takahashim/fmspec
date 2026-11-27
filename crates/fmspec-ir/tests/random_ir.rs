//! ランダムに生成した型の合うIRを読み込み、`fmspec-ir` の検査を通るモデルを中核の型検査と下ろしも受理することを確かめる。
//!
//! 中核の `lower_model` は、下ろしの前に `check_model`（型と大きさの条件）を確かめ、
//! 型の付くモデルでは内部の誤りを返さないことを検証済みである（計画書 docs/plans/lowering_totality.md）。
//! このテストは、`fmspec-ir` の検査と `check_model` の条件が食い違わないことを確かめる。

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use fmspec_ir::{load, LoadError};
use serde_json::{json, Value};

/// 再現できる擬似乱数（xorshift64*）。
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, k: usize, n: usize) -> bool {
        self.below(n) < k
    }
}

#[derive(Clone, PartialEq, Debug)]
enum Ty {
    Bool,
    Int(i64, i64),
    Enum,
    Tuple(Vec<Ty>),
    Record(Vec<Ty>),
    Option(Box<Ty>),
    Set(Box<Ty>),
    Map(Box<Ty>, Box<Ty>),
    List(Box<Ty>, usize),
}

const FIELDS: [&str; 3] = ["a", "b", "c"];

impl Ty {
    fn json(&self) -> Value {
        match self {
            Ty::Bool => json!({"bool": {}}),
            Ty::Int(lo, hi) => json!({"int": {"min": lo, "max": hi}}),
            Ty::Enum => json!({"enum": "color"}),
            Ty::Tuple(ts) => json!({"tuple": ts.iter().map(Ty::json).collect::<Vec<_>>()}),
            Ty::Record(ts) => json!({"record": ts
                .iter()
                .enumerate()
                .map(|(i, t)| json!({"name": FIELDS[i], "type": t.json()}))
                .collect::<Vec<_>>()}),
            Ty::Option(t) => json!({"option": t.json()}),
            Ty::Set(t) => json!({"set": t.json()}),
            Ty::Map(k, v) => json!({"map": {"key": k.json(), "value": v.json()}}),
            Ty::List(t, max) => json!({"list": {"of": t.json(), "max": max}}),
        }
    }
}

fn key_ty(r: &mut Rng, depth: usize) -> Ty {
    match r.below(if depth == 0 { 3 } else { 5 }) {
        0 => Ty::Bool,
        1 => Ty::Int(0, 2),
        2 => Ty::Enum,
        3 => Ty::Option(Box::new(key_ty(r, depth - 1))),
        _ => Ty::Tuple(vec![key_ty(r, 0), key_ty(r, 0)]),
    }
}

fn any_ty(r: &mut Rng, depth: usize) -> Ty {
    if depth == 0 {
        return key_ty(r, 0);
    }
    match r.below(9) {
        0..=2 => key_ty(r, 1),
        3 => Ty::Tuple(vec![any_ty(r, depth - 1), any_ty(r, depth - 1)]),
        4 => Ty::Record(vec![any_ty(r, depth - 1), any_ty(r, depth - 1)]),
        5 => Ty::Option(Box::new(any_ty(r, depth - 1))),
        6 => Ty::Set(Box::new(key_ty(r, 0))),
        7 => Ty::Map(Box::new(key_ty(r, 0)), Box::new(any_ty(r, depth - 1))),
        _ => Ty::List(Box::new(any_ty(r, depth - 1)), 1 + r.below(3)),
    }
}

/// 式から参照できるもの。
#[derive(Clone)]
struct Scope {
    states: Vec<Ty>,
    params: Vec<Ty>,
    next: bool,
    locals: Vec<(String, Ty)>,
    consts: Vec<(String, Ty)>,
}

struct Gen<'a> {
    r: &'a mut Rng,
    fresh: usize,
    /// 評価に失敗しうる演算子（`unwrap`、`get`、`at`、`push` など）を使わない。定数と初期値で使う。
    safe: bool,
}

impl Gen<'_> {
    fn refs(&self, s: &Scope, t: &Ty) -> Vec<Value> {
        let mut out = Vec::new();
        for (i, st) in s.states.iter().enumerate() {
            if st == t {
                out.push(json!({"var": i}));
                if s.next {
                    out.push(json!({"next": i}));
                }
            }
        }
        for (i, pt) in s.params.iter().enumerate() {
            if pt == t {
                out.push(json!({"param": i}));
            }
        }
        // 内側の束縛が外側を隠すので、同じ名前のうち最も内側だけを参照できる。
        for (k, (n, lt)) in s.locals.iter().enumerate() {
            let shadowed = s.locals[k + 1..].iter().any(|(m, _)| m == n);
            if lt == t && !shadowed {
                out.push(json!({"local": n}));
            }
        }
        for (n, ct) in &s.consts {
            if ct == t {
                out.push(json!({"const": n}));
            }
        }
        out
    }

    fn name(&mut self) -> String {
        self.fresh += 1;
        format!("x{}", self.fresh % 3)
    }

    /// 型 `t` の式。
    fn expr(&mut self, s: &Scope, t: &Ty, depth: usize) -> Value {
        let refs = self.refs(s, t);
        if !refs.is_empty() && self.r.chance(1, 3) {
            return refs[self.r.below(refs.len())].clone();
        }
        if depth == 0 {
            return self.lit(s, t);
        }
        let d = depth - 1;
        // 型によらない式
        let pick = self.r.below(12);
        match if self.safe && (4..=6).contains(&pick) { 12 } else { pick } {
            0 => {
                let c = self.expr(s, &Ty::Bool, d);
                let a = self.expr(s, t, d);
                let b = self.expr(s, t, d);
                return json!({"ite": [c, a, b]});
            }
            1 => {
                let vt = any_ty(self.r, 1);
                let value = self.expr(s, &vt, d);
                let n = self.name();
                let mut inner = s.clone();
                inner.locals.push((n.clone(), vt));
                let body = self.expr(&inner, t, d);
                return json!({"let": {"name": n, "value": value, "body": body}});
            }
            2 => {
                let other = any_ty(self.r, 0);
                let tup = Ty::Tuple(vec![t.clone(), other]);
                let of = self.expr(s, &tup, d);
                return json!({"nth": {"of": of, "index": 0}});
            }
            3 => {
                let other = any_ty(self.r, 0);
                let rec = Ty::Record(vec![other, t.clone()]);
                let of = self.expr(s, &rec, d);
                return json!({"field": {"of": of, "name": "b"}});
            }
            4 => {
                let o = self.expr(s, &Ty::Option(Box::new(t.clone())), d);
                return json!({"unwrap": [o]});
            }
            5 => {
                let k = key_ty(self.r, 0);
                let m = self.expr(s, &Ty::Map(Box::new(k.clone()), Box::new(t.clone())), d);
                let x = self.expr(s, &k, d);
                return json!({"get": [m, x]});
            }
            6 => {
                let l = self.expr(s, &Ty::List(Box::new(t.clone()), 2), d);
                return match self.r.below(3) {
                    0 => json!({"first": [l]}),
                    1 => json!({"last": [l]}),
                    _ => {
                        let i = self.expr(s, &Ty::Int(0, 2), d);
                        json!({"at": [l, i]})
                    }
                };
            }
            _ => {}
        }
        self.shaped(s, t, d)
    }

    /// 型 `t` に固有の演算子による式。
    fn shaped(&mut self, s: &Scope, t: &Ty, d: usize) -> Value {
        match t {
            Ty::Bool => match self.r.below(13) {
                0 => {
                    let u = any_ty(self.r, 1);
                    let a = self.expr(s, &u, d);
                    let b = self.expr(s, &u, d);
                    if self.r.chance(1, 2) {
                        json!({"eq": [a, b]})
                    } else {
                        json!({"ne": [a, b]})
                    }
                }
                1 => {
                    let a = self.expr(s, &Ty::Int(0, 2), d);
                    let b = self.expr(s, &Ty::Int(0, 2), d);
                    let op = ["lt", "le", "gt", "ge"][self.r.below(4)];
                    json!({op: [a, b]})
                }
                2 => json!({"not": [self.expr(s, &Ty::Bool, d)]}),
                3 => {
                    let n = self.r.below(3);
                    let xs: Vec<Value> = (0..n).map(|_| self.expr(s, &Ty::Bool, d)).collect();
                    if self.r.chance(1, 2) {
                        json!({"all": xs})
                    } else {
                        json!({"any": xs})
                    }
                }
                4 => {
                    let a = self.expr(s, &Ty::Bool, d);
                    let b = self.expr(s, &Ty::Bool, d);
                    json!({"implies": [a, b]})
                }
                5 => {
                    let k = key_ty(self.r, 0);
                    let c = self.expr(s, &Ty::Set(Box::new(k.clone())), d);
                    let x = self.expr(s, &k, d);
                    json!({"contains": [c, x]})
                }
                6 => {
                    let e = any_ty(self.r, 0);
                    let c = self.expr(s, &Ty::List(Box::new(e.clone()), 2), d);
                    let x = self.expr(s, &e, d);
                    json!({"contains": [c, x]})
                }
                7 => {
                    let k = Ty::Set(Box::new(key_ty(self.r, 0)));
                    let a = self.expr(s, &k, d);
                    let b = self.expr(s, &k, d);
                    json!({"subset": [a, b]})
                }
                8 => {
                    let c = self.collection(s, d);
                    json!({"is_empty": [c]})
                }
                9 => {
                    let k = key_ty(self.r, 0);
                    let v = any_ty(self.r, 0);
                    let m = self.expr(s, &Ty::Map(Box::new(k.clone()), Box::new(v)), d);
                    let x = self.expr(s, &k, d);
                    json!({"has_key": [m, x]})
                }
                10 => {
                    let u = Ty::Option(Box::new(any_ty(self.r, 1)));
                    let o = self.expr(s, &u, d);
                    if self.r.chance(1, 2) {
                        json!({"is_some": [o]})
                    } else {
                        json!({"is_none": [o]})
                    }
                }
                _ => self.quant(s, d),
            },
            Ty::Int(_, _) => match if self.safe { 3 } else { self.r.below(4) } {
                0 => {
                    let a = self.expr(s, t, d);
                    let b = self.expr(s, t, d);
                    let op = ["add", "sub", "mul", "div", "mod"][self.r.below(5)];
                    json!({op: [a, b]})
                }
                1 => {
                    let c = self.collection(s, d);
                    json!({"size": [c]})
                }
                _ => self.lit(s, t),
            },
            Ty::Enum => self.lit(s, t),
            Ty::Tuple(ts) => json!({"tuple": ts.iter().map(|u| self.expr(s, u, d)).collect::<Vec<_>>()}),
            Ty::Record(ts) => json!({"record": ts
                .iter()
                .enumerate()
                .map(|(i, u)| json!({"name": FIELDS[i], "expr": self.expr(s, u, d)}))
                .collect::<Vec<_>>()}),
            Ty::Option(u) => {
                if self.r.chance(1, 3) {
                    json!({"none": u.json()})
                } else {
                    json!({"some": [self.expr(s, u, d)]})
                }
            }
            Ty::Set(k) => match self.r.below(5) {
                0 => {
                    let a = self.expr(s, t, d);
                    let x = self.expr(s, k, d);
                    if self.r.chance(1, 2) {
                        json!({"insert": [a, x]})
                    } else {
                        json!({"remove": [a, x]})
                    }
                }
                1 => {
                    let a = self.expr(s, t, d);
                    let b = self.expr(s, t, d);
                    let op = ["union", "intersection", "difference"][self.r.below(3)];
                    json!({op: [a, b]})
                }
                2 => {
                    let v = any_ty(self.r, 0);
                    let m = self.expr(s, &Ty::Map(k.clone(), Box::new(v)), d);
                    json!({"keys": [m]})
                }
                _ => {
                    let n = self.r.below(3);
                    let items: Vec<Value> = (0..n).map(|_| self.expr(s, k, d)).collect();
                    json!({"set": {"of": k.json(), "items": items}})
                }
            },
            Ty::Map(k, v) => match self.r.below(4) {
                0 => {
                    let m = self.expr(s, t, d);
                    let x = self.expr(s, k, d);
                    let y = self.expr(s, v, d);
                    json!({"put": [m, x, y]})
                }
                1 => {
                    let m = self.expr(s, t, d);
                    let x = self.expr(s, k, d);
                    json!({"delete": [m, x]})
                }
                _ => {
                    let n = self.r.below(3);
                    let items: Vec<Value> = (0..n)
                        .map(|_| json!([self.expr(s, k, d), self.expr(s, v, d)]))
                        .collect();
                    json!({"map": {"key": k.json(), "value": v.json(), "items": items}})
                }
            },
            Ty::List(e, max) => match if self.safe { 3 } else { self.r.below(4) } {
                0 => {
                    let l = self.expr(s, t, d);
                    let x = self.expr(s, e, d);
                    json!({"push": [l, x]})
                }
                1 => {
                    let l = self.expr(s, t, d);
                    if self.r.chance(1, 2) {
                        json!({"pop": [l]})
                    } else {
                        json!({"shift": [l]})
                    }
                }
                _ => {
                    let n = self.r.below(max + 1);
                    let items: Vec<Value> = (0..n).map(|_| self.expr(s, e, d)).collect();
                    json!({"list": {"of": e.json(), "max": max, "items": items}})
                }
            },
        }
    }

    /// Set、Map、Listのどれかの式。
    fn collection(&mut self, s: &Scope, d: usize) -> Value {
        let t = match self.r.below(3) {
            0 => Ty::Set(Box::new(key_ty(self.r, 0))),
            1 => Ty::Map(Box::new(key_ty(self.r, 0)), Box::new(any_ty(self.r, 0))),
            _ => Ty::List(Box::new(any_ty(self.r, 0)), 2),
        };
        self.expr(s, &t, d)
    }

    fn quant(&mut self, s: &Scope, d: usize) -> Value {
        let (over, bt, by_type) = match self.r.below(4) {
            0 => {
                let k = key_ty(self.r, 1);
                (k.json(), k, true)
            }
            1 => {
                let k = key_ty(self.r, 0);
                (self.expr(s, &Ty::Set(Box::new(k.clone())), d), k, false)
            }
            2 => {
                let k = key_ty(self.r, 0);
                let v = any_ty(self.r, 0);
                (self.expr(s, &Ty::Map(Box::new(k.clone()), Box::new(v)), d), k, false)
            }
            _ => {
                let e = any_ty(self.r, 0);
                (self.expr(s, &Ty::List(Box::new(e.clone()), 2), d), e, false)
            }
        };
        let n = self.name();
        let mut inner = s.clone();
        inner.locals.push((n.clone(), bt));
        let body = self.expr(&inner, &Ty::Bool, d);
        let q = if self.r.chance(1, 2) { "forall" } else { "exists" };
        let key = if by_type { "type" } else { "in" };
        json!({q: {"name": n, key: over, "body": body}})
    }

    /// 型 `t` のリテラル、または参照を含まない最小の式。
    fn lit(&mut self, s: &Scope, t: &Ty) -> Value {
        match t {
            Ty::Bool => json!({"bool": self.r.chance(1, 2)}),
            Ty::Int(lo, hi) => json!({"int": lo + self.r.below((hi - lo + 1) as usize) as i64}),
            Ty::Enum => {
                let v = ["red", "green"][self.r.below(2)];
                json!({"enum": {"type": "color", "variant": v}})
            }
            Ty::Option(u) => json!({"none": u.json()}),
            Ty::Set(k) => json!({"set": {"of": k.json(), "items": []}}),
            Ty::Map(k, v) => json!({"map": {"key": k.json(), "value": v.json(), "items": []}}),
            Ty::List(e, max) => json!({"list": {"of": e.json(), "max": max, "items": []}}),
            Ty::Tuple(_) | Ty::Record(_) => self.shaped(s, t, 0),
        }
    }
}

fn model(seed: u64) -> Value {
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let n_states = 1 + rng.below(3);
    let states: Vec<Ty> = (0..n_states).map(|_| any_ty(&mut rng, 2)).collect();
    let mut g = Gen {
        r: &mut rng,
        fresh: 0,
        safe: true,
    };
    let empty = Scope {
        states: vec![],
        params: vec![],
        next: false,
        locals: vec![],
        consts: vec![],
    };
    let mut consts = Vec::new();
    let mut cscope = empty.clone();
    for i in 0..g.r.below(3) {
        let t = any_ty(g.r, 1);
        let value = g.expr(&cscope, &t, 2);
        let name = format!("k{i}");
        consts.push(json!({"name": name, "type": t.json(), "value": value}));
        cscope.consts.push((name, t));
    }
    let base0 = Scope {
        states: states.clone(),
        consts: cscope.consts.clone(),
        ..empty
    };
    let state_json: Vec<Value> = states
        .iter()
        .enumerate()
        .map(|(i, t)| {
            if g.r.chance(1, 2) {
                json!({"id": i, "name": format!("s{i}"), "type": t.json(), "initial": g.lit(&cscope, t)})
            } else {
                let n = 1 + g.r.below(2);
                let es: Vec<Value> = (0..n).map(|_| g.expr(&cscope, t, 2)).collect();
                json!({"id": i, "name": format!("s{i}"), "type": t.json(), "initial_in": es})
            }
        })
        .collect();
    g.safe = false;
    let base = base0;
    let mut actions = Vec::new();
    let mut outputs = Vec::new();
    for a in 0..1 + g.r.below(2) {
        let params: Vec<Ty> = (0..g.r.below(3)).map(|_| any_ty(g.r, 1)).collect();
        let s = Scope {
            params: params.clone(),
            ..base.clone()
        };
        let guard = g.expr(&s, &Ty::Bool, 3);
        let mut updates = Vec::new();
        for (i, st) in states.iter().enumerate() {
            if g.r.chance(2, 3) {
                updates.push(json!({"target": i, "expr": g.expr(&s, st, 3)}));
            }
        }
        let mut act = json!({
            "name": format!("a{a}"),
            "params": params.iter().enumerate().map(|(i, t)| json!({"name": format!("p{i}"), "type": t.json()})).collect::<Vec<_>>(),
            "guard": guard,
            "updates": updates,
        });
        if g.r.chance(1, 2) {
            let ot = [Ty::Bool, Ty::Int(0, 2), Ty::Enum][g.r.below(3)].clone();
            act["output"] = json!({"type": ot.json(), "expr": g.expr(&s, &ot, 2)});
            outputs.push(Some(ot));
        } else {
            outputs.push(None);
        }
        actions.push((act, params));
    }
    let invariants: Vec<Value> = (0..g.r.below(3))
        .map(|i| json!({"name": format!("i{i}"), "expr": g.expr(&base, &Ty::Bool, 3)}))
        .collect();
    let mut contracts = Vec::new();
    for k in 0..g.r.below(3) {
        let a = g.r.below(actions.len());
        let s = Scope {
            params: actions[a].1.clone(),
            next: true,
            ..base.clone()
        };
        let mut e = g.expr(&s, &Ty::Bool, 3);
        if let Some(ot) = &outputs[a] {
            if g.r.chance(1, 2) {
                let x = g.expr(&s, ot, 1);
                e = json!({"implies": [e, {"eq": [{"output": {}}, x]}]});
            }
        }
        contracts.push(json!({"name": format!("c{k}"), "action": format!("a{a}"), "expr": e}));
    }
    let mut m = json!({
        "ir_version": 1,
        "name": "random",
        "enums": [{"name": "color", "variants": ["red", "green"]}],
        "constants": consts,
        "states": state_json,
        "actions": actions.into_iter().map(|(a, _)| a).collect::<Vec<_>>(),
        "invariants": invariants,
        "contracts": contracts,
    });
    if g.r.chance(1, 2) {
        m["terminal"] = g.expr(&base, &Ty::Bool, 2);
    }
    if g.r.chance(1, 3) {
        m["initial_constraint"] = g.expr(&base, &Ty::Bool, 2);
    }
    m
}

#[test]
fn accepted_random_models_pass_the_core_type_check() {
    let mut accepted = 0;
    let n = std::env::var("RANDOM_IR_SEEDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(400);
    for seed in 0..n {
        let ir = model(seed);
        match load(&ir.to_string()) {
            Ok(_) => accepted += 1,
            Err(LoadError::Schema { path, message }) => {
                assert!(!message.contains("内部エラー"), "seed {seed}: {path}: {message}\n{ir}");
                if std::env::var("RANDOM_IR_DEBUG").is_ok() {
                    eprintln!("{path}: {message}");
                }
            }
            Err(LoadError::Invalid { reason, message, .. }) => {
                panic!("seed {seed}: 型の合うモデルが中核のIR検証で拒否された: {reason:?} {message}\n{ir}");
            }
            Err(other) => panic!("seed {seed}: {other:?}\n{ir}"),
        }
    }
    if std::env::var("RANDOM_IR_DEBUG").is_ok() {
        eprintln!("accepted {accepted}/{n}");
    }
    // 生成したモデルの多くが受理されなければ、このテストは何も確かめていない。
    assert!(accepted * 2 > n, "受理されたモデルが少なすぎます: {accepted}/{n}");
}
