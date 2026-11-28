//! 枝が束縛を持つ条件式を入れ子にしたときの、下ろした式の大きさ（docs/performance.md）。
//!
//! `cargo test -p fmspec-core --test lowering_size -- --nocapture` で、深さごとの大きさを表示する。

use fmspec_core::kernel::eval::{eval, Ctx};
use fmspec_core::kernel::model::{BinOp, Expr, Type, Value};
use fmspec_core::lower::lowering::lower_stored;
use fmspec_core::slot::lower_ctx::{Layout, LowerCtx};
use fmspec_core::value::encoding::SType;
use fmspec_core::value::source::TExpr;

fn size(e: &Expr) -> usize {
    match e {
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Arg(_)
        | Expr::Next(_)
        | Expr::Out
        | Expr::Local(_)
        | Expr::Fail(_, _) => 1,
        Expr::Not(a) | Expr::Code(a) | Expr::Forall(_, _, _, a) | Expr::Exists(_, _, _, a) => 1 + size(a),
        Expr::Bin(_, a, b) | Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Let(a, b) => {
            1 + size(a) + size(b)
        }
        Expr::Ite(c, a, b) => 1 + size(c) + size(a) + size(b),
    }
}

fn lit(x: i64) -> TExpr {
    TExpr::Lit(Value::Int(x))
}

fn bin(op: BinOp, a: TExpr, b: TExpr) -> TExpr {
    TExpr::Bin(op, Box::new(a), Box::new(b))
}

/// 各要素が除算（束縛される）の、幅 `w` の組。
fn leaf(w: usize, k: i64) -> TExpr {
    TExpr::Tuple(
        (0..w as i64)
            .map(|i| bin(BinOp::Div, TExpr::Var(0), lit(i + k + 1)))
            .collect(),
    )
}

/// `ite(x < n, ite(x < n-1, ...), leaf)`。両方の枝が束縛を持つ。
fn nested(w: usize, n: usize) -> TExpr {
    let mut e = leaf(w, 0);
    for k in 1..=n {
        e = TExpr::Ite(
            Box::new(bin(BinOp::Lt, TExpr::Var(0), lit(k as i64))),
            Box::new(e),
            Box::new(leaf(w, k as i64)),
        );
    }
    e
}

fn expected(w: usize, n: usize, x: i64) -> Vec<i64> {
    // x < 1 なら最も内側、x < k（k が最小）なら k-1 段目の葉。どれでもなければ n 段目の葉。
    let k = (1..=n as i64).find(|&k| x < k).map(|k| k - 1).unwrap_or(n as i64);
    (0..w as i64).map(|i| x / (i + k + 1)).collect()
}

fn lower(w: usize, n: usize) -> Vec<Expr> {
    let cx = LowerCtx {
        enums: vec![],
        states: Some(vec![Layout {
            ty: SType::Int(0, 10),
            offset: 0,
        }]),
        args: vec![],
        next: false,
        out: None,
        consts: vec![],
    };
    let st = SType::Tuple((0..w).map(|_| SType::Int(-100, 100)).collect());
    lower_stored(&nested(w, n), &cx, &st, 0).ok().expect("下ろせる")
}

#[test]
fn nested_ite_lowers_correctly() {
    let st_tys = vec![Type::Int(0, 10)];
    let no_tys: Vec<Type> = vec![];
    let no_vals: Vec<i64> = vec![];
    for n in 0..=4 {
        let out = lower(3, n);
        for x in 0..=10 {
            let pre = vec![x];
            let ctx = Ctx {
                st_tys: &st_tys,
                arg_tys: &no_tys,
                pre: &pre,
                args: &no_vals,
                post: &no_vals,
                out: None,
            };
            let got: Vec<i64> = out
                .iter()
                .map(|e| match eval(e, &ctx) {
                    Ok(Value::Int(v)) => v,
                    r => panic!("{r:?}"),
                })
                .collect();
            assert_eq!(got, expected(3, n, x), "n={n} x={x}");
        }
    }
}

#[test]
fn nested_ite_size() {
    for w in [2, 4] {
        for n in 0..=4 {
            let out = lower(w, n);
            let total: usize = out.iter().map(size).sum();
            println!("w={w} n={n} size={total}");
        }
    }
    // 幅4、深さ4の大きさ（docs/performance.md の表）。下ろし方を変えたら表を更新する。
    let total: usize = lower(4, 4).iter().map(size).sum();
    assert_eq!(total, 54468);
}

/// 下ろす時間。`cargo test -p fmspec-core --release --test lowering_size -- --ignored --nocapture` で表示する。
#[test]
#[ignore]
fn nested_ite_timing() {
    for n in [5usize, 6, 7] {
        let t = std::time::Instant::now();
        let out = lower(4, n);
        let total: usize = out.iter().map(size).sum();
        println!("w=4 n={n} size={total} ms={}", t.elapsed().as_millis());
    }
}
