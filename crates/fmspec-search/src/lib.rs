//! fmspec の探索器（仕様書 §3.1、§8）。
//!
//! このcrateは検証の対象外である。探索器は証拠（安全性証明書、またはトレース）を生成するだけで、
//! 判定は必ず中核の判定ゲート `fmspec_core::gate::decide` が証拠を検査してから返す。
//! 探索器に不具合があっても、誤った `Verified` や `Violated` にはならない。
//! 探索の完全性、停止性、反例の最短性はテストで検査する（仕様書 §14.1.1）。

pub mod bfs;
pub mod check;
pub mod simulate;

pub use bfs::{bfs, BfsOptions, SearchResult, Stats};
pub use check::{check, check_evidence, sample, Outcome, Sampled, Status};
pub use simulate::{simulate, SimOptions, SimResult, SimStats, PRNG_NAME};
