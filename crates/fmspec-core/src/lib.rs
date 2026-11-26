//! fmspec の検証済み中核。
//!
//! このcrateは Verus で検証する。判定（[`gate::Verdict`]）を返す経路は、すべてここにある。
//! 探索器（BFS など）は別crateに置き、証拠を生成するだけで判定を直接返さない（仕様書 §3.1）。
//!
//! - [`model`]：IR検証前のモデル、値、型、式
//! - [`eval`]：式の形式意味論（spec）と実行Evaluator
//! - [`typing`]：型規則、整形式性、`validate`、型健全性
//! - [`step`]：遷移の意味論と遷移列挙
//! - [`semantics`]：検査条件、到達可能性、安全性の定義
//! - [`evidence`]：証拠（証明書、トレース、主張）の型
//! - [`cert`]：安全性証明書の検査器
//! - [`trace`]：トレースの検査器
//! - [`gate`]：判定ゲートと、未検証コード向けの公開API
//! - [`mbt`]：Model-Based Testing の候補集合

pub mod bindings;
pub mod cert;
pub mod eval;
pub mod evidence;
pub mod gate;
mod impls;
pub mod mbt;
pub mod map_lookup;
pub mod model;
pub mod ranking;
pub mod semantics;
pub mod step;
pub mod trace;
pub mod typing;
