//! モデル全体の下ろし。定数、初期状態、不変条件、操作、遷移契約を下ろし、下ろした中核のモデルの安全性が名前を解決したモデルの安全性と同値であることを示す。
//!
//! - [`srel`]：中核の符号の列と値の列の対応（`rel`）
//! - [`action_lower`]：操作の下ろし
//! - [`lower_error`]：モデルの下ろしが返す誤り（`LowerError`）
//! - [`model_lower`]：モデル全体の下ろし
//! - [`model_init`]：初期状態の計算（定数と初期値の評価、候補の直積、初期条件）
//! - [`lower_spec`]：モデルの下ろしの結果の性質（仕様）
//! - [`model_safe`]：モデル全体の下ろしが安全性を保存することの証明
//! - [`model_total`]：モデル全体の型付けと大きさの条件
//! - [`model_wf`]：下ろしたモデルの整形式性

pub mod action_lower;
pub mod lower_error;
pub mod lower_spec;
pub mod model_init;
pub mod model_lower;
pub mod model_safe;
pub mod model_total;
pub mod model_wf;
pub mod srel;
