//! fmspec の交換形式（仕様書 §6、§10、§14.2）。
//!
//! IR、検査条件、証明書、トレース、値のJSON表現を、中核の型との間で変換する。
//! IRの式は、名前を解決して型を検査し、中核の型付きの式の木にする（`resolve`）。
//! モデルの下ろし（定数と初期値の評価、スロットへの下ろし）は、中核の検証済みの `lower_model` が行う。
//! 中核が返す誤りは、IRの定義の名前と位置で説明する（`diagnostics`）。
//! 組み立てたモデルと名前の表は、中核の検証済みの `ir_check::lower_checked` が入力のIRと対応することを
//! 確かめてから下ろす（`ir_json`）。したがって、名前解決の誤りは内部エラーになり、誤った判定にはならない。
//! それ以外（受理の条件、証拠と値のJSONの変換など）は検証済みの経路の外にあり、残存する信頼基盤に含まれる
//! （仕様書 §14.3）。ここで組み立てたモデルは必ず中核の `validate` を通す。
//! 証明書とトレースは判定ゲートが検査するので、読み込みの誤りが誤った判定に変わることはない。

mod canonical;
mod conditions;
mod diagnostics;
mod evidence;
mod ir_json;
mod json;
mod model;
mod refinement;
mod resolve;
mod type_syntax;
pub mod types;
mod value;

pub use conditions::{conditions_from_json, conditions_to_json, default_conditions};
pub use evidence::{
    certificate_from_json, certificate_to_json, claim_to_json, error_to_json, read_certificate, read_trace,
    trace_from_json, trace_to_json, Loaded, Trace, TraceError,
};
pub use model::{load, parse, ActionNames, EnumNames, LoadError, Model, Names, Source, UpdateSlot};
pub use refinement::{load_refinement, Refinement};
pub use types::{SType, XType};
pub use value::{
    args_from_json, args_to_json, core_type_to_json, output_to_json, output_value_from_json, state_to_json,
    type_to_json, value_from_json, value_to_json,
};

/// このエンジンが読めるIRのバージョン。
pub const IR_VERSION: i64 = 1;
/// トレースの形式のバージョン。
pub const TRACE_VERSION: i64 = 1;
/// 証明書の形式のバージョン。
pub const CERTIFICATE_VERSION: i64 = 1;
/// エンジンのバージョン。トレースと証明書に記録する。
pub const ENGINE_VERSION: &str = env!("CARGO_PKG_VERSION");
