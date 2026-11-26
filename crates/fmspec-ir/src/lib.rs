//! fmspec の交換形式（仕様書 §6、§10、§14.2）。
//!
//! IR、検査条件、証明書、トレースのJSON表現を、中核の型との間で変換する。
//! ここは検証済みの経路の外にあり、残存する信頼基盤に含まれる（仕様書 §14.3）。
//! ただし、ここで組み立てたモデルは必ず中核の `validate` を通す。
//! 証明書とトレースは判定ゲートが検査するので、読み込みの誤りが誤った判定に変わることはない。

mod canonical;
mod conditions;
mod evidence;
mod model;
mod value;

pub use conditions::{conditions_from_json, conditions_to_json, default_conditions};
pub use evidence::{
    certificate_from_json, certificate_to_json, claim_to_json, error_to_json, trace_from_json, trace_to_json, Trace,
    TraceError,
};
pub use model::{load, parse, ActionNames, EnumNames, LoadError, Model, Names, Source};
pub use value::{args_to_json, output_to_json, state_to_json, type_to_json, value_to_json};

/// このエンジンが読めるIRのバージョン。
pub const IR_VERSION: i64 = 1;
/// トレースの形式のバージョン。
pub const TRACE_VERSION: i64 = 1;
/// 証明書の形式のバージョン。
pub const CERTIFICATE_VERSION: i64 = 1;
/// エンジンのバージョン。トレースと証明書に記録する。
pub const ENGINE_VERSION: &str = env!("CARGO_PKG_VERSION");
