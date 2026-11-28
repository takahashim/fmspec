//! IRのJSONと、名前を解決したモデルの対応。JSONの読み方、対応の仕様、その検査。IR検証（`crate::kernel::checked::validate`）とは別である。
//!
//! - [`ir`]、[`ir_check`]：IRのJSONと名前を解決したモデルの対応（仕様）と、その検査
//! - [`ir_json`]：IRのJSONの木（`Json`）の読み方と、名前の表

pub mod ir;
pub mod ir_check;
pub mod ir_json;
