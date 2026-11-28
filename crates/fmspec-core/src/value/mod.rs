//! IRの側の値と型。名前を解決したIRのモデル（`SModel`）と値の上の意味論、式の型付け、値の符号化と番号、型の上の実行関数と大きさの条件。
//!
//! - [`encoding`]：IRの複合型と値の意味、スロットの列への符号化（仕様）
//! - [`stype_exec`]：型（`SType`、`XType`）の上の実行関数（複製、比較、値の数、整形式性、幅、スロットの位置）
//! - [`fits`]：値の型を、格納の型の場所に置けるか（`fits_s`）の仕様と補題
//! - [`keys`]：キーの型の値の正規順と番号（仕様）
//! - [`rank_code`]：キーの型の値の符号の列と、正規順の番号（u64）の相互の変換
//! - [`map_encoding`]：キーに番号を付けたあとの、Mapの符号化
//! - [`default_codes`]：型の既定値の符号の列
//! - [`val_codec`]：値の木（`Val`）と符号の列の、検証済みの相互の変換
//! - [`source`]：IRの式の型付き構文木と、値の上の意味論（仕様）
//! - [`infer`]：IRの式の型付け規則（仕様）と型検査器
//! - [`limits`]：下ろしが大きさの理由で失敗しないための条件（仕様）
//! - [`smodel`]：名前を解決したIRのモデルと、値の上の意味論

pub mod default_codes;
pub mod encoding;
pub mod fits;
pub mod infer;
pub mod keys;
pub mod limits;
pub mod map_encoding;
pub mod rank_code;
pub mod smodel;
pub mod source;
pub mod stype_exec;
pub mod val_codec;
