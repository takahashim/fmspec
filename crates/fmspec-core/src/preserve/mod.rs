//! 下ろしが意味を保存することの補題。式の種類ごとに、`lower` の対応するモジュールの証明を置く。
//!
//! - [`preserve_ops`]、[`preserve_tuple`]、[`preserve_list`]、[`preserve_set`]、[`preserve_map`]、[`preserve_quant`]： 演算子と `let` と条件式、Tuple と Record と Option、List、Set と大きさ、Map、量化の下ろしが意味を保存することの補題
//! - [`preserve_elem`]：要素とキーの下ろしが意味を保存することの補題

pub mod preserve_elem;
pub mod preserve_list;
pub mod preserve_map;
pub mod preserve_ops;
pub mod preserve_quant;
pub mod preserve_set;
pub mod preserve_tuple;
