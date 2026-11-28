//! IRの式から中核の式への下ろし。`lowering` の `low` が式の種類ごとのモジュールに振り分ける相互再帰で、このフォルダの中だけで互いを参照する。
//!
//! - [`lowering`]：IRの型付き構文木から中核の式への下ろし
//! - [`lower_core`]、[`lower_struct`]、[`lower_quant`]、[`lower_set`]、[`lower_map`]、[`lower_list`]： 葉と演算子と条件式、Tuple と Record と Option、量化、Set、Map、List の下ろし（`lowering` の `low` が振り分ける）

pub mod lower_core;
pub mod lower_list;
pub mod lower_map;
pub mod lower_quant;
pub mod lower_set;
pub mod lower_struct;
pub mod lowering;
