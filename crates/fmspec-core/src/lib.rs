//! fmspec の検証済み中核。
//!
//! このcrateは Verus で検証する。判定（[`gate::Verdict`]）を返す経路は、すべてここにある。
//! 探索器（BFS など）は別crateに置き、証拠を生成するだけで判定を直接返さない（仕様書 §3.1）。
//!
//! - [`model`]：IR検証前のモデル、値、型、式
//! - [`encoding`]：IRの複合型と値の意味、スロットの列への符号化（仕様）
//! - [`keys`]：キーの型の値の正規順と番号（仕様）
//! - [`ranking`]：Setの要素とMapのキーに付ける番号（rank）の計算
//! - [`map_encoding`]：キーに番号を付けたあとの、Mapの符号化
//! - [`source`]：IRの式の型付き構文木と、値の上の意味論（仕様）
//! - [`infer`]：IRの式の型付け規則（仕様）と型検査器
//! - [`slots`]：下ろしで使う、スロットの式の組み立て
//! - [`bindings`]：評価の順に並べた束縛の列を、中核の `let` の入れ子にする
//! - [`expr_copy`]：中核の式の複製
//! - [`canon`]：スロットの型と、正規形の判定
//! - [`lists`]：Listのスロットの補題（行への区切り、行の選択、行のつなぎ直し）
//! - [`maps`]：Mapのスロットの補題（行への区切り、行の置き換え、行のつなぎ直し）
//! - [`map_lookup`]：Mapの参照の下ろし
//! - [`lowering`]：IRの型付き構文木から中核の式への下ろし
//! - [`preserve`]：下ろしが意味を保存することの仕様と補題
//! - [`preserve_ops`]、[`preserve_tuple`]、[`preserve_list`]、[`preserve_set`]、[`preserve_map`]、[`preserve_quant`]：
//!   演算子と `let` と条件式、Tuple と Record と Option、List、Set と大きさ、Map、量化の下ろしが意味を保存することの補題
//! - [`limits`]：下ろしが大きさの理由で失敗しないための条件（仕様）
//! - [`total`]：下ろしの全域性の仕様
//! - [`total_check`]：下ろしの全域性の前提を、実行時に確かめる検査
//! - [`smodel`]：名前を解決したIRのモデルと、値の上の意味論
//! - [`model_lower`]：モデル全体の下ろし
//! - [`model_safe`]：モデル全体の下ろしが安全性を保存することの証明
//! - [`model_total`]：モデル全体の型付けと大きさの条件
//! - [`equality`]：等しさの下ろしの補題（符号化の単射性と、値の種類）
//! - [`quant`]：量化の下ろしの部品（値の番号から正規形のスロットを作る式）
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
pub mod canon;
pub mod cert;
pub mod encoding;
pub mod equality;
pub mod eval;
pub mod evidence;
pub mod expr_copy;
pub mod gate;
mod impls;
pub mod infer;
pub mod keys;
pub mod limits;
pub mod lists;
pub mod lowering;
pub mod map_encoding;
pub mod map_lookup;
pub mod maps;
pub mod mbt;
pub mod model;
pub mod model_lower;
pub mod model_safe;
pub mod model_total;
pub mod preserve;
pub mod preserve_list;
pub mod preserve_map;
pub mod preserve_ops;
pub mod preserve_quant;
pub mod preserve_set;
pub mod preserve_tuple;
pub mod quant;
pub mod ranking;
pub mod refine;
pub mod semantics;
pub mod slots;
pub mod smodel;
pub mod source;
pub mod step;
pub mod sym;
pub mod total;
pub mod total_check;
pub mod trace;
pub mod typing;
