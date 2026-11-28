//! スロットの式。下ろしの部品（式の組み立て、束縛の列、格納、行、番号で選ぶ部品）と、その意味の語彙（`preserve`）、型、等しさ、全域性の条件。
//!
//! - [`ranking`]：Setの要素とMapのキーに付ける番号（rank）の計算
//! - [`slots`]：下ろしで使う、スロットの式の操作と、束縛の列（`Block`）の操作
//! - [`slot_store`]：格納の型の値を正規形のスロットに置く式（`store`）と、キーの番号の式
//! - [`lower_ctx`]：下ろしの文脈（`LowerCtx`）と、束縛の列（`Block`）
//! - [`block`]：束縛の列（`Block`）の操作
//! - [`expr_build`]：中核の式の組み立て（spec の構築子と、対応する exec の構築子）
//! - [`rows`]：ListとMapのスロットの、行への区切りの仕様
//! - [`pick`]：番号の位置の値を選ぶ部品（`pick_slot`）と、その仕様
//! - [`bindings`]：評価の順に並べた束縛の列を、中核の `let` の入れ子にする
//! - [`canon`]：正規形の判定
//! - [`slot_types`]：スロットの型（`slot_tys`）の仕様と実行関数
//! - [`members`]：値の符号化が型に属すことの補題
//! - [`lower_types`]：スロットの型と、下ろした中核の式の型
//! - [`lists`]：Listのスロットの補題（行への区切り、行の選択、行のつなぎ直し）
//! - [`maps`]：Mapのスロットの補題（行への区切り、行の置き換え、行のつなぎ直し）
//! - [`map_lookup`]：Mapの参照の下ろし
//! - [`preserve`]：下ろしが意味を保存することの仕様と補題
//! - [`total`]：下ろしの全域性の仕様
//! - [`total_check`]：下ろしの全域性の前提を、実行時に確かめる検査
//! - [`equality`]：等しさの下ろしの補題（符号化の単射性と、値の種類）
//! - [`quant`]：量化の下ろしの部品（値の番号から正規形のスロットを作る式）

pub mod bindings;
pub mod block;
pub mod canon;
pub mod equality;
pub mod expr_build;
pub mod lists;
pub mod lower_ctx;
pub mod lower_types;
pub mod map_lookup;
pub mod maps;
pub mod members;
pub mod pick;
pub mod preserve;
pub mod quant;
pub mod ranking;
pub mod rows;
pub mod slot_store;
pub mod slot_types;
pub mod slots;
pub mod total;
pub mod total_check;
