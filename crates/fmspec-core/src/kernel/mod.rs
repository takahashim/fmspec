//! 判定の核。判定（`Verdict`）を作る経路のすべて：中核のモデルと式の意味論、遷移列挙、検査条件、証拠とその検査器、判定ゲート、詳細化、対称性、Model-Based Testing の候補集合。ほかのフォルダに依存しない。
//!
//! - [`model`]：IR検証前のモデル、値、型、式
//! - [`state_set`]：状態の集合への所属（`in_cert`）と、整列した列の二分探索
//! - [`expr_copy`]：中核の式の複製
//! - [`eval`]：式の形式意味論（spec）と実行Evaluator
//! - [`typing`]：型規則、整形式性、`validate`、型健全性
//! - [`step`]：遷移の意味論と遷移列挙
//! - [`state_enc`]：状態と引数の符号化列（各スロットが型に属すこと、値の符号化）
//! - [`semantics`]：検査条件、到達可能性、安全性の定義
//! - [`evidence`]：証拠（証明書、トレース、主張）の型
//! - [`cert`]：安全性証明書の検査器（対称性による代表元の証明書を含む）
//! - [`checked`]：IR検証を通ったモデル（`CheckedModel`）
//! - [`trace`]：トレースの検査器
//! - [`gate`]：判定ゲートと、未検証コード向けの公開API
//! - [`refine`]：詳細化の検査器と判定
//! - [`sym`]：対称性による状態の削減（付け替えの意味論と、入れ替えで遷移と性質が保たれること）
//! - [`sym_check`]：入れ替えが対称性であることの検査と、状態の正規化
//! - [`mbt`]：Model-Based Testing の候補集合
//! - `impls`：未検証コードが使う、標準トレイトの手書きの実装（証明の対象外）

pub mod cert;
pub mod checked;
pub mod eval;
pub mod evidence;
pub mod expr_copy;
pub mod gate;
mod impls;
pub mod mbt;
pub mod model;
pub mod refine;
pub mod semantics;
pub mod state_enc;
pub mod state_set;
pub mod step;
pub mod sym;
pub mod sym_check;
pub mod trace;
pub mod typing;
