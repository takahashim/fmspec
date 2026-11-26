# 証明の対象と信頼基盤

fmspecの判定のうち、何を機械証明で保証し、何をテストで検査し、何を信頼しているかを示す。
[設計仕様書](ruby_model_checker_spec.md)§14.3が求める、証明済みの定理と未検証部分の一覧にあたる。

## 判定の意味

利用者が受け取る判定は、`fmspec-core` の `decide`（判定ゲート）だけが作る。
`decide` の事後条件 `verdict_sound` が、各判定の意味を定める。

| 判定 | 保証 |
|---|---|
| `Verified` | 証拠は証明書であり、`safe(m, c)` が成り立つ |
| `Violated` | 証拠はトレースであり、そのトレースは有効（`trace_ok`）で、末尾で主張どおりの違反が起きる（`claim_holds`） |
| `Error` | 証拠はトレースであり、そのトレースは有効で、末尾で主張どおりの評価エラーが起きる |
| `Inconclusive` | 証拠が得られなかった場合に限る |
| `InvalidModel` | モデルが整形式でない場合に限る |
| `Rejected` | 証拠が提示された場合に限る |

`safe(m, c)` は、検査条件 `c` の下で、初期状態から対象の操作の遷移で到達できるすべての状態について、次が成り立つことである。

- 対象の不変条件がすべて真に評価される。
- 対象の操作とドメイン内の引数のどの組でも、適用が評価エラーにならず、有効な遷移は対象の契約をすべて満たす。
- デッドロック検査が有効なら、有効な遷移のない状態で終端条件が真に評価される。

これらの定義は `semantics.rs` にあり、探索器にも検査器の実装にも依存しない。

## 証明済みの性質

Verusで検証した定理と、仕様書§14.1の証明義務との対応を示す。
ファイルは `crates/fmspec-core/src/` にある。

| 証明義務 | 定理 | ファイル |
|---|---|---|
| IR Validation | `validate_raw` は、モデルが整形式（`wf`）であるとき、かつそのときに限り受理する | `typing.rs` |
| Type Soundness | `lemma_type_sound`：型の付いた式の評価は、型どおりの値になるか、オーバーフローで失敗する。`lemma_step_typed`：整形式なモデルでは、型に従う状態からの遷移先は型に従い、失敗はオーバーフローか範囲外更新である | `typing.rs` |
| Evaluation Correctness | `eval` の結果は、意味論 `eval_spec` と一致する | `eval.rs` |
| Transition Soundness / Completeness | `step` の結果は `step_spec` と一致する。`enumerate` は、有効な遷移だけを、ドメイン内のすべての引数について漏れなく返すか、評価エラーになる引数を1つ返す | `step.rs` |
| State Equality | 状態は符号化列そのもので、等価性は列の一致である。`lemma_decode_injective`：型に属する符号は値と一対一に対応する | `step.rs` |
| Certificate Soundness | `check_certificate` が受理したなら、証明書は帰納的で、`safe` が成り立つ | `cert.rs` |
| Trace Validity | `check_trace` が受理したなら、`trace_ok` と `claim_holds` が成り立つ。`lemma_trace_reach`：有効なトレースの各状態は到達可能である | `trace.rs` |
| Verdict Gate | `decide` と `decide_raw` は前提条件を持たず、判定は `verdict_sound` を満たす | `gate.rs` |

`lemma_safe_excludes_trace` は、安全なモデルに、主張の成り立つ有効なトレースが存在しないことを示す。
したがって、同じモデルと検査条件に対する `Verified` と、`Violated` または `Error` は両立しない。

検証済みの実行関数とループは、すべて `decreases` を持つ。
検査器は、モデルと証拠の大きさに対して停止する。

`Verdict` と `CheckedModel` はフィールドが非公開で、`fmspec-core` の外では構築できない。
`fmspec-core` の公開関数は `requires` を持たない。

## 証明が空虚でないことの検査

`rake verus` は、証明を通すだけでなく、次の検査も行う。

- 信頼する項目（`assume`、`admit`、`external_body`、`assume_specification` など）が `fmspec-core` に1つもない。
- 証明の対象外のコードは `impls.rs`（標準トレイトの手書き実装）だけで、判定の経路から呼ばれない。
- 公開関数が `requires` を持たない。
- 検査を1つ壊した変異33件が、すべて証明に失敗する。たとえば、証明書の検査で遷移先の所属を調べない、トレースの状態を照合しない、拒否した証明書で `Verified` を返す、といった変異である。
- 到達点に置いた `assert(false)` 18件が、すべて証明に失敗する。

変異と `assert(false)` の一覧は `rakelib/verus.rake` にある。

## テストで検査するもの

次は証明の対象外で、テストで検査する。

| 対象 | 検査 |
|---|---|
| 幅優先探索（`fmspec-search`） | 手作りのグラフでの訪問状態と最短性、状態数の上限、参照実装との比較 |
| シミュレータ（`fmspec-search`） | 同じ乱数列を使う参照実装との、トレースの比較 |
| 縮小（`fmspec-search`） | 縮小結果は判定ゲートが受理したトレースに限る。最短の反例に達することの確認 |
| MBTのセッション（`fmspec-search`） | 仕様書§17.2.1の境界ケース、参照実装との候補集合の比較 |
| MBTのドライバ（`lib/`） | 意図的にバグを入れた実装での、検出と縮小 |
| IRと証拠の読み書き（`fmspec-ir`） | 不正なIRの拒否、往復、参照実装との比較 |
| CLI（`fmspec-cli`） | 終了コードと出力 |
| Ruby DSL（`lib/`） | 生成したIRと期待するIRの比較、参照実装による意味の確認、誤用の拒否 |
| native extension（`ext/fmspec`） | 中断、他スレッドの動作、複数スレッドからの検査、panicの例外化、引数の検査 |
| 仕様書§17.1.1の境界ケース | Rustのテストと、参照実装のテストの両方 |

参照実装（`reference/fmspec_reference.rb`）は、IRを直接解釈する小さなEvaluator、幅優先探索、証明書検査器で、Rustの実装とは独立に書いてある。
比較テストは、固定のモデルとランダムに生成したモデルについて、結果の種類、報告する事象、トレース、訪問状態、証明書の受理と拒否の理由を突き合わせる。

実装との適合性検査（`Model#test`）の結果は、判定ゲートを通らない。
候補集合の更新は検証済みの遷移列挙器を使うが、更新そのものと、Ruby側のドライバ、Bindingは証明の対象外である。

探索器に不具合があっても、誤った `Verified` や `Violated` にはならない。
探索器が保証しないのは、判定への到達、反例の最短性、探索統計の正しさである。

## 信頼基盤

次は証明の外にあり、正しいものとして信頼している。

- Verus、SMTソルバー（Z3）、Rustコンパイラ、標準ライブラリに対する `vstd` の仕様。
- 通常のcargoビルドでghostコードを消去する、`vstd` とVerusのマクロ。
- IRのJSONから中核のモデルを組み立てる `fmspec-ir`。名前の添字への解決、初期値の符号化、n項の `all` と `any` を二項の式の木にたたむ変換を含む。
- 仕様からIRを生成するRuby DSL。受理と拒否の条件式への変換、定数の埋め込み、記号ブロックの構文検査を含む。
- RubyとRustの境界。Nupur、その下の `nupur_sys` と rb-sys、拡張のグルーコード。
- 結果を表示するCLIと `Fmspec::Result`。

`fmspec-ir` が組み立てたモデルは、必ず中核のIR検証を通る。
証明書とトレースは判定ゲートが検査するので、その読み込みの誤りが誤った `Verified` や `Violated` に変わることはない。
一方、IRの生成や読み込みの誤りは、利用者の意図と違うモデルを検査する結果になる。
これは比較テストとIR変換のテストで検査している。
証明済みの定理は検証済みのIRについてのもので、利用者が書いたRubyの仕様についての主張ではない。
生成されたIRは `Model#to_ir` で確認できる。

## Nupurの写し

RubyのC APIとのやりとりは、Makiriのバインディング層Nupurを通す。
Nupurは公開crateではないので、Makiri v0.17.0.rc3（コミット `9ec094cf`）の `nupur` と `nupur_sys` を `vendor/nupur` に写して同梱している。
写しは編集しない。

| 検査 | 内容 |
|---|---|
| `rake nupur:check` | 写しの各ファイルが、記録したSHA-256（`vendor/nupur.sha256`）と一致する。Makiriのチェックアウトは要らない |
| `rake nupur:upstream` | 記録した内容が、Makiriのチェックアウトにある固定コミットの内容と一致する |
| `rake nupur:lint` | 型で表せないNupurの規則を、固定コミットの `nupur_lints` で拡張に対して検査する |

`nupur_lints` は、GVLを解放した処理の中の `Cancel::requested` も報告する。
これは中断要求を問い合わせるためのNupurの関数だが、lintはNupurの関数を一律に「Ruby-freeと分かっていない」と扱う。
拡張では、この2か所を理由付きの `expect` にしている。
lintが直れば `expect` が満たされなくなり、`rake nupur:lint` が失敗する。

## バージョン

| 対象 | バージョン |
|---|---|
| Verus | 0.2026.10.04.426d8b0（`rakelib/verus.rake` の `VERUS_VERSION`） |
| `vstd`（cargoビルド用） | 0.0.0-2026-11-01-0251 |
| Rust | 1.100.0（cargoビルド）、1.98.1（Verus）、nightly-2026-08-20（`nupur_lints`） |
| Nupur | Makiri v0.17.0.rc3（`rakelib/nupur.rake` の `NUPUR_COMMIT`） |
| Ruby | 3.3以上。開発は4.0.10 |

検証に使うVerusと、cargoビルドに使う `vstd` のリリースは一致していない。
仕様書のスパイクはVerus 0.2026.11.02で行っており、リリースを揃えることは残作業である。

## 既知の制限

- 型はBool、有界Int、Enumに限る。
- 判定ゲートには資源上限と中断がない。証明書の検査は、探索と同じだけの計算をして完了する。Rubyからの割り込みは、探索の間はすぐに効くが、証明書の検査に入ったあとは検査が終わってから例外になる。
- 引数のドメインは値を1つずつ列挙する。広い整数範囲の引数を持つ操作は、列挙に時間がかかる。
- 式の入れ子の深さは、JSONの読み込みの上限（128段）で抑えている。Rust APIから直接組み立てた極端に深い式は、再帰でスタックを使い切る可能性がある。
- CIの設定はまだない。検査は `rake` で実行する。
