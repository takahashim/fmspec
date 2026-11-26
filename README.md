# fmspec

Rubyで書く実行可能な形式仕様と、Rust製の検証エンジンによるモデル検査。

設計は [docs/ruby_model_checker_spec.md](docs/ruby_model_checker_spec.md) にある。
現在の実装は、ロードマップの段階1〜3（中核MVP）である。
Ruby DSL、native extension、シミュレータ、Model-Based Testingはまだない。

## 構成

| 場所 | 内容 |
|---|---|
| `crates/fmspec-core` | Verusで検証する中核。IR検証、Evaluator、遷移列挙、証明書とトレースの検査器、判定ゲート |
| `crates/fmspec-ir` | IR、検査条件、証明書、トレースのJSON表現 |
| `crates/fmspec-search` | 幅優先探索。証拠を生成するだけで、判定は判定ゲートが返す |
| `crates/fmspec-cli` | `fmspec` コマンド |
| `reference/` | 比較テスト用のRubyの参照実装 |
| `examples/models/` | IRの例 |
| `spike/` | 設計時の使い捨ての試作 |

## 使い方

```sh
cargo build
target/debug/fmspec validate examples/models/tickets.json
target/debug/fmspec check examples/models/tickets.json --max-states 100000
target/debug/fmspec check MODEL.json --json --certificate-out CERT.json --trace-out TRACE.json
target/debug/fmspec verify-certificate MODEL.json CERT.json
target/debug/fmspec replay MODEL.json TRACE.json
```

IRと出力の形式は [docs/ir.md](docs/ir.md) にある。

## 検査

```sh
rake test    # Rustのテスト、参照実装のテスト、参照実装との比較テスト
rake verus   # 中核の証明と、証明が空虚でないことの検査
rake lint    # rustfmt と clippy
```

`rake verus` には Verus 0.2026.10.04.426d8b0 が必要で、実行ファイルを環境変数 `VERUS` で指定する。
何を証明し、何を信頼しているかは [docs/verification.md](docs/verification.md) にある。
