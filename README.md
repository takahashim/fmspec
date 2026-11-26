# fmspec

Rubyで書く実行可能な形式仕様と、Rust製の検証エンジンによるモデル検査。

設計は [docs/ruby_model_checker_spec.md](docs/ruby_model_checker_spec.md) にある。
現在の実装は、ロードマップの段階1〜6（Rails向け初期リリースの範囲）である。
Rubyで仕様を書いて、モデル検査、シミュレーション、実装との適合性検査（Model-Based Testing）ができる。
状態と引数には、Bool、有界Int、Enumのほか、Tuple、Record、Option、有限Set、有限Map、有界Listを使える。
Railsアプリケーションとの結合は、別gemの `fmspec-rails` にある。
モデル合成、並行処理、有界応答性はまだない。

```ruby
require "fmspec"

Tickets = Fmspec.define(:tickets) do
  state :sold, int(0..4), initial: 0
  constant :capacity, 3

  action :purchase, quantity: 1..2 do |s, quantity|
    guard s.sold + quantity <= s.capacity
    update sold: s.sold + quantity
  end

  action :cancel do |s|
    guard s.sold > 0
    update sold: s.sold - 1
  end

  invariant(:capacity_respected) { |s| s.sold <= s.capacity }
end

result = Tickets.check(max_states: 10_000)
result.status # => :verified

binding = Tickets.bind do
  setup { BoxOffice.new(capacity: 3) }
  command(:purchase) { |office, quantity:| office.sell(quantity) }
  command(:cancel, method: :refund)
  observe(:sold) { |office| office.sold }
end

Tickets.test(binding, cases: 100, steps: 20).assert_passed!
```

DSLの説明は [docs/dsl.md](docs/dsl.md) に、Railsアプリケーションとの結合は [docs/rails.md](docs/rails.md) にある。

## 構成

| 場所 | 内容 |
|---|---|
| `lib/` | Ruby DSL。仕様からIRを生成し、native extensionで検査する |
| `ext/fmspec` | native extension。Nupurを通してRubyとやりとりする |
| `crates/fmspec-core` | Verusで検証する中核。IR検証、Evaluator、遷移列挙、証明書とトレースの検査器、判定ゲート |
| `crates/fmspec-ir` | IR、検査条件、証明書、トレースのJSON表現。複合型を中核の式に下ろす |
| `crates/fmspec-search` | 幅優先探索とシミュレータ。証拠を生成するだけで、判定は判定ゲートが返す |
| `crates/fmspec-api` | JSONレベルのAPI。CLIとnative extensionが共有する |
| `crates/fmspec-cli` | `fmspec` コマンド |
| `fmspec-rails/` | Rails統合の別gem。DBの隔離、Active Job、リクエスト、時刻の固定 |
| `vendor/nupur` | MakiriのNupurの写し。編集しない |
| `reference/` | 比較テスト用のRubyの参照実装 |
| `examples/models/` | IRの例 |

## コマンド

```sh
cargo build
target/debug/fmspec validate examples/models/tickets.json
target/debug/fmspec check examples/models/tickets.json --max-states 100000
target/debug/fmspec simulate examples/models/tickets.json --traces 100 --max-steps 20 --seed 42
target/debug/fmspec check MODEL.json --json --certificate-out CERT.json --trace-out TRACE.json
target/debug/fmspec verify-certificate MODEL.json CERT.json
target/debug/fmspec replay MODEL.json TRACE.json
target/debug/fmspec shrink MODEL.json TRACE.json --trace-out SHORT.json
```

IRと出力の形式は [docs/ir.md](docs/ir.md) にある。

## 検査

```sh
rake compile       # native extension をビルドして lib/fmspec に置く
rake test          # Rustのテスト、参照実装のテスト、参照実装との比較テスト、Rubyのテスト、fmspec-railsのテスト
rake verus         # 中核の証明と、証明が空虚でないことの検査
rake lint          # rustfmt と clippy
rake nupur:check   # Nupurの写しが、固定したコミットの内容と一致することの検査
rake nupur:lint    # Makiriの nupur_lints を拡張に対して実行する
```

`rake test:rails` の前に、`fmspec-rails` で `bundle install` を実行しておく。
`rake verus` には Verus 0.2026.10.04.426d8b0 が必要で、実行ファイルを環境変数 `VERUS` で指定する。
`rake nupur:lint` には、Makiriのチェックアウト（環境変数 `MAKIRI`、既定は `../makiri`）と cargo-dylint が必要である。
何を証明し、何を信頼しているかは [docs/verification.md](docs/verification.md) にある。
