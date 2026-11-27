# プロセスのクラッシュの例

`process` の `crash:`（[docs/dsl.md](../../docs/dsl.md) の「クラッシュ」）を使った、Railsでよく起きる不具合の例。
各ファイルは、変種ごとに仕様を返す `define` を持つ。
期待する結果は `test/crash_examples_test.rb` にある。
設計の未決事項をこれらの例でどう決めたかは、[docs/crash_design.md](../../docs/crash_design.md) §9 にある。

| ファイル | 内容 | 変種と結果 |
|---|---|---|
| `double_charge.rb` | 決済してから注文を保存するジョブ（`crash: :restart`） | `:naive`、`:check_paid` は二重決済、`:idempotent` は通る |
| `discarded_job.rb` | 再試行が尽きたジョブ（`max_crashes:` と `retries:` の違い） | `:bounded_faults` は通る（不具合が見えない）、`:retries` は注文が pending のまま残る、`:after_discard` は通る |
| `outbox.rb` | 注文の確認メール（`crash: :abort` のリクエストと `crash: :restart` のリレー） | `:enqueue_after_save` はメールが漏れる、`:outbox` は二重に送る、`:dedup` は通る |
| `queue_worker.rb` | キューのワーカーのループ。全体のクラッシュの回数の上限を `on_crash` で書く | 既定は通る、`lose_on_crash: true` はメッセージが失われる |

```ruby
require "fmspec"
require_relative "examples/crash/double_charge"

CrashExamples::DoubleCharge.define(:naive).check.trace.steps.map(&:action)
# => [:"job[0].charge", :"job[0].crash", :"job[0].charge"]
```
