# Railsアプリケーションの適合性検査

`fmspec-rails` は、fmspecの仕様をRailsアプリケーションに結合するためのgemである。
DBの変更、Active Jobのキュー、時刻をテストケースの中に閉じ込め、リクエストとジョブの実行を `command` から行えるようにする。
仕様の書き方と `Model#test` は [dsl.md](dsl.md) にある。
設計の背景は[設計仕様書](ruby_model_checker_spec.md)§12にある。

仕様が表すのは、利用者が書いた有限の状態と遷移である。
DBの分離レベルやロック、決済APIの振る舞いは仕様の上の仮定であり、fmspecがそれらの意味論を保証するわけではない。
テストの成功は有限回の照合の成功で、Railsアプリケーション全体の正しさの証明ではない。

## 外部環境を仕様に書く

外部サービスの応答、ジョブの再試行、Webhookの重複は、仕様の操作と内部選択として書く。
次は、注文の決済の仕様の一部である（全体は `fmspec-rails/test/support/checkout_spec.rb`）。

```ruby
Checkout = Fmspec.define(:checkout) do
  # 決済APIの応答。タイムアウトは「決済なし」と「決済済みだが応答喪失」を区別する。
  responses = enum(:response, :ok, :declined, :timeout_lost, :timeout_charged)

  state :status, enum(:status, :pending, :paid, :cancelled), initial: :pending
  state :queued, bool, initial: false
  # 決済APIが実際に行った決済の数。0、1、2以上の3値に飽和させる。
  ghost :charges, int(0..2), initial: 0

  # ワーカーが決済ジョブを実行する。
  action :run_job do |s|
    response = choose(:response, responses)
    guard s.queued & (response.ne(:declined) | s.charges.eq(0))
    calls = s.status.eq(:pending)
    charged = calls & (response.eq(:ok) | response.eq(:timeout_charged))
    update queued: calls & (response.eq(:timeout_lost) | response.eq(:timeout_charged)),
           charges: ite(charged, max(s.charges, 1), s.charges),
           status: ite(calls & response.eq(:ok), :paid, s.status)
  end

  # 決済APIからのWebhook。決済が行われたあとなら、何度でも届きうる。
  action :webhook do |s|
    guard s.charges >= 1
    update status: ite(s.status.eq(:pending), :paid, s.status)
  end

  invariant(:no_double_charge) { |s| s.charges <= 1 }
end
```

`ghost` は**Ghost State**を宣言する。
履歴を記録するための有限の補助状態で、モデル検査では普通の状態変数として扱う。
実装との照合では、期待した回数を代入せず、fakeやDBに残った実際の記録から観測する。

`max(s.charges, 1)` は、再試行の請求が冪等キーによって新しい決済にならないことを表す。
実装が冪等キーを付け忘れると、fakeが記録する決済は2件になり、観測した `charges` が仕様の値と一致しなくなる。

## Binding

```ruby
binding = Fmspec::Rails.bind(Checkout, app: MyApp::Application, records: [Order, Fulfillment]) do
  setup do |c|
    c[:order] = Order.create!(owner_id: 0)
    c[:gateway] = PaymentGateway.client = FakeGateway.new
  end

  command(:checkout) { |c| c.post("/orders/#{c[:order].id}/checkout") }

  command(:run_job, inject: [:response]) do |c, response:|
    c[:gateway].next_response = response
    c.perform_next_job
  end

  command(:webhook) { |c| c.post("/webhooks/payments", params: { order_id: c[:order].id }) }

  observe(:status) { |c| c[:order].reload.status.to_sym }
  observe(:queued) { |c| c.enqueued_jobs.any? }
  observe(:charges) { |c| [c[:gateway].charges.length, 2].min }
end

Checkout.test(binding, cases: 300, steps: 12).assert_passed!
```

`Fmspec::Rails.bind` のブロックの語彙は `Model#bind` と同じである。
`setup`、`teardown`、`command`、`observe` のブロックは、テストケースの実行環境である `Fmspec::Rails::Context` を受け取る。
`setup` は省略できる。

| オプション | 内容 |
|---|---|
| `app:` | Rackアプリケーション。`Context#post` などの送り先 |
| `records:` | 隔離を検査するActive Recordのクラス |
| `isolation:` | `:transaction`（既定）、`:deletion`、`false` |
| `time:` | ケースの開始時刻。`false` なら時刻を固定しない |

### 障害注入

`command` の `inject:` に内部選択の名前を挙げると、その値を実装ではなくテストが決める。
値はブロックにキーワードで渡るので、ブロックはfakeや注入点にそのとおりの振る舞いを指示してから、実装を呼ぶ。
上の例では、決済APIの応答を `FakeGateway` に指示している。

注入した値は、入力の一部として扱う。
候補状態の更新では、注入した値と一致する遷移だけを考える。
失敗の報告と `TestResult#inputs` にも、注入した値が入る。

`inject:` に挙げなかった内部選択は、実装が決めるものとして扱い、テストは観測から候補を絞る。

### Context

| メソッド | 内容 |
|---|---|
| `c[:name]`、`c[:name] = 値` | ケースの中で使う値の置き場 |
| `get`、`post`、`put`、`patch`、`delete` | `app` へのリクエスト。レスポンスを返す |
| `response` | 直前のレスポンス |
| `enqueued_jobs` | キューにあるジョブ |
| `perform_next_job` | キューの先頭のジョブを1つ実行する。再試行を予約したジョブはキューに戻る |
| `travel`、`travel_to` | 時刻を進める |

## 隔離

各テストケースは、新しい `Context` で実行する。
`Context` はケースの始めに次の3つを行い、ケースの終わりに元へ戻す。

- `isolation: :transaction` では、接続にトランザクションを開き、終わりにロールバックする。`:deletion` では、ケースの前後に `records` の行をすべて削除する。
- Active Jobのアダプターを、ケース専用のテスト用アダプターに差し替える。
- 時刻を `time:` に固定する。

ケースの終わりに、`records` の各クラスの行数がケースの前と同じであることと、トランザクションの深さが合っていることを確かめる。
合っていなければ `Fmspec::Rails::IsolationError` を上げ、テストの結果は `:setup_error` になる。
隔離に失敗した実行が、成功として扱われることはない。

`:transaction` が隔離できるのは、ケースの中の変更が同じ接続で行われる場合に限る。
別のスレッドや別の接続、外部のサービスへの変更は、トランザクションでは戻らない。
その場合は `:deletion` と専用のデータ、またはfakeを使う。

メモリ上のSQLiteのように、接続ごとに別のDBになる構成では、複数の接続を使うテストはできない。

## 並行処理と分離レベル

並行するトランザクションは、仕様の `process` と binding の `process` で検査する（[dsl.md](dsl.md) の「並行するプロセス」と「並行するプロセスの実装」）。
各インスタンスは専用のスレッドで動くので、DBの接続もインスタンスごとに分けて持てる。
ステップはテストが選んだ順に1つずつ実行するので、反例のスケジュールを実DBで再現できる。

```ruby
binding = Fmspec::Rails.bind(Withdrawal, records: [Account], isolation: :deletion, time: false) do
  setup { |c| c[:account] = Account.create!(balance: 2) }
  process :withdraw do
    # インスタンスのスレッドで接続を取り、トランザクションを始める。
    setup { |c, _id| Teller.new(c[:account].id, "REPEATABLE READ") }
    teardown(&:close)
    step(:read, method: :read)
    step(:write, method: :write)
    step(:commit, method: :commit)
  end
  observe(:balance) { |c| c[:account].reload.balance }
end
```

分離レベル、ロック、制約は、仕様のステップのguardと更新で書く仮定である。
エンジンがDBの意味を知っているわけではない。
仮定が実DBと合っているかは、適合性検査で確かめる。

- 仕様より強い分離（仕様は成功を求めるが、実DBは直列化に失敗する）や、仕様より弱い分離（仕様は直列化の失敗を求めるが、実DBは成功する）は、戻り値の不一致として見つかる。
- 仕様が書き落としたロックで、実DBのステップが待たされると、そのスケジュールは再現できない。ケースは未完了（`:inconclusive`、理由は `:step_timeout`）になる。

プロセスの接続での変更は、テストのスレッドの接続のトランザクションでは戻らない。
そのため、`process` を使う binding に `isolation: :transaction` は使えず、`Fmspec::BuildError` になる。
`:deletion` と専用のデータ、または専用のDBを使う。

`fmspec-rails/test/isolation_test.rb` に、PostgreSQLでの例がある。
2つのトランザクションが同じ口座から1ずつ引き出す実装を、分離レベルを変えて動かし、分離レベルごとの仕様と照合する。

| 実DBの分離レベル | READ COMMITTED の仕様 | スナップショットの仕様 |
|---|---|---|
| READ COMMITTED | 適合。仕様のとおりに更新が失われ、不変条件の違反（`:model_violation`）に至る | 不適合。直列化の失敗を求める書き込みが成功する |
| REPEATABLE READ、SERIALIZABLE | 不適合。成功を求める書き込みが直列化に失敗する | 適合（`:passed`）。仕様の状態と遷移をすべて覆う |

行のロックを書き落とした仕様では、待たされる書き込みを含むスケジュールが `:step_timeout` になる。
このテストは環境変数 `FMSPEC_PG_DATABASE`（既定は `fmspec_rails_test`）と `FMSPEC_PG_HOST` のDBを使い、なければ作る。
PostgreSQLに接続できなければskipする。

## ジョブのステップとクラッシュ

`Context#perform_next_job` は、ジョブを丸ごと1つの操作として実行する。
ジョブの途中で落ちることや、ジョブの途中に他の操作が割り込むことを検査するには、`job` でジョブを仕様の `process` に結合する。
設計は [rails_jobs_design.md](rails_jobs_design.md) にある。

ジョブの側では、`Fmspec::Rails::Checkpoints` を include し、`perform` の中に `checkpoint` でステップの境界を書く。

```ruby
class ChargeJob < ApplicationJob
  include Fmspec::Rails::Checkpoints
  retry_on PaymentGateway::Timeout, attempts: 3

  def perform(order_id)
    order = Order.find(order_id)
    PaymentGateway.client.charge(order_id: order.id)
    checkpoint :save
    order.update!(status: "paid")
  end
end
```

`perform` の始めから最初の `checkpoint` までが、仕様の最初のステップである。
`checkpoint :save` から次の `checkpoint`（または `perform` の終わり）までが、ステップ `save` である。
`job` の外（本番、普通のテスト）では、`checkpoint` は何もしない。
`checkpoint` はトランザクションの外に書く。
トランザクションの中に書くと、仕様の名前にない `checkpoint` と同じく、`Fmspec::Rails::CheckpointError`（`:execution_error`）になる。

```ruby
binding = Fmspec::Rails.bind(Checkout, records: [Order], isolation: :deletion) do
  setup do |c|
    c[:order] = Order.create!
    c[:gateway] = PaymentGateway.client = FakeGateway.new
  end
  job :job, ChargeJob, crash: :exception, error: PaymentGateway::Timeout,
                       enqueue: ->(c, _id) { ChargeJob.perform_later(c[:order].id) }
  observe(:charges) { |c| [c[:gateway].charges.length, 2].min }
end
```

`job(プロセス, ジョブのクラス, ...)` は、プロセスの `setup`、各ステップ、`crash` と、プログラムカウンタ `job[i].pc` の `observe` を組み立てる。
`process` と同じく、`isolation: :transaction` では使えない。

| オプション | 内容 |
|---|---|
| `crash:` | `:exception`（既定）か `:kill` |
| `error:` | `crash: :exception` で上げる例外のクラス。メッセージを1つ受け取って作れるもの。既定は `Fmspec::Rails::InjectedFailure` |
| `claim:` | `->(payload, id) { ... }`。インスタンスが取り出すジョブを選ぶ。既定は、そのクラスのまだ取り出していない最初のジョブ |
| `enqueue:` | `->(context, id) { ... }`。インスタンスの最初の `setup` でジョブを積む。仕様にジョブを積む操作がないときに使う |
| `timeout:` | `process` と同じ |

各ステップは、`perform` を実行するFiberを、次の `checkpoint` まで進める。
最初のステップで、キューからジョブを取り出す。
ジョブがなければ `Fmspec::Rails::JobNotEnqueued`（`:execution_error`）になる。
`perform` が終わったとき、同じ `job_id` のジョブがキューにあれば（`retry_on` が積み直した）、プログラムカウンタは最初のステップに戻り、次のステップで積み直されたジョブを取り出す。
なければ `:done` である。

クラッシュは、止まっている `checkpoint` から例外を上げる。

- `crash: :exception` は、`error:` の例外を上げ、実装の `retry_on` と `discard_on` に処理させる。積み直されれば最初のステップ、例外が外へ出るか積み直されなければ `:crashed` になる。仕様の `crash: :restart` と `retries:` に対応する。
- `crash: :kill` は、`Fmspec::Rails::Killed`（`Exception` の子）を上げる。`retry_on` は通らない。仕様が `:restart` ならジョブを同じ内容でキューに戻し（止まったワーカーのジョブを拾い直すバックエンド）、`:abort` なら戻さない。仕様の `max_crashes:` か `:abort` と組み合わせる。

`job[i].pc` を観測するので、実装の `retry_on attempts:` と仕様の `retries:` の食い違い、`retry_on` が捕まえない例外、`checkpoint` の書き落としは、観測の不一致になる。

`Killed` は、実際のプロセスの停止と違い、`ensure` を実行する。
`ensure` で行う後始末（ロックの解放など）は、本番では行われないのにテストでは行われる。

`job` に結合したクラスのジョブを `perform_next_job` が取り出せば、`Fmspec::Rails::IsolationError` になる。
`enqueued_jobs` は、`job` が取り出したジョブを含まない。

テストは `fmspec-rails/test/job_test.rb` にある。
`examples/crash/double_charge.rb` の仕様の反例を実装のジョブで再現し、`retry_on attempts:` の変異、`checkpoint` の誤りを検出する。
ジョブはインスタンスのスレッドの接続で動くので、ファイルのSQLiteを使う。

## 代表例と変異

`fmspec-rails/test` に、注文の決済のRailsアプリケーションと、その適合性検査がある。
アプリケーションは、リクエスト（決済の開始、取消）、Active Jobによる決済と再試行、決済APIからのWebhookを持つ。

テストは、正しい実装が適合することに加えて、次の変異を検出することを確かめている。

| 変異 | 一致しない項目 | 縮小後の操作列 |
|---|---|---|
| 拒否した取消が、注文を取り消してしまう | `status` | `cancel(user: 1)` |
| ジョブが冪等キーを付けず、再試行で二重に決済する | `charges` | `checkout`、`run_job(response: :timeout_charged)`、`run_job` |
| 重複したWebhookが、出荷をもう一度指示する | `fulfillments` | `webhook` で終わる4ステップ以内の操作列 |
| 決済APIのタイムアウトで、ジョブが再試行されない | `queued` | `checkout`、`run_job`（タイムアウト） |

## 未対応

- 仕様書§12.1の `requires`、`modifies`。
- コントローラやジョブの雛形からのBindingの生成。
