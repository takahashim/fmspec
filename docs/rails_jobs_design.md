# fmspec-rails のActive Job補助（設計案）

Active Jobのジョブを、仕様の `process` のインスタンスとして実行し、ステップの境界で止め、そこで落とす補助の設計案である。
実装した。使い方は [rails.md](rails.md) の「ジョブのステップとクラッシュ」、テストは `fmspec-rails/test/job_test.rb` と `fmspec-rails/test/job_lock_test.rb`（§6.2 のロックの解放。PostgreSQLのadvisory lock）にある。
§10 に、実装で設計から変えたことを書く。
クラッシュの仕様の側は [crash_design.md](crash_design.md) と [dsl.md](dsl.md) の「クラッシュ」にある。

## 1. 動機

いまの `fmspec-rails` は、ジョブを `Context#perform_next_job` で丸ごと実行する（[rails.md](rails.md)）。
ジョブは1つの操作であり、仕様の上ではatomicである。
決済APIのタイムアウトのような「ジョブの中で起きる失敗」は、操作の内部選択と `inject:` で再現できる。

再現できないのは、次の2つである。

- ジョブの**途中**で落ちること。決済を呼んだあと、注文を保存する前に落ちる、など。`crash:` の仕様の反例（`examples/crash/double_charge.rb`）は、このスケジュールを要求する。
- ジョブの途中で、**他のリクエストやジョブが割り込む**こと。`process` のステップのインターリーブにあたる。

コア（`Fmspec::Binding` の `process` と `crash`）は、インスタンスごとのスレッドで、ステップのハンドラを1つずつ実行する。
足りないのは、1つのメソッドである `perform` を、ステップのハンドラの列に分けることである。

## 2. 方針

- **ジョブのコードに境界を書く。** `perform` の中に `checkpoint :save` と書き、仕様のステップ `save` が始まる位置を示す。fmspecの外では何もしない。
- **Fiberで止める。** ステップのハンドラは、`perform` を実行するFiberを次の `checkpoint` まで進めて返る。Fiberはインスタンスのスレッドで動くので、DBの接続もインスタンスごとになる。
- **Active Jobの仕組みをそのまま通す。** 再試行は、実装の `retry_on` が積み直したジョブを、次の実行で取り出す。再試行の回数や、尽きたときの振る舞いを、補助は真似しない。仕様の `retries:` と実装の `retry_on attempts:` が合っているかは、適合性検査で分かるようにする。
- **プログラムカウンタを観測する。** ジョブがどの `checkpoint` で止まっているか、終わったか、捨てられたかを `job[i].pc` として観測し、仕様と照合する。積み直しの有無、`goto` の行き先、`checkpoint` の書き落としが、観測の不一致として見つかる。
- **コアを変えない。** 補助は `Fmspec::Rails::Binding` の上で、`process`、`step`、`crash`、`observe` を組み立てる。

## 3. ジョブの側

```ruby
class ChargeJob < ApplicationJob
  include Fmspec::Rails::Checkpoints
  retry_on PaymentGateway::Timeout, attempts: 3

  def perform(order_id)
    order = Order.find(order_id)
    PaymentGateway.client.charge(order_id: order.id, idempotency_key: "order-#{order.id}")
    checkpoint :save
    order.update!(status: :paid)
  end
end
```

| 語彙 | 意味 |
|---|---|
| `checkpoint(ステップ)` | ここから、仕様のステップ `ステップ` が始まる。fmspecの補助の外（本番、普通のテスト）では何もしない |

`perform` の始めから最初の `checkpoint` までが、仕様の最初のステップである。
`checkpoint` から次の `checkpoint`（または `perform` の終わり）までが、その名前のステップである。
`goto` で最初のステップに戻るループでは、ループの先頭に最初のステップの名前の `checkpoint` を書いてよい。

`checkpoint` は、トランザクションの中に書けない。
補助の下でトランザクションの中の `checkpoint` に達すると、`Fmspec::Rails::CheckpointError` を上げる（結果は `:execution_error`）。
仕様のステップはatomicで、クラッシュはステップの間でだけ起きる。
トランザクションの途中で止めると、この仮定と実装が食い違うからである。

`checkpoint` の名前が仕様のステップにないときも、`CheckpointError` を上げる。

## 4. Bindingの側

```ruby
binding = Fmspec::Rails.bind(Checkout, app: CheckoutApp, records: [Order], isolation: :deletion) do
  setup do |c|
    c[:order] = Order.create!(owner_id: 0)
    c[:gateway] = PaymentGateway.client = FakeGateway.new
  end

  command(:checkout) { |c| c.post("/orders/#{c[:order].id}/checkout") } # ChargeJob を積む

  job :job, ChargeJob, crash: :exception, error: PaymentGateway::Timeout

  observe(:charges) { |c| [c[:gateway].charges.length, 2].min }
  observe(:paid) { |c| c[:order].reload.paid? }
end
```

`job(プロセス, ジョブのクラス, **オプション)` は、仕様の `process` を、そのクラスのジョブに結合する。
次のものを組み立てる。

- `process` の `setup`：インスタンスの実行器（§5）を作り、Contextに登録する。
- 仕様のすべてのステップの `step`：実行器を次の `checkpoint` まで進める。
- 仕様に `crash:` があれば `crash`：§6 のとおりに落とす。
- `observe(:"job[i].pc")`：実行器のプログラムカウンタ。

| オプション | 内容 |
|---|---|
| `crash:` | `:exception`（既定）か `:kill`。§6 |
| `error:` | `crash: :exception` で上げる例外のクラス。実装の `retry_on` が捕まえるクラスを渡す。既定は `Fmspec::Rails::InjectedFailure`（`StandardError` の子） |
| `claim:` | ジョブの取り出し方。既定は、キューの中で、そのクラスのまだ取り出していないジョブの先頭。`->(payload, id) { ... }` で、インスタンスの番号に合うジョブを選べる |
| `enqueue:` | `->(c, id) { ... }`。インスタンスの `setup` でジョブを積む。仕様にジョブを積む操作がないときに使う |
| `timeout:` | `process` と同じ |

`job` は `process` の糖衣なので、`process` と同じく `isolation: :transaction` では使えない（[rails.md](rails.md) の「並行処理と分離レベル」）。

## 5. 実行器

インスタンスごとに、実行器（`Fmspec::Rails::JobRunner`）を1つ作る。
実行器は、取り出したジョブの内容（payload）と、`perform` を実行するFiberと、プログラムカウンタを持つ。

### 5.1 ステップ

ステップのハンドラは、次のことをする。

1. Fiberがなければ、キューからジョブを取り出し（`claim:`）、`ActiveJob::Base.execute` を実行するFiberを作る。ジョブがなければ `Fmspec::Rails::JobNotEnqueued` を上げる（`:execution_error`）。仕様のguardが「ジョブが積まれている」を表していれば、実装がジョブを積み忘れた不具合である。
2. Fiberを進める。`checkpoint` で止まれば、プログラムカウンタをその名前にして返る。
3. `perform` が終われば、キューに同じ `job_id` のジョブがあるかを見る。あれば再試行が予約されたので、プログラムカウンタを最初のステップにし、Fiberを捨てる（次のステップで積み直されたジョブを取り出す）。なければ `:done` にする。
4. `perform` から例外が出れば、そのまま上げる（`:execution_error`）。

3 により、ステップの中で起きた失敗（fakeが上げたタイムアウトなど）で `retry_on` が積み直したことも、プログラムカウンタが最初のステップに戻ることとして観測される。
仕様でこれを表すには、そのステップに `goto 最初のステップ, 失敗の条件` を書く。

### 5.2 観測

`job[i].pc` の観測は、実行器のプログラムカウンタである。
`setup` の直後は最初のステップ、§5.1、§6 の後はそこで決めた値になる。
仕様は、各操作のあとに `job[i].pc` を照合する。

| 実装の誤り | 不一致として見つかる時点 |
|---|---|
| `retry_on` の `attempts:` が仕様の `retries:` より少ない | 最後の再試行のクラッシュ。仕様は最初のステップ、実装は `:crashed` |
| `retry_on` の `attempts:` が仕様の `retries:` より多い | 再試行が尽きたあとのクラッシュ。仕様は `:crashed`、実装は最初のステップ |
| `retry_on` が落ちた例外を捕まえない | 最初のクラッシュ（`:execution_error` ではなく、`:crashed` との不一致） |
| `checkpoint` を書き落とした、別の位置に書いた | そのステップのあと。仕様は次のステップ、実装はその次のステップか `:done` |

## 6. クラッシュ

`crash:` は、実装がどう落ちるかを選ぶ。
2つは、Railsで起きる別の現象にあたる。

### 6.1 `crash: :exception`

止まっている `checkpoint` から、`error:` の例外を上げる。
例外は `perform` の外へ伝わり、実装の `retry_on` と `discard_on` が処理する。

- `retry_on` が積み直せば、プログラムカウンタを最初のステップにする。
- 例外が `ActiveJob::Base.execute` の外へ出れば（`retry_on` の回数が尽きた）、または積み直さずに終われば（`discard_on`）、`:crashed` にする。仕様に `:crashed` がなければ、観測の不一致になる。

これは、`perform` の中で例外が起きること、つまりアプリケーションが知っている失敗である。
仕様の `crash: :restart` と `retries:` に対応する。

### 6.2 `crash: :kill`

止まっている `perform` を再開せずに捨てる。
`rescue`、`retry_on`、`discard_on`、`ensure` のどれも動かない。
Rubyは、再開しないまま回収したFiberの `ensure` を実行しない。
`perform` が使っていたDBの接続は、接続プールから外して切る。
接続は、`checkpoint` で止まる時点に、Fiberの中から全接続プールの現在の接続として記録しておく。
そのあと、仕様が `crash: :restart` なら、取り出したジョブを同じ内容（`executions` を増やさない）でキューに戻す。
`crash: :abort` なら戻さない。
プログラムカウンタは、戻せば最初のステップ、戻さなければ `:crashed` である。

これは、ワーカーのプロセスが止まること（デプロイ、OOM、SIGKILL）である。
キューに戻すのは、Solid Queueやsuper_fetchのように、止まったワーカーのジョブを別のワーカーが拾い直すバックエンドにあたる。
戻さないのは、取り出したジョブを失うバックエンドにあたる。
どちらを仮定するかは、仕様の `crash:` で決める。
再試行の回数を数えるのはバックエンドなので、`crash: :kill` は仕様の `max_crashes:` と組み合わせる。

プロセスが止まると、Rubyのコードは何も実行されず、DBの接続が切れる。
DBは、切れた接続のセッションのロック（PostgreSQLのadvisory lockなど）を解放し、確定していないトランザクションを捨てる。
接続を切るのは、この振る舞いを実DBに起こさせるためである。
接続をプールに返すだけだと、セッションが残り、ロックも残る。
トランザクションは `checkpoint` の外にしかないので（§3）、捨てるトランザクションは普通はない。

テストのプロセスは止まらないので、次の差は残る。

- Rubyのプロセスの中の資源（`Mutex`、メモリ上のキャッシュ）は、捨てたFiberが持ったままになる。本番では、プロセスごと消える。`checkpoint` をまたいで `Mutex` を持つジョブでは、他のインスタンスが待たされ、`:step_timeout` になる。プロセスの間で共有するロックは、DBやRedisで持つ。
- `ActiveSupport::CurrentAttributes` やexecutorの状態は、インスタンスのスレッドに残る。そのスレッドはクラッシュのあとで終わり、再起動は新しいスレッドで始まるので、次の実行には持ち越さない。

### 6.3 後始末

`crash: :exception` では、Fiberは `perform` の外まで巻き戻ってから終わる。
`crash: :kill` では、Fiberを捨てる。
コアの `crash` の規則どおり、落ちたインスタンスの `teardown` は呼ばない。
テストケースの終わりに `checkpoint` で止まったままの実行器は、`teardown` で `Fmspec::Rails::Killed`（`Exception` の子）を上げて巻き戻す。
これはクラッシュではなく後始末なので、`ensure` を実行してよい。

## 7. 既存の補助との関係

- `Context#perform_next_job` は残す。ジョブをatomicな1つの操作として扱う仕様（`fmspec-rails/test/support/checkout_spec.rb` の `run_job`）は、そのまま使える。
- 同じクラスのジョブを、`job` と `perform_next_job` の両方で実行しない。`job` の実行器が取り出す前のジョブを `perform_next_job` が実行すると、仕様と実装がずれる。`job` に結合したクラスのジョブを `perform_next_job` が取り出せば、`Fmspec::Rails::IsolationError` を上げる。
- `Context#enqueued_jobs` は、実行器が取り出したジョブを含まない。

## 8. テストの計画

`fmspec-rails/test/support` に、`examples/crash/double_charge.rb` と同じ仕様のRailsアプリケーション（`ChargeJob` と注文のDB）を置き、次を確かめる。

- 冪等キーを渡さない実装で、`crash: :exception` の反例のトレースを `replay:` に渡すと、実装も二重に決済する（`:model_violation`）。
- 冪等キーを渡す実装は、`:idempotent` の仕様に適合する（`:passed`）。
- `retry_on attempts:` を仕様の `retries:` と変えた変異が、`job[0].pc` の不一致になる。
- `checkpoint` をトランザクションの中に書いた変異が、`CheckpointError` になる。
- `crash: :kill` で、仕様が `:restart` ならジョブがキューに戻り、`:abort` なら戻らない。
- テストケースの終わりに、DBの行とキューが残らない。

プロセスはインスタンスごとに別の接続を使うので、メモリ上のSQLiteではなく、SQLiteのファイルDBで動かす。
PostgreSQLのテストと違い、環境がなくてもskipしない。

## 9. 未決事項

- `retry_on` の `wait:` で予約した時刻を、`travel` と結び付けるか。いまの案では、時刻を見ずに取り出す。
- ジョブが別のジョブを積む場合（`perform` の中の `perform_later`）に、積まれたジョブを別の `job` のインスタンスに結び付ける方法。`claim:` で足りるか。
- `checkpoint` の名前と仕様のステップの対応を、テストの前に静的に検査できるか（Prismで `perform` を読む）。
- Sidekiqのように、Active Jobを通さないジョブへの対応。

## 10. 実装で決めたこと

- `Checkpoints` を include すると、`before_perform` でも止まる。これにより、最初のステップの前（`crash_at:` に最初のステップを含めたとき）でも、`retry_on` を通して落とせる。`before_perform` の例外は `retry_on` が処理する。
- 実行器はインスタンスごとに Context に1つ置き、再起動したインスタンスのスレッドでも同じものを使う。積み直されたジョブを、同じ `job_id` で取り出すためである。
- `perform` の中で別のジョブを `perform_now` しても、取り出したジョブ（`job_id` が同じもの）の `checkpoint` でだけ止まる。
- トランザクションの中かどうかは、`checkpoint` の時点で、Fiberの中から全接続プールの現在の接続を見て判定する。`isolation_level` が `:fiber` の構成でも、ジョブの接続を見るためである。
- `crash: :exception` で上げた例外を、ジョブ自身が `rescue` して次の `checkpoint` まで進んだときは、そこをプログラムカウンタにする。仕様と食い違えば、観測の不一致になる。
- `Checkpoints` を include していないジョブを `job` に結合すると、最初のステップで `CheckpointError` になる。
- `crash: :kill` は、当初 `checkpoint` から `Killed` を上げていたが、それでは `ensure` が実行され、本番では起きない後始末がテストで起きた。`perform` を再開せずに捨て、DBの接続を切る方式に変えた（§6.2）。`fmspec-rails/test/job_test.rb` で、`ensure` が実行されないこと、接続が切れてプールから外れることを確かめる。
