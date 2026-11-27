# プロセスのクラッシュの自動生成（設計案）

`process` のステップの境界で、インスタンスがクラッシュする遷移を自動で加える機能の設計案である。
§3と§4（検査側）は実装した。使い方は [dsl.md](dsl.md) の「クラッシュ」にある。
§5（実装との適合性検査）も実装した。
§9に、例（`examples/crash/`）で決めたことを、§10に残りの未決事項を書く。

## 1. 動機

Railsの不具合には、「途中で落ちる」ことで起きるものが多い。

- 決済APIを呼んだあと、注文を保存する前にワーカーが落ち、Active Jobの再試行で二重に決済する。
- 注文を保存したあと、メール送信のジョブを積む前にリクエストが落ち、メールが送られない。
- Advisory lockを取ったあとに接続が切れる。

いまのfmspecでも、これらは書ける。
落ちる場合を表す操作を、自分で書けばよい（仕様書§12.3）。
しかし、書く人が「ここで落ちうる」と気づかなければ、モデルに現れない。
ステップが多くなると、落ちる位置の組み合わせを漏れなく書くのは手間でもある。

FizzBee（<https://github.com/fizzbee-io/fizzbee>）は、この問題を既定の振る舞いで解いている。
アクションの文と文の間を割り込みの点（yield point）とし、`crash_on_yield: true`（既定）なら、その点でスレッドが落ちる場合をすべて探索する。
ロールの状態は、クラッシュで失われるもの（ephemeral）と残るもの（durable）に分けられ、失われるものは初期値に戻る。

fmspecの `process` は、すでにステップをatomicな単位として区切っている。
ステップの境界をクラッシュの点にすれば、同じ考え方を、中核を変えずに取り込める。

## 2. 方針

- **中核を変えない。** クラッシュは、DSLが生成する普通の操作である（仕様書§12.6）。IR、Evaluator、判定ゲート、証明書、トレースの形式は変えない。
- **明示的に有効にする。** FizzBeeと違い、既定では無効とする。`process` ごとに `crash:` で指定する。既存の仕様の状態空間と、TLCとの比較テストの結果を変えないためである。
- **ステップはatomicのままにする。** クラッシュはステップの間でだけ起きる。ステップの途中で落ちる場合は、ステップがDBのトランザクションのように全体として起きないことと同じとみなす。トランザクションの外の副作用（外部APIの呼び出し、ジョブの投入）の前後で落ちる場合を見たければ、そこでステップを分ける。
- **共有の状態変数は残る。** 共有の状態変数はDBや外部サービスの状態であり、クラッシュで変わらない。ローカル変数はプロセスのメモリであり、再起動で初期値に戻る。
- **回数に上限を置く。** 再起動するクラッシュは、回数の上限を状態に持つ。

## 3. DSL

```ruby
Checkout = Fmspec.define(:checkout) do
  state :charges, int(0..2), initial: 0 # 決済サービス側の決済の回数
  state :paid, bool, initial: false     # DBの注文の支払い済みフラグ

  process :job, crash: :restart, max_crashes: 1 do
    step(:charge) { |s| update charges: min(s.charges + 1, 2) }
    step(:save) { |s| update paid: true }
  end

  invariant(:charged_at_most_once) { |s| s.charges <= 1 }
end

Checkout.check.trace.steps.map(&:action)
# => [:"job[0].charge", :"job[0].crash", :"job[0].charge"]
```

`charge` のあと `save` の前に落ち、再試行で `charge` をもう一度実行して、二重に決済する。
決済に冪等キーを渡す（決済サービス側の状態で、すでに決済したかを見る）ように直すと、検査が通る。

### 3.1 `process` のオプション

| オプション | 内容 |
|---|---|
| `crash: :abort` | クラッシュしたインスタンスは、そこで終わる。再試行のないWebリクエストにあたる |
| `crash: :restart` | クラッシュしたインスタンスは、最初のステップからやり直す。ローカル変数は初期値に戻る。Active Jobの再試行にあたる |
| `crash_at: [ステップ, ...]` | クラッシュしうる位置。プログラムカウンタがそのステップのとき（そのステップを実行する前）に落ちうる。既定は、最初のステップを除くすべてのステップ |
| `max_crashes: n` | `:restart` のとき、インスタンスごとのクラッシュの回数の上限。既定は1。環境についての仮定で、上限を超えて落ちる実行は検査しない |
| `retries: n` | `:restart` のとき、実装が再試行する回数。尽きたあとに落ちると、インスタンスは `:crashed` で終わる（Active Jobの `retry_on attempts:` で、ジョブを捨てること）。`max_crashes:` とは一緒に書けない |

`crash:` を書かなければ、いままでと同じである。

`crash_at:` の既定から最初のステップを除くのは、最初のステップの前に落ちることは、`:abort` ではプロセスが始まらなかったこと、`:restart` では何も変わらないことになるからである。
`goto` で最初のステップに戻るループでも、既定は変えない（§9.5）。
最初のステップの前で落ちる場合を見たければ、`crash_at:` に最初のステップを含める。

### 3.2 ローカル変数とクラッシュの後始末

| 語彙 | 内容 |
|---|---|
| `local(名前, 型, initial: 値, durable: true)` | `:restart` のとき、クラッシュしても初期値に戻さないローカル変数。ジョブの引数のように、永続化された値にあたる。既定は `false` |
| `on_crash { \|s\| ... }` | クラッシュの遷移の中身。記号ブロックで、`update`、`unchanged`、`choose`、`guard`、`ensures`、`preserves` を使える。`returns` と `goto` は使えない |

`on_crash` は、クラッシュで環境に起きることを書く。
たとえば、接続が切れるとDBがadvisory lockを解放する。

```ruby
process :worker, count: 2, crash: :abort do |id|
  step(:lock) { |s| guard s.holder.eq(-1); update holder: id }
  step(:work) { |s| update count: s.count + 1 }
  step(:unlock) { |_s| update holder: -1 }
  on_crash { |s| update holder: ite(s.holder.eq(id), -1, s.holder) }
end
```

`on_crash` を書かなければ、クラッシュは共有の状態変数を変えない。
`on_crash` の `guard` は、落ちうる状況をさらに絞る。

### 3.3 記号的な状態からの参照

| 書き方 | 内容 |
|---|---|
| `s.job[0].crashed` | `:abort` か `retries:` で、インスタンスがクラッシュして終わった |
| `s.job[0].crashes` | `:restart` で、インスタンスがクラッシュした回数 |
| `s.job[0].done` | いままでどおり、最後のステップまで実行して終えた。クラッシュして終わったときは偽 |

`crashed`、`crashes`、`crash` は、ステップとローカル変数の名前に使えない。

## 4. 基本のIRへの展開

`process :job, count: n` のインスタンス `job[i]` ごとに、次を加える。

| `crash:` | 状態変数 | 操作 `job[i].crash` |
|---|---|---|
| `:abort` | プログラムカウンタの列挙型 `job.pc` に、ラベル `:crashed` を加える | guard は「`job[i].pc` が `crash_at:` のどれか」と `on_crash` のguardの連言。更新は `job[i].pc := :crashed` と `on_crash` の更新 |
| `:restart` | `job[i].crashes`（`int(0..max_crashes)`、初期値0） | guard は「`job[i].pc` が `crash_at:` のどれか」、「`job[i].crashes < max_crashes`」、`on_crash` のguardの連言。更新は、`job[i].pc` を最初のステップに、`durable: true` でないローカル変数を初期値に、`job[i].crashes` を1増やす更新と、`on_crash` の更新 |
| `:restart`、`retries: n` | `job.pc` にラベル `:crashed` を加え、`job[i].crashes`（`int(0..n)`、初期値0）を加える | guard は「`job[i].pc` が `crash_at:` のどれか」と `on_crash` のguardの連言（回数を含めない）。更新は、`job[i].crashes < n` なら `:restart` と同じ更新、そうでなければ `job[i].pc := :crashed`（ローカル変数と回数は変えない）。`on_crash` の更新は、どちらの場合も加える |

ほかに、次のことを決める。

- クラッシュの操作は公開引数を持たない。`on_crash` の `choose` は、操作の内部選択になる。
- `initial_in:` のローカル変数を初期値に戻すときは、候補から選ぶ内部選択にする。内部選択の名前は、ローカル変数の名前である。
- `on_crash` の更新とローカル変数の初期化が同じ変数を更新すれば、`Fmspec::BuildError` にする（ローカル変数は `on_crash` で更新できない）。
- `terminal` を書かないときの終端条件は、「すべてのインスタンスが `:done` か `:crashed`」になる。`:crashed` のない `:restart`（`max_crashes:`）では、いままでどおり「すべてのインスタンスが `:done`」である。
- `on_crash` の `ensures` は、クラッシュの操作の遷移契約になる。名前には、ステップの遷移契約と同じくインスタンスの接頭辞が付く。

クラッシュの操作は普通の操作なので、次のものはそのまま使える。

- 検査条件 `actions:` で、クラッシュの操作を検査の対象から外せる。`check(actions: ...)` で、クラッシュのある場合とない場合を比べられる。
- トレース、反例の縮小、シミュレーション、証明書の検査。
- `Fmspec.compose` は、クラッシュの操作にも名前空間の接頭辞を付ける。クラッシュの操作は `sync` に使えない（同期して落ちる、という意味がないため）。
- 有界応答性の `counting:` に、クラッシュの操作を含めるかどうかを選べる。`:abort` で義務を残したまま終われば、`on_terminal: :violation` の違反として見つかる。メールが送られない、という不具合はこの形で見つかる。
- 参照実装との比較テストと、TLA+への変換。

## 5. 実装との適合性検査

実装でクラッシュを再現するために、bindingの `process` に `crash` を加える。

```ruby
binding = Checkout.bind do
  setup { FakePaymentGateway.new }

  process :job do
    setup { |gateway, id| CheckoutJob.new(gateway, order_id: id) }
    step(:charge, method: :charge)
    step(:save, method: :save)
    crash { |job| job.abandon! } # 接続を閉じ、メモリ上の状態を捨てる
  end

  observe(:charges) { |gateway| gateway.charges }
end
```

| 語彙 | 意味 |
|---|---|
| `crash { \|instance\| ... }` | クラッシュのハンドラ。インスタンスのスレッドで実行する。`method:` と `inject:` は `command` と同じ |

テストがクラッシュの操作を選ぶと、次のことをする。

1. インスタンスのスレッドで `crash` のハンドラを実行する。
2. ハンドラが成功すれば、スレッドを終える。そのインスタンスのコンテキストに `teardown` は呼ばない。後始末をしないことがクラッシュだからである。接続を閉じるなど、資源の解放はハンドラが行う。ハンドラが例外を上げれば `:execution_error` で、スレッドは残し、テストケースの終わりに `teardown` を呼ぶ。
3. `:restart` で再試行が残っていれば（`retries:` なら、そのインスタンスのクラッシュの回数が `retries` 以下なら）、新しいスレッドで `process` の `setup` を同じ番号でもう一度呼び、以後のステップをそのスレッドで実行する。`:abort` と、再試行が尽きたあとは、`setup` を呼ばない。

再試行が残っているかは、そのテストケースで実行したクラッシュの回数で決める。
仕様の `job[i].crashes` と同じ数え方なので、観測しなくても候補によって変わらない。
再起動の `setup` が例外を上げれば、そのクラッシュの操作の `:execution_error` になる。
クラッシュのハンドラも `timeout:` の対象で、時間内に終わらなければ `:inconclusive`（理由は `:step_timeout`）である。

`crash` を登録しない `process` で仕様がクラッシュの操作を持つときは、ほかの操作の `command` がないときと同じく `Fmspec::BuildError` にする。
`crash:` のないプロセスに `crash` を登録しても `Fmspec::BuildError` である。
クラッシュをテストしないなら、`crash` を登録したうえで、`test(actions: ...)` で対象から外す。
暗黙に外すことはしない。

テストは `test/crash_mbt_test.rb` にある。
二重決済の反例のトレースを実装で再現すること、冪等でない実装が冪等な仕様と合わないこと、落ちたスレッドの `teardown` を呼ばず新しいスレッドで `setup` を呼ぶこと、再試行が尽きたら `setup` を呼ばないこと、`on_crash` の環境の変化（ロックの解放）を実装が起こさなければ不適合になることを検査する。

Railsでは、`fmspec-rails` の補助として、Active Jobを途中で落とし、再投入する仕組みを別に設計する（未定）。

## 6. 検証と信頼

- 中核の証明と信頼基盤は変わらない。展開した操作を、中核は他の操作と区別しない。
- 展開の正しさは、DSLの変換のテストで検査する（仕様書§12.6）。同じ仕様を、クラッシュの操作を手で書いた仕様と比べ、IRが一致することと、検査の結果が一致することを確かめる。
- 仕様書§12.6の表に、「クラッシュ → プログラムカウンタとローカル状態のリセット、またはラベル `:crashed` への遷移」を加える。
- クラッシュはステップの間でだけ起きる、という仮定を、`docs/dsl.md` に明記する。ステップの区切り方が、何を検査したかを決める。

## 7. 状態空間への影響

- `:abort` は、インスタンスごとにプログラムカウンタの値を1つ増やす。クラッシュの位置の数だけ遷移が増える。
- `:restart` は、インスタンスごとに `max_crashes + 1` 倍まで状態が増えうる。`max_crashes:` の既定を1にするのはこのためである。
- `count:` の大きいプロセスでは、全インスタンスで落ちうる組み合わせが増える。必要なら `crash_at:` で位置を絞る。

## 8. FizzBeeとの違い

| | FizzBee | fmspec（本案） |
|---|---|---|
| 既定 | 有効（`crash_on_yield: true`） | 無効。`process` ごとに `crash:` で有効にする |
| クラッシュの位置 | `serial` の文と文の間。`atomic` の中では起きない | ステップの間。ステップは常にatomic |
| 失われる状態 | ロールの `ephemeral` のフィールド（既定はすべてdurable） | `:restart` のローカル変数（既定は失われる。`durable: true` で残す）。共有の状態変数は残る |
| 再起動 | ロールのクラッシュ後、ephemeralなフィールドを `Init` の値に戻す | `:restart` で最初のステップから。`:abort` では終わる |
| 回数 | 公平性の仮定と `assume` で扱う | `max_crashes:`（環境の仮定）か `retries:`（実装の再試行）で、回数を状態に持つ |
| 環境の後始末 | なし（明示的にモデル化する） | `on_crash` |
| メッセージの消失 | ロール間のRPCで自動 | 対象外。fmspecにRPCの語彙はない |
| 結果の検査 | 検査器を信頼する | 判定ゲートが証明書とトレースを検査する（変わらない） |

FizzBeeが既定で有効にしているのは、「起きうる障害を書き忘れる」ことを防ぐためである。
fmspecで既定を無効にする代わりに、`process` に `crash:` がないことを警告する仕組み（`Fmspec::Lint` か、検査の報告）を検討する（§9）。

## 9. 例で決めたこと

`examples/crash/` に、Railsでよく起きる4つの例を書き、`test/crash_examples_test.rb` で結果を固定した。
状態数は、探索器が報告した到達状態の数である。

| 例 | 内容 |
|---|---|
| `double_charge.rb` | 決済してから注文を保存するジョブ。素朴な版と、支払い済みを見て飛ばす版は二重に決済し、冪等キーの版は検査が通る |
| `discarded_job.rb` | 再試行が尽きたジョブ。`max_crashes: 2` では検査が通り、`retries: 2` では注文が pending のまま残る反例が出る。捨てるときに注文を failed にすると通る |
| `outbox.rb` | 注文の確認メール。保存してからジョブを積むとメールが漏れ（有界応答性の違反）、Outboxにするとリレーの再起動で二重に送り、メールサービスの冪等キーで通る |
| `queue_worker.rb` | キューのワーカーのループ。落ちたときに処理中のメッセージをキューに戻さないと、メッセージが失われる |

### 9.1 `max_crashes:` はインスタンスごとにする

ワーカー2つの `queue_worker.rb` で、状態数は次のとおりだった。

| 回数の上限 | 状態数（ワーカー2つ） | 状態数（ワーカー3つ） |
|---|---|---|
| ワーカーごとに1回 | 120 | 533 |
| ワーカーごとに2回 | 382 | — |
| 全体で1回（ワーカーごとは2回まで） | 75 | 189 |

全体の上限のほうが状態は少ない。
しかし、全体の上限は `on_crash` の guard と共有の状態変数で書ける（`queue_worker.rb` の `budget:`）。

```ruby
state :faults, int(0..1), initial: 0
process :worker, count: 2, crash: :restart, max_crashes: 2 do
  # ...
  on_crash do |s|
    guard s.faults < 1
    update faults: s.faults + 1
  end
end
```

一方、再試行の回数（`retries:`）はジョブごとの性質で、インスタンスごとに数えるしかない。
`max_crashes:` と `retries:` の数え方を揃え、インスタンスごとにする。
全体の上限の語彙は、同じ書き方が繰り返し現れてから足す。

### 9.2 再開の位置は最初のステップに固定する

`double_charge.rb` の `:check_paid` は、最初のステップで注文が支払い済みかを見て、済んでいれば終える（`goto :done`）。
それでも二重決済は防げない。
決済のあと、保存の前に落ちると、注文は支払い済みになっていないからである。
防げたのは、決済サービス側の状態（冪等キー）を見る `:idempotent` だけだった。

途中から再開したように見える実装は、永続化された状態を見て処理を飛ばしている。
それは仕様でも、最初のステップの guard と `goto` で書ける。
Active Jobの再試行も `perform` の最初からやり直すので、`restart_at:` は足さない。

### 9.3 再試行が尽きたあとを `retries:` で表す

`discarded_job.rb` で、`max_crashes: 2` の版は検査が通り、`retries: 2` の版は反例が出た。
`max_crashes:` は「3回目は落ちない」という環境の仮定で、ジョブは必ず最後まで進む。
実装はそうではなく、3回目に落ちればジョブを捨てる。
捨てられたジョブの注文が pending のまま残る不具合は、`max_crashes:` では見えない。

そこで、`retries: n` を足した（設計案の `then: :abort` にあたる）。
`max_crashes:` と一緒には書けない。
両方を組み合わせる（再試行は3回だが、落ちるのは2回までと仮定する）必要が出たら、そのとき考える。

捨てるときの後始末（Active Jobの `after_discard`）は、`on_crash` で回数を見て書ける。

```ruby
process :job, crash: :restart, retries: 2 do |id|
  # ...
  on_crash { |s| update order: ite(s.job[id].crashes.eq(2), :failed, s.order) }
end
```

`on_crash` の式は遷移前の状態で評価するので、`crashes` が上限に達しているクラッシュが、捨てるときのクラッシュである。

### 9.4 書き忘れは警告しない

`process` を使う仕様には、クラッシュが意味を持たないものも多い。
`examples/tlaplus/models` でプロセスを使う5つの仕様は、PlusCalのアルゴリズムを写したもので、どれもプロセスが落ちることを仮定していない。
`fmspec-rails/test/support/withdrawal_spec.rb` のトランザクションも、分離レベルの検査が目的で、落ちることは別の問題である。
これらで警告を出すと、警告を消すための指定が増えるだけになる。

警告の代わりに、[dsl.md](dsl.md) の「クラッシュ」に、`crash:` を使うべき場面（外部への副作用と、トランザクションの外のステップを持つプロセス）を書く。

### 9.5 ループの先頭は、既定ではクラッシュの位置にしない

`queue_worker.rb` のワーカーは、`fetch`、`handle`、`ack` を繰り返す。
`crash_at:` に `fetch` を含めても、状態数（120）も検査の結果も変わらなかった。
`fetch` にいるとき、ローカル変数はすでに初期値に戻っており（`ack` で消す）、そこで落ちても回数が増えるだけだからである。

ループの途中の値を次の周に持ち越すプロセスでは、先頭で落ちることが意味を持ちうる。
そのときは `crash_at:` に先頭を含める。
一度でも実行したかを状態に持つ既定は、状態を増やす割に得るものが少ないので採らない。

## 10. 未決事項

- bindingの `crash` で、Active Recordの接続とトランザクションをどう捨てるか。`fmspec-rails` の補助の設計（§5）。
- `max_crashes:` と `retries:` を組み合わせる必要があるか。
- 全体のクラッシュの回数の上限を、語彙にするか（§9.1）。
