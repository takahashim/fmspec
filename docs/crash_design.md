# プロセスのクラッシュの自動生成（設計案）

`process` のステップの境界で、インスタンスがクラッシュする遷移を自動で加える機能の設計案である。
§3と§4（検査側）は実装した。使い方は [dsl.md](dsl.md) の「クラッシュ」にある。
§5（実装との適合性検査）は未実装である。
語彙、既定値、名前は試作の段階で、§9の未決事項とともに変わりうる。

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
| `max_crashes: n` | `:restart` のとき、インスタンスごとのクラッシュの回数の上限。既定は1 |

`crash:` を書かなければ、いままでと同じである。

`crash_at:` の既定から最初のステップを除くのは、最初のステップの前に落ちることは、`:abort` ではプロセスが始まらなかったこと、`:restart` では何も変わらないことになるからである。
ただし `goto` で最初のステップに戻るループでは、2周目以降の最初のステップの前も、意味のあるクラッシュの位置になる。
その位置で落ちる場合を見たければ、`crash_at:` に最初のステップを含める。

### 3.2 ローカル変数とクラッシュの後始末

| 語彙 | 内容 |
|---|---|
| `local(名前, 型, initial: 値, durable: true)` | `:restart` のとき、クラッシュしても初期値に戻さないローカル変数。ジョブの引数のように、永続化された値にあたる。既定は `false` |
| `on_crash { \|s\| ... }` | クラッシュの遷移の中身。記号ブロックで、`update`、`unchanged`、`choose`、`guard`、`ensures`、`preserves` を使える。`returns` と `goto` は使えない |

`on_crash` は、クラッシュで環境に起きることを書く。
たとえば、接続が切れるとDBがadvisory lockを解放する。

```ruby
process :worker, count: 2, crash: :abort do |id|
  step(:lock) { |s| guard s.holder.eq(nil); update holder: id }
  step(:work) { |s| update count: s.count + 1 }
  step(:unlock) { |s| update holder: nil }
  on_crash { |s| update holder: ite(s.holder.eq(id), nil, s.holder) }
end
```

`on_crash` を書かなければ、クラッシュは共有の状態変数を変えない。
`on_crash` の `guard` は、落ちうる状況をさらに絞る。

### 3.3 記号的な状態からの参照

| 書き方 | 内容 |
|---|---|
| `s.job[0].crashed` | `:abort` で、インスタンスがクラッシュして終わった |
| `s.job[0].crashes` | `:restart` で、インスタンスがクラッシュした回数 |
| `s.job[0].done` | いままでどおり、最後のステップまで実行して終えた。クラッシュして終わったときは偽 |

`crashed`、`crashes`、`crash` は、ステップとローカル変数の名前に使えない。

## 4. 基本のIRへの展開

`process :job, count: n` のインスタンス `job[i]` ごとに、次を加える。

| `crash:` | 状態変数 | 操作 `job[i].crash` |
|---|---|---|
| `:abort` | プログラムカウンタの列挙型 `job.pc` に、ラベル `:crashed` を加える | guard は「`job[i].pc` が `crash_at:` のどれか」と `on_crash` のguardの連言。更新は `job[i].pc := :crashed` と `on_crash` の更新 |
| `:restart` | `job[i].crashes`（`int(0..max_crashes)`、初期値0） | guard は「`job[i].pc` が `crash_at:` のどれか」、「`job[i].crashes < max_crashes`」、`on_crash` のguardの連言。更新は、`job[i].pc` を最初のステップに、`durable: true` でないローカル変数を初期値に、`job[i].crashes` を1増やす更新と、`on_crash` の更新 |

ほかに、次のことを決める。

- クラッシュの操作は公開引数を持たない。`on_crash` の `choose` は、操作の内部選択になる。
- `initial_in:` のローカル変数を初期値に戻すときは、候補から選ぶ内部選択にする。内部選択の名前は、ローカル変数の名前である。
- `on_crash` の更新とローカル変数の初期化が同じ変数を更新すれば、`Fmspec::BuildError` にする（ローカル変数は `on_crash` で更新できない）。
- `terminal` を書かないときの終端条件は、「すべてのインスタンスが `:done` か `:crashed`」になる。`:restart` では、いままでどおり「すべてのインスタンスが `:done`」である。
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
| `crash { \|instance\| ... }` | クラッシュのハンドラ。インスタンスのスレッドで実行する。`inject:` は `command` と同じ |

テストがクラッシュの操作を選ぶと、次のことをする。

1. インスタンスのスレッドで `crash` のハンドラを実行する。
2. スレッドを終える。`teardown` は呼ばない（後始末をしないことがクラッシュだからである）。ただしテストケースの終わりに、資源を解放するための `teardown` は呼ぶ。
3. `:restart` なら、新しいスレッドで `process` の `setup` を同じ番号でもう一度呼び、以後のステップをそのスレッドで実行する。

`crash` を登録しない `process` で仕様がクラッシュの操作を持つときは、ほかの操作の `command` がないときと同じく `Fmspec::BuildError` にする。
クラッシュをテストしないなら、`test(actions: ...)` で対象から外す。
暗黙に外すことはしない。

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
| 回数 | 公平性の仮定と `assume` で扱う | `max_crashes:` で上限を状態に持つ |
| 環境の後始末 | なし（明示的にモデル化する） | `on_crash` |
| メッセージの消失 | ロール間のRPCで自動 | 対象外。fmspecにRPCの語彙はない |
| 結果の検査 | 検査器を信頼する | 判定ゲートが証明書とトレースを検査する（変わらない） |

FizzBeeが既定で有効にしているのは、「起きうる障害を書き忘れる」ことを防ぐためである。
fmspecで既定を無効にする代わりに、`process` に `crash:` がないことを警告する仕組み（`Fmspec::Lint` か、検査の報告）を検討する（§9）。

## 9. 未決事項

- `max_crashes:` を、インスタンスごとにするか、プロセス全体の合計にするか。合計のほうが状態は少ないが、どのインスタンスが落ちたかの組み合わせが見えにくい。
- `:restart` の再開位置。最初のステップ固定でよいか、`restart_at:` で選べるようにするか。Active Jobの `retry_on` は最初からだが、ステップの中で状態を見て処理を飛ばす（冪等にする）実装も多く、それは仕様のguardで書ける。
- `:restart` でも、再試行の回数が尽きたら `:crashed` で終わる（Active Jobの `discard`）を表すか。表すなら `crash: :restart` に `then: :abort` のような指定を足す。
- 既定を無効にしたとき、書き忘れをどう知らせるか。
- `crash_at:` の既定に、`goto` で戻るループの最初のステップを含めるか。含めるには、そのステップを一度でも実行したかを状態に持つ必要がある。
- bindingの `crash` で、Active Recordの接続とトランザクションをどう捨てるか。`fmspec-rails` の補助の設計。
