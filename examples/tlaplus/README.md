# 第三者が書いたTLA+の仕様との比較

[tlaplus/Examples](https://github.com/tlaplus/Examples) の仕様を、TLA+のままTLCで検査した結果と、同じモデルをDSLで書いてfmspecで検査した結果を比べる。
比べるテストは `test/tlaplus_examples_test.rb` で、`rake test:tlc` から実行する。

`reference/test/tlc_test.rb` は、fmspecのIRを変換したTLA+をTLCで検査する。
変換も比較も同じ作者が書いたので、IRの意味を変換で取り違えると見つからない。
ここでは、TLA+の側は他人が書いた仕様をそのまま使い、DSLの側はその仕様を読んで書き写したものを使う。

## 構成

| 場所 | 内容 |
|---|---|
| `vendor/tlaplus-examples/` | tlaplus/Examples の仕様の写し。編集しない |
| `vendor/tlapm/TLAPS.tla` | EWD840 が `EXTENDS` するモジュール。tlaplus/tlapm の写し。編集しない |
| `models/` | 同じモデルをDSLで書いたもの |

TLCの設定ファイルは、テストが仕様ごとに作る。
定数と仕様（`SPECIFICATION` か `INIT` と `NEXT`）、デッドロック検査の有無は元の設定と同じにし、活性の性質（`PROPERTY`）は除く。
fmspecは安全性だけを検査するからである。

## 仕様

| 仕様 | DSL | 定数 | manifest.json の記録 | 不変条件 |
|---|---|---|---|---|
| `DieHard.tla` | `die_hard.rb` | | safety failure | `NotSolved` → `not_solved` |
| `TCommit.tla` | `t_commit.rb` | `RM = {r1, r2, r3}` | 34状態 | `TCConsistent` → `consistent` |
| `TwoPhase.tla` | `two_phase.rb` | `RM = {r1, r2, r3}` | 288状態 | なし（型の不変条件だけ） |
| `EWD840.tla` | `ewd840.rb` | `N = 3` | 302状態 | `TerminationDetection` → `termination_detection`、`Inv` → `inv` |
| `MissionariesAndCannibals.tla` | `missionaries_and_cannibals.rb` | 宣教師と人食い人種が3人ずつ | safety failure | `Solution` → `solution` |
| `DiningPhilosophers.tla` | `dining_philosophers.rb` | `N = 5` | 58状態 | `NoDeadlock` → デッドロック検査 |
| `Simple.tla`（PlusCal） | `simple.rb` | `N = 5` | 723状態 | `PCorrect` → `p_correct`、`Inv` → `inv` |
| `Lock.tla`（PlusCal） | `lock.rb` | | 12状態 | `LockInv` → `lock_inv` |
| `Peterson.tla`（PlusCal） | `peterson.rb` | | 42状態 | `Inv` → `inv` |
| `DiningPhilosophersPCal.tla`（PlusCal） | `dining_philosophers_pcal.rb` | `NP = 5` | 67状態 | `ExclusiveAccess` → `exclusive_access` |
| `MCBakery.tla`、`Bakery.tla`（PlusCal） | `bakery.rb` | `N = 2`、`Nat <- 0..2` | 記録は `ISpec` の数なので比べない（`Spec` では2303状態） | `MutualExclusion` → `mutual_exclusion` |
| `HourClock.tla` | `hour_clock.rb` | | 12状態 | なし（型の不変条件だけ） |
| `Channel.tla` | `channel.rb` | `Data = {d1, d2, d3}` | 12状態 | なし |
| `AsynchInterface.tla` | `asynch_interface.rb` | `Data = {d1, d2, d3}` | 12状態 | なし |
| `MCInnerFIFO.tla`、`InnerFIFOInstanced.tla` | `inner_fifo.rb` | `Message = {m1, m2, m3}`、`qLen = 3` | 3864状態 | なし |
| `MCAlternatingBit.tla`、`AlternatingBit.tla` | `alternating_bit.rb` | `Data = {d1, d2}`、キューの長さは2まで | 240状態 | なし |
| `MCInternalMemory.tla`、`InternalMemory.tla` | `internal_memory.rb` | プロセス2、番地3、値2 | 4408状態 | なし |
| `GermanControl.tla` | `german_control.rb` | `NODE = {n1, n2}` | 記録は対称性で削減した数なので比べない（削減しなければ1461状態） | `Coherence` → `coherence` |
| `GermanData.tla` | `german_data.rb` | `NODE = {n1, n2}`、`DATA = {d1, d2}` | 記録は対称性で削減した数なので比べない（削減しなければ3390状態） | 6つ（`Coherence`、`DataProp` など） |
| `SlidingPuzzles.tla` | `sliding_puzzles.rb` | | safety failure（最短の解は116手） | `KlotskiGoal` → `klotski_goal` |

型の不変条件（`TypeOK` など）はDSLでは型で表すので、対応する不変条件を書かない。
TLCの側では検査する。

DSLの状態変数は、TLA+の状態変数と一対一に対応させてある。
TLA+で定義域の全体を持つ関数は、すべてのキーを持つMapで表す。
`TwoPhase.tla` の `msgs`（`Prepared`、`Commit`、`Abort` の3種類のメッセージの集合）は、`Prepared` を送ったRMの集合と、`Commit` と `Abort` を送ったかどうかの2つの真偽値で表す。
`MissionariesAndCannibals.tla` の `IsSafe` は、Rubyのlambdaで書いて記号ブロックから呼ぶ。

PlusCalから翻訳された仕様は、DSLの `process` で書く。
PlusCalのプロセス（`proc \in 1..2` など）はインスタンスを持つプロセス `worker` に、ラベルはステップに、`pc` はインスタンスごとのプログラムカウンタに、`"Done"` は `:done` にあたる。
`while (TRUE)` の繰り返しは、最後のステップの `goto` で表す。
PlusCalの翻訳は、すべてのプロセスが終わった状態に足踏みの遷移（`Terminating`）を加える。
DSLの `process` は、`terminal` を書かなければ、すべてのインスタンスが `:done` であることを終端条件にするので、どちらもその状態をデッドロックとしない。

1つのラベルから複数の行き先に分かれるところは、`goto` を複数書く（条件が真になる最初の `goto` の行き先に進む）。
PlusCalの `either A or B` は、内部選択した真偽値で A と B を選び、`goto` で行き先を分ける。
`while (unchecked # {})` の本体の `with (i \in unchecked)` は、`unchecked` が空なら選ばずに次のラベルに進む。
DSLの `choose` は空のドメインでは遷移を持たないので、空のときだけ自分の番号を選ぶ範囲にし、更新はすべて元の値を保つ（`bakery.rb`）。

`DijkstraMutex.tla` は、プロセスの変数 `temp` がプロセスにも集合にもなるので、状態の一対一の対応を作るのが煩雑で、含めていない。

そのほかの書き写しでは、次のように対応させた。

- TLCの `CONSTRAINT`（`MCInnerFIFO`、`MCAlternatingBit` のキューの長さ）は、キューに加える操作の guard にする。TLCは制約を満たさない状態を、到達した状態の集合に加えないので、到達できる状態は同じになる。
- `AlternatingBit.tla` の `Lose(q)`（キューの任意の位置の要素を失う）は、キューの長さが2以下なので、内部選択した真偽値で先頭を除くか末尾を除くかを選ぶ。
- `InternalMemory.tla` の `buf` の値（読み出しの要求、書き込みの要求、値、`NoVal` の和）は、種類と、使う欄だけに値のある番地と値のレコードで表す。
- `NoNode`、`NoData` のような、集合の外の値は、Option の値なしで表す。
- German のプロトコルの元の設定は `SYMMETRY` でノード（とデータ）の入れ替えをまとめる。fmspec に対称性の削減はないので、`SYMMETRY` を外して TLC にかける。
- `SlidingPuzzles.tla` の盤面（駒の集合で、駒はマスの集合）は、DSL の集合の要素に集合を使えないので、駒の形ごとに基準のマスの集合で表す。同じ形の駒は区別しないので、この対応は一対一である。空いたマスの隣の駒をそこへ動かす遷移は、行き先が空いている駒を1マス動かす遷移と同じである。

Paxos（`MCPaxos.tla`）は、依存する `Consensus.tla` が tlapm のライブラリ（`FiniteSetTheorems` など）を `EXTENDS` するので、含めていない。

## 比べること

- 判定。TLCが不変条件の違反を報告するなら、fmspecも対応する不変条件の違反を報告する。
- 反例の長さ。どちらも幅優先で、最短の反例を返す。
- 違反で止まるまでに見つけた状態の数。
- 不変条件を外して最後まで探索したときの、到達できる状態の数。これは manifest.json の記録とも比べる。

## 出典

| 写し | 元 | コミット | ライセンス |
|---|---|---|---|
| `vendor/tlaplus-examples/` | https://github.com/tlaplus/Examples の `specifications/` | `b4f5c74b7cdd9cc7735ed9451858901d330b7815` | MIT（`vendor/tlaplus-examples/LICENSE.md`） |
| `vendor/tlapm/TLAPS.tla` | https://github.com/tlaplus/tlapm の `library/TLAPS.tla` | `e4d66f48707fef5f5f64d69a3436b158f68732b7` | BSD 2条項（`vendor/tlapm/LICENSE`） |

写したファイルの SHA-256 は次のとおりである。

```
295495de6509d86a82b88757835b95e3f91fad8691d764ece4d98886dcf42b66  tlaplus-examples/DieHard.tla
2c4ba4c26ad3a5284e65bba7beaa42b9498ce320da060f2e4a01db2fb7a8db06  tlaplus-examples/DiningPhilosophers.tla
774e52d30200ff2f6ff386cbc90056b67eb13368ad9e7ab3bf38844c68bb9a48  tlaplus-examples/EWD840.tla
afb87e6ebc4af897ab9b27f90729c0170f061f8d95444a54035df1afaf21c65a  tlaplus-examples/MissionariesAndCannibals.tla
59c00946e0f5d997b1d5764586f67855394c03910611c9a986554f8fabaf4720  tlaplus-examples/SyncTerminationDetection.tla
98974d8c5ee007f4f62188737c20c7dcdb05af099cc53a59c8b8651331fd925d  tlaplus-examples/TCommit.tla
dd859866e8be0ee36b0005b0393becd788fe51aae7ebcd7deaa14c259a3c0bab  tlaplus-examples/Simple.tla
f10562642cb5d9cb6a3d3912d93917fa692a97ab9a879fa3b3f2c7989098765f  tlaplus-examples/Lock.tla
0cad3a0a34bdf495606aa0b3a27d58d2a6568b4d1a4fe4bdc4b45d723a90cba7  tlaplus-examples/Peterson.tla
e6e72ed0097cca55e80b97af33c3bc54792a504bcbdf639d6d9c666f49c17817  tlaplus-examples/TwoPhase.tla
5e4174fb94f1653da5b79c085a19aceb840d23be146cbb608b79ba6fbd5e30e0  tlaplus-examples/DiningPhilosophersPCal.tla
3b2a3f370e5f0fde8660b3ef09932d579c9bd2ccd249a5ce2304007bf24da8d5  tlaplus-examples/Bakery.tla
e30e4fc5558357406b890b3249eda6ec0ec7d5e191b1469adc3774990c1fbe25  tlaplus-examples/MCBakery.tla
985903176db4725f9cf25df84ad84dcd53ba94be80d26298b87ec86fbc9b08b3  tlaplus-examples/HourClock.tla
8b2cbd4533a157ae0760e3117e3c008fb9a31dc3673005fc8b537d3879de1bfc  tlaplus-examples/Channel.tla
86adf068c65219ebe140e047dece85a9d04b9492d508e4aa4d5f86685ada09d4  tlaplus-examples/AsynchInterface.tla
bfdb32a7fcf3a45814c2caa03b872ec1569373691422e7affb242ceecfad2c1c  tlaplus-examples/InnerFIFOInstanced.tla
0307ab77efcefd78af6a5ddd2d6f382419a2b1e79112f5f16941ad83315936d7  tlaplus-examples/MCInnerFIFO.tla
27afc8a6ff033f7646d483eb8a987f2f3f89d351bbee8fffbacdc0af61b5ad6e  tlaplus-examples/AlternatingBit.tla
b97edf65c80c0d0a116d1016fc2a95bf51a2e008bb1768bde2c52e828f08785a  tlaplus-examples/MCAlternatingBit.tla
90c960c490f9fa66e919cc025cc4f31e3036be4949f78484799874a27ac6054b  tlaplus-examples/ABCorrectness.tla
8ba1a82a0f418b6b3c6c99ad06adfe808d604670d0d8c31ce05d53ed16d2aa73  tlaplus-examples/InternalMemory.tla
cb496258606d5323b1a8f1f4450460a676df68ca0f945764ac80e763078d2e5a  tlaplus-examples/MemoryInterface.tla
67deb792930526267e556009d41a4eb6bf9ce663d6224d8c745b67acb2faffe2  tlaplus-examples/MCInternalMemory.tla
7eb9498b6f9f5f275b3f0f168cf60141be24b8972d9522e41c3d878cf0ffe912  tlaplus-examples/GermanControl.tla
3898b84bc919d979114ef53e6188f7e7cb7c7ba48d61f5104274a53e85b2c4bd  tlaplus-examples/GermanData.tla
df0d6a46542a0b1aa7cdb5141923df2ea3770d241e4ca5afde0cb5c2234e76fd  tlaplus-examples/SlidingPuzzles.tla
775e88184bf5914c302653ee96a679dbe483e945d150604d9047711822396ea7  tlapm/TLAPS.tla
```
