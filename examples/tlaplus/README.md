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

型の不変条件（`TypeOK` など）はDSLでは型で表すので、対応する不変条件を書かない。
TLCの側では検査する。

DSLの状態変数は、TLA+の状態変数と一対一に対応させてある。
TLA+で定義域の全体を持つ関数は、すべてのキーを持つMapで表す。
`TwoPhase.tla` の `msgs`（`Prepared`、`Commit`、`Abort` の3種類のメッセージの集合）は、`Prepared` を送ったRMの集合と、`Commit` と `Abort` を送ったかどうかの2つの真偽値で表す。
`MissionariesAndCannibals.tla` の `IsSafe` は、Rubyのlambdaで書いて記号ブロックから呼ぶ。

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
e6e72ed0097cca55e80b97af33c3bc54792a504bcbdf639d6d9c666f49c17817  tlaplus-examples/TwoPhase.tla
775e88184bf5914c302653ee96a679dbe483e945d150604d9047711822396ea7  tlapm/TLAPS.tla
```
