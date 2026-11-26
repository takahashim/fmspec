# fmspec IR v1 と証拠の形式

fmspecのエンジンが読み書きするJSONの形式を定める。
対象は、モデルのIR（`ir_version: 1`）、検査条件、安全性証明書、トレース、`fmspec check --json` の結果である。

設計の背景は[設計仕様書](ruby_model_checker_spec.md)にある。
仕様書§18の未決事項のうち、公開引数、内部選択、出力、遷移契約、終端条件のIRでの表現と、探索順に依存する結果の扱いは、本書の内容で実装した。
正式なJSON Schemaと互換性ポリシーは未定である。

## モデル

モデルは次のキーを持つオブジェクトである。
未知のキーは拒否する。

| キー | 必須 | 内容 |
|---|---|---|
| `ir_version` | ○ | `1` |
| `name` | ○ | モデルの名前 |
| `enums` | | 列挙型の配列。`{"name", "variants"}` |
| `states` | ○ | 状態変数の配列。`{"id", "name", "type", "initial"}` |
| `actions` | | 操作の配列 |
| `invariants` | | 状態不変条件の配列。`{"name", "expr"}` |
| `contracts` | | 遷移契約の配列。`{"name", "action", "expr"}` |
| `terminal` | | 終端条件の式。省略時はどの状態も終端でない |

状態変数の `id` は省略できる。
書く場合は、定義順の添字と一致させる。
状態変数、操作、不変条件、遷移契約は、`source`（`{"file", "line"}`）でソース位置を持てる。
ソース位置は診断に使うだけで、モデルの意味にもdigestにも関わらない。

操作は次のキーを持つ。

| キー | 内容 |
|---|---|
| `name` | 操作名 |
| `params` | 公開引数の配列。`{"name", "type"}` |
| `choices` | 内部選択の配列。`{"name", "type"}` |
| `guard` | Bool式。省略時は常に有効 |
| `updates` | 更新の配列。`{"target", "expr"}`。`target` は状態変数の添字 |
| `output` | 出力。`{"type", "expr"}`。省略時は無出力 |

次の例は、同じ公開入力が内部選択に応じて `success` または `forbidden` を返す操作と、`success` を要求する遷移契約を持つ。

```json
{
  "ir_version": 1,
  "name": "responder",
  "enums": [{"name": "result", "variants": ["success", "forbidden"]}],
  "states": [{"id": 0, "name": "x", "type": {"int": {"min": 0, "max": 0}}, "initial": {"int": 0}}],
  "actions": [{
    "name": "request",
    "params": [{"name": "id", "type": {"int": {"min": 7, "max": 7}}}],
    "choices": [{"name": "allowed", "type": {"bool": {}}}],
    "updates": [],
    "output": {
      "type": {"enum": "result"},
      "expr": {"ite": [
        {"choice": 0},
        {"enum": {"type": "result", "variant": "success"}},
        {"enum": {"type": "result", "variant": "forbidden"}}
      ]}
    }
  }],
  "contracts": [{
    "name": "succeeds",
    "action": "request",
    "expr": {"eq": [{"output": {}}, {"enum": {"type": "result", "variant": "success"}}]}
  }]
}
```

`examples/models/tickets.json` に、仕様書§4.1のチケット例のIRがある。

## 型と値

型は3種類ある。
Tuple、Record、Option、Set、Map、Listは未対応である。

| 型 | JSON | 値のJSON（トレース、証明書） |
|---|---|---|
| Bool | `{"bool": {}}` | `true` / `false` |
| 有界Int | `{"int": {"min": 0, "max": 4}}` | 数値 |
| Enum | `{"enum": "result"}` | ラベルの文字列 |

Intは符号付き64ビット整数で、型は閉区間 `min..=max` を表す。
範囲は状態変数、引数、出力の型にだけあり、式の中間結果は64ビット整数の全域を取る。

エンジンの内部では、値を型ごとの整数の**符号**で表す。
Boolは0と1、Intは値そのもの、Enumはラベルの添字である。
状態は状態変数の符号を定義順に並べた列で、状態の等価性はこの列の一致で定義する。
証明書の状態の順序も、この列の辞書順である。

## 式

式は、演算子を表すキーを1つだけ持つオブジェクトである。
未知の演算子は拒否する。

| 式 | 型 | 評価 |
|---|---|---|
| `{"int": 5}`、`{"bool": true}`、`{"enum": {"type", "variant"}}` | リテラル | |
| `{"var": i}` | 状態変数の型 | 遷移前の状態変数。不変条件と終端条件では現在の状態変数 |
| `{"param": i}`、`{"choice": i}` | 引数の型 | 操作の公開引数、内部選択 |
| `{"next": i}` | 状態変数の型 | 遷移後の状態変数。遷移契約でだけ使える |
| `{"output": {}}` | 出力の型 | 操作の出力。出力を宣言した操作の遷移契約でだけ使える |
| `add`、`sub`、`mul` `[a, b]` | Int × Int → Int | 結果が64ビット整数に収まらなければオーバーフロー |
| `lt`、`le`、`gt`、`ge` `[a, b]` | Int × Int → Bool | |
| `eq`、`ne` `[a, b]` | 同じ型どうし → Bool | |
| `not` `[a]` | Bool → Bool | |
| `all` `[a, ...]` | Bool... → Bool | 記述順に評価し、最初の偽で打ち切る。空なら真 |
| `any` `[a, ...]` | Bool... → Bool | 記述順に評価し、最初の真で打ち切る。空なら偽 |
| `implies` `[p, q]` | Bool × Bool → Bool | `p` が偽なら `q` を評価せず真 |
| `ite` `[c, a, b]` | Bool × T × T → T | `c` に続いて、選ばれた枝だけを評価する |

二項演算は左、右の順に両辺を評価する。
評価した部分式の失敗は、そのまま式全体の失敗になる。

型検査はすべての枝を対象にする。
評価されない枝に型エラーや未定義の参照があるモデルも、IR検証で拒否する。
IR検証を通ったモデルでは、評価の失敗はオーバーフローと範囲外更新の2種類に限られる。

除算、剰余、量化は未対応である。

## 遷移

状態 `s` で操作を引数の組（公開引数と内部選択）に適用した結果は、次の順で決まる。

1. `guard` を評価する。偽なら、その組は無効である。更新式も出力式も評価しない。
2. `updates` を記述順に評価する。式はすべて遷移前の状態で評価する（同時代入）。値が対象の状態変数の型の範囲外なら範囲外更新である。
3. `output` を評価する。値が出力の型の範囲外なら範囲外更新である。

途中で評価に失敗した場合は、最初に失敗した箇所（`guard`、`update`、`output`）を報告する。
範囲外更新は評価エラーであり、遷移を黙って除外することはない。
同じ状態変数への重複代入は、IR検証で拒否する。

引数の組は、公開引数、内部選択の順に並べた列の辞書順に列挙する。
各引数の値の順序は、Boolが `false`、`true`、Intが昇順、Enumがラベルの定義順である。
引数のドメインは型全体であり、値を1つずつ列挙する。

## 性質と検査条件

- **状態不変条件**：到達できるすべての状態で真に評価される。
- **遷移契約**：対象の操作のすべての有効な遷移で真に評価される。遷移前の状態、引数、遷移後の状態、出力を参照できる。
- **デッドロック**：有効な遷移が1つもない状態のうち、終端条件が真でないもの。終端条件は、有効な遷移のない状態でだけ評価する。

**検査条件**は、対象の操作、不変条件、遷移契約と、デッドロック検査の有無からなる。
対象外の操作の遷移は、到達可能性にも検査にも含めない。
JSONでは名前で並べる。

```json
{"actions": ["purchase", "cancel"], "invariants": ["capacity_respected"], "contracts": [], "deadlock": false}
```

既定では、すべての操作、不変条件、遷移契約が対象で、デッドロック検査は無効である。

## 探索順と結果

`check` は幅優先探索を行う。
各状態で、操作を定義順に調べる。
1つの操作については、まず全引数の遷移を計算し、評価エラーがあればそれを報告する。
エラーがなければ、遷移を引数の辞書順にたどり、遷移契約、遷移先の不変条件の順に検査する。
すべての操作を調べたあとで、デッドロックを検査する。

状態不変条件の違反は、遷移回数が最小のトレースで報告する。
同じ長さのトレースが複数あるときは、この順で最初に見つかるものを返す。

違反と評価エラーの両方に到達できるモデルでは、この順で先に見つかったほうを報告する。
どちらを報告しても、判定ゲートがトレースを再生して確認した事実である。

`--max-states` は、初期状態を含む、保持する異なる状態の数の上限である。
上限に達したあとも既訪問の状態への辺は検査し、新しい状態を保持する必要が生じた時点で `inconclusive` とする。
このとき、その新しい状態の不変条件は検査していない。

## 証明書

```json
{
  "certificate_version": 1,
  "model_digest": "sha256:...",
  "engine_version": "0.1.0",
  "conditions": {"actions": ["purchase", "cancel"], "invariants": ["capacity_respected"], "contracts": [], "deadlock": false},
  "states": [[0], [1], [2], [3]]
}
```

`states` は状態の配列で、各状態は状態変数の値を定義順に並べた配列である。
到達できる状態の上位集合でもよい。
読み込み時に符号化列の辞書順に整列するので、ファイル中の順序は問わない。

`verify-certificate` は、証明書の検査条件が要求された検査条件と一致することを確かめてから、証明書を検査する。
`model_digest` が違う証明書は、別のモデルに対するものとして拒否する。

## トレース

```json
{
  "trace_version": 1,
  "model_digest": "sha256:...",
  "engine_version": "0.1.0",
  "seed": null,
  "conditions": {"actions": ["purchase", "cancel"], "invariants": ["capacity_respected"], "contracts": [], "deadlock": false},
  "initial": {"sold": 0},
  "steps": [
    {"action": "purchase", "args": {"quantity": 2}, "choices": {}, "output": {"unit": true}, "state": {"sold": 2}},
    {"action": "purchase", "args": {"quantity": 2}, "choices": {}, "output": {"unit": true}, "state": {"sold": 4}}
  ],
  "claim": {"violation": "invariant", "name": "capacity_respected"}
}
```

出力は、無出力なら `{"unit": true}`、出力があれば `{"value": ...}` である。
`claim` は、トレースの末尾で起きる事象の主張である。

| `claim` | 意味 |
|---|---|
| `{"violation": "invariant", "name"}` | 末尾の状態で不変条件が偽 |
| `{"violation": "contract", "name"}` | 最後の遷移で遷移契約が偽 |
| `{"violation": "deadlock"}` | 末尾の状態が非終端のデッドロック |
| `{"error", "site": "invariant", "name"}` | 末尾の状態で不変条件の評価が失敗 |
| `{"error", "site": "contract", "name"}` | 最後の遷移で遷移契約の評価が失敗 |
| `{"error", "site": "terminal"}` | 有効な遷移のない末尾の状態で、終端条件の評価が失敗 |
| `{"error", "site": "guard" \| "update" \| "output", "action", "args", "choices"}` | 末尾の状態で、操作と引数の適用が指定の箇所で失敗。`update` では `target` に状態変数名を書く |

`error` は `{"kind": "overflow"}` または `{"kind": "out_of_range", "value": 5, "type": {...}}` である。
`type` は表示用で、読み込み時には使わない。

`replay` は、トレースに記録された検査条件で、各ステップの出力と状態、末尾の主張を検査する。

## `check --json` の結果

| キー | 内容 |
|---|---|
| `status` | `verified`、`violated`、`error`、`inconclusive`、`internal_error` |
| `model`、`model_digest`、`engine_version`、`ir_version` | モデルとエンジンの識別 |
| `conditions` | 検査条件 |
| `search` | 探索器の報告。`complete`、`visited_states`、`transitions`、`time_ms`。検査済みの値ではない |
| `gate` | 判定ゲートが証拠の検査にかけた時間 |
| `certificate_states` | `verified` のとき、判定ゲートが受理した証明書の状態数 |
| `property`、`trace` | `violated`、`error` のとき、起きた事象と、判定ゲートが受理したトレース |
| `reason` | `inconclusive` のとき、`max_states` または `interrupted` |
| `rejected` | `internal_error` のとき、判定ゲートが証拠を拒否した理由 |

`verify-certificate` と `replay` の結果は同じ形で、`search` を持たない。
提示された証拠を判定ゲートが拒否した場合の `status` は `rejected` である。

終了コードは、`verified` が0、`violated` と `rejected` が1、`error`、不正な入力、`internal_error` が2、`inconclusive` が3である。
