# fmspec IR v1 と証拠の形式

fmspecのエンジンが読み書きするJSONの形式を定める。
対象は、モデルのIR（`ir_version: 1`）、検査条件、安全性証明書、トレース、`fmspec check --json` と `fmspec simulate --json` の結果である。
Rubyの `Fmspec::Result#to_h` も同じ結果を返す。

設計の背景は[設計仕様書](ruby_model_checker_spec.md)にある。
仕様書§18の未決事項のうち、公開引数、内部選択、出力、遷移契約、終端条件のIRでの表現と、探索順に依存する結果の扱いは、本書の内容で実装した。
証拠の形式の互換性ポリシーは未定である。

## JSON Schema

モデルのIRの構造は、JSON Schema（draft 2020-12）の [ir.schema.json](ir.schema.json) で定める。
スキーマが検査するのは、キーの有無と種類、演算子のオペランドの数、リテラルの形である。
名前の一意性、名前と添字の参照の解決、式の型、値の範囲、型のスロット数の上限は、エンジンの読み込みとIR検証が検査する。
したがって、スキーマを満たすことは、エンジンがIRを受理するための必要条件であり、十分条件ではない。
エンジンが受理するIRは、どれもスキーマを満たす。
`test/schema_test.rb` が、例のモデル、DSLの出力、ランダムに生成したモデルとそれを1か所壊したモデルで、このことを確かめる。

当面、`ir_version` は `1` のままとする。
開発中は、受理していたIRの意味を変える変更や、受理していたIRを拒否するようになる変更も、`ir_version` を上げずに行うことがある。
IRの互換性ポリシーは未定である。

## モデル

モデルは次のキーを持つオブジェクトである。
未知のキーは拒否する。

| キー | 必須 | 内容 |
|---|---|---|
| `ir_version` | ○ | `1` |
| `name` | ○ | モデルの名前 |
| `enums` | | 列挙型の配列。`{"name", "variants"}` |
| `constants` | | 名前付きの定数の配列。`{"name", "type", "value"}` |
| `states` | ○ | 状態変数の配列。`{"id", "name", "type", "initial"}` または `{"id", "name", "type", "initial_in"}` |
| `actions` | | 操作の配列 |
| `invariants` | | 状態不変条件の配列。`{"name", "expr"}` |
| `contracts` | | 遷移契約の配列。`{"name", "action", "expr"}` |
| `terminal` | | 終端条件の式。省略時はどの状態も終端でない |
| `initial_constraint` | | 初期条件の式。省略時は初期値の候補の組み合わせがすべて初期状態になる |

状態変数の `id` は省略できる。
書く場合は、定義順の添字と一致させる。

状態変数の `initial` と定数の `value` は、状態も引数も参照しない式で、読み込み時に評価する。
値は宣言した型に属さなければならない。
定数は `{"const": "名前"}` で参照し、それより前に定義した定数の値の式にも使える。
状態変数、操作、不変条件、遷移契約は、`source`（`{"file", "line"}`）でソース位置を持てる。
ソース位置は診断に使うだけで、モデルの意味にもdigestにも関わらない。

### 初期状態

状態変数には、`initial` と `initial_in` のどちらか一方を書く。
`initial` は初期値の式、`initial_in` は初期値の候補の式の、空でない配列である。
どちらの式も `initial` と同じく、読み込み時に評価する。

初期状態の集合は、状態変数ごとの候補の直積から、`initial_constraint` が真になるものを残し、正規順に整列して重複を除いたものである。
`initial_constraint` は状態変数と定数を参照できるBool式で、引数、`next`、`output` は参照できない。
初期条件の評価が失敗する組み合わせがある場合と、初期条件を満たす組み合わせがない場合は、読み込みを拒否する。
直積の大きさの上限は 2^20 である。

次の例は、`n` が 0 か 2 から始まるモデルの状態変数である。

```json
{"id": 0, "name": "n", "type": {"int": {"min": 0, "max": 3}}, "initial_in": [{"int": 0}, {"int": 2}]}
```

操作は次のキーを持つ。

| キー | 内容 |
|---|---|
| `name` | 操作名 |
| `params` | 公開引数の配列。`{"name", "type", "in"}`。`in` は省略できる |
| `choices` | 内部選択の配列。`{"name", "type", "in"}`。`in` は省略できる |
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
`examples/models/basket.json` は、SetとListを使う例である。

## 型と値

| 型 | JSON | 値のJSON（トレース、証明書） |
|---|---|---|
| Bool | `{"bool": {}}` | `true` / `false` |
| 有界Int | `{"int": {"min": 0, "max": 4}}` | 数値 |
| Enum | `{"enum": "result"}` | ラベルの文字列 |
| Tuple | `{"tuple": [型, ...]}` | 要素の配列 |
| Record | `{"record": [{"name", "type"}, ...]}` | フィールド名から値へのオブジェクト |
| Option | `{"option": 型}` | 値がなければ `null`、あれば `{"some": 値}` |
| 有限Set | `{"set": 要素の型}` | 要素の配列。正規順に並べ、重複を含めない |
| 有限Map | `{"map": {"key": 型, "value": 型}}` | `[キー, 値]` の配列。キーの正規順に並べる |
| 有界List | `{"list": {"of": 型, "max": 4}}` | 要素の配列。長さは `max` 以下 |

Intは符号付き64ビット整数で、型は閉区間 `min..=max` を表す。
Tupleは1つ以上の要素を、Recordは1つ以上の、名前の重複しないフィールドを持つ。
Recordのフィールドの順序は型の一部である。

Setの要素とMapのキーの型（**キー型**）は、値の数が4096以下で、Set、Map、Listを含まない型に限る。

値のJSONを読むときは、SetとMapの並びの順序を問わない。
ただし、Setの要素の重複と、Mapのキーの重複は（値が同じでも）誤りとする。
トレースや証明書の状態や引数にあれば形式の誤りとする。適合性検査では、観測値にあれば、どの値とも一致しない値とし、入力の引数にあれば要求の誤りとする。
Setのリテラルの式（`{"set": {"of": 型, "items": [...]}}`）は値のJSONではなく、要素を記述順に加えるので、同じ要素を2度書いてもよい。
Listの `max` は1024以下である。
1つの型が占めるスロット（後述）は65536以下である。

### 正規順

型の値には、次の**正規順**がある。

- Boolは `false`、`true` の順、Intは昇順、Enumはラベルの定義順である。
- TupleとRecordは、要素の辞書式順序である。
- Optionは、値がないものが先で、値のあるもの同士は値の順である。
- Setは、要素の型の値を正規順に並べ、各値を含むかどうかの真偽値の列（`false` が先）の辞書式順序である。
- Mapは、キー型の値を正規順に並べ、キーごとの「値なし、または値」（値なしが先）の列の辞書式順序である。
- Listは長さの順で、同じ長さなら要素の辞書式順序である。

正規順は、値のJSONの並び、量化でたどる順、引数の列挙順、証明書の状態の順に使う。

### スロット

エンジンの内部では、値を、型ごとに長さの決まった整数の列（**スロット**）で表す。
Bool、Int、Enumは1スロットで、Boolは0と1、Intは値そのもの、Enumはラベルの添字である。
複合型は次の形になる。

| 型 | スロット |
|---|---|
| Tuple、Record | 要素のスロットを順に並べる |
| Option | 値の有無（Bool）に続けて、値のスロット |
| Set | 要素の型の値ごとに、含むかどうか（Bool）を正規順に並べる |
| Map | キー型の値ごとに、キーの有無（Bool）と値のスロットを正規順に並べる |
| List | 長さ（Int）に続けて、`max` 個の要素のスロット |

値のない部分（値のないOptionの中身、Mapにないキーの値、Listの長さより後ろの要素）は、既定値（`false`、Intの下限、Enumの最初のラベル）で埋める。
この表し方は値と一対一に対応するので、状態の等価性はスロットの列の一致で定義できる。
スロットの列の辞書式順序は、正規順と一致する。

状態は状態変数のスロットを定義順に並べた列である。
## 式

式は、演算子を表すキーを1つだけ持つオブジェクトである。
未知の演算子は拒否する。

### 式の型

式の型は値の型とほぼ同じだが、整数の範囲を持たない。
`{"var": 0}` が `int(0..4)` の状態変数でも、式の型は単にIntで、`add` の結果も範囲を持たない。
Tuple、Record、Optionの式も、中の整数は範囲を持たない。
ただし、Set、Map、Listの式の型は、要素の型を範囲まで含めて持つ。
`set(int(0..3))` と `set(int(0..4))` は別の型で、`eq` や `union` で混ぜられない。

値を型の決まった場所（状態変数、出力、Setの要素、Mapのキーと値、Listの要素）に置くときに、範囲を検査する。

式の型付けの規則は、中核の `crates/fmspec-core/src/infer.rs` の `type_of` に仕様として書いてある。
中核は、下ろしの前にモデルのすべての式がこの規則で型を持つことを確かめる（`model_total.rs` の `check_model`）。

### 基本の式

| 式 | 型 | 評価 |
|---|---|---|
| `{"int": 5}`、`{"bool": true}`、`{"enum": {"type", "variant"}}` | リテラル | |
| `{"var": i}` | 状態変数の型 | 遷移前の状態変数。不変条件と終端条件では現在の状態変数 |
| `{"param": i}`、`{"choice": i}` | 引数の型 | 操作の公開引数、内部選択 |
| `{"next": i}` | 状態変数の型 | 遷移後の状態変数。遷移契約でだけ使える |
| `{"output": {}}` | 出力の型 | 操作の出力。出力を宣言した操作の遷移契約でだけ使える |
| `{"const": "名前"}` | 定数の型 | 定数の値 |
| `add`、`sub`、`mul` `[a, b]` | Int × Int → Int | 結果が64ビット整数に収まらなければ `overflow` |
| `div`、`mod` `[a, b]` | Int × Int → Int | 床除算と、その剰余。`b` が0なら `division_by_zero` |
| `lt`、`le`、`gt`、`ge` `[a, b]` | Int × Int → Bool | |
| `eq`、`ne` `[a, b]` | 同じ型どうし → Bool | 構造の等しさ。値のないOptionは中身を比べない |
| `not` `[a]` | Bool → Bool | |
| `all` `[a, ...]` | Bool... → Bool | 記述順に評価し、最初の偽で打ち切る。空なら真 |
| `any` `[a, ...]` | Bool... → Bool | 記述順に評価し、最初の真で打ち切る。空なら偽 |
| `implies` `[p, q]` | Bool × Bool → Bool | `p` が偽なら `q` を評価せず真 |
| `ite` `[c, a, b]` | Bool × T × T → T | `c` に続いて、選ばれた枝だけを評価する |
| `{"let": {"name", "value", "body"}}` | T | `value` を評価して `name` に束縛し、`body` を評価する |
| `{"local": "名前"}` | 束縛した値の型 | 内側から探して最初に見つかった、`let` または量化の束縛 |

床除算は、商を負の無限大の方向に丸める（Rubyの `/` と `%` と同じ）。
`-7 / 2` は `-4`、`-7 % 2` は `1`、`7 % -2` は `-1` である。
剰余は0か、除数と同じ符号を持つ。
`-2^63 / -1` は `overflow` で、`-2^63 % -1` は `0` である。

### 量化

`{"forall": {"name", "in", "body"}}` と `{"exists": {"name", "in", "body"}}` は、`in` の式の値の要素を順に `name` に束縛し、`body` を評価する。
`in` には次のどれかを書く。

| `in` の型 | たどる値 | 順序 |
|---|---|---|
| Set | 要素 | 正規順 |
| Map | キー | 正規順 |
| List | 要素 | 位置の順。同じ値が複数あれば、それぞれたどる |

`in` の代わりに `{"type": 型}` と書くと、型のすべての値を正規順にたどる。
型はキー型に限る。

`forall` は最初の偽で、`exists` は最初の真で打ち切る。
たどる値がなければ、`forall` は真、`exists` は偽である。

### 複合型の値を作る式

| 式 | 型 | 評価 |
|---|---|---|
| `{"tuple": [a, ...]}` | Tuple | 要素を記述順に評価する |
| `{"record": [{"name", "expr"}, ...]}` | Record | フィールドを記述順に評価する。フィールドの順序が型の順序になる |
| `{"none": 型}` | Option | 値のないOption |
| `{"some": [a]}` | Option | 値のあるOption |
| `{"set": {"of": 型, "items": [a, ...]}}` | Set | 要素を記述順に評価する。要素の型に属さない値なら `not_in_domain` |
| `{"map": {"key": 型, "value": 型, "items": [[k, v], ...]}}` | Map | 組を記述順に `put` する |
| `{"list": {"of": 型, "max": n, "items": [a, ...]}}` | List | 要素を記述順に評価する。要素の型に属さない値なら `not_in_domain`。要素の数が `max` を超えるモデルは拒否する |

### 複合型の値を調べる式

| 式 | 型 | 評価 |
|---|---|---|
| `{"nth": {"of", "index"}}` | 要素の型 | Tupleの要素。`index` は整数のリテラル |
| `{"field": {"of", "name"}}` | フィールドの型 | Recordのフィールド |
| `is_some`、`is_none` `[o]` | Bool | Optionの値の有無 |
| `unwrap` `[o]` | 中身の型 | Optionの値。値がなければ `none` |
| `contains` `[c, x]` | Bool | Setの要素か、Listに含まれる。Setでは、要素の型に属さない値は含まれない |
| `insert`、`remove` `[s, x]` | Set | 要素を加えた、または除いたSet。`insert` では、要素の型に属さない値なら `not_in_domain` |
| `union`、`intersection`、`difference` `[a, b]` | Set | 同じ型のSetどうしの和、共通部分、差 |
| `subset` `[a, b]` | Bool | `a` が `b` の部分集合 |
| `size`、`is_empty` `[c]` | Int、Bool | Set、Listの要素の数、Mapのキーの数 |
| `has_key` `[m, k]` | Bool | Mapがキーを持つ。キー型に属さない値は持たない |
| `get` `[m, k]` | 値の型 | キーの値。キーがなければ `missing_key` |
| `put` `[m, k, v]` | Map | キーに値を置いたMap。`k`、`v` の順に評価し、それぞれ型に属さなければ `not_in_domain` |
| `delete` `[m, k]` | Map | キーを除いたMap |
| `keys` `[m]` | Set | Mapのキーの集合。要素の型はキー型 |
| `at` `[l, i]` | 要素の型 | Listの `i` 番目（0から数える）。`i` が負か長さ以上なら `index_out_of_range` |
| `first`、`last` `[l]` | 要素の型 | Listの最初と最後の要素。空なら `empty` |
| `push` `[l, x]` | List | 末尾に `x` を加えたList。要素の型に属さなければ `not_in_domain`、そうでなく長さが `max` なら `full` |
| `pop`、`shift` `[l]` | List | 末尾、または先頭の要素を除いたList。空なら `empty` |

### 評価の順序と失敗

演算子は、オペランドを記述順にすべて評価してから計算する。
例外は、打ち切る演算（`all`、`any`、`implies`、`ite`）と量化で、これらは結果が決まったところで残りを評価しない。
また、値を型の決まった場所に置く演算（Set、Map、Listのリテラル、`insert`、`put`、`push`）は、置く値を1つ評価するたびに、その値が型に属するかを検査する。
`put` でキーが型に属さなければ、値の式は評価しない。
複合型の値の `ite` も、選ばれた枝だけを評価する。
`let` の `value` は、`body` で使わなくても評価する。

評価した部分式の失敗は、そのまま式全体の失敗になる。
失敗の種類は次のとおりである。

| `kind` | 原因 |
|---|---|
| `overflow` | 整数の演算の結果が64ビット整数に収まらない |
| `division_by_zero` | `div`、`mod` の除数が0 |
| `out_of_range` | 状態変数か出力に、型の範囲外の整数を置く（遷移を参照） |
| `none` | 値のないOptionの `unwrap` |
| `missing_key` | Mapにないキーの `get` |
| `index_out_of_range` | Listの範囲外の `at` |
| `full` | 長さが `max` のListへの `push` |
| `empty` | 空のListの `first`、`last`、`pop`、`shift` |
| `not_in_domain` | Setの要素、Mapのキーや値、Listの要素に、型に属さない値を置く |

型検査はすべての枝を対象にする。
評価されない枝に型エラーや未定義の参照があるモデルも、IR検証で拒否する。
IR検証を通ったモデルでは、評価の失敗は上の種類に限られる。

## 遷移

状態 `s` で操作を引数の組（公開引数と内部選択）に適用した結果は、次の順で決まる。

1. 動的ドメイン（後述）を、引数の宣言順に調べる。引数の値がドメインに含まれなければ、その組は無効である。
2. `guard` を評価する。偽なら、その組は無効である。更新式も出力式も評価しない。
3. `updates` を記述順に評価する。式はすべて遷移前の状態で評価する（同時代入）。値の中の整数が、対象の状態変数の型の範囲外なら範囲外更新である。
4. `output` を評価する。値が出力の型の範囲外なら範囲外更新である。

途中で評価に失敗した場合は、最初に失敗した箇所（`guard`、`update`、`output`）を報告する。
動的ドメインの評価の失敗は `guard` として報告する。
範囲外更新は評価エラーであり、遷移を黙って除外することはない。
同じ状態変数への重複代入は、IR検証で拒否する。
出力の型は、Bool、Int、Enumに限る。

複合型の値の範囲外更新では、値の中の整数をスロットの順に調べ、最初に範囲外だったものを報告する。

引数の組は、公開引数、内部選択の順に、各引数の値を正規順に並べた列の辞書順に列挙する。
引数のドメインは型全体であり、値を1つずつ列挙する。
Setの引数なら、要素の型の値が3つのとき、8通りの値をとる。

引数の宣言に `in` を書くと、その引数の値は `in` の式の値（SetかList）の要素に限られる（**動的ドメイン**）。
`in` の式は、状態と、それより前に宣言した引数（公開引数のあとに内部選択）を参照できる。
列挙するのは型全体のままで、ドメインに含まれない値の組を無効にする。
`in` の評価の失敗は、`guard` の失敗として報告する。

```json
{"name": "drop", "params": [{"name": "x", "type": {"enum": "item"}, "in": {"var": 0}}],
 "updates": [{"target": 0, "expr": {"remove": [{"var": 0}, {"param": 0}]}}]}
```

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
初期状態を正規順に起点にし、それぞれの不変条件を、探索を始める前にこの順で検査する。
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

## 証拠の検査の資源上限と中断

判定ゲートは、証拠の検査にかかる計算を、式の評価回数の上限で見積もる。
量化の範囲と引数のドメインはモデルの中で固定なので、1つの状態の検査（対象の不変条件、対象の操作の全引数での遷移と遷移契約、終端条件）にかかる評価回数の上限は、状態によらず、モデルと検査条件だけで決まる。
`ite` は重いほうの枝を、`all` と `any` は打ち切らない場合を数えるので、見積もりは実際の評価回数以上になる。
証明書の見積もりは、この上限に状態の数を掛けたものである。
トレースの見積もりは、この上限にステップ数と1の和を掛けたものである。

`check` と `verify-certificate` の `--max-check-cost`（`max_check_cost`）は、この見積もりの上限である。
見積もりが上限を超える証拠は検査せず、`inconclusive`（理由は `max_check_cost`）とする。
省略時は上限を設けない。

証明書の検査は、状態の数を区切って進める。
区切りは、見積もりで約2^20回の評価ごとで、1つの状態の見積もりがこれを超えるモデルでは1状態ごとである。
区切りごとに中断要求を確かめ、要求があれば `inconclusive`（理由は `interrupted`）とする。
トレースの検査は区切らないが、`max_check_cost` で抑えられる。

打ち切った検査の `inconclusive` は、モデルについて何も主張しない。
打ち切るかどうかの判断は検証の対象外のコードで行うが、どう判断しても `verified` と `violated` の意味は変わらない。

## シミュレーション

`simulate` は、各トレースを初期状態から始め、有効な具体的遷移から1つを一様に選んで進む。
初期状態が複数あれば、トレースごとに開始状態を一様に選ぶ。
初期状態が1つなら、開始状態の選択に乱数を使わない。
遷移の列挙順は幅優先探索と同じで、操作の定義順、引数の辞書順である。
初期状態と各到達状態の不変条件、選んだ辺の遷移契約を検査し、違反または評価エラーで止まる。
有効な遷移のない状態では、デッドロックを検査してから、そのトレースを終える。

乱数はSplitMix64である。
`n` 個の遷移から選ぶときは、64ビットの乱数 `x` が `2^64 mod n` 以上になるまで引き直し、`x mod n` 番目を選ぶ。
開始状態も、同じ方法で正規順の初期状態から選ぶ。
同じモデル、検査条件、seed、トレース数、最大ステップ数に対して、結果は同じになる。

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

`states` は状態の配列で、各状態は状態変数の値のJSONを定義順に並べた配列である。
初期状態をすべて含まなければならない。
到達できる状態の上位集合でもよい。
読み込み時にスロットの列の辞書順（正規順）に整列するので、ファイル中の順序は問わない。

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

`seed` は、シミュレーションが見つけたトレースではそのseed、それ以外では `null` である（省略してもよい）。再生には使わない。

`initial` は、トレースの開始状態である。
初期状態が1つのモデルでは省略でき、省略するとその初期状態から始める。
判定ゲートは、開始状態がモデルの初期状態の1つであることを確かめる。
そうでないトレースは、理由 `bad_start` で拒否する。

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

`error` は `{"kind": 種類}` で、種類は「評価の順序と失敗」の表のとおりである。
範囲外更新は `{"kind": "out_of_range", "value": 5, "type": {...}}` で、範囲外の値と、その値を置こうとした整数の型を持つ。
`type` は表示用で、読み込み時には使わない。
複数のスロットを持つ状態変数の範囲外更新では、`claim` の `slot` に、範囲外の整数のスロットの位置（状態変数の中で0から数える）を書く。

`replay` は、トレースに記録された検査条件で、各ステップの出力と状態、末尾の主張を検査する。

`shrink` は、トレースを、同じ主張を保ったまま短くする。
操作列からステップを削った候補を同じ開始状態から再実行して状態と出力を計算し直し、判定ゲートが同じ主張で受理した候補だけを採用する。
結果は局所最小である。
結果の `original_steps` に、縮小前のステップ数を記録する。
判定ゲートが受理しないトレースは縮小せず、`rejected` を返す。

## 検査の結果

| キー | 内容 |
|---|---|
| `status` | `verified`、`violated`、`error`、`inconclusive`、`internal_error` |
| `model`、`model_digest`、`engine_version`、`ir_version` | モデルとエンジンの識別 |
| `conditions` | 検査条件 |
| `search` | 探索器の報告。`complete`、`visited_states`、`transitions`、`time_ms`。検査済みの値ではない |
| `gate` | 判定ゲートが証拠の検査にかけた時間 |
| `certificate_states` | `verified` のとき、判定ゲートが受理した証明書の状態数 |
| `property`、`trace` | `violated`、`error` のとき、起きた事象と、判定ゲートが受理したトレース |
| `reason` | `inconclusive` のとき、`max_states`、`max_check_cost`、`interrupted` のいずれか |
| `rejected` | 探索器が生成した証拠を判定ゲートが拒否した `internal_error` のとき、拒否した理由 |
| `inconsistency` | 探索器が内部の不整合で証拠を生成できなかった `internal_error` のとき、不整合の内容。このとき `reason` と `rejected` は付けない |
| `message` | `internal_error` のとき、fmspec の不具合であることを示す説明 |

`inconsistency` は `{"kind": "successors", "action", "state", "encoded_state", "message"}` で、
状態での操作の遷移を列挙できなかったことを表す（操作が未定義か、状態が状態型に従わない）。
`action` は操作名で、未定義の操作なら添字である。
`encoded_state` は状態の符号化列で、`state` は状態型に従うときだけ値を示し、従わなければ `null` である。
カバレッジとテスト経路の結果（`coverage`、`test_paths`）も、グラフを集める途中で不整合を見つけたら、
`status` を `internal_error` とし、`model`、`model_digest`、`engine_version`、`inconsistency`、`message` だけを返す。

`simulate --json` の結果は、`search` と `gate` の代わりに `simulation` を持つ。
`simulation` はシミュレータの報告で、`seed`、`traces`、`max_steps`、`prng`、`completed_traces`、`steps`、`time_ms` からなる。
違反も評価エラーも見つからなければ `status` は `sampled` で、指定したサンプルの検査を完了したことだけを表す。
見つかった場合の `status`、`property`、`trace` は `check` と同じで、トレースの `seed` にシミュレーションのseedを記録する。

`verify-certificate` と `replay` の結果は同じ形で、`search` を持たない。
提示された証拠を判定ゲートが拒否した場合の `status` は `rejected` である。

終了コードは、`verified` と `sampled` が0、`violated` と `rejected` が1、`error`、不正な入力、`internal_error` が2、`inconclusive` が3である。
