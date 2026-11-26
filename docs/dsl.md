# 仕様記述DSL

Rubyで状態遷移の仕様を書き、モデル検査を行うためのAPIを説明する。
設計の背景は[設計仕様書](ruby_model_checker_spec.md)§4にある。
DSLが生成するIRの形式と、検査の意味は [ir.md](ir.md) にある。

## 仕様の定義

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

Tickets.check(max_states: 10_000).verified? # => true
```

`Fmspec.define` はブロックを一度だけ実行して型付きIRを組み立て、`Fmspec::Model` を返す。
検査のときにRubyのコードが呼ばれることはない。

ブロックに渡る `s` は**記号的な状態**である。
状態変数や定数を名前で参照すると、値ではなく**記号式**が返る。
記号式どうしの演算は、計算をせずに式を組み立てる。

`require "fmspec/dsl"` だけなら、native extensionを読み込まずに、仕様の定義とIRの生成（`Model#to_ir`）までを行える。

## 型

| 書き方 | 型 | Rubyの値 |
|---|---|---|
| `int(0..4)`、または整数の範囲 `0..4` | 有界の整数 | Integer |
| `bool` | 真偽値 | `true`、`false` |
| `enum(:result, :success, :forbidden)` | 列挙型。ラベルはSymbolで書く | Symbol |
| `tuple(int(0..2), bool)` | 組 | Array |
| `record(x: int(0..2), y: int(0..2))` | フィールド名の付いた組 | Hash（キーはSymbol） |
| `option(user)` | 値がないこと（`nil`）を含む型 | `nil`、または値 |
| `set_of(item)` | 有限集合 | Set、またはArray |
| `map_of(item, int(0..3))` | 有限写像 | Hash |
| `list_of(int(0..3), max: 4)` | 長さに上限のある列 | Array |

`enum` は列挙型を宣言して、その型を返す。
同じ名前とラベルで繰り返し呼ぶと、同じ型を返す。

`set_of` の要素と `map_of` のキーの型は、値の数が4096以下で、`set_of`、`map_of`、`list_of` を含まない型に限る。
型の意味、値の正規順、上限は [ir.md](ir.md) にある。

列挙型の値と複合型の値は、型が文脈から決まる位置ではRubyの値で書ける。
状態変数の初期値と更新、`eq` と `ne` の右辺、`ite` のもう一方の枝が型の決まった式である場合、`include?` や `put` などの要素の位置がこれにあたる。

```ruby
state :basket, set_of(item), initial: Set[]
state :holder, option(user), initial: nil
state :pos, record(x: int(0..2), y: int(0..2)), initial: { x: 0, y: 0 }

update pos: { x: s.pos[:x] + 1, y: s.pos[:y] }
guard s.holder.eq(nil)
```

型が決まらない位置では、列挙型の値を `result[:success]`、Optionの値を `some(x)`、`none(user)`、そのほかの複合型の値を `型.value(値)` と書く。
`ite` の両方の枝がRubyの値の場合がこれにあたる。
複合型のリテラルを型の決まらない位置に書くと、`Fmspec::BuildError` になる。

```ruby
seats = list_of(user, max: 2)
update seated: ite(s.seated[0].eq(out), seats.value([inn, s.seated[1]]), [s.seated[0], inn])
```

## 状態変数と定数

```ruby
state :sold, int(0..4), initial: 0
constant :capacity, 3
constant :menu, set_of(item), Set[:apple, :bread]
```

定数は、記号的な状態から状態変数と同じように参照できる。
複合型の定数は、型を添えて `constant(名前, 型, 値)` と書く。
IRには、参照した位置にリテラルとして埋め込まれる。

`ghost :charges, int(0..2), initial: 0` は、履歴を記録するための補助状態（Ghost State）を宣言する。
モデル検査では `state` と同じで、`Model#ghosts` で名前を取り出せる。
使い方は [rails.md](rails.md) にある。

## 操作

```ruby
action :purchase, quantity: 1..2 do |s, quantity|
  guard s.sold + quantity <= s.capacity
  update sold: s.sold + quantity
end
```

キーワード引数は**公開引数**で、値はそのドメイン（型、または整数の範囲）である。
ドメインに、記号的な状態（と、それより前の引数）を受け取ってSetかListの式を返すlambdaを書くと、引数はその要素から選ばれる（**動的ドメイン**）。
引数の型は、要素の型になる。

```ruby
action :seat, u: ->(s) { s.waiting } do |s, u|
  update waiting: s.waiting.delete(u), seated: s.seated.push(u)
end

action :swap, out: ->(s) { s.seated }, inn: ->(s, out) { s.waiting.delete(out) } do |s, out, inn|
  # ...
end
```
ブロックは、記号的な状態と、各引数の記号式を受け取る。

| 語彙 | 意味 |
|---|---|
| `guard 式` | 遷移の有効性。複数書くと、すべてが真のときに有効になる。省略すれば常に有効 |
| `update 名前: 式, ...` | 状態更新。同時代入で、式は遷移前の状態で評価する。書かなかった変数は維持する |
| `unchanged` | 状態を変えないことの明示 |
| `choose(:名前, 型)` | 内部選択を宣言し、その値の記号式を返す。型の代わりにSetかListの式を渡すと、その要素から選ぶ |
| `returns 式` | 出力。型は式から決まる。整数の出力に範囲を付けるときは `returns 式, int(0..3)` と書く。出力の型は bool、整数、列挙型に限る |
| `ensures(:名前) { \|after, result\| 式 }` | 遷移契約。この操作のすべての有効な遷移で成り立つべき事後条件 |
| `preserves :名前, ...` | 指定した状態変数がこの操作で変わらない、という遷移契約 |

`ensures` のブロックは、遷移後の記号的な状態と、出力の記号式を受け取る。
遷移前の状態と引数は、操作のブロックの変数をそのまま使う。

内部選択は、同じ公開入力に対する複数の許容結果を表す。
次の操作は、同じ `id` に対して `success` と `forbidden` のどちらも返しうる。

```ruby
action :request, id: 7..7 do |_s, _id|
  allowed = choose(:allowed, bool)
  returns ite(allowed, :success, :forbidden), result
  ensures(:succeeds) { |_after, out| out.eq(:success) }
end
```

### 受理と拒否

無効なguardは「実装が拒否すること」の仕様にならない。
拒否を検査する場合は、拒否も有効な遷移として書く。
`accept_if` は業務上の受理条件を宣言し、`on_accept` と `on_reject` が受理と拒否それぞれの更新と出力を書く。

```ruby
action :cancel, user: 0..1 do |s, user|
  accept_if s.owner.eq(user) & s.order.eq(:open)
  on_accept do
    update order: :cancelled
    returns :success
  end
  on_reject do
    unchanged
    returns :forbidden
  end
end
```

この操作は1つの操作としてIRになる。
`order` の更新は `ite(受理条件, :cancelled, order)`、出力は `ite(受理条件, :success, :forbidden)` である。
`guard` と違い、受理条件が偽でも遷移は有効で、状態と出力が検査の対象になる。

仕様書§12.1の `requires`、`modifies` は未実装である。

## 不変条件と終端条件

```ruby
invariant(:capacity_respected) { |s| s.sold <= s.capacity }
terminal { |s| s.sold.eq(s.capacity) }
```

`terminal` が真になる状態は、有効な遷移がなくてもデッドロックとみなさない。

## 式

| 書き方 | 意味 |
|---|---|
| `a + b`、`a - b`、`a * b`、`-a` | 整数の演算。64ビット整数に収まらなければ評価エラー |
| `a < b`、`a <= b`、`a > b`、`a >= b` | 整数の比較 |
| `a.eq(b)`、`a.ne(b)` | 同じ型どうしの等価性 |
| `a & b`、`a \| b` | 論理積、論理和。左から評価し、結果が決まれば右を評価しない |
| `a.not_` | 否定 |
| `a.implies(b)` | 含意。`a` が偽なら `b` を評価しない |
| `ite(条件, x, y)` | 条件式。選ばれた枝だけを評価する |
| `min(a, b)`、`max(a, b)` | 整数の小さいほう、大きいほう。`min(s.n + 1, 2)` は2で飽和する増分になる |
| `all(a, b, ...)`、`any(a, b, ...)` | 記述順に評価し、結果が決まれば打ち切る |
| `a / b`、`a % b` | 床除算と、その剰余（Rubyの整数と同じ）。`b` が0なら評価エラー |
| `let(式) { \|x\| 本体 }` | 式を一度だけ評価して、本体に渡す |
| `forall(集合か型) { \|x\| 式 }`、`exists(...)` | 量化。集合は `set_of`、`map_of`（キー）、`list_of` の式で、型ならそのすべての値をたどる |

`&` と `|` はRubyの比較演算子より優先順位が高いので、両辺を括弧で囲む。

```ruby
guard (s.sold > 0) & (s.sold < 3)
```

`ite`、`all`、`any`、`implies`、`not_` は、定義の外では `Fmspec.ite(...)` のように呼べる。

### 複合型の式

複合型の値の式は、RubyのArray、Hash、Setに似たメソッドを持つ。
どのメソッドも新しい値の式を返し、元の値を変えない。
`s.queue.push(x)` は、`x` を末尾に加えた列の式であり、`update queue: s.queue.push(x)` で状態を更新する。

| 型 | 書き方 | 意味 |
|---|---|---|
| tuple | `t[0]` | 要素。位置は整数のリテラル |
| record | `r[:x]` | フィールド |
| option | `o.some?`、`o.none?`、`o.unwrap` | 値の有無と、値。値がなければ `unwrap` は評価エラー |
| set_of | `s.include?(x)`、`s.add(x)`、`s.delete(x)` | 要素か、要素を加えたSet、除いたSet |
| set_of | `a \| b`（`a + b`）、`a & b`、`a - b`、`a <= b` | 和、共通部分、差、部分集合。`union`、`intersection`、`difference`、`subset?` とも書ける |
| map_of | `m[k]`、`m.key?(k)`、`m.put(k, v)`、`m.delete(k)`、`m.keys` | キーの値、キーの有無、キーに値を置いたMap、キーを除いたMap、キーのSet。キーがなければ `m[k]` は評価エラー |
| list_of | `l[i]`、`l.first`、`l.last`、`l.include?(x)` | 要素。範囲外や空なら評価エラー |
| list_of | `l.push(x)`、`l.pop`、`l.shift` | 末尾に加えたList、末尾、先頭を除いたList。満杯や空なら評価エラー |
| 共通 | `c.size`、`c.empty?`、`c.all? { \|x\| ... }`、`c.any? { \|x\| ... }` | 要素の数、空か、量化。map_of ではキーについて |

Setの要素、Mapのキーと値、Listの要素に、型に属さない値を置くと評価エラーになる。
`include?` と `key?` は、型に属さない値には偽を返す。

```ruby
item = enum(:item, :apple, :bread, :milk)
state :items, set_of(item), initial: Set[]

action :add, x: item do |s, x|
  guard s.items.include?(x).not_
  update items: s.items.add(x)
end

invariant(:small) { |s| s.items.size <= 2 }
invariant(:no_milk_alone) { |s| s.items.include?(:milk).implies(s.items.any? { |y| y.ne(:milk) }) }
```

## 記号ブロックで使えない構文

記号ブロック（`action`、`invariant`、`terminal`、`ensures`、`on_accept`、`on_reject` のブロック）の中で、次の構文は使えない。

| 構文 | 代わりに使うもの |
|---|---|
| `if`、`unless`、条件演算子、`case` | `ite` |
| `&&`、`and` | `&` |
| `\|\|`、`or` | `\|` |
| `!`、`not` | `not_` |
| `==`、`!=` | `eq`、`ne` |
| `while`、`until` | なし |

記号式はRubyの値としては常に真である。
`s.sold > 2 ? 0 : 1` と書くと、Rubyは仕様の構築時に `0` を選び、条件は式に残らない。
`s.sold == 0` は、式ではなく `false` になる。
こうした誤りを防ぐために、`Fmspec.define` は記号ブロックのソースをPrismで読み、上の構文があれば `Fmspec::BuildError` で拒否する。

この検査には次の性質がある。

- 記号ブロックの中の構文すべてが対象で、記号式に使っているかどうかは区別しない。静的な分岐や繰り返しは、記号ブロックの外に書く。
- ブロックから呼ぶメソッドの中は見ない。`==`、`!=`、`!` は記号式の演算子が実行時に拒否するが、メソッドの中の `if` や `&&` は検出できない。
- ソースを読めないブロック（`eval` した文字列の中など）は検査できないので拒否する。
- 同じ行で始まるブロックが複数あれば、すべて検査する。

## 検査

| メソッド | 内容 |
|---|---|
| `check(max_states: nil, certificate: false, **検査条件)` | 幅優先探索によるモデル検査 |
| `simulate(traces: 100, max_steps: 100, seed: nil, **検査条件)` | ランダムシミュレーション |
| `verify_certificate(証明書, **検査条件)` | 証明書の検査 |
| `replay(トレース)` | トレースの再生 |

検査条件は、`deadlock:`（非終端のデッドロックを検査する）と、`actions:`、`invariants:`、`contracts:`（対象の名前の配列）である。
省略時は、すべての操作、不変条件、遷移契約が対象で、デッドロック検査は無効である。

検査の間はGVLを解放するので、他のRubyスレッドが動作できる。
`Timeout` や `Thread#kill` などの割り込みは、探索を打ち切って例外として伝わる。

結果は `Fmspec::Result` である。

| メソッド | 内容 |
|---|---|
| `status` | `:verified`、`:violated`、`:error`、`:inconclusive`、`:sampled`、`:rejected`、`:internal_error` |
| `verified?` など | `status` の判定 |
| `property` | 違反した性質、または評価エラーの箇所。定義のソース位置を含む |
| `trace` | 違反または評価エラーに至るトレース（`steps`、`states`、`initial`） |
| `certificate` | `check(certificate: true)` で受理された証明書 |
| `reason` | `:inconclusive` の理由 |
| `visited_states`、`search`、`simulation` | 探索器の報告。検査済みの値ではない |
| `to_s` | 人間向けの報告 |
| `to_h` | エンジンの結果（[ir.md](ir.md)の形式） |

`:verified`、`:violated`、`:error` は、エンジンの判定ゲートが証拠を検査してから返した判定である。
`:sampled` は指定したサンプルの検査を完了しただけで、網羅性の主張はない。

`Model#shrink(トレース)` は、モデル違反のトレースを、同じ違反を保ったまま短くする。
シミュレーションで見つけたトレースに使う。
幅優先探索の反例は、不変条件の違反については最初から最短である。

エンジン内部のpanicは `Fmspec::InternalError` になる。
これは `Exception` の子で、`rescue => e` では捕まらない。

## 実装との適合性検査

仕様から操作列を生成して実装に適用し、戻り値と観測値を仕様と照合する。
これは有限回のテストであり、成功しても実装の正しさの証明にはならない。
モデル検査の `:verified` とは別の結果である。

### Binding

```ruby
binding = Tickets.bind do
  setup { BoxOffice.new(capacity: 3) }

  command(:purchase) { |office, quantity:| office.sell(quantity) }
  command(:cancel, method: :refund)

  observe(:sold) { |office| office.sold }
end
```

| 語彙 | 意味 |
|---|---|
| `setup { ... }` | 各テストケースで、新しい実装のコンテキストを返す |
| `teardown { \|context\| ... }` | 各テストケースの終わりに呼ばれる。失敗したケースでも呼ばれる |
| `command(:操作) { \|context, 引数:\| ... }` | 操作のハンドラ。操作の公開引数をキーワードで受け取る |
| `observe(:状態変数) { \|context\| ... }` | 実装の状態を、仕様上の値に射影する |

`command(:操作, inject: [:内部選択]) { ... }` は障害注入である。
名前を挙げた内部選択の値をテストが決め、ブロックにキーワードで渡す。
Railsアプリケーションとの結合と合わせて、[rails.md](rails.md) で説明する。

`command :cancel, method: :refund` と `observe :sold, method: :sold` は、コンテキストのメソッドを呼ぶ短縮形である。
メソッド名を暗黙に推測することはない。

`command` と `observe` のブロックは実装を操作する普通のRubyで、記号ブロックではない。

`bind` は、登録を実行の前に仕様と照合する。
`command` のない操作、仕様にない操作や状態変数の登録、操作の引数と合わないキーワード引数は `Fmspec::BuildError` になる。

値の対応は次のとおりである。
仕様の値にならない値（別の型の値、`option` でない型の `nil`、範囲外の整数、未定義のラベル）は、仕様のどの値とも一致しない。

| 仕様の型 | 実装の値（`observe` と戻り値） | `command` に渡す値 |
|---|---|---|
| 整数 | Integer | Integer |
| bool | `true`、`false` | `true`、`false` |
| 列挙型 | ラベルと同じ名前のSymbolまたはString | Symbol |
| tuple | Array | Array |
| record | Hash（キーはSymbolかString）、または `to_h` で Hash になるもの | Hash（キーはSymbol） |
| option | `nil`、または値 | `nil`、または値 |
| set_of | Set、またはArray | Set |
| map_of | Hash | Hash |
| list_of | Array | Array |

### テストの実行

```ruby
result = Tickets.test(binding, cases: 100, steps: 20, seed: 42)
result.assert_passed!
```

各ケースで、`setup` のあとに初期状態を観測し、以後は1ステップずつ、入力の選択、`command` の実行、観測、照合を繰り返す。
入力は仕様から選ぶ。
仕様で無効な入力を実装に適用することはない。

照合するのは次の2つである。

- 操作が `returns` で出力を宣言していれば、`command` の戻り値と出力。宣言していなければ、戻り値は見ない。
- `observe` を登録した状態変数の値。登録していない状態変数は、観測できないものとして扱う。

`test` のオプションは次のとおりである。

| オプション | 内容 |
|---|---|
| `cases:`、`steps:` | テストケースの数と、1ケースの最大ステップ数 |
| `seed:` | 省略すると無作為に選び、結果に記録する |
| `actions:` | 対象の操作の名前の配列 |
| `shrink:`、`shrink_runs:` | 失敗した操作列を縮小するか、縮小で再実行する回数の上限 |
| `replay:` | 操作列。生成せずに、その操作列を1回だけ再実行する |
| `max_candidates:` | 候補状態の数の上限 |

### 非決定性と部分観測

内部選択のある仕様や、観測しない状態変数のある仕様では、実装がいまどの状態にあるかが一意に決まらない。
テストは、これまでの入力、戻り値、観測と矛盾しない仕様の状態を、**候補**としてすべて持つ。
応答を受け取るたびに、その応答を生じうる遷移の遷移先だけを残す。

- 候補が空になれば、不適合である。複数の候補が残ることは失敗ではない。
- 次の入力は、全候補で有効な入力から選ぶ。
- どの候補にも有効な入力がなければ、そのケースはそこで終わる。
- 有効な入力を持つ候補があるのに、全候補に共通する入力がなければ、そのケースは未完了（`:inconclusive`、理由は `:no_common_input`）で終わる。

### 結果

`test` は `Fmspec::TestResult` を返す。

| `status` | 意味 |
|---|---|
| `:passed` | すべてのケースで、戻り値と観測が仕様と一致した |
| `:conformance_failure` | 戻り値または観測が、仕様の許すどの結果とも一致しない |
| `:execution_error` | `command` または `observe` が例外を上げた |
| `:setup_error` | `setup` または `teardown` が例外を上げた |
| `:model_error` | 仕様の評価エラーに行き当たった |
| `:model_violation` | 仕様の不変条件または遷移契約の違反に行き当たった |
| `:inconclusive` | 未完了のケースがあった |

`assert_passed!` は、`:passed` でなければ `Fmspec::TestFailed` を上げる。
未完了のケースを含む実行は成功として扱わない。

失敗した結果は、次の報告になる。

```text
Conformance failure: tickets / sold
  seed: 42
  1. purchase(quantity: 2)
  2. cancel()
  expected sold: 1
  observed sold: 0
  specification: spec/models/tickets.rb:12
  binding: spec/models/tickets_binding.rb:8
```

`:conformance_failure` と `:execution_error` の操作列は、報告の前に縮小する。
縮小は、操作列からステップを削った候補を、新しいコンテキストで再実行し、同じ操作で同じ項目の不一致（または同じクラスの例外）が起きる候補を採用する。
削ったために後続の入力が仕様で無効になる候補は、実装に適用せずに捨てる。
結果は局所最小である。

`TestResult#inputs` は失敗に至る操作列で、`Tickets.test(binding, replay: result.inputs)` でそのまま再実行できる。
`matched_steps` は、`command` を実行して戻り値と状態の照合まで完了した回数である。
