# 下ろしの全域性と整形式性の証明計画

型の合うモデルの読み込みが内部エラーにならないことと、下ろしたモデルが必ずIR検証を通ることを、Verusで証明する計画である。
作業の内容と手順を、別の作業者や別のセッションが引き継げるように書く。
証明の現状は [verification.md](../verification.md) にある。

## 現状の保証と足りないもの

中核の下ろし（`lower_model`）について、今は部分正当性だけを証明している。
`lemma_safe`（`model_safe.rs`）は、`lower_model` が中核のモデル `m` を返したなら、どの検査条件でも、`m` の安全性と、名前を解決したモデルの値の意味論での安全性が同値であることを示す。
したがって、下ろしに不具合があっても、誤った `Verified` にはならない。

一方、次の2つは証明していない。

- **全域性**：型の合うモデルなら、`lower_model` が内部の誤りを返さないこと。下ろしは、型が合わない入力に `None` や `Fault::Lower` を返し、`fmspec-ir` はそれを内部エラーにする。この経路が型の合うモデルで起きないことは、参照実装との比較テストとランダムなモデルで確かめているだけである。
- **整形式性**：`lower_model` が返したモデルが整形式（`typing.rs` の `wf`）であること。今は `fmspec-ir` が下ろしの後に `validate` を呼ぶ。下ろしの不具合で `validate` が拒否すると、利用者の誤り（`InvalidModel`）のように報告される。

## 目標の形

読み込みの経路の各段に、次の役割と保証を持たせる。

| 段 | 役割 | 保証 |
|---|---|---|
| `fmspec-ir` | 名前の解決、型の推論、型付きの式の木の組み立て。誤りのメッセージとJSONの位置を作る | テスト（信頼基盤に残る） |
| `check`（中核、`infer.rs`） | 式の木の型を検査し直す | 結果が型付け規則 `type_of` と完全に一致する |
| `lower_model`（中核） | 定数と初期値の評価、下ろし | 型が付き、大きさの条件を満たすモデルでは内部の誤りを返さない。返したモデルは `wf` を満たし、安全性を保つ |
| `validate`（中核） | IR検証 | 下ろしたモデルを必ず受理する |

`fmspec-ir` の型推論は残す。
式の木の頂点の種類（`SetContains` か `ListContains` か、など）は型で決まるので、木を組み立てるのに型推論が要る。
JSONの位置付きのメッセージを作るのも `fmspec-ir` である。
中核の `check` は、その結果を検査し直す。

最終的な `lower_model` の事後条件は、前提なしで次の形にする。

- 内部の誤りを返すなら、モデルの型付けか大きさの条件が成り立たない。
- `Ok(m)` なら、`wf(m)` が成り立ち、`lowers_model(sm, m)` が成り立つ。

この形にすると、読み込みの誤りは次の3種類に分かれる。

- **`fmspec-ir` が報告する利用者の誤り**：JSONの形、名前、型の誤り。JSONの位置付きで報告する。
- **中核が報告する利用者の誤り**：値で決まる誤り。定数や初期値が型の範囲外、候補の組が多すぎる、初期条件の評価エラー、初期状態がない、の場合である。
- **内部エラー**：`fmspec-ir` が組み立てた木を、中核の `check` か大きさの条件の検査が拒否した場合だけ。原因は `fmspec-ir` と中核の検査のずれに絞られる。

## 決めた方針

### 大きさの条件は型付け規則とは別に持つ

下ろしは、型が合っていても、大きさの理由で `None` を返す。
たとえば、長さの上限が `0x7fff_ffff` を超えるListの等価比較と添字、キーの数が `0x7fff_ffff` を超える型の量化、スロットの数の計算のオーバーフローである。
最初の段階では、これらを `type_of` に入れず、別の述語（仮の名前は `limits_ok`）として持つ。
定理の前提は「`type_of` で型が付き、`limits_ok` が成り立つ」になる。
`type_of` に入れる方法より、`infer.rs` の変更が少なく済むからである。

`fmspec-ir` の上限（`types.rs` の `MAX_KEYS` = 4096、`MAX_LIST` = 1024、`MAX_WIDTH` = 65536）は、中核の上限より厳しい。
`fmspec-ir` が受理した型は中核の条件も満たすはずだが、これは確かめていない。
手順1の棚卸しで確かめる。

統合するかどうかは、全体を終えた後に検討する（「後で検討すること」の節）。

### 整形式性を範囲に入れる

`validate` が下ろしたモデルを拒否しないことまで証明する（手順6）。
これがないと、下ろしの不具合が利用者の誤りのように報告される経路が残る。

### `infer.rs` を作り直して使う

`infer.rs` は、型付け規則 `type_of` と型検査器 `check` を持つ。
今はどこからも使われていない。
現状には、次の問題がある。

- `check` の事後条件は片方向で、「型を返したら `type_of` の値」だけである。型の付く式を拒否しないことは証明していない。
- 冒頭の説明に「規則は今の Rust 側の型検査（fmspec-ir の下ろし）と同じ」とあるが、`fmspec-ir` の型検査とも中核の下ろしの検査とも、一致は確かめていない。
- 式の木の頂点の種類は、作った後に変わっている可能性がある。

`type_of` を、下ろしが受理する条件の仕様として作り直し、`check` を `type_of` と完全に一致させる。

## 作業手順

`main` から切ったブランチで、段階ごとにコミットする。
各段階の終わりに「各段階の確認」の節の検査をすべて通してから、次の段階に進む。
時間は目安である。

### 1. 棚卸し（約1時間）

`lowering.rs`、`smodel.rs`、`model_lower.rs` で誤りを返す箇所を一覧にする。
`lowering.rs` だけで `None` を返す箇所が約80ある。
各箇所を次のどれかに分類する。

- **型の不一致**：部分式の型が期待と違う。
- **内部の整合性**：スロットの数の不一致、純粋でない式（`pure_exec`）、添字の範囲外など。
- **大きさの条件**：`0x7fff_ffff` などの上限、`keys_exec` が `None` になる型。
- **算術のオーバーフロー**：`checked_mul`、`checked_add` の失敗。
- **値による誤り**：定数、初期値、初期条件の評価の結果で決まるもの。

あわせて、次を突き合わせる。

- 型の不一致に分類した箇所と、`infer.rs` の `type_of` の規則。食い違いがあれば記録する。
- 大きさの条件に分類した箇所と、`fmspec-ir` の上限。`fmspec-ir` が受理するのに中核が拒否する型がないかを確かめる。
- `LowerError` の各変種が、利用者の誤りか内部の誤りか。たとえば、`InitCount` は「候補の列の数が状態変数の数と違う」（内部）と「候補の組が多すぎる」（利用者）の両方を表しているので、分ける必要がある。

成果物は、この文書に追記する分類の表である。
見つけた食い違いのうち、今の利用者に影響するもの（受理すべきモデルを内部エラーにする、など）は、不具合として別に記録する。

### 2. 型付け規則を受理条件の仕様にする（1〜2時間）

- `type_of` を、手順1の結果に合わせて直す。
- `check` の事後条件を「結果は `type_of` と一致する」（`r.map(xty) == type_of(...)` の形）に強める。
- 大きさの条件 `limits_ok` を、spec関数として定める。
- モデル全体の型付け `model_typed(sm)` を定める。次の各式に、その文脈での型が付くことを要求する。
  - 定数の式（状態を参照できない文脈）
  - 初期値の候補（状態を参照できない文脈）
  - 初期条件（状態を参照できる文脈）
  - 操作のguard（Bool）
  - 代入（状態変数の型に収まる）
  - 出力（出力の型に収まる）
  - 不変条件と終端条件（Bool）
  - 遷移契約（遷移後の状態と出力を参照できる文脈で、Bool）

文脈は `infer.rs` の `SCtx` で表す。
`SCtx` と下ろしの文脈 `LowerCtx` の対応も、ここで spec関数にしておく。

### 3. スロットの構造の事実（約1時間）

`lowering.rs` の `low` の事後条件に、環境によらない事実を加える。
返したスロットの数が型の幅と等しい、という事実である。
今のこの事実は、意味保存の主張 `lowers`（環境についての全称）の内側にしかない。
手順4のどの場合にも要るので、先に入れる。
`lower_prop` と `lower_stored` にも同じ事実を持ち上げる。

### 4. 式の下ろしの全域性（3〜5時間）

次を証明する。
「`type_of` で型 `x` が付き、`limits_ok` が成り立ち、局所変数の束縛の列 `sc` が型付けの局所変数の型の列に対応するなら、`low` は `Some` を返し、返した型は `x` である」。

意味保存の証明と同じ順で進める。

1. リテラル、参照、スカラーの演算、`not`、`all` と `any`、`implies`、条件式、`let`
2. 状態変数、引数、出力、定数、局所変数の参照と、`Map#get`
3. 量化（型の全体、Setの要素、Mapのキー、Listの要素）
4. Tuple、Record、Option
5. Set、Map、Listのリテラルと演算
6. 等価比較

最後に、`lower_prop` と `lower_stored` に持ち上げる。
`lower_stored` は入れ子の深さ（`depth`）を引数に持つので、深さの条件も前提に加える。

### 5. モデル全体の全域性（約1時間）

`model_typed(sm)` と `limits_ok` が成り立つなら、`lower_action` と `lower_model` が内部の誤りを返さないことを示す。
内部の誤りは、`Fault::Lower` を含む変種、`Guard`、`Update`、`Output`、`Invariant`、`Contract`、`Terminal` などである。
正確な範囲は、手順1の分類で決める。
内部の誤りを表す spec関数（仮の名前は `internal`）を定め、事後条件を「`internal(e)` なら `!(model_typed(sm) && limits_ok(sm))`」の形にする。

### 6. 整形式性（3〜6時間）

`lower_model` が `Ok(m)` を返したなら `wf(m)` が成り立つことを示す。
`wf` が要求するのは、主に次である。

- 状態の型が整形式である。
- 初期状態が1つ以上あり、各初期状態が型に従う。
- 操作の引数のドメインが整形式で、guard、代入、出力が中核の型規則（`typing.rs` の `type_of_spec`）で正しい型を持つ。
- 不変条件、遷移契約、終端条件がBoolの型を持つ。

このうち式の型が作業の大半になる。
下ろしで作る中核の式（スロットの式と、`let` で束縛する式）が、正しい型を持つことを示す必要がある。
式を作る部品（`slots.rs`、`ranking.rs`、`quant.rs`、`lists.rs`、`maps.rs`、`map_lookup.rs`、`equality.rs`、`canon.rs`）ごとに、作った式の型の補題を加え、`low` の事後条件に「各スロットの式は、スロットの型の中核の型を持つ」を加える。

この段階は見積もりの幅が最も大きい。
手順1〜5を先に `main` に入れ、この段階は別のPRにしてよい。

### 7. 経路への組み込みとテスト（1〜2時間）

- `lower_model` の中で、下ろしの前に `check` と `limits_ok` の検査を呼ぶ。これで、手順5の前提を検証済みのコードが確かめることになり、事後条件から前提が消える。拒否したときの誤りは、新しい変種（仮の名前は `LowerError::Type`）にする。
- `fmspec-ir` は、この新しい誤りを内部エラー（「`fmspec-ir` と中核の型検査が食い違います」）として報告する。手順6を終えた後は、`validate` の拒否も内部エラーとして報告してよい。
- ランダムに生成したIRで、`fmspec-ir` が受理することと、中核の `check` と `limits_ok` が受理することが一致するかを調べるテストを加える。
- 文書を更新する（「完了後に更新する文書」の節）。

## 手順1の結果（棚卸し）

`lowering.rs`、`smodel.rs`、`model_lower.rs` と、式を作る部品（`slots.rs`、`quant.rs`、`ranking.rs`、`map_lookup.rs`、`canon.rs`、`equality.rs`、`map_encoding.rs`）で、下ろしが `None` か `Err` を返す箇所を調べた。
`ranking.rs` と `map_lookup.rs` の `Err(ErrKind::...)` は、評価の意味論（spec関数の値）であり、下ろしの失敗ではないので除いた。

### 失敗の分類

| 分類 | 主な箇所 | 型の合うモデルで起きるか |
|---|---|---|
| 型の不一致 | `sub_scalar`、`bool_in` の型、`element`・`element_rank`・`lookup_rank` の `fits`、`low_leaf` の参照（状態のない文脈の `Var`、`next` のない文脈の `Next` と `Out`、添字の範囲外、範囲外の列挙型のラベル）、`low_core` の演算子と `Eq` の型、`low_struct` の `Nth`・`Field`・`IsSome`・`Unwrap`、`low_quant` のたどる値の型、`low_coll`・`low_access`・`low_get` の型と注釈の `stype_eq`、空の `Tuple` | 起きない（`type_of` が同じ条件で拒否する）。手順4で示す |
| 内部の整合性 | スロットの数の検査（`slots.len() != 1`、`s.len() == 0`、`cs.len() != n`、`at >= cs.len()`、`xs.len() != ys.len()`、`j >= xa.len()`）、`split`・`select`・`heads`・`ite_rows`・`list_parts`・`map_rows`・`eq_slots`・`store`・`rank_expr`・`mixed`・`unrank`・`map_slot_indices`・`encode_map_rows` の長さの検査、`ite_slots` の `pure_exec`、`eval_slots` と `eval_stored` の長さ | 起きない。スロットの数が型の幅と等しいこと（手順3）と、スロットの式が純粋であることから従う |
| 大きさ（中核の定数から従う） | キーの数が `0x7fff_ffff` 以下（`low_quant`、`low_set_lit`、`Size` の Map、`Delete` の行の数、`HasKey` と `Keys` の `present`）、`select` の行の数、`ranking.rs` の `append_rank_digit` | 起きない。中核の `keys` は `MAX_KEYS` = 4096 以下でしか `Some` にならない |
| 大きさ（中核の定数から従わない） | Listの長さの上限が `0x7fff_ffff` 以下（`At`、`First`、`Last`、`ListContains`、`List` をたどる量化、`Size` の List、`eq_slots` の `small_stype`）、`ListLit` の要素の数が `0x7fff_ffff` 以下 | `limits_ok` に入れる。`fmspec-ir` の `MAX_LIST` = 1024 で満たされる |
| 算術のオーバーフロー | `stype_width`・`xtype_width` の幅、`layout_slots` と `layouts_of` の位置、`split` の `at + w`、`list_parts` の `p * w + 1 + w`、`map_rows` と `low_quant` の `j * stride`、`k * w + 1 + j`、`push_block` の `off + j`、`arg_exprs` | `limits_ok` に入れる。式に現れるすべての型の幅が `usize` に十分収まること |
| 束縛の深さ | `bind`（深さ + 1 が `usize::MAX`）、`new_block`（深さが `usize::MAX`）、`low_quant` の `d.checked_add(1)`、これらを呼ぶ `atom`・`atoms`・`check`・`keep` | 型と大きさの条件だけでは除けない（下の「見つかった問題」） |
| 値による誤り | `Const(i, Eval)`、`Init(i, j, Eval)`、`Constraint(Eval)`、`NoInit`、候補の組が `MAX_INITIAL_CANDIDATES` を超える `InitCount`、`eval_slots` の範囲外の値 | 利用者の誤り |

### `LowerError` の各変種

| 変種 | 原因 | 区分 |
|---|---|---|
| `State(i)`、`Args(a, i)` | 状態変数と引数の型の `wf_stype`・`small_stype`（`check_types`）、位置の和のオーバーフロー（`layouts_of`）、`guard_fold` の正規形の判定の失敗 | 内部（`fmspec-ir` が型を先に検査する） |
| `Const(i, Lower)`、`Init(i, j, Lower)`、`Constraint(Lower)` | 下ろしの失敗 | 内部 |
| `Const(i, Eval)`、`Init(i, j, Eval)`、`Constraint(Eval)` | 評価の失敗 | 利用者 |
| `InitCount` | 初期値の候補の列の数が状態変数の数と違う | 内部。分ける |
| `InitCount` | 候補の組の数が `MAX_INITIAL_CANDIDATES` を超える、または `usize` に収まらない | 利用者。分ける |
| `NoInit` | 初期条件を満たす初期状態がない | 利用者 |
| `Guard(a)`、`Invariant(i)`、`Contract(k)`、`Terminal` | 下ろしの失敗 | 内部 |
| `Update(a, u)` | 状態のない文脈、代入先の添字の範囲外、下ろしの失敗、空のスロット、`push_block` のオーバーフロー | 内部 |
| `Output(a)` | 出力の型がスカラーでない、下ろしの失敗、スロットが1つでない | 内部（`model_typed` が出力の型をスカラーに限る） |

### `type_of` との突き合わせ

- 下ろしの方が緩い箇所がある。`Field` はフィールドの名前を確かめず、`Record` は名前の重複を確かめない。`type_of` の方が厳しいので、全域性の妨げにはならない。
- 下ろしは要素の型を `fits(t, st)` で確かめ、`type_of` は `type_of(x) == to_xty(st)` を要求する。`fits_s(to_xty(st), st)` の補題が要る。
- `type_of` が返す型が整形式であること（文脈の型が整形式なら `wf_xtype`）を示す補題が要る。Setの要素の `keys` が `Some` であること、Listの要素の幅などを、型から引き出すためである。
- `check` は、目で見た限り `type_of` と同じ条件で拒否する。完全性（型の付く式を拒否しないこと）は手順2で証明する。

### `fmspec-ir` の上限との突き合わせ

- 宣言と注釈の型は、すべて `parse_type` を通るので、幅が `MAX_WIDTH` = 65536 以下、Listの長さの上限が `MAX_LIST` = 1024 以下、キーの数が `MAX_KEYS` = 4096 以下である。中核の条件はこれより緩いので、`fmspec-ir` が受理した型を中核が大きさの理由で拒否することはない。
- 一方、式の途中の型（`Tuple`、`Record`、`Some` で組み立てた型）の幅は、`fmspec-ir` が検査しない。宣言の型の幅の和で抑えられるが、`limits_ok` は型だけでなく式の形にもよる条件になる。
- 中核の `MAX_KEYS` と `fmspec-ir` の `MAX_KEYS` は同じ値（4096）で、別々に定義されている。

### 見つかった問題

1. **束縛の深さは、型と大きさの条件では除けない。**
   `bind` は深さが `usize::MAX` に近いと `None` を返す。
   深さは下ろす式の大きさで決まり、`Vec` の長さが実際には `usize::MAX` に届かないことを、Verusは仮定なしでは示せない。
   全域性の定理には、次のどちらかが要る。
   - (A) 下ろしの失敗を「型」と「深さ」に分ける。`low` などの戻り値を `Result<_, Fail>`（`Fail::Type` と `Fail::Depth`）にし、定理を「型が付き `limits_ok` が成り立つなら、`Fail::Type` を返さない」にする。`Fail::Depth` は資源の上限として、利用者向けの誤り（式が大きすぎる）にする。`lowering.rs` の失敗の箇所（約240）を機械的に書き換える。
   - (B) 下ろしが加える束縛の数の上限を spec関数で定め、前提に「深さ + 上限 < `usize::MAX`」を加える。戻り値の型は変えないが、各場合で束縛の数を数える証明が要り、手順4と同じくらいの量になる。
   (A) を推す。数える証明が要らず、深さの上限に達した場合も内部エラーにならない。

   **(A) に決めた。**
   `slots.rs` に `Fail`（`Type` と `Depth`）と、`Option` を `Fail::Type` の `Result` にする `need` を置いた。
   `bind` と `new_block` だけが `Fail::Depth` を返し、`atom`、`keep`、`check` はそれを伝える。
   `lowering.rs` の下ろしの再帰（`low` とその部品、`lower_prop`、`lower_stored`）は `Result<_, Fail>` を返す。
   内部の整合性だけで失敗する部品（`store`、`split` など）は `Option` のままで、呼び出し側で `need` を通す。
2. **`low_ite` は、枝に束縛があると、スロットごとに枝を下ろし直す**（`closed_in` をスロットの数だけ呼ぶ）。
   入れ子の `ite` で、下ろしの時間と式の大きさが入れ子の深さに対して指数的に増えうる。
   正しさの問題ではないので、この計画では扱わず、別に記録する。

## 各段階の確認

各段階の終わりに次を通す。

- `rake verus:proof`：中核の証明、信頼する項目がないこと、証明の対象外のコードの範囲、公開関数が前提条件を持たないこと。公開関数（`pub fn`）は `requires` を持てない。前提を持つ関数は `pub(crate) fn` にする。
- 新しい証明ごとに、検査を1つ壊した変異と、到達点に置いた `assert(false)` を `rakelib/verus.rake` に加え、どれも証明に失敗することを確かめる。全件の検査は `rake verus:mutants` で、重いのでCIでは `main` へのPRと定期実行でだけ回る。
- `rake lint` と `rake test`。整形はワークスペース全体の `cargo fmt` を使わず、`rake lint` と同じパッケージを指定する。ワークスペース全体にかけると `vendor/` の写しまで書き換わる。

途中の検証は、`crates/fmspec-core` で Verus を直接呼ぶと速い。

```sh
cd crates/fmspec-core
$HOME/.local/share/verus/0.2026.10.04.426d8b0/verus --crate-type=lib --triggers-mode silent src/lib.rs --verify-module lowering
$HOME/.local/share/verus/0.2026.10.04.426d8b0/verus --crate-type=lib --triggers-mode silent src/lib.rs --verify-only-module lowering --verify-function low_core
```

## 危ういところ

- **検証の資源**：`lowering.rs` は約7500行で、相互に再帰する関数でできている。手順3、4、6で事後条件を強めるので、資源の上限（rlimit）に当たり、関数や補題を分け直す必要が出る可能性がある。
- **規則の食い違い**：手順1で、`type_of`、下ろし、`fmspec-ir` の食い違いが多く見つかれば、手順2の作業が増える。
- **手順6の大きさ**：式を作る部品が多く、型の証明が意味保存の証明と同程度の量になる可能性がある。

## 完了後に更新する文書

- `docs/verification.md`：
  - 「証明済みの性質」の表に、全域性と整形式性の定理を加える。
  - 「信頼基盤」の `fmspec-ir` の説明を、2つの型検査のずれが内部エラーになることに合わせる。
  - 変異と `assert(false)` の件数を更新する。
  - 下ろしの説明の「下ろしは、型が合わないなど想定外の入力に `None` を返し」以降の段落を、全域性に合わせて書き直す。
- `docs/ir.md`：式の型付けの規則が `infer.rs` の `type_of` にあることを書く。
- `crates/fmspec-core/src/infer.rs` の冒頭の説明。
- この計画書は、完了したら削除するか、結果の記録に書き換える。

## 後で検討すること

### 大きさの条件を型付け規則に統合するか

全体を終えた後に、`limits_ok` を `type_of` に統合するかを検討する。
統合すると、「型が付く」ことが「下ろせる」ことと一致し、IRの受理条件の仕様が1か所になる。
`fmspec-ir` の上限も中核の定数を参照する形にでき、2つの上限のずれがなくなる。
一方、`type_of` と `check` の場合分けが増え、手順2と4の証明を直す必要がある。

判断の材料として、次を記録しておく。

- 手順1で見つかった、`fmspec-ir` の上限と中核の上限のずれの数。
- `limits_ok` が、型だけで決まる条件か、式の形にもよる条件か。型だけで決まるなら、統合しなくても型の検査の場所（`check_types`）にまとめられる。
- 手順4で、`limits_ok` を前提から引き出す補題がどれだけ要ったか。

### 元の言語の型安全性

`type_of` で型が付く式の値の意味論での評価（`source.rs` の `eval_src`）が、型どおりの値になるか、実行時の誤り（オーバーフロー、0による除算、キーがない、など）で失敗することの証明は、この計画の範囲外とする。
下ろしたモデルについては、手順6の整形式性と、中核の型安全性（`typing.rs` の `lemma_type_sound`）から同じ性質が得られる。
