# Verusの読み方と書き方

fmspecの中核（`crates/fmspec-core`）は、[Verus](https://github.com/verus-lang/verus)で検証している。
この文書は、中核のコードを読み書きするのに必要なVerusの構文と、このリポジトリでの使い方を示す。
何を証明し、何を信頼しているかは [verification.md](verification.md) にある。
Verus自体の詳しい説明は、公式の[Verus Guide](https://verus-lang.github.io/verus/guide/)にある。

## Verusとは

Verusは、Rustのコードに仕様と証明を書き込み、SMTソルバー（Z3）でその正しさを機械的に確かめるツールである。
テストが選んだ入力についてだけ確かめるのに対して、Verusはすべての入力について、関数が仕様どおりに動くことを確かめる。

fmspecでは、利用者が受け取る判定（`Verified`、`Violated` など）を作る経路をすべて `fmspec-core` に置き、Verusで検証する。
たとえば、`check_certificate` が証明書を受理したなら、モデルが本当に安全であることを、Verusが証明している。
探索器（`fmspec-search`）は証拠を作るだけで、判定は作らないので、検証しなくても誤った判定にはならない。

## コードの置き方

検証するコードは、ファイルごとに1つの `verus! { ... }` ブロックに入れる。

```rust
use vstd::prelude::*;

verus! {

pub open spec fn in_cert(cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    exists|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s
}

// ...

} // verus!
```

`verus!` の外には、`use`、属性、コメントしか置かない（`rake verus:coverage` が確かめる）。
例外は `impls.rs` で、`Clone` や `PartialEq` などの標準トレイトを `verus!` の外に手で書いている。
Verusは、再帰的な型や `Vec` を持つ型の `derive` に仕様を付けられないためである。
`impls.rs` は証明の対象外で、判定の経路からは呼ばない。

同じソースは、2通りにビルドする。

| ビルド | 何が起きるか |
|---|---|
| `verus --crate-type=lib src/lib.rs`（`rake verus`） | 仕様と証明を検査する |
| `cargo build` | `vstd` のマクロが仕様と証明（ghostコード）を消去し、普通のRustとしてコンパイルする |

したがって、`cargo build` や `cargo test` だけでは証明は検査されない。
証明を変えたら `rake verus` を実行する。
`Cargo.toml` の `cfg(verus_keep_ghost)` は、Verusがghostコードを残すときに使う設定で、cargoビルドの警告を抑えるために書いてある。

## 3種類の関数

Verusの関数は、モードによって3種類に分かれる。

| モード | 書き方 | 役割 | 実行されるか |
|---|---|---|---|
| spec | `spec fn` | 数学的な定義。意味論や性質を書く | されない |
| proof | `proof fn` | 定理（補題）とその証明 | されない |
| exec | `fn` | 普通の実行コード | される |

fmspecでは、ほとんどの機能が「spec の定義」と「exec の実装」の対になっている。
exec の関数の `ensures` が、実装の結果が spec の定義と一致することを述べる。

| spec（意味論） | exec（実装） | ファイル |
|---|---|---|
| `eval_spec`、`eval_l` | `eval`、`eval_in` | `eval.rs` |
| `step_spec` | `step`、`enumerate` | `step.rs` |
| `wf` | `validate_raw` | `typing.rs` |
| `inductive`、`safe` | `check_certificate` | `cert.rs` |
| `trace_ok`、`claim_holds` | `check_trace` | `trace.rs` |
| `verdict_sound` | `decide` | `gate.rs` |

spec の関数は、実装の都合（オーバーフロー、借用、計算量）を気にせず、素直に書く。
読み手は spec の定義だけを見れば、判定の意味が分かる。
その定義と実装の一致は、Verusが保証する。

### spec fn

```rust
/// `s` は初期状態から対象の操作の遷移 `n` 回で到達できる。
pub open spec fn reach(m: RawModel, c: Conditions, s: Seq<i64>, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        is_init(m, s)
    } else {
        exists|p: Seq<i64>, a: int, args: Seq<i64>, o: Option<i64>|
            reach(m, c, p, (n - 1) as nat) && #[trigger] is_edge(m, c, p, a, args, o, s)
    }
}
```

（`semantics.rs`）

- `open spec fn` は、本体をほかのモジュールにも見せる。証明でその定義を展開できる。
- `closed spec fn` は、本体をモジュールの外に見せない。外からは名前と型しか分からない。fmspecでは、非公開のフィールドを持つ型の「見え方」を定めるのに使う（後述）。
- 再帰する spec 関数には `decreases` が要る。
- spec の中では、`exists` や `forall` のように、実行できない式も書ける。

### proof fn

```rust
/// 帰納的な証明書があれば、モデルは安全である。
pub proof fn lemma_inductive_safe(m: RawModel, c: Conditions, cert: Seq<Vec<i64>>)
    requires
        inductive(m, c, cert),
    ensures
        safe(m, c),
{
    // 証明
}
```

（`cert.rs`）

`requires` が仮定、`ensures` が結論である。
本体で、仮定から結論が導けることをVerusに納得させる。
fmspecでは、proof 関数の名前を `lemma_` で始める。
定理の一覧は [verification.md](verification.md) の「証明済みの性質」にある。

`ensures false` の補題は、仮定が両立しないことを示す。
`lemma_safe_excludes_trace`（`trace.rs`）は、安全なモデルに、主張の成り立つ有効なトレースがないことを示す。

### exec fn

```rust
/// 安全性証明書を検査する。`None`（受理）を返すなら、証明書は帰納的で、モデルは安全である。
pub fn check_certificate(m: &RawModel, c: &Conditions, cert: &Vec<Vec<i64>>) -> (r: Option<Reject>)
    ensures
        r is None ==> inductive(*m, *c, cert@) && safe(*m, *c),
{
    // ...
}
```

（`cert.rs`）

- 戻り値に名前を付けると（`-> (r: Option<Reject>)`）、`ensures` で参照できる。
- `requires` は呼び出し側が満たすべき前提、`ensures` は関数が保証する結果である。
- exec の関数の中で証明を書くときは、`proof { ... }` ブロックを使う。ここに書いたものは、cargoビルドで消える。

```rust
    proof {
        lemma_inductive_safe(*m, *c, cert@);
    }
    None
```

### ghost 変数

exec の関数の中で、証明のためだけの値を持つときは `let ghost` を使う。

```rust
let ghost ls0 = ls@;
```

関数の引数で ghost の値を受け取るときは、`Ghost<T>` を使う。

```rust
fn var_cands(sm: &SModel, cx: &LowerCtx, i: usize, Ghost(cv): Ghost<Seq<SVal>>) -> ...
```

（`model_lower.rs`）

構造体のフィールドにも置ける。
`mbt::Session` は、これまでの応答の列を `Ghost<Seq<Answer>>` で持ち、実行時には何も持たない。

## 仕様に出てくる型と演算子

### 数学的な整数と列

| 型 | 意味 |
|---|---|
| `int` | 上限も下限もない整数。オーバーフローしない |
| `nat` | 0以上の `int` |
| `Seq<T>` | 有限の列。`vstd` が定める数学的な値 |

spec と proof では、`int` と `nat` を使う。
exec の `usize` や `i64` との変換は `x as int`、`(n - 1) as nat` のように書く。
`int` のまま比べられるので、たとえば `i < m.inits@.len()` は、`usize` の上限を気にせずに書ける。

列は `s.len()`、`s[i]`、`s.push(x)`、`s.subrange(i, j)`、`Seq::empty()`、`seq![a, b]` で扱う。

### `@`（ビュー）

`x@` は、exec の値 `x` の数学的な見え方（ビュー）である。
`Vec<T>` のビューは `Seq<T>` で、仕様では `v@.len()` や `v@[i]` のように列として扱う。
状態は `Vec<i64>` で持つので、`s@` は `Seq<i64>` になる。

fmspecの型も、独自のビューを持つことがある。
`CheckedModel` のビュー `cm@` は、中にある `RawModel` である。
`Ctx` のビュー `c@` は、意味論の環境 `Env` である。

### 論理演算子

| 書き方 | 意味 |
|---|---|
| `a ==> b` | a ならば b |
| `a <==> b` | a と b は同値 |
| `&&& a`<br>`&&& b` | 行頭に並べた連言。`a && b` と同じ |
| `a =~= b` | 列などの外延的な等しさ。要素ごとに等しい |
| `r is None` | `r` が `None` の場合である |
| `r matches Some(e) ==> P(e)` | `r` が `Some(e)` なら、その `e` について `P(e)` |

```rust
pub fn validate_raw(m: &RawModel) -> (r: Result<(), InvalidModel>)
    ensures
        r is Ok <==> wf(*m),
```

（`typing.rs`）これは「`validate_raw` は、モデルが整形式であるとき、かつそのときに限り受理する」と読む。

`=~=` は、2つの列が等しいことをVerusに示すときに使う。
`==` だけでは、Verusは列の等しさを自動では導かないことがある。

```rust
let mut ls: Vec<Value> = Vec::new();
assert(ls@ =~= Seq::<Value>::empty());
```

### `old` と `final`

`&mut` の引数について、`old(x)` は関数に入ったときの値、`final(x)` は関数を出るときの値である。

```rust
fn eval_in(e: &Expr, c: &Ctx, ls: &mut Vec<Value>) -> (r: Result<Value, ErrKind>)
    ensures
        r == eval_l(*e, c@, old(ls)@),
        final(ls)@ == old(ls)@,
```

（`eval.rs`）評価の途中で局所変数の列 `ls` に値を積むが、終わったら元に戻すことを保証している。

## 量化とトリガー

### forall と exists

```rust
forall|i: int| 0 <= i < cert.len() ==> state_closed(m, c, cert, (#[trigger] cert[i])@)
exists|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s
```

`forall` は「すべての `i` について」、`exists` は「ある `i` について」である。

### `#[trigger]`

SMTソルバーは、`forall` の式をどの値に当てはめるかを、トリガーで決める。
`#[trigger]` を付けた項（上の例では `cert[i]`）と同じ形の項が証明の中に現れると、ソルバーはその値で `forall` を具体化する。
たとえば `cert[3]` が現れれば、`state_closed(m, c, cert, cert[3]@)` が使えるようになる。

トリガーが適切でないと、証明が通らなかったり、ソルバーが具体化を繰り返して遅くなったりする。
fmspecでは、すべての量化にトリガーを明示している。
証明が通らないときは、必要な項を `assert` で書いてトリガーを発火させることが多い。

```rust
assert(state_closed(m, c, cert, cert[i]@));
```

### choose

`choose|x| P(x)` は、`P(x)` を満たす値を1つ取り出す。
`exists` が成り立つことが分かっているときに、その証拠の値に名前を付けるのに使う。

```rust
let i = choose|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s;
```

### assert forall ... implies ... by

`forall` を証明するときは、任意の値を固定して示す。

```rust
assert forall|s: Seq<i64>, n: nat| #[trigger] reach(m, c, s, n) implies state_safe(m, c, s) by {
    lemma_reach_in_cert(m, c, cert, s, n);
    // ...
}
```

（`cert.rs`）`by { ... }` の中では、`s` と `n` が固定され、`reach(m, c, s, n)` を仮定できる。
その中で `state_safe(m, c, s)` を示せば、`forall` が成り立つ。

## 停止性：decreases

Verusは、再帰する関数とループが停止することを要求する。
`decreases` に、呼ぶたびに（回るたびに）減る量を書く。

```rust
pub open spec fn reach(m: RawModel, c: Conditions, s: Seq<i64>, n: nat) -> bool
    decreases n,
```

```rust
while k < cert.len()
    invariant
        // ...
    decreases cert@.len() - k,
```

式の木を再帰でたどるときは、式そのものを書く。部分式は元の式より小さいとみなされる。
相互再帰では、辞書式の組で書く。

```rust
pub open spec fn eval_l(e: Expr, env: Env, ls: Seq<Value>) -> Result<Value, ErrKind>
    decreases e, 0int,

pub open spec fn quant_l(...)
    decreases body, hi - x + 1,
```

（`eval.rs`）`eval_l` は量化の本体 `body` について `quant_l` を呼び、`quant_l` は同じ `body` について `eval_l` を呼ぶ。
`body` は元の式より小さいので、組の1番目で減る。
`quant_l` が自分を呼ぶときは、`body` が同じで、2番目の `hi - x + 1` が減る。

fmspecの検証済みの実行関数とループは、すべて `decreases` を持つ。
したがって、検査器は必ず停止する。
`exec_allows_no_decreases_clause` で停止性の検査を外すことは、信頼する項目として禁止している（後述）。

## ループ不変条件

ループの後で何が成り立つかを、Verusは `invariant` だけから考える。
ループの中で何をしたかは、不変条件に書かない限り、ループの後には伝わらない。

```rust
let mut k: usize = 0;
while k < cert.len()
    invariant
        k <= cert@.len(),
        forall|j: int| 0 <= j < k ==> state_closed(*m, *c, cert@, (#[trigger] cert@[j])@),
    decreases cert@.len() - k,
{
    match check_state(m, c, cert, k) {
        Some(r) => {
            return Some(r);
        },
        None => {},
    }
    k = k + 1;
}
// ここでは k == cert@.len() なので、すべての状態が state_closed である。
```

（`cert.rs`）Verusは、次の3つを確かめる。

1. ループに入るとき、不変条件が成り立つ（`k == 0` なので、`forall` は空で真）。
2. 不変条件と条件 `k < cert.len()` が成り立つ状態から1回回ると、不変条件がまた成り立つ。
3. ループを出たら、不変条件と、条件の否定 `k >= cert.len()` が成り立つ。

### `#[verifier::loop_isolation(false)]`

既定では、ループの中から、ループの前に分かっていた事実（関数の `requires` など）は見えない。
必要な事実は、すべて `invariant` に書き直す。
`#[verifier::loop_isolation(false)]` を関数に付けると、ループの前の事実がループの中でも使える。
fmspecでは、`requires` を不変条件に繰り返すのが煩雑な関数に付けている（`cert.rs`、`eval.rs` など）。

## 証明の書き方

### assert

`assert(P)` は、`P` が成り立つことをVerusに確かめさせ、その後の証明で `P` を使えるようにする。
証明が通らないときに、途中の事実を `assert` で書き足していくのが基本の進め方である。

`assert(P) by { ... }` は、`P` の証明を局所的に書く。
`by` の中で使った補題や事実は、外に漏れない。

```rust
assert(state_ok(m, acc2)) by {
    // state_ok(m, acc2) の証明
}
```

### 補題を呼ぶ

proof 関数を呼ぶと、その `requires` が確かめられ、`ensures` が使えるようになる。

```rust
lemma_reach_in_cert(m, c, cert, s, n);   // これ以降、in_cert(cert, s) が使える
```

帰納法は、proof 関数の再帰で書く。
`lemma_reach_in_cert`（`cert.rs`）は、`n - 1` についての自分を呼ぶことで、到達回数 `n` についての帰納法になっている。

### 非線形算術：by (nonlinear_arith)

SMTソルバーは、変数どうしの掛け算を含む式（非線形算術）が苦手である。
Verusは既定で、非線形算術を自動では推論しない。
必要なときは、仮定を限って別に解かせる。

```rust
assert(q as int <= x) by (nonlinear_arith)
    requires
        x == d * q + rr,
        // ...
;
```

（`eval.rs`）床除算と剰余の正しさの証明で使っている。
`vstd` の補題（`lemma_fundamental_div_mod`、`lemma_mod_pos_bound` など）も使う。

### 展開の深さ：reveal_with_fuel

再帰する spec 関数を、Verusは既定で1段だけ展開する。
2段以上の展開が要るときは、`reveal_with_fuel(f, n)` で段数を増やす。

```rust
reveal_with_fuel(eval_l, 2);
```

### recommends

`recommends` は、spec 関数の引数に期待する条件である。
`requires` と違い、満たさなくてもエラーにはならない（spec 関数はどんな引数でも何らかの値を持つ）。
引数の意図を示すために使う。

```rust
pub open spec fn eval_bindings(bindings: Seq<Expr>, n: nat, env: Env, locals: Seq<Value>) -> ...
    recommends n <= bindings.len(),
```

### `#[verifier::spinoff_prover]`

その関数を、別のSMTソルバーのプロセスで検証する。
大きな証明がほかの関数の検証に影響したり、遅くなったりするのを防ぐ。
`canon.rs` などの大きな補題に付けている。

## 型不変条件とカプセル化

判定（`Verdict`）や検証済みのモデル（`CheckedModel`）は、勝手に作られると困る。
fmspecでは、フィールドを非公開にし、型不変条件を付けて、作れる値を制限する。

```rust
/// IR検証を通過したモデル。`validate` だけが構築する。
pub struct CheckedModel {
    raw: RawModel,
}

impl CheckedModel {
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        wf(self.raw)
    }

    pub closed spec fn view(self) -> RawModel {
        self.raw
    }

    pub fn raw(&self) -> (r: &RawModel)
        ensures
            *r == self@,
            wf(*r),
    {
        proof {
            use_type_invariant(self);
        }
        &self.raw
    }
}
```

（`gate.rs`）

- `#[verifier::type_invariant]` を付けた spec 関数は、その型の値が常に満たす条件である。値を作るとき、フィールドを書き換えるときに、Verusが確かめる。
- `use_type_invariant(x)` を proof の中で呼ぶと、`x` が型不変条件を満たすことが使える。上の例では、`CheckedModel` の中のモデルが整形式であることを取り出している。
- `closed spec fn view` は、外からの見え方を定める。外のモジュールは `cm@` でモデルについて述べられるが、フィールドには触れない。

したがって、`decide` が受け取る `CheckedModel` は、必ず `validate` を通ったモデルである。
`CertCheck` と `mbt::Session` も、同じ方法で、検査の途中の状態についての不変条件を保つ。

## このリポジトリでの約束

### 公開関数は requires を持たない

Verusは、未検証のコードからの呼び出しについて、`requires` を確かめない。
`fmspec-core` の公開関数（`pub fn`）は、探索器やnative extensionなどの未検証コードから呼ばれるので、前提条件を持たせない。
必要な条件は関数の中で検査し、満たさない入力には `InvalidModel` や `None` を返す。
`rake verus:contract` が確かめる。
`pub(crate)` やモジュール内の関数は、検証済みのコードからしか呼ばれないので、`requires` を持ってよい。

### 信頼する項目を使わない

次の構文は、証明を省いて仮定を置くものなので、`fmspec-core` では1つも使わない。
`rake verus:trusted` が確かめる（正規表現は `rakelib/verus.rake` の `VERUS_TRUST`）。

| 構文 | 意味 |
|---|---|
| `assume(P)` | `P` を証明せずに仮定する |
| `admit()` | その時点の証明の義務をすべて認める |
| `#[verifier::external_body]` | 本体を検証せず、仕様だけを信頼する |
| `#[verifier::external]`、`external_fn_specification`、`external_type_specification` | 検証の対象から外す、外部の関数や型に仕様を与える |
| `assume_specification` | 外部の関数の仕様を信頼する |
| `exec_allows_no_decreases_clause` | 停止性の検査を外す |
| `#[verifier::truncate]` | 範囲外になりうる数値の変換を検査しない |

外部の関数（標準ライブラリなど）は、`vstd` が仕様を与えたものだけを使う。
`vstd` の仕様は、信頼基盤の一部である。

### 証明が空虚でないことを確かめる

仮定が矛盾していると、どんな結論でも証明できてしまう。
`rake verus:mutants` は、検査を1つ壊した変異と、到達点に `assert(false)` を置いた変種が、証明に失敗することを確かめる。
一覧は `rakelib/verus.rake` の `VERUS_MUTANTS` と `VERUS_CANARIES` にある。

変異は `[ファイル, 元の文字列, 置き換え, 説明]` の形で書く。
元の文字列は、ファイルにちょうど1回現れなければならない。
コードを書き換えて元の文字列が見つからなくなったら、一覧を更新する。

```ruby
["cert.rs", "元のコード", "壊したコード", "遷移先が証明書にあることを検査しない"],
```

検査を足したら、それを壊す変異も足す。
変異が証明を通ってしまうなら、その検査は証明に必要とされていない（`ensures` が弱い）。

### 書き方とlint

検証済みのコードは、Verusが扱える書き方に従う。
`&Vec<T>` の引数、`i = i + 1`、イテレータでなく `while` ループ、網羅的な `match` などである。
`crates/fmspec-core/Cargo.toml` で、書き方に関する clippy の lint（style、complexity など）を外している。
誤りを指摘する lint は有効のままである。

## 実行のしかた

```sh
export VERUS=/path/to/verus        # なければ PATH の verus
rake verus                          # = rake verus:proof
VERUS_MUTANTS_FILES=cert.rs rake verus:mutants
```

`rake verus:proof` は、次を順に行う。

1. `verus:version`：Verusの版と、`Cargo.lock` の `vstd` などの版が、固定したものと一致する。
2. `verus:trusted`：信頼する項目がない。
3. `verus:coverage`：`verus!` の外にコードがない（`impls.rs` を除く）。
4. `verus:contract`：公開関数が `requires` を持たない。
5. `verus --crate-type=lib crates/fmspec-core/src/lib.rs` で証明を検査し、エラーも警告もない。

Verusの版は `rakelib/verus.rake` の `VERUS_VERSION` に固定している。
リリースは [Verusのリリースページ](https://github.com/verus-lang/verus/releases) から取得する。
CIでの取得の手順は `.github/actions/setup-verus/action.yml` にある。
Verusは、自分が使うRustのツールチェーンを `rustup` で要求する。`verus --version` が、足りないツールチェーンの名前を示す。
Verusを更新するときは、`VERUS_CRATES_VERSION`（cargoビルドで使う `vstd` の版）も対応するものに選び直し、証明を確かめ直す。

### 失敗したとき

Verusのエラーは、どの `ensures`、`requires`、`invariant`、`assert` が示せなかったかを指す。
よくある原因と対処を示す。

| 症状 | よくある原因 | 対処 |
|---|---|---|
| `postcondition not satisfied` | 結論に必要な事実が、ソルバーに見えていない | 途中の事実を `assert` で書き足す。必要な補題を呼ぶ |
| `invariant not satisfied at end of loop body` | 不変条件が1回の繰り返しで保たれない | 繰り返しの末尾で不変条件の各項を `assert` し、どれが落ちるか調べる |
| `precondition not satisfied` | 呼んだ関数の `requires` を示せていない | 呼ぶ前に `requires` の各項を `assert` する |
| `forall` の事実が使われない | トリガーの項が現れていない | トリガーの形の項を `assert` で書く |
| 掛け算を含む式が示せない | 非線形算術 | `by (nonlinear_arith)` や `vstd::arithmetic` の補題を使う |
| 再帰の定義が展開されない | 展開は既定で1段 | 補題で1段ずつ示すか、`reveal_with_fuel` を使う |
| 検証が遅い、`rlimit exceeded` | 量化の具体化が多すぎる | 証明を補題に分ける。`assert ... by` で事実の範囲を限る。`spinoff_prover` を付ける |

## 読み進め方

初めて読むときは、次の順が分かりやすい。

1. `semantics.rs`：`reach`、`safe` など、判定の意味の定義。spec 関数だけで書いてある。
2. `gate.rs`：`verdict_sound` と `decide`。判定ゲートが保証することの全体。
3. `cert.rs`：証明書の検査。spec の定義（`inductive`）、補題（`lemma_inductive_safe`）、実装（`check_certificate`）が1つのファイルにそろっている。
4. `trace.rs`：トレースの検査。
5. `eval.rs`、`step.rs`：式の評価と遷移の、意味論と実装の対応。

## 参考

- [Verus Guide](https://verus-lang.github.io/verus/guide/)：構文、モード、トリガー、ループ不変条件、非線形算術などの説明。
- [vstd のAPIドキュメント](https://verus-lang.github.io/verus/verusdoc/vstd/)：`Seq` などの型と補題。
- [Verus のリポジトリ](https://github.com/verus-lang/verus)
