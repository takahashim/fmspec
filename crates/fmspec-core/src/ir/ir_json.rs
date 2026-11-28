//! IRのJSONの木（`Json`）の読み方。キーで値を取り出す、配列と整数と文字列として読む、名前を探す。仕様と、それに一致する実行関数を並べて置く。

use vstd::prelude::*;

verus! {

/// オブジェクトの1つのキーと値。
pub struct Member {
    pub key: Vec<char>,
    pub value: Json,
}

/// JSONの値。数は符号付き64ビット整数だけを持つ。それ以外の数は `Other` にする。
pub enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Str(Vec<char>),
    Arr(Vec<Json>),
    Obj(Vec<Member>),
    Other,
}

/// 名前の表。`fmspec-ir` が組み立て、検査の条件や証拠を名前で読むときと、結果を表示するときに使う。
pub struct IrNames {
    pub enums: Vec<Vec<char>>,
    /// 列挙型ごとのラベル。
    pub variants: Vec<Vec<Vec<char>>>,
    pub consts: Vec<Vec<char>>,
    pub states: Vec<Vec<char>>,
    pub actions: Vec<Vec<char>>,
    /// 操作ごとの公開引数と内部選択の名前。
    pub params: Vec<Vec<Vec<char>>>,
    pub choices: Vec<Vec<Vec<char>>>,
    pub invariants: Vec<Vec<char>>,
    pub contracts: Vec<Vec<char>>,
    /// Recordのフィールドの名前。`SType::Record` と `TExpr::Record`、`TExpr::Field` の番号はこの表の添字である。
    pub fields: Vec<Vec<char>>,
}

/// キー `k` を持つ最初のメンバーの位置。
pub open spec fn find(ms: Seq<Member>, k: Seq<char>) -> Option<int>
    decreases ms.len(),
{
    if ms.len() == 0 {
        None
    } else if ms[0].key@ == k {
        Some(0)
    } else {
        match find(ms.drop_first(), k) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// オブジェクトのキー `k` の値。
pub open spec fn get(j: Json, k: Seq<char>) -> Option<Json> {
    match j {
        Json::Obj(ms) => match find(ms@, k) {
            Some(i) => Some(ms@[i].value),
            None => None,
        },
        _ => None,
    }
}

/// キー `k` がないか、値が `null`。
pub open spec fn absent(j: Json, k: Seq<char>) -> bool {
    get(j, k) is None || get(j, k) == Some(Json::Null)
}

/// キー `k` の値。[`absent`] でないときに使う。
pub open spec fn at(j: Json, k: Seq<char>) -> Json {
    get(j, k)->Some_0
}

/// キーを1つだけ持つオブジェクトの、そのキーと値。式と型はこの形である。
pub open spec fn one(j: Json) -> Option<(Seq<char>, Json)> {
    match j {
        Json::Obj(ms) => if ms@.len() == 1 {
            Some((ms@[0].key@, ms@[0].value))
        } else {
            None
        },
        _ => None,
    }
}

/// 配列の要素の列。
pub open spec fn arr(j: Json) -> Option<Seq<Json>> {
    match j {
        Json::Arr(xs) => Some(xs@),
        _ => None,
    }
}

/// 省略できる配列のキー。省略か `null` なら空の列。
pub open spec fn opt_arr(j: Json, k: Seq<char>) -> Option<Seq<Json>> {
    if absent(j, k) {
        Some(Seq::empty())
    } else {
        arr(at(j, k))
    }
}

pub open spec fn str_of(j: Json) -> Option<Seq<char>> {
    match j {
        Json::Str(s) => Some(s@),
        _ => None,
    }
}

/// 0以上の整数。
pub open spec fn nat_of(j: Json) -> Option<nat> {
    match j {
        Json::Int(n) => if n >= 0 {
            Some(n as nat)
        } else {
            None
        },
        _ => None,
    }
}

/// 空のオブジェクト（`{"bool": {}}` と `{"output": {}}` の値）。
pub open spec fn empty_obj(j: Json) -> bool {
    match j {
        Json::Obj(ms) => ms@.len() == 0,
        _ => false,
    }
}

pub open spec fn strs(v: Seq<Vec<char>>) -> Seq<Seq<char>> {
    v.map_values(|s: Vec<char>| s@)
}

/// 名前 `x` の最初の位置。
pub open spec fn index_of(s: Seq<Seq<char>>, x: Seq<char>) -> Option<int>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s[0] == x {
        Some(0)
    } else {
        match index_of(s.drop_first(), x) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// 名前 `x` の最後の位置（内側から探す局所変数）。
pub open spec fn last_of(s: Seq<Seq<char>>, x: Seq<char>) -> Option<int>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if s.last() == x {
        Some(s.len() - 1)
    } else {
        last_of(s.drop_last(), x)
    }
}

pub open spec fn distinct(s: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// 名前の表の名前に重複がない（列挙型、ラベル、定数、操作、Recordのフィールド）。
pub open spec fn names_ok(ns: IrNames) -> bool {
    &&& distinct(strs(ns.enums@))
    &&& ns.variants@.len() == ns.enums@.len()
    &&& forall|i: int| 0 <= i < ns.variants@.len() ==> distinct(#[trigger] strs(ns.variants@[i]@))
    &&& distinct(strs(ns.consts@))
    &&& distinct(strs(ns.actions@))
    &&& distinct(strs(ns.fields@))
}

/// 文字の列が、ASCIIの文字列リテラル `s` と等しい。
pub(crate) fn eqk(a: &Vec<char>, s: &str) -> (r: bool)
    requires
        s.is_ascii(),
    ensures
        r == (a@ == s@),
{
    let n = s.unicode_len();
    if a.len() != n {
        return false;
    }
    let mut i = 0;
    while i < n
        invariant
            n == s@.len(),
            a@.len() == n,
            i <= n,
            s.is_ascii(),
            forall|j: int| 0 <= j < i ==> a@[j] == s@[j],
        decreases n - i,
    {
        if a[i] != s.get_char(i) {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= s@);
    }
    true
}

pub(crate) fn chars_eq(a: &Vec<char>, b: &Vec<char>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

pub(crate) fn copy_chars(a: &Vec<char>) -> (r: Vec<char>)
    ensures
        r@ == a@,
{
    let mut out = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            out@ == a@.subrange(0, i as int),
        decreases a.len() - i,
    {
        out.push(a[i]);
        i += 1;
    }
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }
    out
}

pub(crate) proof fn lemma_index_of(s: Seq<Seq<char>>, x: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        forall|q: int| 0 <= q < i ==> s[q] != x,
    ensures
        i < s.len() && s[i] == x ==> index_of(s, x) == Some(i),
        i == s.len() ==> index_of(s, x) is None,
    decreases i,
{
    if i > 0 {
        assert forall|q: int| 0 <= q < i - 1 implies s.drop_first()[q] != x by {
            assert(s.drop_first()[q] == s[q + 1]);
        }
        if i < s.len() && s[i] == x {
            assert(s.drop_first()[i - 1] == s[i]);
        }
        lemma_index_of(s.drop_first(), x, i - 1);
    }
}

/// 名前の表で、名前 `x` の最初の位置。
pub(crate) fn index_of_exec(v: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => index_of(strs(v@), x@) == Some(i as int),
            None => index_of(strs(v@), x@) is None,
        },
{
    let ghost s = strs(v@);
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|q: int| 0 <= q < i ==> s[q] != x@,
        decreases v.len() - i,
    {
        if chars_eq(&v[i], x) {
            proof {
                lemma_index_of(s, x@, i as int);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_index_of(s, x@, i as int);
    }
    None
}

pub(crate) proof fn lemma_last_of(s: Seq<Seq<char>>, x: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        forall|q: int| i <= q < s.len() ==> s[q] != x,
    ensures
        i > 0 && s[i - 1] == x ==> last_of(s, x) == Some(i - 1),
        i == 0 ==> last_of(s, x) is None,
    decreases s.len(),
{
    if s.len() > 0 && i < s.len() {
        assert(s.last() != x);
        let t = s.drop_last();
        assert forall|q: int| i <= q < t.len() implies t[q] != x by {
            assert(t[q] == s[q]);
        }
        if i > 0 && s[i - 1] == x {
            assert(t[i - 1] == s[i - 1]);
        }
        lemma_last_of(t, x, i);
    }
}

/// 局所変数の名前の列で、名前 `x` の最後の位置。
pub(crate) fn last_of_exec(v: &Vec<Vec<char>>, x: &Vec<char>) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => last_of(strs(v@), x@) == Some(i as int),
            None => last_of(strs(v@), x@) is None,
        },
{
    let ghost s = strs(v@);
    let mut i = v.len();
    while i > 0
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|q: int| i <= q < s.len() ==> s[q] != x@,
        decreases i,
    {
        if chars_eq(&v[i - 1], x) {
            proof {
                lemma_last_of(s, x@, i as int);
            }
            return Some(i - 1);
        }
        i -= 1;
    }
    proof {
        lemma_last_of(s, x@, 0);
    }
    None
}

/// 名前の列に重複がない。
pub(crate) fn distinct_exec(v: &Vec<Vec<char>>) -> (r: bool)
    ensures
        r ==> distinct(strs(v@)),
{
    let ghost s = strs(v@);
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == strs(v@),
            forall|p: int, q: int| 0 <= p < q < i ==> s[p] != s[q],
        decreases v.len() - i,
    {
        let mut j = 0;
        while j < i
            invariant
                j <= i < v@.len(),
                s == strs(v@),
                forall|p: int, q: int| 0 <= p < q < i ==> s[p] != s[q],
                forall|p: int| 0 <= p < j ==> s[p] != s[i as int],
            decreases i - j,
        {
            if chars_eq(&v[j], &v[i]) {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

pub(crate) proof fn lemma_find_at(ms: Seq<Member>, k: Seq<char>, i: int)
    requires
        0 <= i <= ms.len(),
        forall|q: int| 0 <= q < i ==> ms[q].key@ != k,
    ensures
        i < ms.len() && ms[i].key@ == k ==> find(ms, k) == Some(i),
        i == ms.len() ==> find(ms, k) is None,
    decreases i,
{
    if i > 0 {
        assert forall|q: int| 0 <= q < i - 1 implies ms.drop_first()[q].key@ != k by {
            assert(ms.drop_first()[q] == ms[q + 1]);
        }
        if i < ms.len() && ms[i].key@ == k {
            assert(ms.drop_first()[i - 1] == ms[i]);
        }
        lemma_find_at(ms.drop_first(), k, i - 1);
    }
}

/// オブジェクトのキー `k` の値。
pub(crate) fn get_exec<'a>(j: &'a Json, k: &str) -> (r: Option<&'a Json>)
    requires
        k.is_ascii(),
    ensures
        match r {
            Some(v) => get(*j, k@) == Some(*v),
            None => get(*j, k@) is None,
        },
{
    match j {
        Json::Obj(ms) => {
            let mut i = 0;
            while i < ms.len()
                invariant
                    i <= ms@.len(),
                    k.is_ascii(),
                    *j == Json::Obj(*ms),
                    forall|q: int| 0 <= q < i ==> ms@[q].key@ != k@,
                decreases ms.len() - i,
            {
                if eqk(&ms[i].key, k) {
                    proof {
                        lemma_find_at(ms@, k@, i as int);
                    }
                    return Some(&ms[i].value);
                }
                i += 1;
            }
            proof {
                lemma_find_at(ms@, k@, i as int);
            }
            None
        },
        _ => None,
    }
}

/// キー `k` の値が省略か `null` でなければ、その値。
pub(crate) fn present<'a>(j: &'a Json, k: &str) -> (r: Option<&'a Json>)
    requires
        k.is_ascii(),
    ensures
        match r {
            Some(v) => !absent(*j, k@) && at(*j, k@) == *v,
            None => absent(*j, k@),
        },
{
    match get_exec(j, k) {
        Some(Json::Null) => None,
        Some(v) => Some(v),
        None => None,
    }
}

pub(crate) fn one_exec(j: &Json) -> (r: Option<(&Vec<char>, &Json)>)
    ensures
        match r {
            Some((k, b)) => one(*j) == Some((k@, *b)),
            None => one(*j) is None,
        },
{
    match j {
        Json::Obj(ms) => if ms.len() == 1 {
            Some((&ms[0].key, &ms[0].value))
        } else {
            None
        },
        _ => None,
    }
}

pub(crate) fn arr_exec(j: &Json) -> (r: Option<&Vec<Json>>)
    ensures
        match r {
            Some(xs) => arr(*j) == Some(xs@) && *j == Json::Arr(*xs),
            None => arr(*j) is None,
        },
{
    match j {
        Json::Arr(xs) => Some(xs),
        _ => None,
    }
}

pub(crate) fn str_exec(j: &Json) -> (r: Option<&Vec<char>>)
    ensures
        match r {
            Some(s) => str_of(*j) == Some(s@),
            None => str_of(*j) is None,
        },
{
    match j {
        Json::Str(s) => Some(s),
        _ => None,
    }
}

/// JSONの値が、0以上の整数 `x` である。
pub(crate) fn is_nat(j: &Json, x: usize) -> (r: bool)
    ensures
        r ==> nat_of(*j) == Some(x as nat),
{
    match j {
        Json::Int(n) => *n >= 0 && (*n as u128) == (x as u128),
        _ => false,
    }
}

pub(crate) fn is_empty_obj(j: &Json) -> (r: bool)
    ensures
        r == empty_obj(*j),
{
    match j {
        Json::Obj(ms) => ms.len() == 0,
        _ => false,
    }
}

} // verus!
