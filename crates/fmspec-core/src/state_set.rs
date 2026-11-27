//! 状態の集合（証明書の状態の列）への所属。所属の仕様（`in_cert`）と、整列した列の二分探索（`find`）。

use vstd::prelude::*;

verus! {

pub open spec fn in_cert(cert: Seq<Vec<i64>>, s: Seq<i64>) -> bool {
    exists|i: int| 0 <= i < cert.len() && (#[trigger] cert[i])@ == s
}

/// 符号化列の辞書順の比較。`0` を返すのは、2つの列が等しいときだけである。
pub(crate) fn cmp_state(a: &Vec<i64>, b: &Vec<i64>) -> (r: i8)
    ensures
        r == 0 ==> a@ == b@,
{
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a@.len(),
            i <= b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] < b[i] {
            return -1;
        }
        if a[i] > b[i] {
            return 1;
        }
        i = i + 1;
    }
    if a.len() < b.len() {
        -1
    } else if a.len() > b.len() {
        1
    } else {
        assert(a@ =~= b@);
        0
    }
}

/// 二分探索による所属判定。`true` を返すのは、状態が証明書に含まれるときだけである。
/// 証明書が整列されていなければ、含まれる状態を見落として `false` を返すことがある。
/// その場合は証明書を拒否するだけで、誤って受理することはない（仕様書 §7.3）。
pub(crate) fn find(cert: &Vec<Vec<i64>>, t: &Vec<i64>) -> (r: bool)
    ensures
        r ==> in_cert(cert@, t@),
{
    let mut lo: usize = 0;
    let mut hi: usize = cert.len();
    while lo < hi
        invariant
            lo <= hi <= cert@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let c = cmp_state(&cert[mid], t);
        if c == 0 {
            assert(cert@[mid as int]@ == t@);
            return true;
        } else if c < 0 {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    false
}

} // verus!
