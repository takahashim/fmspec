//! IRの型と、中核の符号の列（スロット）への配置。
//!
//! 複合型の値は、固定幅のスロットの列に符号化する。各スロットは中核の型（Bool、有界Int、Enum）を持つ。
//!
//! | 型 | スロット |
//! |---|---|
//! | Bool、Int、Enum | 1つ |
//! | Tuple、Record | 要素のスロットを順に並べる |
//! | Option | 有無を表すBoolのあとに、中身のスロット |
//! | Set | 要素の型の値ごとに、含むかどうかを表すBool。値の順は正規順 |
//! | Map | キーの型の値ごとに、キーがあるかどうかを表すBoolと、値のスロット |
//! | List | 長さを表すInt（`0..=max`）のあとに、`max` 個の要素のスロット |
//!
//! 値の符号化は正規形に限る。Optionが空なら中身のスロットは既定値で、
//! Mapにないキーの値と、Listの長さより後ろの要素も既定値である。
//! したがって、同じ値は同じスロットの列になり、状態の等価性はスロットの列の一致になる。
//! 既定値は、Boolが偽、Intが範囲の最小値、Enumが最初のラベルである。
//!
//! 値の**正規順**は、Boolが偽、真の順、Intが昇順、Enumがラベルの定義順、
//! Tuple と Record が要素の辞書順、Option が空、中身の順である。
//! Setの要素とMapのキーには、この順で番号（rank）を付ける。

use crate::model::EnumNames;
use fmspec_core::model::{Type, Value as CoreValue};

/// Setの要素の型と、Mapのキーの型が取れる値の数の上限。
pub const MAX_KEYS: u64 = 4096;
/// Listの長さの上限。
pub const MAX_LIST: usize = 1024;
/// 1つの型のスロット数の上限。
pub const MAX_WIDTH: usize = 1 << 16;

/// 状態変数、引数、出力、集合の要素などの型。整数は範囲を持つ。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SType {
    Bool,
    Int(i64, i64),
    Enum(usize),
    Tuple(Vec<SType>),
    Record(Vec<(String, SType)>),
    Option(Box<SType>),
    Set(Box<SType>),
    Map(Box<SType>, Box<SType>),
    List(Box<SType>, usize),
}

/// 式の型。整数の範囲は、Set、Map、Listの中だけにある（符号化がその範囲に依存するため）。
/// 式の中間結果の整数は64ビット整数の全域を取る。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum XType {
    Bool,
    Int,
    Enum(usize),
    Tuple(Vec<XType>),
    Record(Vec<(String, XType)>),
    Option(Box<XType>),
    Set(Box<SType>),
    Map(Box<SType>, Box<SType>),
    List(Box<SType>, usize),
}

impl SType {
    pub fn is_scalar(&self) -> bool {
        matches!(self, SType::Bool | SType::Int(_, _) | SType::Enum(_))
    }

    /// 中核の型。スカラー型でなければ `None`。
    pub fn core(&self) -> Option<Type> {
        match self {
            SType::Bool => Some(Type::Bool),
            SType::Int(lo, hi) => Some(Type::Int(*lo, *hi)),
            SType::Enum(id) => Some(Type::Enum(*id)),
            _ => None,
        }
    }

    pub fn xtype(&self) -> XType {
        match self {
            SType::Bool => XType::Bool,
            SType::Int(_, _) => XType::Int,
            SType::Enum(id) => XType::Enum(*id),
            SType::Tuple(ts) => XType::Tuple(ts.iter().map(SType::xtype).collect()),
            SType::Record(fs) => XType::Record(fs.iter().map(|(n, t)| (n.clone(), t.xtype())).collect()),
            SType::Option(t) => XType::Option(Box::new(t.xtype())),
            SType::Set(t) => XType::Set(t.clone()),
            SType::Map(k, v) => XType::Map(k.clone(), v.clone()),
            SType::List(t, n) => XType::List(t.clone(), *n),
        }
    }

    /// 値の数。Setの要素とMapのキーになれない型（Set、Map、List を含む型）は `None`。
    /// `MAX_KEYS` を超える場合も `None`。
    pub fn keys(&self, enums: &[EnumNames]) -> Option<u64> {
        let n = match self {
            SType::Bool => 2,
            SType::Int(lo, hi) => {
                let n = i128::from(*hi) - i128::from(*lo) + 1;
                if n < 1 || n > i128::from(MAX_KEYS) {
                    return None;
                }
                n as u64
            }
            SType::Enum(id) => enums.get(*id)?.variants.len() as u64,
            SType::Tuple(ts) => product(ts.iter().map(|t| t.keys(enums)))?,
            SType::Record(fs) => product(fs.iter().map(|(_, t)| t.keys(enums)))?,
            SType::Option(t) => t.keys(enums)?.checked_add(1)?,
            SType::Set(_) | SType::Map(_, _) | SType::List(_, _) => return None,
        };
        (n <= MAX_KEYS).then_some(n)
    }

    /// スロット数。
    pub fn width(&self, enums: &[EnumNames]) -> usize {
        match self {
            SType::Bool | SType::Int(_, _) | SType::Enum(_) => 1,
            SType::Tuple(ts) => ts.iter().map(|t| t.width(enums)).sum(),
            SType::Record(fs) => fs.iter().map(|(_, t)| t.width(enums)).sum(),
            SType::Option(t) => 1 + t.width(enums),
            SType::Set(t) => t.keys(enums).unwrap_or(0) as usize,
            SType::Map(k, v) => k.keys(enums).unwrap_or(0) as usize * (1 + v.width(enums)),
            SType::List(t, n) => 1 + n * t.width(enums),
        }
    }

    /// スロットの中核の型を `out` に追加する。
    pub fn slot_types(&self, enums: &[EnumNames], out: &mut Vec<Type>) {
        match self {
            SType::Bool => out.push(Type::Bool),
            SType::Int(lo, hi) => out.push(Type::Int(*lo, *hi)),
            SType::Enum(id) => out.push(Type::Enum(*id)),
            SType::Tuple(ts) => ts.iter().for_each(|t| t.slot_types(enums, out)),
            SType::Record(fs) => fs.iter().for_each(|(_, t)| t.slot_types(enums, out)),
            SType::Option(t) => {
                out.push(Type::Bool);
                t.slot_types(enums, out);
            }
            SType::Set(t) => {
                for _ in 0..t.keys(enums).unwrap_or(0) {
                    out.push(Type::Bool);
                }
            }
            SType::Map(k, v) => {
                for _ in 0..k.keys(enums).unwrap_or(0) {
                    out.push(Type::Bool);
                    v.slot_types(enums, out);
                }
            }
            SType::List(t, n) => {
                out.push(Type::Int(0, *n as i64));
                for _ in 0..*n {
                    t.slot_types(enums, out);
                }
            }
        }
    }

    /// 既定値の符号を `out` に追加する。
    pub fn defaults(&self, enums: &[EnumNames], out: &mut Vec<i64>) {
        let mut tys = Vec::new();
        self.slot_types(enums, &mut tys);
        out.extend(tys.iter().map(default_code));
    }

    /// 正規順で `r` 番目の値の符号。`keys` が `Some` の型に限る。
    pub fn unrank(&self, enums: &[EnumNames], r: u64, out: &mut Vec<i64>) {
        match self {
            SType::Bool | SType::Enum(_) => out.push(r as i64),
            SType::Int(lo, _) => out.push(lo + r as i64),
            SType::Tuple(ts) => unrank_all(ts.iter(), enums, r, out),
            SType::Record(fs) => unrank_all(fs.iter().map(|(_, t)| t), enums, r, out),
            SType::Option(t) => {
                if r == 0 {
                    out.push(0);
                    t.defaults(enums, out);
                } else {
                    out.push(1);
                    t.unrank(enums, r - 1, out);
                }
            }
            SType::Set(_) | SType::Map(_, _) | SType::List(_, _) => {}
        }
    }

    /// 符号の正規順での番号。値が型に属さなければ `None`。Option が空なら中身の符号は見ない。
    pub fn rank(&self, enums: &[EnumNames], codes: &[i64]) -> Option<u64> {
        match self {
            SType::Bool => (0..=1).contains(&codes[0]).then_some(codes[0] as u64),
            SType::Int(lo, hi) => (*lo..=*hi).contains(&codes[0]).then(|| (codes[0] - lo) as u64),
            SType::Enum(id) => {
                let n = enums.get(*id)?.variants.len() as i64;
                (0..n).contains(&codes[0]).then_some(codes[0] as u64)
            }
            SType::Tuple(ts) => rank_all(ts.iter(), enums, codes),
            SType::Record(fs) => rank_all(fs.iter().map(|(_, t)| t), enums, codes),
            SType::Option(t) => match codes[0] {
                0 => Some(0),
                1 => Some(1 + t.rank(enums, &codes[1..])?),
                _ => None,
            },
            SType::Set(_) | SType::Map(_, _) | SType::List(_, _) => None,
        }
    }
}

impl XType {
    pub fn is_scalar(&self) -> bool {
        matches!(self, XType::Bool | XType::Int | XType::Enum(_))
    }

    pub fn width(&self, enums: &[EnumNames]) -> usize {
        match self {
            XType::Bool | XType::Int | XType::Enum(_) => 1,
            XType::Tuple(ts) => ts.iter().map(|t| t.width(enums)).sum(),
            XType::Record(fs) => fs.iter().map(|(_, t)| t.width(enums)).sum(),
            XType::Option(t) => 1 + t.width(enums),
            XType::Set(t) => SType::Set(t.clone()).width(enums),
            XType::Map(k, v) => SType::Map(k.clone(), v.clone()).width(enums),
            XType::List(t, n) => SType::List(t.clone(), *n).width(enums),
        }
    }

    /// 値を型 `st` の場所に置けるか。整数の範囲は問わない（値ごとに検査する）。
    pub fn fits(&self, st: &SType) -> bool {
        match (self, st) {
            (XType::Bool, SType::Bool) | (XType::Int, SType::Int(_, _)) => true,
            (XType::Enum(a), SType::Enum(b)) => a == b,
            (XType::Tuple(xs), SType::Tuple(ts)) => xs.len() == ts.len() && xs.iter().zip(ts).all(|(x, t)| x.fits(t)),
            (XType::Record(xs), SType::Record(ts)) => {
                xs.len() == ts.len() && xs.iter().zip(ts).all(|((a, x), (b, t))| a == b && x.fits(t))
            }
            (XType::Option(x), SType::Option(t)) => x.fits(t),
            (XType::Set(a), SType::Set(b)) => a == b,
            (XType::Map(ka, va), SType::Map(kb, vb)) => ka == kb && va == vb,
            (XType::List(a, n), SType::List(b, m)) => a == b && n == m,
            _ => false,
        }
    }
}

fn product(it: impl Iterator<Item = Option<u64>>) -> Option<u64> {
    let mut n: u64 = 1;
    for k in it {
        n = n.checked_mul(k?)?;
        if n > MAX_KEYS {
            return None;
        }
    }
    Some(n)
}

fn unrank_all<'a>(
    ts: impl DoubleEndedIterator<Item = &'a SType> + Clone,
    enums: &[EnumNames],
    r: u64,
    out: &mut Vec<i64>,
) {
    // 辞書順。最後の要素が最も速く変わる。
    let sizes: Vec<u64> = ts.clone().map(|t| t.keys(enums).unwrap_or(1)).collect();
    let mut digits = vec![0u64; sizes.len()];
    let mut rest = r;
    for (i, n) in sizes.iter().enumerate().rev() {
        digits[i] = rest % n;
        rest /= n;
    }
    for (t, d) in ts.zip(digits) {
        t.unrank(enums, d, out);
    }
}

fn rank_all<'a>(ts: impl Iterator<Item = &'a SType>, enums: &[EnumNames], codes: &[i64]) -> Option<u64> {
    let mut r: u64 = 0;
    let mut at = 0;
    for t in ts {
        let w = t.width(enums);
        let n = t.keys(enums)?;
        r = r * n + t.rank(enums, codes.get(at..at + w)?)?;
        at += w;
    }
    Some(r)
}

/// 中核の型の既定値の符号。
pub fn default_code(ty: &Type) -> i64 {
    match ty {
        Type::Bool | Type::Enum(_) => 0,
        Type::Int(lo, _) => *lo,
    }
}

/// 中核の型の符号を、中核の値にする。
pub fn core_value(ty: &Type, x: i64) -> CoreValue {
    match ty {
        Type::Bool => CoreValue::Bool(x != 0),
        Type::Int(_, _) => CoreValue::Int(x),
        Type::Enum(id) => CoreValue::Enum(*id, x),
    }
}

/// 中核の値の符号。
pub fn core_code(v: &CoreValue) -> i64 {
    match v {
        CoreValue::Bool(b) => i64::from(*b),
        CoreValue::Int(x) => *x,
        CoreValue::Enum(_, k) => *k,
    }
}
