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
use fmspec_core::kernel::model::Type;
use fmspec_core::value::encoding::SType as CoreSType;
use fmspec_core::value::rank_code::{rank_codes, unrank_codes};
use fmspec_core::value::stype_exec::{keys_exec, stype_width};

/// Setの要素の型と、Mapのキーの型が取れる値の数の上限。
pub const MAX_KEYS: u64 = fmspec_core::value::encoding::MAX_KEYS;
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
    /// `MAX_KEYS` を超える場合も `None`。中核の [`keys_exec`] で求める（仕様 `keys` に一致する）。
    pub fn keys(&self, enums: &[EnumNames]) -> Option<u64> {
        keys_exec(&self.core_stype(), &label_counts(enums))
    }

    /// スロット数。中核の [`stype_width`] で求める（仕様 `width` に一致する）。
    /// 型か部分の型の幅が大きすぎて中核が計算しない型では `usize::MAX`（`MAX_WIDTH` の検査で拒否する）。
    pub fn width(&self, enums: &[EnumNames]) -> usize {
        stype_width(&self.core_stype(), &label_counts(enums)).unwrap_or(usize::MAX)
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

    /// 正規順で `r` 番目の値の符号。キーの型でないか、`r` が値の数以上なら `None`。
    /// 中核の [`unrank_codes`] で求める（番号 `r` の値の符号化であることが証明されている）。
    pub fn unrank(&self, enums: &[EnumNames], r: u64) -> Option<Vec<i64>> {
        unrank_codes(&self.core_stype(), &label_counts(enums), r)
    }

    /// 符号の正規順での番号。値が型に属さなければ `None`。Option が空なら中身の符号は見ない。
    /// 中核の [`rank_codes`] で求める（値の符号化なら、値の番号であることが証明されている）。
    pub fn rank(&self, enums: &[EnumNames], codes: &[i64]) -> Option<u64> {
        rank_codes(&self.core_stype(), &label_counts(enums), &codes.to_vec())
    }

    /// 値の数、幅、番号の計算に使う中核の型。Recordのフィールドの名前はこれらに関わらないので、位置の番号を付ける。
    fn core_stype(&self) -> CoreSType {
        match self {
            SType::Bool => CoreSType::Bool,
            SType::Int(lo, hi) => CoreSType::Int(*lo, *hi),
            SType::Enum(id) => CoreSType::Enum(*id),
            SType::Tuple(ts) => CoreSType::Tuple(ts.iter().map(SType::core_stype).collect()),
            SType::Record(fs) => CoreSType::Record(
                (0..fs.len()).collect(),
                fs.iter().map(|(_, t)| t.core_stype()).collect(),
            ),
            SType::Option(t) => CoreSType::Option(Box::new(t.core_stype())),
            SType::Set(t) => CoreSType::Set(Box::new(t.core_stype())),
            SType::Map(k, v) => CoreSType::Map(Box::new(k.core_stype()), Box::new(v.core_stype())),
            SType::List(t, n) => CoreSType::List(Box::new(t.core_stype()), *n),
        }
    }
}

/// 各列挙型のラベルの数（中核の `enums`）。
fn label_counts(enums: &[EnumNames]) -> Vec<i64> {
    enums
        .iter()
        .map(|e| i64::try_from(e.variants.len()).unwrap_or(i64::MAX))
        .collect()
}

impl XType {
    pub fn is_scalar(&self) -> bool {
        matches!(self, XType::Bool | XType::Int | XType::Enum(_))
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

/// 中核の型の既定値の符号。
pub fn default_code(ty: &Type) -> i64 {
    match ty {
        Type::Bool | Type::Enum(_) => 0,
        Type::Int(lo, _) => *lo,
    }
}
