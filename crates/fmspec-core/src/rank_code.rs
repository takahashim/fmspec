//! fmspec-ir が値に付ける番号（u64）の計算。
//!
//! 番号は、中核の正規順の番号（`crate::keys` の `rank`）と同じ付け方をするが、その一致はここでは証明していない。
//! 事後条件は、桁の組み合わせとしての算術の性質だけである。

use vstd::prelude::*;

verus! {

/// キーの値を符号化するときに、番号に1桁加える。
pub fn append_rank_digit(prefix: u64, radix: u64, digit: u64) -> (out: Option<u64>)
    ensures
        out is Some <==> digit < radix && (prefix as int) * (radix as int) + digit <= u64::MAX,
        out matches Some(rank) ==> rank as int == (prefix as int) * (radix as int) + digit,
{
    if digit >= radix {
        return None;
    }
    prefix.checked_mul(radix)?.checked_add(digit)
}

pub open spec fn rank_digit_step(prefix: Option<u64>, radix: u64, digit: u64) -> Option<u64> {
    match prefix {
        Some(value) => {
            let rank = (value as int) * (radix as int) + (digit as int);
            if digit < radix && rank <= u64::MAX as int { Some(rank as u64) } else { None }
        },
        None => None,
    }
}

pub open spec fn rank_digits_value(parts: Seq<(u64, u64)>, count: nat) -> Option<u64>
    recommends count <= parts.len(),
    decreases count,
{
    if count == 0 {
        Some(0)
    } else {
        rank_digit_step(
            rank_digits_value(parts, (count - 1) as nat),
            parts[count - 1].1,
            parts[count - 1].0,
        )
    }
}

/// 要素の番号を順にたたむ。各桁が基数の範囲内にあることを検査する。
pub fn rank_digits_exec(parts: &Vec<(u64, u64)>) -> (out: Option<u64>)
    ensures out == rank_digits_value(parts@, parts@.len() as nat),
{
    let mut out = Some(0u64);
    let mut used = 0;
    while used < parts.len()
        invariant
            used <= parts@.len(),
            out == rank_digits_value(parts@, used as nat),
        decreases parts@.len() - used,
    {
        let _prefix = out;
        out = match out {
            Some(value) => append_rank_digit(value, parts[used].1, parts[used].0),
            None => None,
        };
        used = used + 1;
        proof {
            reveal(rank_digits_value);
            assert(out == rank_digit_step(_prefix, parts@[used as int - 1].1, parts@[used as int - 1].0));
        }
    }
    out
}

/// スカラーの符号の、閉区間での番号。
pub fn rank_interval_code(value: i64, min: i64, max: i64) -> (out: Option<u64>)
    ensures
        out is Some <==> min <= value <= max,
        out matches Some(rank) ==> rank as int == value as int - min as int,
{
    if value < min || value > max {
        return None;
    }
    let offset = (value as i128) - (min as i128);
    Some(offset as u64)
}

/// 中身の番号があり、1を足してもあふれない。
pub open spec fn rank_payload_can_increment(payload_rank: Option<u64>) -> bool {
    match payload_rank {
        Some(rank) => rank < u64::MAX,
        None => false,
    }
}

/// Optionの有無 `tag` と中身の番号から、番号を作る。空なら0、値があれば中身の番号に1を足す。
pub fn rank_option_code(tag: i64, payload_rank: Option<u64>) -> (out: Option<u64>)
    ensures
        out is Some <==> tag == 0 || (tag == 1 && rank_payload_can_increment(payload_rank)),
        tag == 0 ==> out == Some(0),
        tag == 1 ==> match payload_rank {
            Some(rank) if rank < u64::MAX => out matches Some(result) && result as int == rank as int + 1,
            _ => out is None,
        },
{
    match tag {
        0 => Some(0),
        1 => payload_rank?.checked_add(1),
        _ => None,
    }
}

} // verus!
