//! 探索と証拠の検査の打ち切り。中断要求と時間の上限を、区切りごとに確かめる。
//!
//! 打ち切りの判断は検証の対象外である。打ち切った探索や検査は `Unavailable` を判定ゲートに渡すか、
//! 判定ゲートの検査を `Inconclusive` で終えるので、判断がどう誤っても `Verified` や `Violated` の意味は変わらない。

use fmspec_core::evidence::Limit;
use std::time::Instant;

/// 中断要求か時間の上限に達していれば、その理由。両方なら中断要求を優先する。
/// 時間の上限は、`deadline` の時刻ちょうどで達したものとする。
pub(crate) fn stopped(interrupt: Option<&dyn Fn() -> bool>, deadline: Option<Instant>) -> Option<Limit> {
    if interrupt.is_some_and(|requested| requested()) {
        return Some(Limit::Interrupted);
    }
    if deadline.is_some_and(|at| Instant::now() >= at) {
        return Some(Limit::MaxTime);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::stopped;
    use fmspec_core::evidence::Limit;
    use std::time::{Duration, Instant};

    #[test]
    fn an_interrupt_takes_precedence_over_the_deadline() {
        let past = Some(Instant::now());
        assert_eq!(stopped(Some(&|| true), past), Some(Limit::Interrupted));
        assert_eq!(stopped(Some(&|| false), past), Some(Limit::MaxTime));
        assert_eq!(stopped(None, past), Some(Limit::MaxTime));
    }

    #[test]
    fn nothing_stops_before_the_deadline() {
        let later = Instant::now().checked_add(Duration::from_secs(3600));
        assert_eq!(stopped(None, later), None);
        assert_eq!(stopped(Some(&|| false), None), None);
        assert_eq!(stopped(None, None), None);
    }
}
