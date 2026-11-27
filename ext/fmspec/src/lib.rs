//! fmspec の Ruby native extension（仕様書 §3.2）。
//!
//! Ruby に公開するオブジェクトは2種類ある。どちらのペイロードも Ruby の値を持たない。
//!
//! - `Fmspec::Native::Model`: IRのJSON文字列を受け取り、Rust 側で検証してから包んだ、不変のオブジェクト。
//! - `Fmspec::Native::Session`: Model-Based Testing の1ケース分の候補状態集合を持つオブジェクト。
//!   操作は GVL を保持したまま行う。
//!
//! 境界の規則は次のとおり。
//!
//! - IR、オプション、証拠、結果は、いずれもJSON文字列で受け渡す。CLIと同じ `fmspec-api` を呼ぶ。
//! - 拡張は Ruby のブロックやメソッドを呼び出さない。
//! - 探索と証拠の検査は GVL を解放して実行する。検査、シミュレーション、証明書の検査、カバレッジ、テスト経路は、
//!   Ruby の中断要求で打ち切る。割り込みは Ruby の例外として伝わり、例外が発生しなかった場合は `inconclusive` の結果を返す。
//!   `replay` と `shrink` は打ち切らない。
//! - panic は `Fmspec::InternalError` になる。`Exception` の子で、`rescue => e` では捕まらない。

use nupur::args::string_arg;
use nupur::rb::{prelude::*, Builtin, DataClass, Error, RbConst, Ruby, Value};
use nupur::string::ReadError;
use nupur::typed::{Birth, Payload, TypedType};
use nupur::{function, method};
use serde_json::Value as Json;
use std::sync::{Arc, Mutex, MutexGuard};

/// IR検証を通ったモデル。セッションと共有する。
struct ModelBox {
    model: Arc<fmspec_api::Model>,
}

impl Payload for ModelBox {}

/// MBTのセッション。メソッドは GVL を保持したまま呼ばれるので、ロックが競合することはない。
struct SessionBox {
    session: Mutex<fmspec_api::Session>,
}

impl Payload for SessionBox {}

impl SessionBox {
    /// セッションを借りる。前の操作が panic していても、そのまま使う。
    fn lock(&self) -> MutexGuard<'_, fmspec_api::Session> {
        self.session.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

static MODEL: TypedType<ModelBox, 0> = TypedType::base(c"Fmspec::Native::Model");
static MODEL_CLASS: RbConst<DataClass> = RbConst::new();
static SESSION: TypedType<SessionBox, 0> = TypedType::base(c"Fmspec::Native::Session");
static SESSION_CLASS: RbConst<DataClass> = RbConst::new();

fn read(ruby: &Ruby, v: Value) -> Result<String, Error> {
    let copy = nupur::string::read_utf8(ruby, string_arg(v)?, |_| None::<()>).map_err(|e| match e {
        ReadError::Raised(e) => e,
        _ => Error::new(Builtin::ArgumentError, "fmspec: the String is not valid UTF-8"),
    })?;
    Ok(copy.as_str().to_owned())
}

fn text(ruby: &Ruby, s: &str) -> Result<Value, Error> {
    Ok(nupur::string::utf8_str(ruby, s)?.as_value())
}

fn read_json(ruby: &Ruby, v: Value) -> Result<Json, Error> {
    serde_json::from_str(&read(ruby, v)?)
        .map_err(|_| Error::new(Builtin::ArgumentError, "fmspec: the String is not JSON"))
}

/// `Model.load(ir_json)`: IRを読み込んで検証する。
/// 受理すれば `Model` を、拒否すれば理由を書いたJSON文字列を返す。
fn model_load(ruby: &Ruby, ir: Value) -> Result<Value, Error> {
    match fmspec_api::load(&read(ruby, ir)?) {
        Ok(model) => {
            let birth = Birth {
                klass: MODEL_CLASS.defined(ruby)?,
                data: ModelBox { model: Arc::new(model) },
                roots: [],
            };
            Ok(MODEL.wrap::<Value>(ruby, birth)?.value())
        }
        Err(e) => text(ruby, &fmspec_api::load_error(&e).to_string()),
    }
}

/// `#describe`: モデルの概要のJSON文字列。
fn model_describe(ruby: &Ruby, this: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    text(ruby, &fmspec_api::describe(&handle.data().model).to_string())
}

/// GVL を解放して探索を実行し、結果のJSON文字列を返す。Ruby の中断要求で探索を打ち切る。
fn search<F>(ruby: &Ruby, run: F) -> Result<Value, Error>
where
    F: FnOnce(fmspec_api::Interrupt<'_>) -> Result<Json, String> + Send,
{
    // `Cancel::requested` は、GVL を解放した処理が中断要求を問い合わせるための Nupur の関数で、
    // アトミックな値を読むだけである。nupur_lints は Nupur の関数を一律に Ruby-free でないものと
    // 扱うので、ここで例外にする。lint が直れば、この expect が満たされなくなって検査に失敗する。
    #[cfg_attr(
        dylint_lib = "nupur_lints",
        expect(ruby_in_gvl_released_body, reason = "Cancel::requested only loads an atomic")
    )]
    let result = nupur::gvl::without_gvl_cancellable(ruby, move |cancel| {
        let interrupt = || cancel.requested();
        fmspec_api::to_text(run(Some(&interrupt)))
    })?;
    text(ruby, &result)
}

/// `#check(options_json)`: 幅優先探索で検査し、結果のJSON文字列を返す。
fn model_check(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    search(ruby, move |interrupt| fmspec_api::check(model, &options, interrupt))
}

/// `#simulate(options_json)`: ランダムシミュレーションで検査し、結果のJSON文字列を返す。
fn model_simulate(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    search(ruby, move |interrupt| fmspec_api::simulate(model, &options, interrupt))
}

/// `#verify_certificate(certificate_json, options_json)`: 提示された証明書を検査する。
fn model_verify_certificate(ruby: &Ruby, this: Value, certificate: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let certificate = read(ruby, certificate)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    search(ruby, move |interrupt| {
        fmspec_api::verify_certificate(model, &certificate, &options, interrupt)
    })
}

/// `#coverage(options_json)`: テストで確実に通った状態と遷移を、到達可能な状態と遷移と比べる。
fn model_coverage(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    search(ruby, move |interrupt| fmspec_api::coverage(model, &options, interrupt))
}

/// `#test_paths(options_json)`: 到達可能な状態と入力の組を覆うテスト経路を作る。
fn model_test_paths(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    search(ruby, move |interrupt| {
        fmspec_api::test_paths(model, &options, interrupt)
    })
}

/// `#replay(trace_json)`: 提示されたトレースを再生する。
fn model_replay(ruby: &Ruby, this: Value, trace: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let trace = read(ruby, trace)?;
    let model: &fmspec_api::Model = &handle.data().model;
    let result = nupur::gvl::without_gvl(ruby, move || fmspec_api::replay(model, &trace).to_string())?;
    text(ruby, &result)
}

/// `#shrink(trace_json, options_json)`: モデル違反のトレースを縮小する。
fn model_shrink(ruby: &Ruby, this: Value, trace: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let trace = read(ruby, trace)?;
    let options = read_json(ruby, options)?;
    let model: &fmspec_api::Model = &handle.data().model;
    let result = nupur::gvl::without_gvl(ruby, move || {
        fmspec_api::to_text(fmspec_api::shrink(model, &trace, &options))
    })?;
    text(ruby, &result)
}

/// `Session.start(model, options_json)`: セッションを作る。
/// オプションに誤りがあれば、その内容を書いたJSON文字列を返す。
fn session_start(ruby: &Ruby, model: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(model)?;
    let options = read_json(ruby, options)?;
    match fmspec_api::Session::new(Arc::clone(&handle.data().model), &options) {
        Ok(session) => {
            let data = SessionBox {
                session: Mutex::new(session),
            };
            let birth = Birth {
                klass: SESSION_CLASS.defined(ruby)?,
                data,
                roots: [],
            };
            Ok(SESSION.wrap::<Value>(ruby, birth)?.value())
        }
        Err(message) => text(ruby, &fmspec_api::to_text(Err(message))),
    }
}

/// `#initial(observation_json)`: 初期観測を渡す。
fn session_initial(ruby: &Ruby, this: Value, observation: Value) -> Result<Value, Error> {
    let handle = SESSION.check(this)?;
    let observation = read_json(ruby, observation)?;
    let result = handle.data().lock().start(&observation);
    text(ruby, &fmspec_api::to_text(result))
}

/// `#next_input`: 次の入力を問い合わせる。
fn session_next_input(ruby: &Ruby, this: Value) -> Result<Value, Error> {
    let handle = SESSION.check(this)?;
    let result = handle.data().lock().next_input();
    text(ruby, &fmspec_api::to_text(result))
}

/// `#check_input(input_json)`: 入力が全候補で有効かを確かめる。
fn session_check_input(ruby: &Ruby, this: Value, input: Value) -> Result<Value, Error> {
    let handle = SESSION.check(this)?;
    let input = read_json(ruby, input)?;
    let result = handle.data().lock().check_input(&input);
    text(ruby, &fmspec_api::to_text(result))
}

/// `#observe(report_json)`: 実装の応答を渡して、候補集合を更新する。
fn session_observe(ruby: &Ruby, this: Value, report: Value) -> Result<Value, Error> {
    let handle = SESSION.check(this)?;
    let report = read_json(ruby, report)?;
    let result = handle.data().lock().observe(&report);
    text(ruby, &fmspec_api::to_text(result))
}

/// `#candidates`: 現在の候補の状態のJSON文字列。
fn session_candidates(ruby: &Ruby, this: Value) -> Result<Value, Error> {
    let handle = SESSION.check(this)?;
    let candidates = handle.data().lock().candidates();
    text(ruby, &candidates.to_string())
}

/// `Native.format(result_json)`: 結果の人間向けの表示。
fn format_result(ruby: &Ruby, result: Value) -> Result<Value, Error> {
    text(ruby, &fmspec_api::human(&read_json(ruby, result)?))
}

/// `Native.version`: この拡張のバージョン。gem のバージョンと照合する。
fn version(ruby: &Ruby) -> Result<Value, Error> {
    text(ruby, env!("CARGO_PKG_VERSION"))
}

/// テスト用。GVL を解放した処理の中で panic する。
#[cfg(feature = "test-hooks")]
fn test_panic(ruby: &Ruby) -> Result<Value, Error> {
    #[allow(clippy::panic, reason = "the test hook exists to panic")]
    nupur::gvl::without_gvl(ruby, || -> () { panic!("fmspec: test panic") })?;
    Ok(ruby.qnil().as_value())
}

fn check(ruby: &Ruby) -> Result<(), Error> {
    nupur::abi::check_running_api("fmspec", "rake compile")?;
    nupur::abi::check_raise_state(ruby)
}

fn init(ruby: &Ruby) -> Result<(), Error> {
    let fmspec = ruby.define_module("Fmspec")?;
    let internal = fmspec.define_error("InternalError", ruby.exception_exception())?;
    nupur::rb::error::INTERNAL_ERROR.set(internal)?;

    let native = fmspec.define_module("Native")?;
    native.define_module_function("version", function!(version, 0))?;
    native.define_module_function("format", function!(format_result, 1))?;
    #[cfg(feature = "test-hooks")]
    native.define_module_function("test_panic", function!(test_panic, 0))?;

    let model = native.define_data_class(ruby, "Model", None)?;
    MODEL_CLASS.set(model)?;
    model.define_singleton_method("load", function!(model_load, 1))?;
    model.define_method("describe", method!(model_describe, 0))?;
    model.define_method("check", method!(model_check, 1))?;
    model.define_method("simulate", method!(model_simulate, 1))?;
    model.define_method("verify_certificate", method!(model_verify_certificate, 2))?;
    model.define_method("replay", method!(model_replay, 1))?;
    model.define_method("shrink", method!(model_shrink, 2))?;
    model.define_method("coverage", method!(model_coverage, 1))?;
    model.define_method("test_paths", method!(model_test_paths, 1))?;

    let session = native.define_data_class(ruby, "Session", None)?;
    SESSION_CLASS.set(session)?;
    session.define_singleton_method("start", function!(session_start, 2))?;
    session.define_method("initial", method!(session_initial, 1))?;
    session.define_method("next_input", method!(session_next_input, 0))?;
    session.define_method("check_input", method!(session_check_input, 1))?;
    session.define_method("observe", method!(session_observe, 1))?;
    session.define_method("candidates", method!(session_candidates, 0))?;
    Ok(())
}

#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn Init_fmspec() {
    // SAFETY: Ruby calls `Init_fmspec` on its thread, with the GVL held.
    unsafe { nupur::rb::method::run_init(check, init) };
}
