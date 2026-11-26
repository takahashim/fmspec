//! fmspec の Ruby native extension（仕様書 §3.2）。
//!
//! Ruby に公開するのは `Fmspec::Native::Model` だけである。IRのJSON文字列を受け取り、
//! Rust 側で検証してから包んだ、不変のオブジェクトである。ペイロードは Ruby の値を持たない。
//!
//! 境界の規則は次のとおり。
//!
//! - IR、オプション、証拠、結果は、いずれもJSON文字列で受け渡す。CLIと同じ `fmspec-api` を呼ぶ。
//! - 拡張は Ruby のブロックやメソッドを呼び出さない。
//! - 探索と証拠の検査は GVL を解放して実行し、Ruby の中断要求で探索を打ち切る。
//!   割り込みは Ruby の例外として伝わり、例外が発生しなかった場合は `inconclusive` の結果を返す。
//! - panic は `Fmspec::InternalError` になる。`Exception` の子で、`rescue => e` では捕まらない。

use nupur::args::string_arg;
use nupur::rb::{prelude::*, Builtin, DataClass, Error, ExceptionClass, RbConst, Ruby, Value};
use nupur::string::ReadError;
use nupur::typed::{Birth, Payload, TypedType};
use nupur::{function, method};
use serde_json::Value as Json;

/// IR検証を通ったモデル。
struct ModelBox {
    model: fmspec_api::Model,
}

impl Payload for ModelBox {}

static MODEL: TypedType<ModelBox, 0> = TypedType::base(c"Fmspec::Native::Model");
static MODEL_CLASS: RbConst<DataClass> = RbConst::new();
static INTERNAL: RbConst<ExceptionClass> = RbConst::new();

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
                data: ModelBox { model },
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

/// `#check(options_json)`: 幅優先探索で検査し、結果のJSON文字列を返す。
fn model_check(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model = &handle.data().model;
    // `Cancel::requested` は、GVL を解放した処理が中断要求を問い合わせるための Nupur の関数で、
    // アトミックな値を読むだけである。nupur_lints は Nupur の関数を一律に Ruby-free でないものと
    // 扱うので、ここで例外にする。lint が直れば、この expect が満たされなくなって検査に失敗する。
    #[cfg_attr(
        dylint_lib = "nupur_lints",
        expect(ruby_in_gvl_released_body, reason = "Cancel::requested only loads an atomic")
    )]
    let result = nupur::gvl::without_gvl_cancellable(ruby, move |cancel| {
        let interrupt = || cancel.requested();
        fmspec_api::to_text(fmspec_api::check(model, &options, Some(&interrupt)))
    })?;
    text(ruby, &result)
}

/// `#simulate(options_json)`: ランダムシミュレーションで検査し、結果のJSON文字列を返す。
fn model_simulate(ruby: &Ruby, this: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let options = read_json(ruby, options)?;
    let model = &handle.data().model;
    // `model_check` と同じ理由の例外。
    #[cfg_attr(
        dylint_lib = "nupur_lints",
        expect(ruby_in_gvl_released_body, reason = "Cancel::requested only loads an atomic")
    )]
    let result = nupur::gvl::without_gvl_cancellable(ruby, move |cancel| {
        let interrupt = || cancel.requested();
        fmspec_api::to_text(fmspec_api::simulate(model, &options, Some(&interrupt)))
    })?;
    text(ruby, &result)
}

/// `#verify_certificate(certificate_json, options_json)`: 提示された証明書を検査する。
fn model_verify_certificate(ruby: &Ruby, this: Value, certificate: Value, options: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let certificate = read(ruby, certificate)?;
    let options = read_json(ruby, options)?;
    let model = &handle.data().model;
    let result = nupur::gvl::without_gvl(ruby, move || {
        fmspec_api::to_text(fmspec_api::verify_certificate(model, &certificate, &options))
    })?;
    text(ruby, &result)
}

/// `#replay(trace_json)`: 提示されたトレースを再生する。
fn model_replay(ruby: &Ruby, this: Value, trace: Value) -> Result<Value, Error> {
    let handle = MODEL.check(this)?;
    let trace = read(ruby, trace)?;
    let model = &handle.data().model;
    let result = nupur::gvl::without_gvl(ruby, move || fmspec_api::replay(model, &trace).to_string())?;
    text(ruby, &result)
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
    INTERNAL.set(internal)?;
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
    Ok(())
}

#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn Init_fmspec() {
    // SAFETY: Ruby calls `Init_fmspec` on its thread, with the GVL held.
    unsafe { nupur::rb::method::run_init(check, init) };
}
