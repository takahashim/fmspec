//! `fmspec` コマンド（仕様書 §15）。
//!
//! 引数を fmspec-api のオプションに直して呼び出し、結果をJSONまたは人間向けの形で出力する。
//! 終了コードは次のとおり。成功の種類は出力の `status` で区別する。
//!
//! - `0`: 要求された検査の正常完了（`verified`、`sampled`、`valid`）
//! - `1`: 反例、または提示された証明書やトレースの拒否
//! - `2`: 評価エラー、不正な入力、内部エラー
//! - `3`: 探索未完了

use fmspec_api::Model;
use serde_json::{json, Map, Value};

pub const EXIT_OK: i32 = 0;
pub const EXIT_VIOLATED: i32 = 1;
pub const EXIT_ERROR: i32 = 2;
pub const EXIT_INCONCLUSIVE: i32 = 3;

pub struct Run {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

const USAGE: &str = "\
使い方:
  fmspec validate MODEL.json
  fmspec check MODEL.json [--strategy bfs] [--max-states N] [検査条件] [--certificate-out FILE] [--trace-out FILE]
  fmspec simulate MODEL.json [--traces N] [--max-steps N] [--seed N] [検査条件] [--trace-out FILE]
  fmspec verify-certificate MODEL.json CERTIFICATE.json [検査条件]
  fmspec replay MODEL.json TRACE.json

検査条件（省略時は、すべての操作・不変条件・遷移契約が対象で、デッドロック検査は無効）:
  --actions A,B,...      対象の操作
  --invariants A,B,...   対象の不変条件
  --contracts A,B,...    対象の遷移契約
  --deadlock             非終端のデッドロックを検査する

共通:
  --json                 結果を機械可読のJSONで出力する
";

/// 値を取るオプション。[フラグ, オプションのキー, 種類]。
const VALUED: [(&str, &str, Kind); 8] = [
    ("--max-states", "max_states", Kind::Count),
    ("--traces", "traces", Kind::Count),
    ("--max-steps", "max_steps", Kind::Count),
    ("--seed", "seed", Kind::Count),
    ("--actions", "actions", Kind::Names),
    ("--invariants", "invariants", Kind::Names),
    ("--contracts", "contracts", Kind::Names),
    ("--strategy", "strategy", Kind::Text),
];

#[derive(Clone, Copy)]
enum Kind {
    Count,
    Names,
    Text,
}

struct Args {
    positional: Vec<String>,
    json: bool,
    /// fmspec-api に渡すオプション。
    options: Map<String, Value>,
    strategy: Option<String>,
    certificate_out: Option<String>,
    trace_out: Option<String>,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        positional: Vec::new(),
        json: false,
        options: Map::new(),
        strategy: None,
        certificate_out: None,
        trace_out: None,
    };
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        let mut value = || -> Result<String, String> {
            i += 1;
            args.get(i).cloned().ok_or_else(|| format!("{arg} には値が必要です"))
        };
        match arg {
            "--json" => parsed.json = true,
            "--deadlock" => {
                parsed.options.insert("deadlock".to_string(), json!(true));
            }
            "--certificate-out" => parsed.certificate_out = Some(value()?),
            "--trace-out" => parsed.trace_out = Some(value()?),
            _ => match VALUED.iter().find(|(name, _, _)| *name == arg) {
                Some((_, key, kind)) => {
                    let text = value()?;
                    match kind {
                        Kind::Count => match text.parse::<u64>() {
                            Ok(n) => parsed.options.insert(key.to_string(), json!(n)),
                            Err(_) => return Err(format!("{arg} は0以上の整数です（{text:?}）")),
                        },
                        Kind::Names => {
                            let names: Vec<&str> = text.split(',').filter(|s| !s.is_empty()).collect();
                            parsed.options.insert(key.to_string(), json!(names))
                        }
                        Kind::Text => {
                            parsed.strategy = Some(text);
                            None
                        }
                    };
                }
                None if arg.starts_with("--") => return Err(format!("未知のオプション {arg}")),
                None => parsed.positional.push(arg.to_string()),
            },
        }
        i += 1;
    }
    Ok(parsed)
}

struct Io<'a> {
    read: &'a dyn Fn(&str) -> std::io::Result<String>,
    write: &'a dyn Fn(&str, &str) -> std::io::Result<()>,
}

/// 失敗を、終了コード2の結果にする。
fn failure(json: bool, status: &str, message: String) -> Run {
    if json {
        let body = json!({"status": status, "message": message});
        Run {
            code: EXIT_ERROR,
            stdout: format!("{body}\n"),
            stderr: String::new(),
        }
    } else {
        Run {
            code: EXIT_ERROR,
            stdout: String::new(),
            stderr: format!("{status}: {message}\n"),
        }
    }
}

fn exit_code(body: &Value) -> i32 {
    match body["status"].as_str() {
        Some("verified" | "sampled" | "valid") => EXIT_OK,
        Some("violated" | "rejected") => EXIT_VIOLATED,
        Some("inconclusive") => EXIT_INCONCLUSIVE,
        _ => EXIT_ERROR,
    }
}

fn finish(json: bool, body: Value) -> Run {
    let stdout = if json {
        format!("{}\n", serde_json::to_string_pretty(&body).unwrap_or_default())
    } else {
        fmspec_api::human(&body)
    };
    Run {
        code: exit_code(&body),
        stdout,
        stderr: String::new(),
    }
}

fn read(io: &Io, path: &str, json: bool) -> Result<String, Run> {
    (io.read)(path).map_err(|e| failure(json, "input_error", format!("{path}: {e}")))
}

fn load_model(io: &Io, path: &str, json: bool) -> Result<Model, Run> {
    let text = read(io, path, json)?;
    fmspec_api::load(&text).map_err(|e| failure(json, "invalid_model", format!("{path}: {e}")))
}

fn write_file(io: &Io, path: &str, body: &Value, json: bool) -> Result<(), Run> {
    let text = format!("{}\n", serde_json::to_string_pretty(body).unwrap_or_default());
    (io.write)(path, &text).map_err(|e| failure(json, "input_error", format!("{path}: {e}")))
}

fn usage<T>(json: bool, message: impl Into<String>) -> Result<T, Run> {
    Err(failure(json, "usage_error", message.into()))
}

fn save_trace(io: &Io, a: &Args, body: &Value) -> Result<(), Run> {
    if let (Some(out), Some(trace)) = (&a.trace_out, body.get("trace")) {
        write_file(io, out, trace, a.json)?;
    }
    Ok(())
}

fn cmd_validate(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return usage(a.json, "validate にはモデルのファイルを1つ指定します");
    };
    let model = load_model(io, path, a.json)?;
    Ok(finish(a.json, fmspec_api::describe(&model)))
}

fn cmd_check(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return usage(a.json, "check にはモデルのファイルを1つ指定します");
    };
    if let Some(s) = a.strategy.as_deref().filter(|s| *s != "bfs") {
        return usage(a.json, format!("未対応の探索方式 {s:?}（対応しているのは bfs）"));
    }
    let model = load_model(io, path, a.json)?;
    let mut options = a.options.clone();
    options.insert("certificate".to_string(), json!(a.certificate_out.is_some()));
    let mut body =
        fmspec_api::check(&model, &Value::Object(options), None).map_err(|e| failure(a.json, "usage_error", e))?;
    if let Some(certificate) = body.as_object_mut().and_then(|map| map.remove("certificate")) {
        if let Some(out) = &a.certificate_out {
            write_file(io, out, &certificate, a.json)?;
        }
    }
    save_trace(io, a, &body)?;
    Ok(finish(a.json, body))
}

fn cmd_simulate(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return usage(a.json, "simulate にはモデルのファイルを1つ指定します");
    };
    let model = load_model(io, path, a.json)?;
    let body = fmspec_api::simulate(&model, &Value::Object(a.options.clone()), None)
        .map_err(|e| failure(a.json, "usage_error", e))?;
    save_trace(io, a, &body)?;
    Ok(finish(a.json, body))
}

fn cmd_verify_certificate(io: &Io, a: &Args) -> Result<Run, Run> {
    let [model_path, cert_path] = a.positional.as_slice() else {
        return usage(a.json, "verify-certificate にはモデルと証明書のファイルを指定します");
    };
    let model = load_model(io, model_path, a.json)?;
    let certificate = read(io, cert_path, a.json)?;
    let body = fmspec_api::verify_certificate(&model, &certificate, &Value::Object(a.options.clone()))
        .map_err(|e| failure(a.json, "usage_error", e))?;
    Ok(finish(a.json, body))
}

fn cmd_replay(io: &Io, a: &Args) -> Result<Run, Run> {
    let [model_path, trace_path] = a.positional.as_slice() else {
        return usage(a.json, "replay にはモデルとトレースのファイルを指定します");
    };
    let model = load_model(io, model_path, a.json)?;
    let trace = read(io, trace_path, a.json)?;
    Ok(finish(a.json, fmspec_api::replay(&model, &trace)))
}

/// コマンドを実行する。ファイルの読み書きは引数の関数で行う。
pub fn run(
    args: &[String],
    read: &dyn Fn(&str) -> std::io::Result<String>,
    write: &dyn Fn(&str, &str) -> std::io::Result<()>,
) -> Run {
    let io = Io { read, write };
    let Some((command, rest)) = args.split_first() else {
        return Run {
            code: EXIT_ERROR,
            stdout: String::new(),
            stderr: USAGE.to_string(),
        };
    };
    if command == "--help" || command == "-h" || command == "help" {
        return Run {
            code: EXIT_OK,
            stdout: USAGE.to_string(),
            stderr: String::new(),
        };
    }
    if command == "--version" {
        return Run {
            code: EXIT_OK,
            stdout: format!("fmspec {}\n", env!("CARGO_PKG_VERSION")),
            stderr: String::new(),
        };
    }
    let json = rest.iter().any(|a| a == "--json");
    let parsed = match parse_args(rest) {
        Ok(a) => a,
        Err(e) => return failure(json, "usage_error", e),
    };
    let result = match command.as_str() {
        "validate" => cmd_validate(&io, &parsed),
        "check" => cmd_check(&io, &parsed),
        "simulate" => cmd_simulate(&io, &parsed),
        "verify-certificate" => cmd_verify_certificate(&io, &parsed),
        "replay" => cmd_replay(&io, &parsed),
        "shrink" => usage(json, "shrink はまだ実装していません（ロードマップの段階5）"),
        _ => usage(json, format!("未知のコマンド {command:?}\n{USAGE}")),
    };
    match result {
        Ok(run) | Err(run) => run,
    }
}
