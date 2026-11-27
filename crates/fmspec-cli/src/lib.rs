//! `fmspec` コマンド（仕様書 §15）。
//!
//! 引数を fmspec-api のオプションに直して呼び出し、結果をJSONまたは人間向けの形で出力する。
//! 終了コードは次のとおり。成功の種類は出力の `status` で区別する。
//!
//! - `0`: 要求された検査の正常完了（`verified`、`sampled`、`valid`、`refines`）
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

impl Run {
    fn stdout(code: i32, stdout: String) -> Run {
        Run {
            code,
            stdout,
            stderr: String::new(),
        }
    }

    fn stderr(code: i32, stderr: String) -> Run {
        Run {
            code,
            stdout: String::new(),
            stderr,
        }
    }
}

const USAGE: &str = "\
使い方:
  fmspec validate MODEL.json
  fmspec check MODEL.json [--strategy bfs] [--max-states N] [--max-depth N] [--max-time-ms N] [--max-check-cost N] [検査条件] [--certificate-out FILE] [--trace-out FILE]
  fmspec simulate MODEL.json [--traces N] [--max-steps N] [--seed N] [--max-time-ms N] [検査条件] [--trace-out FILE]
  fmspec verify-certificate MODEL.json CERTIFICATE.json [--max-check-cost N] [--max-time-ms N] [検査条件] [--allow-other-model]
  fmspec replay MODEL.json TRACE.json [--max-check-cost N] [--allow-other-model]
  fmspec shrink MODEL.json TRACE.json [--attempts N] [--max-time-ms N] [--max-check-cost N] [--trace-out FILE] [--allow-other-model]
  fmspec refine REFINEMENT.json [--max-states N] [--max-depth N] [--max-time-ms N] [--actions A,B,...]

検査条件（省略時は、すべての操作・不変条件・遷移契約が対象で、デッドロック検査は無効）:
  --actions A,B,...      対象の操作
  --invariants A,B,...   対象の不変条件
  --contracts A,B,...    対象の遷移契約
  --deadlock             非終端のデッドロックを検査する

証拠（verify-certificate、replay、shrink）:
  --allow-other-model    model_digest が違う証拠も、このモデルの名前と型で読んで検査する

縮小（shrink）:
  --attempts N           試す候補（ステップの削除と引数の変更）の数の上限（既定 10000）
  --max-time-ms N        縮小の時間の上限。上限に達したら、それまでに判定ゲートが受理したトレースを返す

共通:
  --json                 結果を機械可読のJSONで出力する
  -h, --help             この使い方を表示する
  --                     以降の引数を、すべてファイルとして読む
";

/// fmspec-api に渡す、値を取るオプション。[フラグ, オプションのキー, 種類]。
const VALUED: [(&str, &str, Kind); 11] = [
    ("--max-states", "max_states", Kind::Count(1)),
    ("--max-depth", "max_depth", Kind::Count(0)),
    ("--max-time-ms", "max_time_ms", Kind::Count(0)),
    ("--max-check-cost", "max_check_cost", Kind::Count(0)),
    ("--traces", "traces", Kind::Count(1)),
    ("--max-steps", "max_steps", Kind::Count(0)),
    ("--seed", "seed", Kind::Count(0)),
    ("--attempts", "attempts", Kind::Count(1)),
    ("--actions", "actions", Kind::Names),
    ("--invariants", "invariants", Kind::Names),
    ("--contracts", "contracts", Kind::Names),
];

#[derive(Clone, Copy)]
enum Kind {
    /// 下限以上の整数。下限は fmspec-api と同じで、誤りはフラグの名前で報告する。
    Count(u64),
    Names,
}

/// 数字だけからなる、`min` 以上の整数。`u64::from_str` は `+5` も受け付けるので、先に数字だけかを確かめる。
fn count(flag: &str, text: &str, min: u64) -> Result<u64, String> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{flag} は{min}以上の整数です（{text:?}）"));
    }
    match text.parse::<u64>() {
        Ok(n) if n >= min => Ok(n),
        Ok(_) => Err(format!("{flag} は{min}以上の整数です（{text:?}）")),
        Err(_) => Err(format!("{flag} が大きすぎます（{text:?}）")),
    }
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

/// 値を取らない、または fmspec-api のオプションに直さないフラグ。
const OTHER_FLAGS: [&str; 5] = [
    "--deadlock",
    "--allow-other-model",
    "--strategy",
    "--certificate-out",
    "--trace-out",
];

/// `--` より前の引数。`--` 以降はすべて位置引数として読む。
fn before_separator(args: &[String]) -> &[String] {
    let end = args.iter().position(|a| a == "--").unwrap_or(args.len());
    &args[..end]
}

/// コマンド `command` の引数を、そのコマンドが受け付けるオプション（`allowed` と、`conditions` なら検査条件）で
/// 解析する。左から順に読み、最初に見つけた誤りを返す。値を読む前に、オプションを受け付けるかを確かめる。
fn parse_args(command: &str, allowed: &[&str], conditions: bool, args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        positional: Vec::new(),
        json: false,
        options: Map::new(),
        strategy: None,
        certificate_out: None,
        trace_out: None,
    };
    let mut seen: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        if arg == "--" {
            parsed.positional.extend(args[i + 1..].iter().cloned());
            break;
        }
        if !arg.starts_with("--") {
            parsed.positional.push(arg.to_string());
            i += 1;
            continue;
        }
        if arg == "--json" {
            parsed.json = true;
            i += 1;
            continue;
        }
        if !OTHER_FLAGS.contains(&arg) && !VALUED.iter().any(|(name, _, _)| *name == arg) {
            return Err(format!("未知のオプション {arg}"));
        }
        // コマンドが使わないオプションを拒否する。黙って無視すると、指定が効いたと誤解させる。
        if !allowed.contains(&arg) && !(conditions && CONDITION_FLAGS.contains(&arg)) {
            return Err(format!("{command} は {arg} を受け付けません"));
        }
        // 重ねた指定の後のほうだけを使うと、順序で結果が変わり、前の指定が効いたと誤解させる。
        // `--json` は重ねても意味が変わらないので、上で受け付けている。
        if seen.contains(&arg) {
            return Err(format!("{arg} は1回だけ指定できます"));
        }
        seen.push(arg);
        // `--` で始まる語は値として読まない。`--trace-out --json` の `--json` を値として消費すると、
        // run が引数全体から判定する出力の形式と食い違う。
        let mut value = || -> Result<String, String> {
            match args.get(i + 1) {
                Some(next) if !next.starts_with("--") => {
                    i += 1;
                    Ok(next.clone())
                }
                _ => Err(format!("{arg} には値が必要です")),
            }
        };
        match arg {
            "--deadlock" => {
                parsed.options.insert("deadlock".to_string(), json!(true));
            }
            "--allow-other-model" => {
                parsed.options.insert("allow_other_model".to_string(), json!(true));
            }
            "--strategy" => parsed.strategy = Some(value()?),
            "--certificate-out" => parsed.certificate_out = Some(value()?),
            "--trace-out" => parsed.trace_out = Some(value()?),
            _ => {
                if let Some((_, key, kind)) = VALUED.iter().find(|(name, _, _)| *name == arg) {
                    let text = value()?;
                    let option = match kind {
                        Kind::Count(min) => json!(count(arg, &text, *min)?),
                        Kind::Names => json!(text.split(',').filter(|s| !s.is_empty()).collect::<Vec<_>>()),
                    };
                    parsed.options.insert(key.to_string(), option);
                }
            }
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
        Run::stdout(EXIT_ERROR, format!("{body}\n"))
    } else {
        Run::stderr(EXIT_ERROR, format!("{status}: {message}\n"))
    }
}

/// 使い方の誤り。fmspec-api がオプションを拒否したときにも使う。
fn usage(json: bool, message: impl Into<String>) -> Run {
    failure(json, "usage_error", message.into())
}

fn exit_code(body: &Value) -> i32 {
    match body["status"].as_str() {
        Some("verified" | "sampled" | "valid" | "refines") => EXIT_OK,
        Some("violated" | "rejected" | "not_refines") => EXIT_VIOLATED,
        Some("inconclusive") => EXIT_INCONCLUSIVE,
        _ => EXIT_ERROR,
    }
}

/// 整形したJSONの文字列。末尾に改行を付ける。
fn pretty(body: &Value) -> String {
    format!("{}\n", serde_json::to_string_pretty(body).unwrap_or_default())
}

fn finish(json: bool, body: Value) -> Run {
    let stdout = if json { pretty(&body) } else { fmspec_api::human(&body) };
    Run::stdout(exit_code(&body), stdout)
}

fn read(io: &Io, path: &str, json: bool) -> Result<String, Run> {
    (io.read)(path).map_err(|e| failure(json, "input_error", format!("{path}: {e}")))
}

fn load_model(io: &Io, path: &str, json: bool) -> Result<Model, Run> {
    let text = read(io, path, json)?;
    fmspec_api::load(&text).map_err(|e| failure(json, "invalid_model", format!("{path}: {e}")))
}

fn write_file(io: &Io, path: &str, body: &Value, json: bool) -> Result<(), Run> {
    (io.write)(path, &pretty(body)).map_err(|e| failure(json, "output_error", format!("{path}: {e}")))
}

/// 検査条件のオプション。
const CONDITION_FLAGS: [&str; 4] = ["--actions", "--invariants", "--contracts", "--deadlock"];

type Command = fn(&Io, &Args) -> Result<Run, Run>;

/// コマンドの一覧。[名前, 受け付けるオプション, 検査条件を受け付けるか, 実行する関数]。
const COMMANDS: [(&str, &[&str], bool, Command); 7] = [
    ("validate", &[], false, cmd_validate),
    (
        "check",
        &[
            "--strategy",
            "--max-states",
            "--max-depth",
            "--max-time-ms",
            "--max-check-cost",
            "--certificate-out",
            "--trace-out",
        ],
        true,
        cmd_check,
    ),
    (
        "simulate",
        &["--traces", "--max-steps", "--seed", "--max-time-ms", "--trace-out"],
        true,
        cmd_simulate,
    ),
    (
        "verify-certificate",
        &["--max-check-cost", "--max-time-ms", "--allow-other-model"],
        true,
        cmd_verify_certificate,
    ),
    (
        "replay",
        &["--max-check-cost", "--allow-other-model"],
        false,
        cmd_replay,
    ),
    (
        "shrink",
        &[
            "--attempts",
            "--max-time-ms",
            "--max-check-cost",
            "--trace-out",
            "--allow-other-model",
        ],
        false,
        cmd_shrink,
    ),
    (
        "refine",
        &["--max-states", "--max-depth", "--max-time-ms", "--actions"],
        false,
        cmd_refine,
    ),
];

/// 判定ゲートが受理したトレース（違反か評価エラー）だけを書き出す。拒否されたトレースは書き出さない。
fn save_trace(io: &Io, a: &Args, body: &Value) -> Result<(), Run> {
    if !matches!(body["status"].as_str(), Some("violated" | "error")) {
        return Ok(());
    }
    if let (Some(out), Some(trace)) = (&a.trace_out, body.get("trace")) {
        write_file(io, out, trace, a.json)?;
    }
    Ok(())
}

fn cmd_validate(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return Err(usage(a.json, "validate にはモデルのファイルを1つ指定します"));
    };
    let model = load_model(io, path, a.json)?;
    Ok(finish(a.json, fmspec_api::describe(&model)))
}

fn cmd_check(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return Err(usage(a.json, "check にはモデルのファイルを1つ指定します"));
    };
    if let Some(s) = a.strategy.as_deref().filter(|s| *s != "bfs") {
        return Err(usage(a.json, format!("未対応の探索方式 {s:?}（対応しているのは bfs）")));
    }
    let model = load_model(io, path, a.json)?;
    let mut options = a.options.clone();
    options.insert("certificate".to_string(), json!(a.certificate_out.is_some()));
    let mut body = fmspec_api::check(&model, &Value::Object(options), None).map_err(|e| usage(a.json, e))?;
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
        return Err(usage(a.json, "simulate にはモデルのファイルを1つ指定します"));
    };
    let model = load_model(io, path, a.json)?;
    let body = fmspec_api::simulate(&model, &Value::Object(a.options.clone()), None).map_err(|e| usage(a.json, e))?;
    save_trace(io, a, &body)?;
    Ok(finish(a.json, body))
}

fn cmd_verify_certificate(io: &Io, a: &Args) -> Result<Run, Run> {
    let [model_path, cert_path] = a.positional.as_slice() else {
        return Err(usage(
            a.json,
            "verify-certificate にはモデルと証明書のファイルを指定します",
        ));
    };
    let model = load_model(io, model_path, a.json)?;
    let certificate = read(io, cert_path, a.json)?;
    let body = fmspec_api::verify_certificate(&model, &certificate, &Value::Object(a.options.clone()), None)
        .map_err(|e| usage(a.json, e))?;
    Ok(finish(a.json, body))
}

fn cmd_replay(io: &Io, a: &Args) -> Result<Run, Run> {
    let [model_path, trace_path] = a.positional.as_slice() else {
        return Err(usage(a.json, "replay にはモデルとトレースのファイルを指定します"));
    };
    let model = load_model(io, model_path, a.json)?;
    let trace = read(io, trace_path, a.json)?;
    let body =
        fmspec_api::replay_with(&model, &trace, &Value::Object(a.options.clone())).map_err(|e| usage(a.json, e))?;
    Ok(finish(a.json, body))
}

fn cmd_shrink(io: &Io, a: &Args) -> Result<Run, Run> {
    let [model_path, trace_path] = a.positional.as_slice() else {
        return Err(usage(a.json, "shrink にはモデルとトレースのファイルを指定します"));
    };
    let model = load_model(io, model_path, a.json)?;
    let trace = read(io, trace_path, a.json)?;
    let body =
        fmspec_api::shrink(&model, &trace, &Value::Object(a.options.clone()), None).map_err(|e| usage(a.json, e))?;
    save_trace(io, a, &body)?;
    Ok(finish(a.json, body))
}

fn cmd_refine(io: &Io, a: &Args) -> Result<Run, Run> {
    let [path] = a.positional.as_slice() else {
        return Err(usage(a.json, "refine には詳細化の文書のファイルを1つ指定します"));
    };
    let text = read(io, path, a.json)?;
    let r = fmspec_api::load_refinement(&text).map_err(|e| failure(a.json, "invalid_model", format!("{path}: {e}")))?;
    let body = fmspec_api::refine(&r, &Value::Object(a.options.clone()), None).map_err(|e| usage(a.json, e))?;
    Ok(finish(a.json, body))
}

/// コマンドを実行する。ファイルの読み書きは引数の関数で行う。
pub fn run(
    args: &[String],
    read: &dyn Fn(&str) -> std::io::Result<String>,
    write: &dyn Fn(&str, &str) -> std::io::Result<()>,
) -> Run {
    let io = Io { read, write };
    let Some((command, rest)) = args.split_first() else {
        return Run::stderr(EXIT_ERROR, USAGE.to_string());
    };
    if command == "--help" || command == "-h" || command == "help" {
        return Run::stdout(EXIT_OK, USAGE.to_string());
    }
    if command == "--version" {
        return Run::stdout(EXIT_OK, format!("fmspec {}\n", env!("CARGO_PKG_VERSION")));
    }
    // parse_args は `--json` を値として消費しないので、引数の解析に失敗したときも、成功したときの
    // `Args::json` と同じ形式になる。
    let options = before_separator(rest);
    let json = options.iter().any(|a| a == "--json");
    let Some(&(name, allowed, conditions, cmd)) = COMMANDS.iter().find(|(name, ..)| name == command) else {
        let message = format!("未知のコマンド {command:?}");
        return if json {
            usage(json, message)
        } else {
            Run::stderr(EXIT_ERROR, format!("usage_error: {message}\n{USAGE}"))
        };
    };
    if options.iter().any(|a| a == "--help" || a == "-h") {
        return Run::stdout(EXIT_OK, USAGE.to_string());
    }
    let parsed = match parse_args(name, allowed, conditions, rest) {
        Ok(a) => a,
        Err(e) => return usage(json, e),
    };
    match cmd(&io, &parsed) {
        Ok(run) | Err(run) => run,
    }
}
