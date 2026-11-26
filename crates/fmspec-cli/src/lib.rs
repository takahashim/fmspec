//! `fmspec` コマンド（仕様書 §15）。
//!
//! 終了コードは次のとおり。成功の種類は出力の `status` で区別する。
//!
//! - `0`: 要求された検査の正常完了
//! - `1`: 反例、または提示された証明書やトレースの拒否
//! - `2`: 評価エラー、不正な入力、内部エラー
//! - `3`: 探索未完了

mod report;

use fmspec_core::evidence::Evidence;
use fmspec_core::gate::{decide, VerdictKind};
use fmspec_core::semantics::Conditions;
use fmspec_ir::{
    certificate_from_json, certificate_to_json, default_conditions, load, trace_from_json, LoadError, Model,
};
use fmspec_search::{check, BfsOptions, Status};
use serde_json::{json, Value};

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

struct Options {
    positional: Vec<String>,
    json: bool,
    max_states: Option<usize>,
    deadlock: bool,
    actions: Option<Vec<String>>,
    invariants: Option<Vec<String>>,
    contracts: Option<Vec<String>>,
    certificate_out: Option<String>,
    trace_out: Option<String>,
}

fn names(list: &str) -> Vec<String> {
    list.split(',').filter(|s| !s.is_empty()).map(str::to_string).collect()
}

fn parse_options(args: &[String]) -> Result<Options, String> {
    let mut o = Options {
        positional: Vec::new(),
        json: false,
        max_states: None,
        deadlock: false,
        actions: None,
        invariants: None,
        contracts: None,
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
            "--json" => o.json = true,
            "--deadlock" => o.deadlock = true,
            "--strategy" => {
                let s = value()?;
                if s != "bfs" {
                    return Err(format!("未対応の探索方式 {s:?}（対応しているのは bfs）"));
                }
            }
            "--max-states" => {
                let v = value()?;
                match v.parse::<usize>() {
                    Ok(n) if n >= 1 => o.max_states = Some(n),
                    _ => return Err(format!("--max-states は1以上の整数です（{v:?}）")),
                }
            }
            "--actions" => o.actions = Some(names(&value()?)),
            "--invariants" => o.invariants = Some(names(&value()?)),
            "--contracts" => o.contracts = Some(names(&value()?)),
            "--certificate-out" => o.certificate_out = Some(value()?),
            "--trace-out" => o.trace_out = Some(value()?),
            _ if arg.starts_with("--") => return Err(format!("未知のオプション {arg}")),
            _ => o.positional.push(arg.to_string()),
        }
        i += 1;
    }
    Ok(o)
}

fn select(
    mask: &mut [bool],
    wanted: &Option<Vec<String>>,
    what: &str,
    find: impl Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let Some(wanted) = wanted else {
        return Ok(());
    };
    mask.fill(false);
    for name in wanted {
        match find(name) {
            Some(i) => mask[i] = true,
            None => return Err(format!("未定義の{what} {name:?}")),
        }
    }
    Ok(())
}

fn conditions(model: &Model, o: &Options) -> Result<Conditions, String> {
    let mut c = default_conditions(model, o.deadlock);
    select(&mut c.actions, &o.actions, "操作", |n| model.names.action_index(n))?;
    select(&mut c.invariants, &o.invariants, "不変条件", |n| {
        model.names.invariant_index(n)
    })?;
    select(&mut c.contracts, &o.contracts, "遷移契約", |n| {
        model.names.contract_index(n)
    })?;
    Ok(c)
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

fn finish(json: bool, code: i32, body: Value, model: Option<&Model>) -> Run {
    let stdout = if json {
        format!("{}\n", serde_json::to_string_pretty(&body).unwrap_or_default())
    } else {
        report::human(&body, model)
    };
    Run {
        code,
        stdout,
        stderr: String::new(),
    }
}

fn load_model(io: &Io, path: &str, json: bool) -> Result<Model, Run> {
    let text = (io.read)(path).map_err(|e| failure(json, "input_error", format!("{path}: {e}")))?;
    load(&text).map_err(|e| match &e {
        LoadError::Invalid { .. } => failure(json, "invalid_model", format!("{path}: {e}")),
        _ => failure(json, "invalid_model", format!("{path}: {e}")),
    })
}

fn write_file(io: &Io, path: &str, body: &Value, json: bool) -> Result<(), Run> {
    let text = format!("{}\n", serde_json::to_string_pretty(body).unwrap_or_default());
    (io.write)(path, &text).map_err(|e| failure(json, "input_error", format!("{path}: {e}")))
}

fn cmd_validate(io: &Io, o: &Options) -> Result<Run, Run> {
    let [path] = o.positional.as_slice() else {
        return Err(failure(
            o.json,
            "usage_error",
            "validate にはモデルのファイルを1つ指定します".to_string(),
        ));
    };
    let model = load_model(io, path, o.json)?;
    let body = json!({
        "status": "valid",
        "model": model.names.model,
        "model_digest": model.digest,
        "states": model.names.states.len(),
        "actions": model.names.actions.len(),
        "invariants": model.names.invariants.len(),
        "contracts": model.names.contracts.len(),
    });
    Ok(finish(o.json, EXIT_OK, body, Some(&model)))
}

fn cmd_check(io: &Io, o: &Options) -> Result<Run, Run> {
    let [path] = o.positional.as_slice() else {
        return Err(failure(
            o.json,
            "usage_error",
            "check にはモデルのファイルを1つ指定します".to_string(),
        ));
    };
    let model = load_model(io, path, o.json)?;
    let cond = conditions(&model, o).map_err(|e| failure(o.json, "usage_error", e))?;
    let opts = BfsOptions {
        max_states: o.max_states,
        ..BfsOptions::default()
    };
    let outcome = check(model.checked(), &cond, &opts);
    let body = report::check_report(&model, &cond, &outcome);
    if let (Some(out), Evidence::Certificate(cert), Status::Verified) =
        (&o.certificate_out, &outcome.evidence, outcome.status)
    {
        write_file(io, out, &certificate_to_json(&model, cert), o.json)?;
    }
    if let (Some(out), Some(trace)) = (&o.trace_out, body.get("trace")) {
        write_file(io, out, trace, o.json)?;
    }
    let code = match outcome.status {
        Status::Verified => EXIT_OK,
        Status::Violated => EXIT_VIOLATED,
        Status::Error | Status::InternalError(_) => EXIT_ERROR,
        Status::Inconclusive(_) => EXIT_INCONCLUSIVE,
    };
    Ok(finish(o.json, code, body, Some(&model)))
}

fn cmd_verify_certificate(io: &Io, o: &Options) -> Result<Run, Run> {
    let [model_path, cert_path] = o.positional.as_slice() else {
        return Err(failure(
            o.json,
            "usage_error",
            "verify-certificate にはモデルと証明書のファイルを指定します".to_string(),
        ));
    };
    let model = load_model(io, model_path, o.json)?;
    let cond = conditions(&model, o).map_err(|e| failure(o.json, "usage_error", e))?;
    let text = (io.read)(cert_path).map_err(|e| failure(o.json, "input_error", format!("{cert_path}: {e}")))?;
    let cert = match certificate_from_json(&model, &text) {
        Ok(cert) => cert,
        Err(e) => {
            let body = report::unreadable_evidence(&model, &e.to_string());
            return Ok(finish(o.json, EXIT_VIOLATED, body, Some(&model)));
        }
    };
    let evidence = Evidence::Certificate(cert);
    let verdict = decide(model.checked(), &cond, &evidence);
    let body = report::evidence_report(&model, &cond, &evidence, &verdict);
    let code = if verdict.kind() == VerdictKind::Verified {
        EXIT_OK
    } else {
        EXIT_VIOLATED
    };
    Ok(finish(o.json, code, body, Some(&model)))
}

fn cmd_replay(io: &Io, o: &Options) -> Result<Run, Run> {
    let [model_path, trace_path] = o.positional.as_slice() else {
        return Err(failure(
            o.json,
            "usage_error",
            "replay にはモデルとトレースのファイルを指定します".to_string(),
        ));
    };
    let model = load_model(io, model_path, o.json)?;
    let text = (io.read)(trace_path).map_err(|e| failure(o.json, "input_error", format!("{trace_path}: {e}")))?;
    let trace = match trace_from_json(&model, &text) {
        Ok(trace) => trace,
        Err(e) => {
            let body = report::unreadable_evidence(&model, &e.to_string());
            return Ok(finish(o.json, EXIT_VIOLATED, body, Some(&model)));
        }
    };
    let cond = trace.conditions.clone();
    let evidence = Evidence::Trace(trace.steps, trace.claim);
    let verdict = decide(model.checked(), &cond, &evidence);
    let body = report::evidence_report(&model, &cond, &evidence, &verdict);
    let code = match verdict.kind() {
        VerdictKind::Error => EXIT_ERROR,
        _ => EXIT_VIOLATED,
    };
    Ok(finish(o.json, code, body, Some(&model)))
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
            stdout: format!("fmspec {}\n", fmspec_ir::ENGINE_VERSION),
            stderr: String::new(),
        };
    }
    let json = rest.iter().any(|a| a == "--json");
    let options = match parse_options(rest) {
        Ok(o) => o,
        Err(e) => return failure(json, "usage_error", e),
    };
    let result = match command.as_str() {
        "validate" => cmd_validate(&io, &options),
        "check" => cmd_check(&io, &options),
        "verify-certificate" => cmd_verify_certificate(&io, &options),
        "replay" => cmd_replay(&io, &options),
        "simulate" | "shrink" => Err(failure(
            json,
            "usage_error",
            format!("{command} はまだ実装していません（ロードマップの段階4、5）"),
        )),
        _ => Err(failure(
            json,
            "usage_error",
            format!("未知のコマンド {command:?}\n{USAGE}"),
        )),
    };
    match result {
        Ok(run) | Err(run) => run,
    }
}
