use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let run = fmspec_cli::run(&args, &|path| std::fs::read_to_string(path), &|path, text| {
        std::fs::write(path, text)
    });
    if !run.stdout.is_empty() {
        let _ = std::io::stdout().write_all(run.stdout.as_bytes());
    }
    if !run.stderr.is_empty() {
        let _ = std::io::stderr().write_all(run.stderr.as_bytes());
    }
    std::process::exit(run.code);
}
