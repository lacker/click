use std::env;
use std::fs;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use click::lang::click::{
    CProofClaim, expand_c0_claim_source, expand_c0_tactic_source, verifying_source_paths,
};

const USAGE: &str = "usage: click-expand [--time-limit <DURATION>] <sidecar.click> <function> <ensure:N|effect:N|grouped> [tactic:N]";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-expand: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    click_path: String,
    function_name: String,
    claim: String,
    tactic_index: Option<usize>,
    time_limit: Option<Duration>,
}

fn entry() -> Result<(), String> {
    let arguments = parse_arguments(env::args().skip(1))?;
    if let Some(time_limit) = arguments.time_limit {
        run_with_time_limit(&arguments, time_limit)
    } else {
        run(&arguments)
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if argument == "--time-limit" {
            if time_limit.is_some() {
                return Err("`--time-limit` may only be supplied once".to_string());
            }
            let duration = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            time_limit = Some(parse_duration(&duration)?);
        } else if argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else {
            positional.push(argument);
        }
    }
    let (click_path, function_name, claim, tactic_index) = match positional.as_slice() {
        [click_path, function_name, claim] => (click_path, function_name, claim, None),
        [click_path, function_name, claim, tactic] => (
            click_path,
            function_name,
            claim,
            Some(parse_tactic_selector(tactic)?),
        ),
        _ => return Err(USAGE.to_string()),
    };
    Ok(Arguments {
        click_path: click_path.clone(),
        function_name: function_name.clone(),
        claim: claim.clone(),
        tactic_index,
        time_limit,
    })
}

fn parse_duration(source: &str) -> Result<Duration, String> {
    let (digits, multiplier) = if let Some(digits) = source.strip_suffix("ms") {
        (digits, 1_u128)
    } else if let Some(digits) = source.strip_suffix('s') {
        (digits, 1_000)
    } else if let Some(digits) = source.strip_suffix('m') {
        (digits, 60_000)
    } else {
        (source, 1_000)
    };
    let amount = digits
        .parse::<u128>()
        .map_err(|_| format!("invalid time limit `{source}`; use milliseconds, seconds, or minutes (for example `500ms`, `30s`, or `2m`)"))?;
    let milliseconds = amount
        .checked_mul(multiplier)
        .ok_or_else(|| format!("time limit `{source}` is too large"))?;
    if milliseconds == 0 {
        return Err("time limit must be greater than zero".to_string());
    }
    let milliseconds =
        u64::try_from(milliseconds).map_err(|_| format!("time limit `{source}` is too large"))?;
    Ok(Duration::from_millis(milliseconds))
}

fn run_with_time_limit(arguments: &Arguments, time_limit: Duration) -> Result<(), String> {
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-expand executable: {error}"))?;
    let mut command = Command::new(executable);
    command
        .arg(&arguments.click_path)
        .arg(&arguments.function_name)
        .arg(&arguments.claim);
    if let Some(tactic_index) = arguments.tactic_index {
        command.arg(format!("tactic:{tactic_index}"));
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start timed expansion: {error}"))?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "failed to capture timed expansion output".to_string())?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| "failed to capture timed expansion diagnostics".to_string())?;
    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("failed to poll timed expansion: {error}"))?
        {
            break Some(status);
        }
        if start.elapsed() >= time_limit {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        let remaining = time_limit.saturating_sub(start.elapsed());
        thread::sleep(remaining.min(Duration::from_millis(10)));
    };
    let stdout = join_reader(stdout_reader, "output")?;
    let stderr = join_reader(stderr_reader, "diagnostics")?;
    let Some(status) = status else {
        return Err(format!(
            "time limit of {} exceeded",
            format_duration(time_limit)
        ));
    };
    if !status.success() {
        let message = String::from_utf8_lossy(&stderr);
        let message = message
            .trim()
            .strip_prefix("click-expand: ")
            .unwrap_or(message.trim());
        return Err(if message.is_empty() {
            format!("timed expansion exited with {status}")
        } else {
            message.to_string()
        });
    }
    std::io::stdout()
        .write_all(&stdout)
        .map_err(|error| format!("failed to write expanded source: {error}"))?;
    std::io::stderr()
        .write_all(&stderr)
        .map_err(|error| format!("failed to write expansion diagnostics: {error}"))?;
    Ok(())
}

fn read_all(mut reader: impl Read) -> std::io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn join_reader(
    reader: thread::JoinHandle<std::io::Result<Vec<u8>>>,
    description: &str,
) -> Result<Vec<u8>, String> {
    reader
        .join()
        .map_err(|_| format!("timed expansion {description} reader panicked"))?
        .map_err(|error| format!("failed to read timed expansion {description}: {error}"))
}

fn format_duration(duration: Duration) -> String {
    let milliseconds = duration.as_millis();
    if milliseconds % 60_000 == 0 {
        format!("{}m", milliseconds / 60_000)
    } else if milliseconds % 1_000 == 0 {
        format!("{}s", milliseconds / 1_000)
    } else {
        format!("{milliseconds}ms")
    }
}

fn run(arguments: &Arguments) -> Result<(), String> {
    let click_path = PathBuf::from(&arguments.click_path);
    let click_source = fs::read_to_string(&click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let parent = click_path
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."));
    let mut owned_sources = Vec::new();
    for source_path in
        verifying_source_paths(&click_source).map_err(|error| error.message().to_string())?
    {
        let disk_path = parent.join(&source_path);
        let source = fs::read_to_string(&disk_path)
            .map_err(|error| format!("failed to read `{}`: {error}", disk_path.display()))?;
        owned_sources.push((source_path, source));
    }
    let sources = owned_sources
        .iter()
        .map(|(path, source)| (path.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let claim = parse_claim(&arguments.claim)?;
    let expanded = match arguments.tactic_index {
        Some(tactic_index) => expand_c0_tactic_source(
            &click_source,
            &sources,
            &arguments.function_name,
            claim,
            tactic_index,
        ),
        None => expand_c0_claim_source(&click_source, &sources, &arguments.function_name, claim),
    }
    .map_err(|error| error.message().to_string())?;
    print!("{expanded}");
    Ok(())
}

fn parse_tactic_selector(source: &str) -> Result<usize, String> {
    let index = source
        .strip_prefix("tactic:")
        .ok_or_else(|| format!("invalid tactic selector `{source}`; use `tactic:N`"))?;
    index
        .parse::<usize>()
        .map_err(|_| format!("invalid tactic index `{index}`"))
}

fn parse_claim(source: &str) -> Result<CProofClaim, String> {
    if source == "grouped" {
        return Ok(CProofClaim::Grouped);
    }
    let (kind, index) = source
        .split_once(':')
        .ok_or_else(|| "claim must be `ensure:N`, `effect:N`, or `grouped`".to_string())?;
    let index = index
        .parse::<usize>()
        .map_err(|_| format!("invalid claim index `{index}`"))?;
    match kind {
        "ensure" => Ok(CProofClaim::Ensure(index)),
        "effect" => Ok(CProofClaim::Effect(index)),
        _ => Err(format!("unknown claim kind `{kind}`")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_time_limit_units_and_plain_seconds() {
        assert_eq!(parse_duration("250ms"), Ok(Duration::from_millis(250)));
        assert_eq!(parse_duration("30s"), Ok(Duration::from_secs(30)));
        assert_eq!(parse_duration("2m"), Ok(Duration::from_secs(120)));
        assert_eq!(parse_duration("7"), Ok(Duration::from_secs(7)));
        assert!(parse_duration("0").is_err());
        assert!(parse_duration("later").is_err());
    }

    #[test]
    fn parses_time_limit_before_or_after_positionals() {
        let before = parse_arguments(
            [
                "--time-limit",
                "30s",
                "example.click",
                "pipeline",
                "grouped",
            ]
            .map(str::to_string),
        )
        .expect("leading time limit should parse");
        let after = parse_arguments(
            [
                "example.click",
                "pipeline",
                "grouped",
                "--time-limit",
                "30s",
            ]
            .map(str::to_string),
        )
        .expect("trailing time limit should parse");

        assert_eq!(before, after);
        assert_eq!(before.time_limit, Some(Duration::from_secs(30)));
    }

    #[test]
    fn parses_single_tactic_selector() {
        let arguments = parse_arguments(
            [
                "example.click",
                "pipeline",
                "grouped",
                "tactic:7",
                "--time-limit",
                "30s",
            ]
            .map(str::to_string),
        )
        .expect("single tactic selector should parse");

        assert_eq!(arguments.tactic_index, Some(7));
        assert_eq!(arguments.time_limit, Some(Duration::from_secs(30)));
    }
}
