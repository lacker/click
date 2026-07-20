use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use click::lang::click::verify_c0_sources;

const USAGE: &str = "usage: click-profile [--threshold <DURATION>] [--time-limit <DURATION>] <example-project|examples-directory>";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-profile: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    threshold: Duration,
    time_limit: Duration,
    child: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StepKey {
    claim: String,
    tactic_index: usize,
    tactic_name: String,
    statement_index: usize,
}

#[derive(Clone, Debug)]
struct SlowStep {
    project: String,
    key: StepKey,
    elapsed: Duration,
}

#[derive(Clone, Debug)]
struct ProjectProfile {
    project: String,
    slow_steps: Vec<SlowStep>,
    active: Vec<StepKey>,
    timed_out: bool,
}

fn entry() -> Result<(), String> {
    let arguments = parse_arguments(env::args().skip(1))?;
    if arguments.child {
        return verify_project(&arguments.path);
    }

    let projects = find_projects(&arguments.path)?;
    let mut profiles = Vec::new();
    for project in projects {
        profiles.push(profile_project(
            &project,
            arguments.threshold,
            arguments.time_limit,
        )?);
    }
    print_profiles(&profiles, arguments.threshold, arguments.time_limit);
    Ok(())
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut threshold = Duration::from_secs(1);
    let mut time_limit = Duration::from_secs(60);
    let mut child = false;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--threshold" => {
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing duration after `--threshold`\n{USAGE}"))?;
                threshold = parse_duration(&source)?;
            }
            "--time-limit" => {
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
                time_limit = parse_duration(&source)?;
            }
            "--child" => child = true,
            _ if argument.starts_with('-') => {
                return Err(format!("unknown option `{argument}`\n{USAGE}"));
            }
            _ if path.is_none() => path = Some(PathBuf::from(argument)),
            _ => return Err(USAGE.to_string()),
        }
    }
    Ok(Arguments {
        path: path.ok_or_else(|| USAGE.to_string())?,
        threshold,
        time_limit,
        child,
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
    let amount = digits.parse::<u128>().map_err(|_| {
        format!(
            "invalid duration `{source}`; use milliseconds, seconds, or minutes (for example `500ms`, `30s`, or `2m`)"
        )
    })?;
    let milliseconds = amount
        .checked_mul(multiplier)
        .ok_or_else(|| format!("duration `{source}` is too large"))?;
    if milliseconds == 0 {
        return Err("duration must be greater than zero".to_string());
    }
    Ok(Duration::from_millis(u64::try_from(milliseconds).map_err(
        |_| format!("duration `{source}` is too large"),
    )?))
}

fn find_projects(path: &Path) -> Result<Vec<PathBuf>, String> {
    if !path.is_dir() {
        return Err(format!("`{}` is not a directory", path.display()));
    }
    if contains_click_file(path)? {
        return Ok(vec![path.to_path_buf()]);
    }
    let mut projects = fs::read_dir(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|candidate| candidate.is_dir())
        .filter_map(|candidate| match contains_click_file(&candidate) {
            Ok(true) => Some(Ok(candidate)),
            Ok(false) => None,
            Err(error) => Some(Err(error)),
        })
        .collect::<Result<Vec<_>, _>>()?;
    projects.sort();
    if projects.is_empty() {
        return Err(format!(
            "`{}` contains no example projects with Click sidecars",
            path.display()
        ));
    }
    Ok(projects)
}

fn contains_click_file(path: &Path) -> Result<bool, String> {
    Ok(fs::read_dir(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?
        .filter_map(Result::ok)
        .any(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "click")
        }))
}

fn profile_project(
    project: &Path,
    threshold: Duration,
    time_limit: Duration,
) -> Result<ProjectProfile, String> {
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-profile executable: {error}"))?;
    let mut child = Command::new(executable)
        .arg("--child")
        .arg(project)
        .env("CLICK_TIMINGS", "1")
        .env("CLICK_TIMING_STARTS", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| {
            format!(
                "failed to start profiler for `{}`: {error}",
                project.display()
            )
        })?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| "failed to capture profiler output".to_string())?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| "failed to capture profiler diagnostics".to_string())?;
    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("failed to poll profiler child: {error}"))?
        {
            break Some(status);
        }
        if start.elapsed() >= time_limit {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        thread::sleep(
            time_limit
                .saturating_sub(start.elapsed())
                .min(Duration::from_millis(10)),
        );
    };
    let stdout = join_reader(stdout_reader, "output")?;
    let stderr = join_reader(stderr_reader, "diagnostics")?;
    if status.is_some_and(|status| !status.success()) {
        let stdout = String::from_utf8_lossy(&stdout);
        let stderr = String::from_utf8_lossy(&stderr);
        return Err(format!(
            "verification failed for `{}`\n{}{}",
            project.display(),
            stdout,
            stderr
        ));
    }

    let project_name = project
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| project.as_os_str().to_str().unwrap_or("example"))
        .to_string();
    Ok(parse_profile(
        &project_name,
        &String::from_utf8_lossy(&stderr),
        threshold,
        status.is_none(),
    ))
}

fn parse_profile(
    project: &str,
    output: &str,
    threshold: Duration,
    timed_out: bool,
) -> ProjectProfile {
    let mut slow_steps = Vec::new();
    let mut active = Vec::new();
    for line in output.lines() {
        if let Some(key) = parse_started_step(line) {
            active.push(key);
        } else if let Some((key, elapsed)) = parse_finished_step(line) {
            if let Some(index) = active.iter().rposition(|candidate| candidate == &key) {
                active.remove(index);
            }
            if elapsed >= threshold {
                slow_steps.push(SlowStep {
                    project: project.to_string(),
                    key,
                    elapsed,
                });
            }
        }
    }
    ProjectProfile {
        project: project.to_string(),
        slow_steps,
        active,
        timed_out,
    }
}

fn parse_started_step(line: &str) -> Option<StepKey> {
    let fields = line.split_whitespace().collect::<Vec<_>>();
    if fields.len() != 9 || fields[..4] != ["click", "timing:", "started", "tactic"] {
        return None;
    }
    parse_step_key(&fields[4..])
}

fn parse_finished_step(line: &str) -> Option<(StepKey, Duration)> {
    let fields = line.split_whitespace().collect::<Vec<_>>();
    if fields.len() != 9 || fields[..3] != ["click", "timing:", "tactic"] {
        return None;
    }
    let elapsed = fields[8].strip_suffix('s')?.parse::<f64>().ok()?;
    Some((
        parse_step_key(&fields[3..8])?,
        Duration::from_secs_f64(elapsed),
    ))
}

fn parse_step_key(fields: &[&str]) -> Option<StepKey> {
    if fields.len() != 5 || fields[3] != "statement" {
        return None;
    }
    Some(StepKey {
        claim: fields[0].to_string(),
        tactic_index: fields[1].parse().ok()?,
        tactic_name: fields[2].to_string(),
        statement_index: fields[4].parse().ok()?,
    })
}

fn print_profiles(profiles: &[ProjectProfile], threshold: Duration, time_limit: Duration) {
    let mut slow_steps = profiles
        .iter()
        .flat_map(|profile| profile.slow_steps.iter())
        .collect::<Vec<_>>();
    slow_steps.sort_by(|left, right| right.elapsed.cmp(&left.elapsed));
    println!(
        "slow proof steps (at least {}):",
        format_duration(threshold)
    );
    if slow_steps.is_empty() {
        println!("  none completed");
    }
    for step in slow_steps {
        println!(
            "  {:>10}  {}  {}  tactic {} {}  statement {}",
            format_duration(step.elapsed),
            step.project,
            step.key.claim,
            step.key.tactic_index,
            step.key.tactic_name,
            step.key.statement_index,
        );
    }
    for profile in profiles.iter().filter(|profile| profile.timed_out) {
        println!(
            "  timed out: {} after {}",
            profile.project,
            format_duration(time_limit)
        );
        for key in &profile.active {
            println!(
                "    active: {} tactic {} {} statement {}",
                key.claim, key.tactic_index, key.tactic_name, key.statement_index
            );
        }
    }
}

fn verify_project(project: &Path) -> Result<(), String> {
    let mut c_paths = files_with_extension(project, "c")?;
    let mut click_paths = files_with_extension(project, "click")?;
    c_paths.sort();
    click_paths.sort();
    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` has no Click sidecar",
            project.display()
        ));
    }
    let c_sources = c_paths
        .iter()
        .map(|path| {
            let filename = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| format!("invalid UTF-8 path `{}`", path.display()))?
                .to_string();
            let source = fs::read_to_string(path)
                .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
            Ok((filename, source))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let source_refs = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        verify_c0_sources(&click_source, &source_refs).map_err(|error| {
            format!(
                "example sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        })?;
    }
    Ok(())
}

fn files_with_extension(directory: &Path, extension: &str) -> Result<Vec<PathBuf>, String> {
    Ok(fs::read_dir(directory)
        .map_err(|error| format!("failed to read `{}`: {error}", directory.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|actual| actual == extension))
        .collect())
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
        .map_err(|_| format!("profiler {description} reader panicked"))?
        .map_err(|error| format!("failed to read profiler {description}: {error}"))
}

fn format_duration(duration: Duration) -> String {
    let milliseconds = duration.as_secs_f64() * 1_000.0;
    if milliseconds >= 1_000.0 {
        format!("{:.3}s", milliseconds / 1_000.0)
    } else {
        format!("{milliseconds:.0}ms")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_timing_events_and_keeps_the_active_stack() {
        let output = r#"
click timing: started tactic example.contract 2 execute_step statement 4
click timing: started tactic example.contract 2 certified_statement_step statement 4
click timing: tactic example.contract 2 certified_statement_step statement 4 1.250000s
"#;
        let profile = parse_profile("sample", output, Duration::from_secs(1), true);
        assert_eq!(profile.slow_steps.len(), 1);
        assert_eq!(
            profile.slow_steps[0].key.tactic_name,
            "certified_statement_step"
        );
        assert_eq!(profile.active.len(), 1);
        assert_eq!(profile.active[0].tactic_name, "execute_step");
    }

    #[test]
    fn parses_profile_arguments() {
        assert_eq!(
            parse_arguments([
                "--threshold".to_string(),
                "250ms".to_string(),
                "--time-limit".to_string(),
                "2m".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                path: PathBuf::from("examples"),
                threshold: Duration::from_millis(250),
                time_limit: Duration::from_secs(120),
                child: false,
            })
        );
    }
}
