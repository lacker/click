use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use click::lang::click::{SourcePosition, c0_tactic_source_position, verify_c0_sources};

const DEFAULT_SMART_THRESHOLD: Duration = Duration::from_secs(2);
const DEFAULT_SIMPLE_THRESHOLD: Duration = Duration::from_millis(500);
const DEFAULT_CONTROL_THRESHOLD: Duration = Duration::from_secs(2);
const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(30);
const EXPANSION_TIME_LIMIT: Duration = Duration::from_secs(60);

const USAGE: &str = "\
usage: click-profile [OPTIONS] <example-project|examples-directory>

defaults:
  --smart-threshold 2s      smart tactics are expansion candidates
  --simple-threshold 500ms  slow simple tactics are verifier bugs; do not expand them
  --control-threshold 2s    inspect slow control-flow containers and their nested steps
  --time-limit 30s          wall-clock limit per project

options:
  --smart-threshold <DURATION>
  --simple-threshold <DURATION>
  --control-threshold <DURATION>
  --threshold <DURATION>    shorthand setting all three thresholds
  --time-limit <DURATION>";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-profile: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    thresholds: Thresholds,
    time_limit: Duration,
    child: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Thresholds {
    smart: Duration,
    simple: Duration,
    control: Duration,
}

impl Default for Thresholds {
    fn default() -> Self {
        Self {
            smart: DEFAULT_SMART_THRESHOLD,
            simple: DEFAULT_SIMPLE_THRESHOLD,
            control: DEFAULT_CONTROL_THRESHOLD,
        }
    }
}

impl Thresholds {
    fn for_category(self, category: TacticCategory) -> Duration {
        match category {
            TacticCategory::Smart => self.smart,
            TacticCategory::Simple => self.simple,
            TacticCategory::Control => self.control,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum TacticCategory {
    Smart,
    Simple,
    Control,
}

impl TacticCategory {
    fn parse(source: &str) -> Option<Self> {
        match source {
            "smart" => Some(Self::Smart),
            "simple" => Some(Self::Simple),
            "control" => Some(Self::Control),
            _ => None,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Smart => "SMART",
            Self::Simple => "SIMPLE",
            Self::Control => "CONTROL",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StepKey {
    source_path: PathBuf,
    claim: String,
    tactic_index: usize,
    source_index: usize,
    tactic_name: String,
    category: TacticCategory,
    statement_index: usize,
    position: Option<SourcePosition>,
}

#[derive(Clone, Debug)]
struct SlowStep {
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
    let raw_arguments = env::args().skip(1).collect::<Vec<_>>();
    if matches!(raw_arguments.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw_arguments)?;
    if arguments.child {
        return verify_project(&arguments.path);
    }

    let projects = find_projects(&arguments.path)?;
    let mut profiles = Vec::new();
    for project in projects {
        profiles.push(profile_project(
            &project,
            arguments.thresholds,
            arguments.time_limit,
        )?);
    }
    print_profiles(&profiles, arguments.thresholds, arguments.time_limit);
    Ok(())
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut thresholds = Thresholds::default();
    let mut common_threshold = None;
    let mut class_threshold_supplied = false;
    let mut time_limit = DEFAULT_TIME_LIMIT;
    let mut child = false;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--threshold" => {
                if common_threshold.is_some() {
                    return Err("`--threshold` may only be supplied once".to_string());
                }
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing duration after `--threshold`\n{USAGE}"))?;
                common_threshold = Some(parse_duration(&source)?);
            }
            "--smart-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--smart-threshold`\n{USAGE}")
                })?;
                thresholds.smart = parse_duration(&source)?;
                class_threshold_supplied = true;
            }
            "--simple-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--simple-threshold`\n{USAGE}")
                })?;
                thresholds.simple = parse_duration(&source)?;
                class_threshold_supplied = true;
            }
            "--control-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--control-threshold`\n{USAGE}")
                })?;
                thresholds.control = parse_duration(&source)?;
                class_threshold_supplied = true;
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
    if common_threshold.is_some() && class_threshold_supplied {
        return Err("`--threshold` cannot be combined with class-specific thresholds".to_string());
    }
    if let Some(threshold) = common_threshold {
        thresholds = Thresholds {
            smart: threshold,
            simple: threshold,
            control: threshold,
        };
    }
    Ok(Arguments {
        path: path.ok_or_else(|| USAGE.to_string())?,
        thresholds,
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
    thresholds: Thresholds,
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
    let mut profile = parse_profile(
        &project_name,
        &String::from_utf8_lossy(&stderr),
        thresholds,
        status.is_none(),
    );
    resolve_source_positions(&mut profile)?;
    Ok(profile)
}

fn parse_profile(
    project: &str,
    output: &str,
    thresholds: Thresholds,
    timed_out: bool,
) -> ProjectProfile {
    let mut slow_steps = Vec::new();
    let mut active = Vec::new();
    let mut source_path = PathBuf::new();
    for line in output.lines() {
        if let Some(path) = line.strip_prefix("click timing: source ") {
            source_path = PathBuf::from(path);
        } else if let Some(key) = parse_started_step(line, &source_path) {
            active.push(key);
        } else if let Some((key, elapsed)) = parse_finished_step(line, &source_path) {
            if let Some(index) = active.iter().rposition(|candidate| candidate == &key) {
                active.remove(index);
            }
            if elapsed >= thresholds.for_category(key.category) {
                slow_steps.push(SlowStep { key, elapsed });
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

fn parse_started_step(line: &str, source_path: &Path) -> Option<StepKey> {
    let fields = line.split_whitespace().collect::<Vec<_>>();
    if fields.len() != 13 || fields[..4] != ["click", "timing:", "started", "tactic"] {
        return None;
    }
    parse_step_key(&fields[4..], source_path)
}

fn parse_finished_step(line: &str, source_path: &Path) -> Option<(StepKey, Duration)> {
    let fields = line.split_whitespace().collect::<Vec<_>>();
    if fields.len() != 13 || fields[..3] != ["click", "timing:", "tactic"] {
        return None;
    }
    let elapsed = fields[12].strip_suffix('s')?.parse::<f64>().ok()?;
    Some((
        parse_step_key(&fields[3..12], source_path)?,
        Duration::from_secs_f64(elapsed),
    ))
}

fn parse_step_key(fields: &[&str], source_path: &Path) -> Option<StepKey> {
    if fields.len() != 9
        || fields[3] != "class"
        || fields[5] != "statement"
        || fields[7] != "source"
    {
        return None;
    }
    Some(StepKey {
        source_path: source_path.to_path_buf(),
        claim: fields[0].to_string(),
        tactic_index: fields[1].parse().ok()?,
        tactic_name: fields[2].to_string(),
        category: TacticCategory::parse(fields[4])?,
        statement_index: fields[6].parse().ok()?,
        source_index: fields[8].parse().ok()?,
        position: None,
    })
}

fn resolve_source_positions(profile: &mut ProjectProfile) -> Result<(), String> {
    for key in profile
        .slow_steps
        .iter_mut()
        .map(|step| &mut step.key)
        .chain(profile.active.iter_mut())
    {
        if key.source_path.as_os_str().is_empty() {
            return Err("timing event had no Click source path".to_string());
        }
        let source = fs::read_to_string(&key.source_path)
            .map_err(|error| format!("failed to read `{}`: {error}", key.source_path.display()))?;
        let parent = key.source_path.parent().unwrap_or_else(|| Path::new("."));
        let c_sources = files_with_extension(parent, "c")?
            .into_iter()
            .map(|path| {
                let name = path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .ok_or_else(|| format!("invalid UTF-8 path `{}`", path.display()))?
                    .to_string();
                let source = fs::read_to_string(&path)
                    .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
                Ok((name, source))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let source_refs = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        key.position = Some(
            c0_tactic_source_position(&source, &source_refs, &key.claim, key.source_index)
                .map_err(|error| error.message().to_string())?,
        );
    }
    Ok(())
}

fn print_profiles(profiles: &[ProjectProfile], thresholds: Thresholds, time_limit: Duration) {
    print!("{}", render_profiles(profiles, thresholds, time_limit));
}

fn render_profiles(
    profiles: &[ProjectProfile],
    thresholds: Thresholds,
    time_limit: Duration,
) -> String {
    let mut slow_steps = profiles
        .iter()
        .flat_map(|profile| profile.slow_steps.iter())
        .collect::<Vec<_>>();
    slow_steps.sort_by(|left, right| right.elapsed.cmp(&left.elapsed));

    let mut output = String::new();
    writeln!(
        output,
        "Click proof profile (smart >= {}, simple >= {}, control >= {}; project limit {})",
        format_duration(thresholds.smart),
        format_duration(thresholds.simple),
        format_duration(thresholds.control),
        format_duration(time_limit),
    )
    .expect("writing a String cannot fail");
    writeln!(
        output,
        "Classification is emitted by the verifier; do not infer it from a tactic's name."
    )
    .expect("writing a String cannot fail");

    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Simple,
        "SIMPLE — FIX THE ENGINE; DO NOT EXPAND",
        "A slow simple tactic is deterministic certificate replay. Reduce its verifier path and fix that bottleneck before expanding more smart tactics.",
    );
    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Smart,
        "SMART — EXPAND TO TRADE PROOF SIZE FOR SPEED",
        "Expand one location, apply the verified rewritten sidecar, then profile again.",
    );
    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Control,
        "CONTROL — INSPECT NESTED STEPS",
        "This is a proof container. Use its nested SMART/SIMPLE timings; do not optimize or expand it based on the container row alone.",
    );

    let timed_out = profiles
        .iter()
        .filter(|profile| profile.timed_out)
        .collect::<Vec<_>>();
    if !timed_out.is_empty() {
        writeln!(output, "\nTIMEOUTS").expect("writing a String cannot fail");
    }
    for profile in timed_out {
        writeln!(
            output,
            "  timed out: {} after {}",
            profile.project,
            format_duration(time_limit)
        )
        .expect("writing a String cannot fail");
        for key in &profile.active {
            let position = key
                .position
                .expect("active steps have resolved source positions");
            writeln!(
                output,
                "    [{}] {}:{}:{}  {}  {}  statement {}",
                key.category.label(),
                key.source_path.display(),
                position.line,
                position.column,
                key.claim,
                key.tactic_name,
                key.statement_index
            )
            .expect("writing a String cannot fail");
            if key.category == TacticCategory::Smart {
                render_expansion_command(&mut output, key, position);
            }
        }
    }

    let has_simple_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Simple)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Simple)
        });
    let has_smart_candidate = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Smart)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Smart)
        });
    let has_control_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Control)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Control)
        });
    if has_simple_problem {
        writeln!(
            output,
            "\nNEXT: fix or reduce the SIMPLE bottleneck first. Expanding surrounding SMART tactics can only move or expose this deterministic cost."
        )
        .expect("writing a String cannot fail");
    } else if has_smart_candidate {
        writeln!(
            output,
            "\nNEXT: expand one SMART location, apply its verified output, and rerun this profile."
        )
        .expect("writing a String cannot fail");
    } else if has_control_problem {
        writeln!(
            output,
            "\nNEXT: inspect the nested timings inside the CONTROL container; act on a nested SIMPLE or SMART step, not on the container row."
        )
        .expect("writing a String cannot fail");
    } else {
        writeln!(
            output,
            "\nNEXT: no completed smart expansion candidates or simple engine bottlenecks crossed the configured thresholds."
        )
        .expect("writing a String cannot fail");
    }

    output
}

fn render_category(
    output: &mut String,
    slow_steps: &[&SlowStep],
    category: TacticCategory,
    title: &str,
    advice: &str,
) {
    writeln!(output, "\n{title}").expect("writing a String cannot fail");
    writeln!(output, "  {advice}").expect("writing a String cannot fail");
    let matching = slow_steps
        .iter()
        .copied()
        .filter(|step| step.key.category == category)
        .collect::<Vec<_>>();
    if matching.is_empty() {
        writeln!(output, "  none completed").expect("writing a String cannot fail");
        return;
    }
    if category == TacticCategory::Simple {
        writeln!(
            output,
            "  WARNING: expanding an enclosing smart tactic is not a fix for the simple steps below."
        )
        .expect("writing a String cannot fail");
    }
    for step in matching {
        let position = step
            .key
            .position
            .expect("profiled steps have resolved source positions");
        writeln!(
            output,
            "  {:>10}  {}:{}:{}  {}  {}  statement {}",
            format_duration(step.elapsed),
            step.key.source_path.display(),
            position.line,
            position.column,
            step.key.claim,
            step.key.tactic_name,
            step.key.statement_index,
        )
        .expect("writing a String cannot fail");
        if category == TacticCategory::Smart {
            render_expansion_command(output, &step.key, position);
        }
    }
}

fn render_expansion_command(output: &mut String, key: &StepKey, position: SourcePosition) {
    writeln!(
        output,
        "              expand: cargo run --quiet --bin click-expand -- --time-limit {} {}:{}:{}",
        format_cli_duration(EXPANSION_TIME_LIMIT),
        key.source_path.display(),
        position.line,
        position.column,
    )
    .expect("writing a String cannot fail");
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
        if env::var_os("CLICK_TIMINGS").is_some() {
            eprintln!("click timing: source {}", click_path.display());
        }
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

fn format_cli_duration(duration: Duration) -> String {
    if duration.subsec_millis() == 0 {
        format!("{}s", duration.as_secs())
    } else {
        format!("{}ms", duration.as_millis())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_timing_events_and_keeps_the_active_stack() {
        let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 2 execute_step class smart statement 4 source 5
click timing: started tactic example.contract 2 certified_statement_step class simple statement 4 source 5
click timing: tactic example.contract 2 certified_statement_step class simple statement 4 source 5 1.250000s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), true);
        assert_eq!(profile.slow_steps.len(), 1);
        assert_eq!(
            profile.slow_steps[0].key.tactic_name,
            "certified_statement_step"
        );
        assert_eq!(profile.slow_steps[0].key.category, TacticCategory::Simple);
        assert_eq!(profile.active.len(), 1);
        assert_eq!(profile.active[0].tactic_name, "execute_step");
        assert_eq!(profile.active[0].category, TacticCategory::Smart);
    }

    #[test]
    fn parses_profile_arguments() {
        assert_eq!(
            parse_arguments([
                "--simple-threshold".to_string(),
                "250ms".to_string(),
                "--smart-threshold".to_string(),
                "3s".to_string(),
                "--time-limit".to_string(),
                "2m".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                path: PathBuf::from("examples"),
                thresholds: Thresholds {
                    smart: Duration::from_secs(3),
                    simple: Duration::from_millis(250),
                    control: DEFAULT_CONTROL_THRESHOLD,
                },
                time_limit: Duration::from_secs(120),
                child: false,
            })
        );
    }

    #[test]
    fn common_threshold_sets_every_tactic_class() {
        let arguments = parse_arguments([
            "--threshold".to_string(),
            "750ms".to_string(),
            "examples".to_string(),
        ])
        .expect("common threshold should parse");

        assert_eq!(
            arguments.thresholds,
            Thresholds {
                smart: Duration::from_millis(750),
                simple: Duration::from_millis(750),
                control: Duration::from_millis(750),
            }
        );
        assert_eq!(arguments.time_limit, DEFAULT_TIME_LIMIT);
    }

    #[test]
    fn report_separates_actions_and_only_suggests_expanding_smart_tactics() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 certified_statement_step class simple statement 1 source 10 0.750000s
click timing: tactic example.contract 1 execute_step class smart statement 2 source 20 2.500000s
click timing: tactic example.contract 2 have class control statement 3 source 30 2.100000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false);
        for (index, step) in profile.slow_steps.iter_mut().enumerate() {
            step.key.position = Some(SourcePosition {
                line: index + 10,
                column: 5,
            });
        }

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("SIMPLE — FIX THE ENGINE; DO NOT EXPAND"));
        assert!(report.contains("WARNING: expanding an enclosing smart tactic is not a fix"));
        assert!(report.contains("SMART — EXPAND TO TRADE PROOF SIZE FOR SPEED"));
        assert!(report.contains("CONTROL — INSPECT NESTED STEPS"));
        assert!(report.contains("NEXT: fix or reduce the SIMPLE bottleneck first"));
        assert_eq!(report.matches("expand: cargo run").count(), 1);
        assert!(report.contains("--time-limit 60s"));
    }

    #[test]
    fn control_only_report_directs_attention_to_nested_steps() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 have class control statement 1 source 10 2.500000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false);
        profile.slow_steps[0].key.position = Some(SourcePosition {
            line: 10,
            column: 5,
        });

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("NEXT: inspect the nested timings inside the CONTROL container"));
        assert!(!report.contains("expand: cargo run"));
    }
}
