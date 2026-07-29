use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use click::cli::{
    BoundedOutput, files_with_extension, find_projects, format_duration,
    format_fractional_duration, parse_duration, run_bounded,
};
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
    verification_failure: Option<String>,
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
    let failed = profiles
        .iter()
        .filter(|profile| profile.verification_failure.is_some())
        .count();
    if failed == 0 {
        Ok(())
    } else {
        Err(format!(
            "{failed} project(s) failed verification; partial profile printed above"
        ))
    }
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

fn profile_project(
    project: &Path,
    thresholds: Thresholds,
    time_limit: Duration,
) -> Result<ProjectProfile, String> {
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-profile executable: {error}"))?;
    let mut command = Command::new(executable);
    command
        .arg("--child")
        .arg(project)
        .env("CLICK_TIMINGS", "1")
        .env("CLICK_TIMING_STARTS", "1");
    let label = format!("profiler for `{}`", project.display());
    let (status, stdout, stderr) = match run_bounded(command, time_limit, &label)? {
        BoundedOutput::Completed(output) => (Some(output.status), output.stdout, output.stderr),
        BoundedOutput::TimedOut { stdout, stderr, .. } => (None, stdout, stderr),
    };
    let project_name = project
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| project.as_os_str().to_str().unwrap_or("example"))
        .to_string();
    let stderr = String::from_utf8_lossy(&stderr);
    let mut profile = parse_profile(&project_name, &stderr, thresholds, status.is_none());
    if status.is_some_and(|status| !status.success()) {
        profile.verification_failure = Some(extract_verification_failure(
            &String::from_utf8_lossy(&stdout),
            &stderr,
            status.expect("failed status should be present"),
        ));
    }
    resolve_source_positions(&mut profile)?;
    Ok(profile)
}

fn extract_verification_failure(
    stdout: &str,
    stderr: &str,
    status: std::process::ExitStatus,
) -> String {
    let diagnostics = stderr
        .lines()
        .filter(|line| !line.starts_with("click timing:"))
        .collect::<Vec<_>>()
        .join("\n");
    let diagnostics = diagnostics
        .trim()
        .strip_prefix("click-profile: ")
        .unwrap_or(diagnostics.trim());
    if !diagnostics.is_empty() {
        diagnostics.to_string()
    } else if !stdout.trim().is_empty() {
        stdout.trim().to_string()
    } else {
        format!("profiler child exited with {status}")
    }
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
        verification_failure: None,
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
        format_fractional_duration(thresholds.smart),
        format_fractional_duration(thresholds.simple),
        format_fractional_duration(thresholds.control),
        format_fractional_duration(time_limit),
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
        "Expand one location, apply the rewritten sidecar, then verify by profiling again.",
    );
    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Control,
        "CONTROL — INSPECT NESTED STEPS",
        "This is a proof container. Use its nested SMART/SIMPLE timings; do not optimize or expand it based on the container row alone.",
    );

    let failed = profiles
        .iter()
        .filter_map(|profile| {
            profile
                .verification_failure
                .as_deref()
                .map(|failure| (profile, failure))
        })
        .collect::<Vec<_>>();
    if !failed.is_empty() {
        writeln!(output, "\nVERIFICATION FAILURES").expect("writing a String cannot fail");
    }
    for (profile, failure) in failed {
        writeln!(output, "  {}:", profile.project).expect("writing a String cannot fail");
        for line in failure.lines() {
            writeln!(output, "    {line}").expect("writing a String cannot fail");
        }
    }

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
            format_fractional_duration(time_limit)
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
    let has_verification_failure = profiles
        .iter()
        .any(|profile| profile.verification_failure.is_some());
    if has_verification_failure {
        writeln!(
            output,
            "\nNEXT: fix the verification failure first. Timings from other projects are preserved, but the failed project profile is incomplete."
        )
        .expect("writing a String cannot fail");
    } else if has_simple_problem {
        writeln!(
            output,
            "\nNEXT: fix or reduce the SIMPLE bottleneck first. Expanding surrounding SMART tactics can only move or expose this deterministic cost."
        )
        .expect("writing a String cannot fail");
    } else if has_smart_candidate {
        writeln!(
            output,
            "\nNEXT: expand one SMART location, apply its output, and rerun this profile to verify the rewrite."
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
            format_fractional_duration(step.elapsed),
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
        format_duration(EXPANSION_TIME_LIMIT),
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
        assert!(report.contains("--time-limit 1m"));
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

    #[test]
    fn report_preserves_timings_when_another_project_fails_verification() {
        let mut successful = parse_profile(
            "successful",
            r#"
click timing: source examples/successful.click
click timing: tactic example.contract 0 execute_step class smart statement 1 source 10 2.500000s
"#,
            Thresholds::default(),
            false,
        );
        successful.slow_steps[0].key.position = Some(SourcePosition {
            line: 12,
            column: 5,
        });
        let mut failed = parse_profile(
            "failed",
            "click timing: source examples/failed.click",
            Thresholds::default(),
            false,
        );
        failed.verification_failure =
            Some("example sidecar failed: certificate did not replay".to_string());

        let report = render_profiles(
            &[failed, successful],
            Thresholds::default(),
            DEFAULT_TIME_LIMIT,
        );

        assert!(report.contains("VERIFICATION FAILURES"));
        assert!(report.contains("certificate did not replay"));
        assert!(report.contains("examples/successful.click:12:5"));
        assert!(report.contains("fix the verification failure first"));
    }

    #[test]
    fn failure_diagnostic_omits_timing_stream() {
        let status = std::process::Command::new("sh")
            .arg("-c")
            .arg("exit 1")
            .status()
            .expect("test shell should run");
        let diagnostic = extract_verification_failure(
            "",
            "click timing: source example.click\nclick-profile: proof failed",
            status,
        );

        assert_eq!(diagnostic, "proof failed");
    }
}
