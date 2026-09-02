use std::env;
use std::fs;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::Duration;

use click::cli::{
    DEFAULT_VERIFY_TIME_LIMIT, files_with_extension, find_projects, format_duration,
    looks_like_source_location, parse_duration, parse_source_location, read_verifying_sources,
    source_refs,
};
use click::surface::{
    c0_function_names, c0_incremental_selection, verify_c0_sources, verify_c0_sources_at,
    verify_c0_sources_functions, verifying_source_paths,
};

const USAGE: &str = "\
usage: click verify [--time-limit <DURATION>] <sidecar.click>[:<line>:<column>]
       click verify [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>

Verifies the whole sidecar, or, when a one-based :LINE:COLUMN suffix is
supplied, only the proof unit containing that source location and the C
functions it calls.

Given a directory, verifies every sidecar in it: either the project directory
itself when it holds sidecars, or each immediate subdirectory that does. This
is the command to run after applying an expansion emitted by `click expand`.
Each sidecar has a 30-second limit by default.";

const INCREMENTAL_CACHE_SCHEMA: &str = "click-verified-v1";
type LoadedSidecar = (String, Vec<(String, String)>);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    target: String,
    time_limit: Duration,
    changed_since: Option<String>,
    explain: bool,
}

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-verify: {message}");
        std::process::exit(1);
    }
}

fn entry() -> Result<(), String> {
    entry_with(env::args().skip(1))
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let raw = arguments.into_iter().collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    if let Some(revision) = &arguments.changed_since {
        let path = Path::new(&arguments.target);
        return verify_changed(path, revision, arguments.time_limit, arguments.explain);
    }
    if arguments.explain {
        return Err("`--explain` requires `--changed-since`".to_string());
    }
    if looks_like_source_location(&arguments.target) {
        let (click_path, line, column) = parse_source_location(&arguments.target)?;
        return verify_location(&click_path, line, column, arguments.time_limit);
    }
    let path = Path::new(&arguments.target);
    if path.is_dir() {
        verify_directory(path, arguments.time_limit)
    } else {
        verify_file(path, arguments.time_limit)
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut target = None;
    let mut time_limit = DEFAULT_VERIFY_TIME_LIMIT;
    let mut changed_since = None;
    let mut explain = false;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if parse_options && argument == "--time-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            time_limit = parse_duration(&value)?;
        } else if parse_options && argument == "--changed-since" {
            if changed_since.is_some() {
                return Err("`--changed-since` may only be supplied once".to_string());
            }
            changed_since = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing revision after `--changed-since`\n{USAGE}"))?,
            );
        } else if parse_options && argument == "--explain" {
            explain = true;
        } else if parse_options && argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else if target.replace(argument).is_some() {
            return Err(USAGE.to_string());
        }
    }
    Ok(Arguments {
        target: target.ok_or_else(|| USAGE.to_string())?,
        time_limit,
        changed_since,
        explain,
    })
}

/// Verifies every sidecar under a project or examples directory, reporting
/// each one as it passes so a long run shows progress.
fn verify_directory(path: &Path, time_limit: Duration) -> Result<(), String> {
    let projects = find_projects(path)?;
    let mut sidecars = Vec::new();
    for project in &projects {
        let mut project_sidecars = files_with_extension(project, "click")?;
        project_sidecars.sort();
        sidecars.append(&mut project_sidecars);
    }
    if sidecars.is_empty() {
        return Err(format!(
            "`{}` contains no Click sidecars to verify",
            path.display()
        ));
    }
    for sidecar in &sidecars {
        verify_file(sidecar, time_limit)?;
        println!("verified {}", display_path(sidecar, path));
    }
    println!(
        "verified {} sidecar{} in {} project{}",
        sidecars.len(),
        plural(sidecars.len()),
        projects.len(),
        plural(projects.len())
    );
    Ok(())
}

fn verify_changed(
    path: &Path,
    revision: &str,
    time_limit: Duration,
    explain_only: bool,
) -> Result<(), String> {
    let sidecars = if path.is_dir() {
        let projects = find_projects(path)?;
        let mut sidecars = Vec::new();
        for project in projects {
            sidecars.extend(files_with_extension(&project, "click")?);
        }
        sidecars.sort();
        sidecars
    } else {
        vec![path.to_path_buf()]
    };
    if sidecars.is_empty() {
        return Err(format!("`{}` contains no Click sidecars", path.display()));
    }
    let repo = git_repo_root(path)?;
    let baseline_commit = git_commit_id(&repo, revision)?;

    let mut verified = 0usize;
    let mut skipped = 0usize;
    for sidecar in sidecars {
        let sidecar = fs::canonicalize(&sidecar)
            .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
        let (click_source, sources) = load_sidecar(&sidecar)?;
        let refs = source_refs(&sources);
        let baseline_attested = has_full_verification_marker(&repo, &baseline_commit, &sidecar)?;
        let mut full_rebuild = !baseline_attested;
        let mut reasons = if !baseline_attested {
            vec![format!(
                "baseline commit {baseline_commit} has no valid full-verification marker for this sidecar and verifier binary"
            )]
        } else {
            Vec::new()
        };
        let (selected, reused) = if full_rebuild {
            (
                c0_function_names(&click_source, &refs).map_err(click_message)?,
                Vec::new(),
            )
        } else if let Some((baseline_click, baseline_sources)) =
            load_baseline_sidecar(&repo, revision, &sidecar)?
        {
            let baseline_refs = source_refs(&baseline_sources);
            let selection =
                c0_incremental_selection(&click_source, &refs, &baseline_click, &baseline_refs)
                    .map_err(click_message)?;
            full_rebuild = selection.full_rebuild;
            reasons = selection.reasons;
            (selection.selected_functions, selection.reused_functions)
        } else {
            full_rebuild = true;
            reasons.push(
                "sidecar or one of its declared C sources is absent at the baseline".to_string(),
            );
            (
                c0_function_names(&click_source, &refs).map_err(click_message)?,
                Vec::new(),
            )
        };

        print_incremental_selection(
            &sidecar,
            revision,
            &selected,
            &reused,
            &reasons,
            full_rebuild,
        );
        if explain_only || selected.is_empty() {
            skipped += usize::from(selected.is_empty());
            continue;
        }
        click::instrumentation::with_deadline(time_limit, || {
            if full_rebuild {
                verify_c0_sources(&click_source, &refs)
            } else {
                verify_c0_sources_functions(&click_source, &refs, selected.clone())
            }
            .map_err(|error| {
                format!(
                    "incremental sidecar `{}` failed under its {} limit: {}",
                    sidecar.display(),
                    format_duration(time_limit),
                    error.message()
                )
            })
        })?;
        if full_rebuild {
            // The rebuild verified the current sources; attest the requested
            // baseline too only when its sidecar and sources are identical,
            // so the next `--changed-since {revision}` run can select instead
            // of rebuilding again.
            let also_attest = match load_baseline_sidecar(&repo, revision, &sidecar)? {
                Some(baseline)
                    if baseline_matches_current(
                        &baseline,
                        &(click_source.clone(), sources.clone()),
                    ) =>
                {
                    vec![baseline_commit.clone()]
                }
                _ => Vec::new(),
            };
            if let Err(message) = record_full_verification(&sidecar, &also_attest) {
                eprintln!(
                    "click-verify: warning: could not record incremental baseline: {message}"
                );
            }
        }
        verified += 1;
        println!("  result: verified");
    }
    if explain_only {
        println!("dry run: no proofs were executed");
    } else {
        println!(
            "incremental verification completed: {verified} sidecars verified, {skipped} unchanged sidecars skipped"
        );
    }
    Ok(())
}

fn click_message(error: click::surface::ClickError) -> String {
    error.message().to_string()
}

fn print_incremental_selection(
    sidecar: &Path,
    revision: &str,
    selected: &[String],
    reused: &[String],
    reasons: &[String],
    full_rebuild: bool,
) {
    println!("INCREMENTAL {} since {revision}", sidecar.display());
    println!(
        "  mode: {}",
        if full_rebuild {
            "full rebuild"
        } else {
            "semantic function selection"
        }
    );
    println!(
        "  selected ({}): {}",
        selected.len(),
        bounded_names(selected)
    );
    println!("  reused ({}): {}", reused.len(), bounded_names(reused));
    for reason in reasons.iter().take(12) {
        println!("  because: {reason}");
    }
    if reasons.len() > 12 {
        println!("  because: ... {} more reasons", reasons.len() - 12);
    }
}

fn bounded_names(names: &[String]) -> String {
    if names.is_empty() {
        return "(none)".to_string();
    }
    let mut shown = names.iter().take(12).cloned().collect::<Vec<_>>();
    if names.len() > shown.len() {
        shown.push(format!("... {} more", names.len() - shown.len()));
    }
    shown.join(", ")
}

fn git_repo_root(path: &Path) -> Result<PathBuf, String> {
    let anchor = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or_else(|| Path::new("."))
    };
    let output = Command::new("git")
        .args([
            "-C",
            &anchor.display().to_string(),
            "rev-parse",
            "--show-toplevel",
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "`{}` is not inside a readable git worktree",
            path.display()
        ));
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

fn git_commit_id(repo: &Path, revision: &str) -> Result<String, String> {
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--verify",
            &format!("{revision}^{{commit}}"),
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(format!("unknown git revision `{revision}`"))
    }
}

fn verification_marker_path(repo: &Path, commit: &str, sidecar: &Path) -> Result<PathBuf, String> {
    let relative = sidecar.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    let mut hasher = DefaultHasher::new();
    relative.hash(&mut hasher);
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--git-path",
            INCREMENTAL_CACHE_SCHEMA,
        ])
        .output()
        .map_err(|error| format!("failed to locate git metadata: {error}"))?;
    if !output.status.success() {
        return Err("git did not expose its metadata path".to_string());
    }
    let root = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
    let root = if root.is_absolute() {
        root
    } else {
        repo.join(root)
    };
    Ok(root.join(commit).join(format!("{:016x}", hasher.finish())))
}

fn verifier_fingerprint() -> Result<&'static str, String> {
    static FINGERPRINT: OnceLock<Result<String, String>> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let executable = env::current_exe()
                .map_err(|error| format!("failed to locate the Click executable: {error}"))?;
            let bytes = fs::read(&executable).map_err(|error| {
                format!(
                    "failed to fingerprint Click executable `{}`: {error}",
                    executable.display()
                )
            })?;
            let mut hasher = DefaultHasher::new();
            bytes.hash(&mut hasher);
            Ok(format!("{:016x}", hasher.finish()))
        })
        .as_deref()
        .map_err(Clone::clone)
}

/// The verifier switches that change a verdict: every `CLICK_*` environment
/// variable, sorted, so a baseline attested with budgets or the memory DAG
/// disabled is never reused by a run with them enabled.
fn environment_switches() -> String {
    environment_switches_from(env::vars())
}

fn environment_switches_from(variables: impl IntoIterator<Item = (String, String)>) -> String {
    let mut switches = variables
        .into_iter()
        .filter(|(name, _)| name.starts_with("CLICK_"))
        .map(|(name, value)| format!("env={name}={value}\n"))
        .collect::<Vec<_>>();
    switches.sort();
    switches.concat()
}

fn marker_contents(commit: &str, relative: &Path, fingerprint: &str, switches: &str) -> String {
    format!(
        "{INCREMENTAL_CACHE_SCHEMA}\nverifier={fingerprint}\ncommit={commit}\nsidecar={}\n{switches}",
        relative.display()
    )
}

fn valid_marker(contents: &str, commit: &str, relative: &Path, fingerprint: &str) -> bool {
    contents == marker_contents(commit, relative, fingerprint, &environment_switches())
}

/// A full rebuild verifies the current sources, so it may attest the
/// requested baseline only when the baseline's sidecar and C sources are
/// byte-identical to the current ones.
fn baseline_matches_current(baseline: &LoadedSidecar, current: &LoadedSidecar) -> bool {
    baseline == current
}

fn has_full_verification_marker(repo: &Path, commit: &str, sidecar: &Path) -> Result<bool, String> {
    let marker = verification_marker_path(repo, commit, sidecar)?;
    let relative = sidecar.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    let fingerprint = verifier_fingerprint()?;
    match fs::read_to_string(marker) {
        Ok(contents) => Ok(valid_marker(&contents, commit, relative, fingerprint)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(_) => Ok(false),
    }
}

/// Records that `sidecar` was fully verified at `HEAD`, and at each commit in
/// `also_attest` (a `--changed-since` baseline whose sources match the
/// current ones), unless tracked sources are dirty.
fn record_full_verification(sidecar: &Path, also_attest: &[String]) -> Result<(), String> {
    let sidecar = fs::canonicalize(sidecar)
        .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
    let repo = git_repo_root(&sidecar)?;
    let commit = git_commit_id(&repo, "HEAD")?;
    let relative = sidecar.strip_prefix(&repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    let (click_source, _) = load_sidecar(&sidecar)?;
    let mut tracked = vec![relative.to_path_buf()];
    let parent = relative.parent().unwrap_or_else(|| Path::new(""));
    tracked.extend(
        verifying_source_paths(&click_source)
            .map_err(click_message)?
            .into_iter()
            .map(|name| parent.join(name)),
    );
    for path in &tracked {
        let status = Command::new("git")
            .args([
                "-C",
                &repo.display().to_string(),
                "ls-files",
                "--error-unmatch",
                "--",
            ])
            .arg(path)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map_err(|error| format!("failed to inspect tracked sources: {error}"))?;
        if !status.success() {
            return Ok(());
        }
    }
    for staged in [false, true] {
        let mut command = Command::new("git");
        command.args(["-C", &repo.display().to_string(), "diff"]);
        if staged {
            command.arg("--cached");
        }
        command.arg("--quiet").arg("HEAD").arg("--");
        command.args(&tracked);
        let status = command
            .status()
            .map_err(|error| format!("failed to inspect git worktree: {error}"))?;
        if !status.success() {
            return Ok(());
        }
    }
    for attested in std::iter::once(&commit).chain(also_attest) {
        let marker = verification_marker_path(&repo, attested, &sidecar)?;
        let parent = marker
            .parent()
            .ok_or_else(|| "incremental marker has no parent directory".to_string())?;
        fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create `{}`: {error}", parent.display()))?;
        let temporary = parent.join(format!(".tmp-{}", std::process::id()));
        fs::write(
            &temporary,
            marker_contents(
                attested,
                relative,
                verifier_fingerprint()?,
                &environment_switches(),
            ),
        )
        .map_err(|error| format!("failed to write `{}`: {error}", temporary.display()))?;
        fs::rename(&temporary, &marker)
            .map_err(|error| format!("failed to install `{}`: {error}", marker.display()))?;
    }
    Ok(())
}

fn git_show(repo: &Path, revision: &str, path: &Path) -> Result<Option<String>, String> {
    let relative = path.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            path.display(),
            repo.display()
        )
    })?;
    let spec = format!("{revision}:{}", relative.display());
    let output = Command::new("git")
        .args(["-C", &repo.display().to_string(), "show", &spec])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(Some(String::from_utf8_lossy(&output.stdout).into_owned()))
    } else {
        Ok(None)
    }
}

fn load_baseline_sidecar(
    repo: &Path,
    revision: &str,
    click_path: &Path,
) -> Result<Option<LoadedSidecar>, String> {
    let Some(click_source) = git_show(repo, revision, click_path)? else {
        return Ok(None);
    };
    let parent = click_path.parent().unwrap_or_else(|| Path::new("."));
    let mut sources = Vec::new();
    for name in verifying_source_paths(&click_source).map_err(click_message)? {
        let source_path = parent.join(&name);
        let Some(source) = git_show(repo, revision, &source_path)? else {
            return Ok(None);
        };
        sources.push((name, source));
    }
    Ok(Some((click_source, sources)))
}

/// Shows a discovered sidecar relative to the directory the user named, since
/// project discovery canonicalizes to absolute paths.
fn display_path(sidecar: &Path, root: &Path) -> String {
    let Ok(root) = fs::canonicalize(root) else {
        return sidecar.display().to_string();
    };
    let relative = sidecar.strip_prefix(&root).unwrap_or(sidecar);
    let shown: PathBuf = if relative == sidecar {
        sidecar.to_path_buf()
    } else {
        root.file_name().map_or_else(
            || relative.to_path_buf(),
            |name| Path::new(name).join(relative),
        )
    };
    shown.display().to_string()
}

fn plural(count: usize) -> &'static str {
    if count == 1 { "" } else { "s" }
}

fn verify_file(click_path: &Path, time_limit: Duration) -> Result<(), String> {
    click::instrumentation::with_deadline(time_limit, || {
        let (click_source, sources) = load_sidecar(click_path)?;
        verify_c0_sources(&click_source, &source_refs(&sources)).map_err(|error| {
            format!(
                "sidecar `{}` failed under its {} limit: {}",
                click_path.display(),
                format_duration(time_limit),
                error.message()
            )
        })
    })?;
    if let Err(message) = record_full_verification(click_path, &[]) {
        eprintln!("click-verify: warning: could not record incremental baseline: {message}");
    }
    Ok(())
}

fn verify_location(
    click_path: &Path,
    line: usize,
    column: usize,
    time_limit: Duration,
) -> Result<(), String> {
    click::instrumentation::with_deadline(time_limit, || {
        let (click_source, sources) = load_sidecar(click_path)?;
        verify_c0_sources_at(&click_source, &source_refs(&sources), line, column).map_err(
            |error| {
                format!(
                    "proof unit `{}:{line}:{column}` failed under its {} limit: {}",
                    click_path.display(),
                    format_duration(time_limit),
                    error.message()
                )
            },
        )?;
        Ok::<(), String>(())
    })?;
    Ok(())
}

fn load_sidecar(click_path: &Path) -> Result<LoadedSidecar, String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let sources = read_verifying_sources(click_path, &click_source)?;
    Ok((click_source, sources))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn location_suffixes_win_over_paths_that_could_be_directories() {
        assert!(looks_like_source_location("examples/tiny/tiny.click:12:5"));
        assert!(!looks_like_source_location("examples/tiny"));
        assert!(!looks_like_source_location("examples"));
    }

    #[test]
    fn parses_default_and_overridden_time_limits() {
        assert_eq!(
            parse_arguments(["example.click".to_string()]),
            Ok(Arguments {
                target: "example.click".to_string(),
                time_limit: DEFAULT_VERIFY_TIME_LIMIT,
                changed_since: None,
                explain: false,
            })
        );
        assert_eq!(
            parse_arguments([
                "--time-limit".to_string(),
                "250ms".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                target: "example.click".to_string(),
                time_limit: Duration::from_millis(250),
                changed_since: None,
                explain: false,
            })
        );
        assert_eq!(
            parse_arguments([
                "--changed-since".to_string(),
                "HEAD~1".to_string(),
                "--explain".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                target: "examples".to_string(),
                time_limit: DEFAULT_VERIFY_TIME_LIMIT,
                changed_since: Some("HEAD~1".to_string()),
                explain: true,
            })
        );
    }

    #[test]
    fn marker_contents_include_environment_switches() {
        let relative = Path::new("examples/tiny/tiny.click");
        let plain = marker_contents("abc", relative, "fp", "");
        let switches = environment_switches_from([(
            "CLICK_DISABLE_TACTIC_BUDGETS".to_string(),
            "1".to_string(),
        )]);
        let budgets_off = marker_contents("abc", relative, "fp", &switches);
        assert_ne!(plain, budgets_off);
        assert!(budgets_off.ends_with("env=CLICK_DISABLE_TACTIC_BUDGETS=1\n"));
    }

    #[test]
    fn environment_switches_are_sorted_and_limited_to_click_variables() {
        let switches = environment_switches_from([
            ("PATH".to_string(), "x".to_string()),
            ("CLICK_DISABLE_MEMORY_DAG".to_string(), "1".to_string()),
            ("CLICK_DISABLE_CERT_ARMS".to_string(), "1".to_string()),
        ]);
        assert_eq!(
            switches,
            "env=CLICK_DISABLE_CERT_ARMS=1\nenv=CLICK_DISABLE_MEMORY_DAG=1\n"
        );
    }

    #[test]
    fn a_baseline_is_attested_only_when_its_sources_match_the_current_ones() {
        let current: LoadedSidecar = (
            "verifying \"a.c\";".to_string(),
            vec![("a.c".to_string(), "int32 f() { return 0; }".to_string())],
        );
        assert!(baseline_matches_current(&current, &current));
        let edited: LoadedSidecar = (
            current.0.clone(),
            vec![("a.c".to_string(), "int32 f() { return 1; }".to_string())],
        );
        assert!(!baseline_matches_current(&edited, &current));
    }

    #[test]
    fn discovered_sidecars_display_under_the_named_directory() {
        let root = fs::canonicalize("examples").expect("the examples directory should exist");
        let sidecar = root.join("input-cursor").join("input_cursor.click");
        assert_eq!(
            display_path(&sidecar, Path::new("examples")),
            "examples/input-cursor/input_cursor.click"
        );
    }

    #[test]
    fn directory_mode_finds_every_sidecar_in_a_single_project() {
        let projects =
            find_projects(Path::new("examples/input-cursor")).expect("the project should resolve");
        assert_eq!(projects.len(), 1);
        let sidecars =
            files_with_extension(&projects[0], "click").expect("sidecars should be listed");
        assert!(!sidecars.is_empty());
    }

    #[test]
    fn corrupted_or_mismatched_incremental_markers_are_cache_misses() {
        let path = Path::new("examples/sample.click");
        let valid = marker_contents("abc123", path, "verifier-a", &environment_switches());
        assert!(valid_marker(&valid, "abc123", path, "verifier-a"));
        assert!(!valid_marker("truncated", "abc123", path, "verifier-a"));
        assert!(!valid_marker(&valid, "different", path, "verifier-a"));
        assert!(!valid_marker(&valid, "abc123", path, "verifier-b"));
        assert!(!valid_marker(
            &valid,
            "abc123",
            Path::new("examples/other.click"),
            "verifier-a"
        ));
        // A marker written under a verifier switch this process does not have
        // set is a cache miss as well.
        let other_switches = format!(
            "{}env=CLICK_DISABLE_TACTIC_BUDGETS=1\n",
            environment_switches()
        );
        let attested_elsewhere = marker_contents("abc123", path, "verifier-a", &other_switches);
        assert!(!valid_marker(
            &attested_elsewhere,
            "abc123",
            path,
            "verifier-a"
        ));
    }
}
