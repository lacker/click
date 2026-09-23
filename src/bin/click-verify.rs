use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::Duration;

use click::cli::{
    CInput, DEFAULT_VERIFY_TIME_LIMIT, contains_click_file, files_with_extension, find_projects,
    looks_like_source_location, parse_duration, parse_source_location, read_click_project_at_root,
    source_refs,
};
use click::languages::c::source as c_source;
use click::languages::c::target::CTarget;
#[cfg(test)]
use click::surface::verify_c0_sources;
use click::surface::{
    ClickError, ClickErrorKind, ClickProject, VerifiedCTheorem, c0_incremental_selection,
    c0_prepared_project_external_dependencies, c0_prepared_project_selected_proof_count,
    c0_prepared_project_selected_proof_names, c0_prepared_project_tactic_source_position,
    c0_project_external_dependencies, c0_project_selected_proof_count,
    c0_project_selected_proof_names, c0_project_tactic_source_position,
    cpp_prepared_project_external_dependencies, cpp_prepared_project_selected_proof_count,
    cpp_prepared_project_tactic_source_position, nested_tactic_source_position, selected_c_target,
    verify_c0_prepared_project, verify_c0_prepared_project_at,
    verify_c0_prepared_project_functions, verify_c0_project, verify_c0_project_at,
    verify_c0_project_functions, verify_cpp_prepared_project, verify_cpp_prepared_project_at,
    verifying_source_paths, with_proof_trace,
};

const USAGE: &str = "\
usage: click verify [--time-limit <DURATION>] <sidecar.click>[:<line>:<column>]
       click verify --trace-proof <FUNCTION> <sidecar.click>
       click verify [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>

Verifies proofs owned by the selected sidecar, or, when a one-based
:LINE:COLUMN suffix is supplied, only the proof unit containing that source
location. Imported declarations and unselected C function contracts are
assumptions; their proof bodies are not recursively selected.

Given a directory, verifies every sidecar in it: either the project directory
itself when it holds sidecars, or each immediate subdirectory that does. This
is the command to run after applying an expansion emitted by `click expand`.
Each sidecar has a 30-second limit by default.

`--trace-proof FUNCTION` verifies one C function and shows checked fact and
resource changes on the failing path. Ordinary proof errors suggest this
command with the failing function filled in.

`--allow-sorry` enables the dev-only `sorry` proof hole: a proof unit whose
body is exactly `sorry();` is admitted without checking. This is purely a
debugging tool for reducing a failure to its minimal shape; it is never
sound. Admissions are reported loudly, never recorded in incremental
baselines or caches, and `click audit`, `click expand`, and `scripts/check.sh`
never enable the flag, so sorry can never sneak into a passing gate.";

const INCREMENTAL_CACHE_SCHEMA: &str = "click-verified-v1";
type LoadedSidecar = (String, Vec<(String, String)>);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    target: String,
    time_limit: Duration,
    changed_since: Option<String>,
    explain: bool,
    allow_sorry: bool,
    trace_proof: Option<String>,
}

fn main() {
    if let Err(message) = entry() {
        if message.starts_with("proof error:")
            || message.starts_with("syntax error:")
            || message.starts_with("type error:")
            || message.starts_with("internal error:")
        {
            eprintln!("{message}");
        } else {
            eprintln!("click-verify: {message}");
        }
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
    if arguments.trace_proof.is_some()
        && (arguments.changed_since.is_some()
            || arguments.explain
            || arguments.allow_sorry
            || looks_like_source_location(&arguments.target)
            || Path::new(&arguments.target).is_dir())
    {
        return Err(
            "`--trace-proof` requires one sidecar file without a location, incremental options, or `--allow-sorry`"
                .to_string(),
        );
    }
    if arguments.allow_sorry {
        // An admission records what an ordinary run did not check, so it
        // cannot say which proofs a baseline still has to check, and it must
        // never be recorded as verified.
        if arguments.changed_since.is_some() {
            return Err("`--allow-sorry` cannot be combined with `--changed-since`".to_string());
        }
        let arguments = Arguments {
            allow_sorry: false,
            ..arguments
        };
        return click::surface::with_allow_sorry(|| run(arguments));
    }
    run(arguments)
}

fn run(arguments: Arguments) -> Result<(), String> {
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
        verify_file(
            path,
            arguments.time_limit,
            path.parent(),
            arguments.trace_proof.as_deref(),
        )
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut target = None;
    let mut time_limit = DEFAULT_VERIFY_TIME_LIMIT;
    let mut changed_since = None;
    let mut explain = false;
    let mut allow_sorry = false;
    let mut trace_proof = None;
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
        } else if parse_options && argument == "--allow-sorry" {
            allow_sorry = true;
        } else if parse_options && argument == "--trace-proof" {
            if trace_proof.is_some() {
                return Err("`--trace-proof` may only be supplied once".to_string());
            }
            trace_proof = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing function after `--trace-proof`\n{USAGE}"))?,
            );
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
        allow_sorry,
        trace_proof,
    })
}

/// Verifies every sidecar under a project or examples directory, reporting
/// each one as it passes so a long run shows progress.
fn verify_directory(path: &Path, time_limit: Duration) -> Result<(), String> {
    let projects = find_projects(path)?;
    let project_root = if contains_click_file(path)? {
        path.parent().unwrap_or_else(|| Path::new("."))
    } else {
        path
    };
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
        verify_file(sidecar, time_limit, Some(project_root), None)?;
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
    let project_root = if path.is_file() {
        path.parent().unwrap_or_else(|| Path::new("."))
    } else if contains_click_file(path)? {
        path.parent().unwrap_or_else(|| Path::new("."))
    } else {
        path
    };
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
        let (click_source, project, inputs) = load_sidecar_inputs(&sidecar, Some(project_root))?;
        if inputs.is_prepared() {
            return Err(
                "`--changed-since` is not supported for compiler-prepared projects".to_string(),
            );
        }
        let sources = match &inputs {
            CInput::Bundle(sources) => sources.clone(),
            CInput::Prepared(_) | CInput::PreparedCpp(_) => unreachable!(),
        };
        let refs = source_refs(&sources);
        let baseline_attested = has_full_verification_marker(
            &repo,
            &baseline_commit,
            &sidecar,
            click::surface::selected_project_c_target(&project).map_err(click_message)?,
        )?;
        let mut full_rebuild = !baseline_attested;
        let mut reasons = if !baseline_attested {
            vec![format!(
                "baseline commit {baseline_commit} has no valid full-verification marker for this sidecar and verifier binary"
            )]
        } else {
            Vec::new()
        };
        if let Some(reason) = imported_project_rebuild_reason(&project) {
            full_rebuild = true;
            reasons = vec![reason.to_string()];
        }
        let (selected, reused) = if full_rebuild {
            (
                c0_project_selected_proof_names(&project, &refs).map_err(click_message)?,
                Vec::new(),
            )
        } else if let Some((baseline_click, baseline_sources)) =
            load_baseline_sidecar(&repo, &baseline_commit, &sidecar)?
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
                c0_project_selected_proof_names(&project, &refs).map_err(click_message)?,
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
        if explain_only {
            continue;
        }
        if !full_rebuild && selected.is_empty() {
            skipped += 1;
            continue;
        }
        let dependencies =
            c0_project_external_dependencies(&project, &refs).map_err(click_message)?;
        let verified_theorems = click::instrumentation::with_deadline(time_limit, || {
            if full_rebuild {
                verify_c0_project(&project, &refs)
            } else {
                verify_c0_project_functions(&project, &refs, selected.clone())
            }
            .map_err(|error| proof_error_report(&error, &sidecar, true, &project, &inputs))
        })?;
        print_external_dependencies(&dependencies, &verified_theorems);
        if full_rebuild
            && project.modules().len() == 1
            && project.c_profile().is_none()
            && let Err(message) = record_full_verification(
                &sidecar,
                &click_source,
                &sources,
                std::slice::from_ref(&baseline_commit),
            )
        {
            eprintln!("click-verify: warning: could not record incremental baseline: {message}");
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

fn imported_project_rebuild_reason(project: &ClickProject) -> Option<&'static str> {
    if project.c_profile().is_some() {
        return Some(
            "the sidecar uses project C configuration; conservative full rebuild prevents reuse across configuration changes",
        );
    }
    (project.modules().len() > 1).then_some(
        "the sidecar has Click imports; conservative import-aware rebuild of the selected entry scope",
    )
}

fn click_message(error: click::surface::ClickError) -> String {
    error.concise_report()
}

fn shell_word(value: &str) -> String {
    if value
        .bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || b"/._-".contains(&byte))
    {
        value.to_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn proof_error_report(
    error: &ClickError,
    sidecar: &Path,
    suggest_trace: bool,
    project: &ClickProject,
    inputs: &CInput,
) -> String {
    let mut report = if suggest_trace {
        error.concise_report()
    } else {
        error.report()
    };
    if suggest_trace {
        if let Some(source) = project.entry_source()
            && let Some(position) = proof_source_position(error, project, inputs, source)
            && let Some(excerpt) = source_excerpt(sidecar, source, &position)
        {
            report.push('\n');
            report.push_str(&excerpt);
        }
        if let Some(location) = error.proof_step_location() {
            report.push_str("\n  step: ");
            report.push_str(location);
        }
    }
    if suggest_trace
        && error.kind() == ClickErrorKind::Proof
        && let Some(function) = error
            .proof_claim_label()
            .and_then(|claim| claim.split_once('.'))
    {
        report.push_str(&format!(
            "\n  trace: click verify --trace-proof {} {}",
            shell_word(function.0),
            shell_word(&sidecar.display().to_string())
        ));
    }
    report
}

fn proof_source_position(
    error: &ClickError,
    project: &ClickProject,
    inputs: &CInput,
    source: &str,
) -> Option<click::surface::SourcePosition> {
    let claim = error.proof_claim_label()?;
    let path = error.proof_source_tactic_path()?;
    let source_index = *path.first()?;
    let outer = match inputs {
        CInput::Bundle(sources) => {
            c0_project_tactic_source_position(project, &source_refs(sources), claim, source_index)
        }
        CInput::Prepared(imports) => {
            c0_prepared_project_tactic_source_position(project, imports, claim, source_index)
        }
        CInput::PreparedCpp(import) => {
            cpp_prepared_project_tactic_source_position(project, import, claim, source_index)
        }
    }
    .ok()?;
    if path.len() == 1 {
        Some(outer)
    } else {
        nested_tactic_source_position(source, &outer, &path[1..]).ok()
    }
}

fn source_excerpt(
    sidecar: &Path,
    source: &str,
    position: &click::surface::SourcePosition,
) -> Option<String> {
    let line = source.lines().nth(position.line.checked_sub(1)?)?;
    let chars = line.chars().collect::<Vec<_>>();
    let column = position.column.checked_sub(1)?;
    if column > chars.len() {
        return None;
    }
    let start = column.saturating_sub(48);
    let end = chars.len().min(start + 160);
    let snippet = chars[start..end].iter().collect::<String>();
    let left = if start == 0 { "" } else { "…" };
    let right = if end == chars.len() { "" } else { "…" };
    let marker = chars[column..]
        .iter()
        .take_while(|character| character.is_alphanumeric() || **character == '_')
        .take(12)
        .count()
        .max(1);
    let caret_offset = chars[start..column]
        .iter()
        .map(|character| if *character == '\t' { 4 } else { 1 })
        .sum::<usize>()
        + usize::from(start > 0);
    let width = position.line.to_string().len();
    Some(format!(
        "  --> {}:{}:{}\n  {:width$} | {}{}{}\n  {:width$} | {}{}",
        sidecar.display(),
        position.line,
        position.column,
        position.line,
        left,
        snippet,
        right,
        "",
        " ".repeat(caret_offset),
        "^".repeat(marker),
        width = width,
    ))
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

fn marker_contents(
    commit: &str,
    relative: &Path,
    fingerprint: &str,
    switches: &str,
    target: CTarget,
) -> String {
    format!(
        "{INCREMENTAL_CACHE_SCHEMA}\ntarget={}\nverifier={fingerprint}\ncommit={commit}\nsidecar={}\n{switches}",
        target.name(),
        relative.display()
    )
}

fn valid_marker(
    contents: &str,
    commit: &str,
    relative: &Path,
    fingerprint: &str,
    target: CTarget,
) -> bool {
    contents
        == marker_contents(
            commit,
            relative,
            fingerprint,
            &environment_switches(),
            target,
        )
}

/// Compare the commit's complete input bundle with the snapshot that was
/// actually verified, including transitively included headers.
fn baseline_matches_verified(
    baseline: &LoadedSidecar,
    click_source: &str,
    sources: &[(String, String)],
) -> bool {
    baseline.0 == click_source && baseline.1 == sources
}

fn has_full_verification_marker(
    repo: &Path,
    commit: &str,
    sidecar: &Path,
    target: CTarget,
) -> Result<bool, String> {
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
        Ok(contents) => Ok(valid_marker(
            &contents,
            commit,
            relative,
            fingerprint,
            target,
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(_) => Ok(false),
    }
}

/// Attest only commits whose complete input bundle equals the verified
/// snapshot. Re-reading the working tree here could certify a different
/// program if a file changed after verification.
fn record_full_verification(
    sidecar: &Path,
    click_source: &str,
    sources: &[(String, String)],
    also_attest: &[String],
) -> Result<(), String> {
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
    for attested in std::iter::once(&commit).chain(also_attest) {
        let Some(baseline) = load_baseline_sidecar(&repo, attested, &sidecar)? else {
            continue;
        };
        if !baseline_matches_verified(&baseline, click_source, sources) {
            continue;
        }
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
                selected_c_target(click_source).map_err(click_message)?,
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
    let Some(sources) = load_baseline_sources(parent, &click_source, |source_path| {
        git_show(repo, revision, source_path)
    })?
    else {
        return Ok(None);
    };
    Ok(Some((click_source, sources)))
}

fn load_baseline_sources(
    parent: &Path,
    click_source: &str,
    mut load: impl FnMut(&Path) -> Result<Option<String>, String>,
) -> Result<Option<Vec<(String, String)>>, String> {
    let mut pending = verifying_source_paths(click_source).map_err(click_message)?;
    let target = selected_c_target(click_source).map_err(click_message)?;
    let mut sources = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut next = 0;
    while next < pending.len() {
        let name = pending[next].clone();
        next += 1;
        if !seen.insert(name.clone()) {
            continue;
        }
        let source_path = parent.join(&name);
        let Some(source) = load(&source_path)? else {
            return Ok(None);
        };
        let includes = c_source::local_include_paths_for_target(&name, &source, target)
            .map_err(|error| format!("failed to process baseline C source includes: {error}"))?;
        pending.extend(includes);
        sources.push((name, source));
    }
    Ok(Some(sources))
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

fn verify_file(
    click_path: &Path,
    time_limit: Duration,
    project_root: Option<&Path>,
    trace_proof: Option<&str>,
) -> Result<(), String> {
    // A previous failed sidecar may have left admissions behind; each file
    // reports only its own.
    let _ = click::surface::take_sorry_admissions();
    let (click_source, project, inputs) = load_sidecar_inputs(click_path, project_root)?;
    if let Some(function) = trace_proof {
        let names = match &inputs {
            CInput::Bundle(sources) => {
                c0_project_selected_proof_names(&project, &source_refs(sources))
                    .map_err(click_message)?
            }
            CInput::Prepared(imports) => {
                c0_prepared_project_selected_proof_names(&project, imports)
                    .map_err(click_message)?
            }
            CInput::PreparedCpp(_) => {
                return Err(
                    "`--trace-proof` currently supports C sidecars, not prepared C++ inputs".into(),
                );
            }
        };
        if !names
            .iter()
            .any(|name| name == &format!("function:{function}"))
        {
            return Err(format!(
                "`{function}` is not a selected proof in `{}`",
                click_path.display()
            ));
        }
    }
    let dependencies = match &inputs {
        CInput::Bundle(sources) => {
            c0_project_external_dependencies(&project, &source_refs(sources))
                .map_err(click_message)?
        }
        CInput::Prepared(imports) => {
            c0_prepared_project_external_dependencies(&project, imports).map_err(click_message)?
        }
        CInput::PreparedCpp(import) => {
            cpp_prepared_project_external_dependencies(&project, import).map_err(click_message)?
        }
    };
    let verified = click::instrumentation::with_deadline(time_limit, || {
        let run_selected = || match (&inputs, trace_proof) {
            (CInput::Bundle(sources), Some(function)) => {
                verify_c0_project_functions(&project, &source_refs(sources), [function.to_owned()])
            }
            (CInput::Prepared(imports), Some(function)) => {
                verify_c0_prepared_project_functions(&project, imports, [function.to_owned()])
            }
            (CInput::PreparedCpp(_), Some(_)) => unreachable!(),
            (CInput::Bundle(sources), None) => verify_c0_project(&project, &source_refs(sources)),
            (CInput::Prepared(imports), None) => verify_c0_prepared_project(&project, imports),
            (CInput::PreparedCpp(import), None) => verify_cpp_prepared_project(&project, import),
        };
        let report = |error: ClickError| {
            proof_error_report(&error, click_path, trace_proof.is_none(), &project, &inputs)
        };
        match trace_proof {
            Some(function) => with_proof_trace(function, || run_selected().map_err(report)),
            None => run_selected().map_err(report),
        }
    })?;
    print_external_dependencies(&dependencies, &verified);
    let selected = if trace_proof.is_some() {
        1
    } else {
        match &inputs {
            CInput::Bundle(sources) => {
                c0_project_selected_proof_count(&project, &source_refs(sources))
                    .map_err(click_message)?
            }
            CInput::Prepared(imports) => {
                c0_prepared_project_selected_proof_count(&project, imports)
                    .map_err(click_message)?
            }
            CInput::PreparedCpp(import) => {
                cpp_prepared_project_selected_proof_count(&project, import)
                    .map_err(click_message)?
            }
        }
    };
    println!("{selected} selected proof{} verified", plural(selected));
    let admissions = click::surface::take_sorry_admissions();
    if admissions.is_empty() {
        if let CInput::Bundle(sources) = &inputs
            && trace_proof.is_none()
            && project.modules().len() == 1
            && project.c_profile().is_none()
            && let Err(message) = record_full_verification(click_path, &click_source, sources, &[])
        {
            eprintln!("click-verify: warning: could not record incremental baseline: {message}");
        }
    } else {
        eprintln!(
            "click-verify: WARNING: {} proof unit{} admitted via `sorry` in `{}`: NOTHING HERE IS PROVED. `sorry` is a dev-only hole (enabled by `--allow-sorry`); it never verifies in the gate.",
            admissions.len(),
            plural(admissions.len()),
            click_path.display(),
        );
        for admission in &admissions {
            eprintln!(
                "click-verify: WARNING: sorry admitted `{}`",
                admission.label
            );
        }
        eprintln!("click-verify: WARNING: no incremental baseline recorded for a sorry run.");
    }
    Ok(())
}

fn verify_location(
    click_path: &Path,
    line: usize,
    column: usize,
    time_limit: Duration,
) -> Result<(), String> {
    let (_click_source, project, inputs) = load_sidecar_inputs(click_path, click_path.parent())?;
    let dependencies = match &inputs {
        CInput::Bundle(sources) => {
            c0_project_external_dependencies(&project, &source_refs(sources))
                .map_err(click_message)?
        }
        CInput::Prepared(imports) => {
            c0_prepared_project_external_dependencies(&project, imports).map_err(click_message)?
        }
        CInput::PreparedCpp(import) => {
            cpp_prepared_project_external_dependencies(&project, import).map_err(click_message)?
        }
    };
    let verified = click::instrumentation::with_deadline(time_limit, || {
        let result = match &inputs {
            CInput::Bundle(sources) => {
                verify_c0_project_at(&project, &source_refs(sources), line, column)
            }
            CInput::Prepared(imports) => {
                verify_c0_prepared_project_at(&project, imports, line, column)
            }
            CInput::PreparedCpp(import) => {
                verify_cpp_prepared_project_at(&project, import, line, column)
            }
        };
        result.map_err(|error| proof_error_report(&error, click_path, true, &project, &inputs))
    })?;
    print_external_dependencies(&dependencies, &verified);
    println!("1 selected proof verified");
    Ok(())
}

fn print_external_dependencies(
    dependencies: &BTreeMap<String, Vec<String>>,
    verified: &[VerifiedCTheorem],
) {
    if let Some(selection) = verified
        .first()
        .and_then(|theorem| theorem.selection.as_ref())
    {
        for assumption in &selection.runtime_assumptions {
            println!("runtime assumption: {assumption}");
        }
    }
    let verified_functions = verified
        .iter()
        .map(|theorem| theorem.function_block.signature().name())
        .collect::<std::collections::BTreeSet<_>>();
    for (function, external) in dependencies {
        if verified_functions.contains(function.as_str()) {
            println!(
                "external assumptions: {function} -> {}",
                external.join(", ")
            );
        }
    }
}

fn load_sidecar_inputs(
    click_path: &Path,
    project_root: Option<&Path>,
) -> Result<(String, ClickProject, CInput), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let project = read_click_project_at_root(
        click_path,
        &click_source,
        project_root.unwrap_or_else(|| click_path.parent().unwrap_or_else(|| Path::new("."))),
    )?;
    let inputs = click::cli::read_c_inputs_for_project(click_path, &click_source, &project)?;
    Ok((click_source, project, inputs))
}

#[cfg(test)]
#[path = "click-verify/incremental_tests.rs"]
mod incremental_tests;

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
    fn parses_allow_sorry_and_rejects_it_with_changed_since() {
        assert_eq!(
            parse_arguments(["--allow-sorry".to_string(), "example.click".to_string()]),
            Ok(Arguments {
                target: "example.click".to_string(),
                time_limit: DEFAULT_VERIFY_TIME_LIMIT,
                changed_since: None,
                explain: false,
                allow_sorry: true,
                trace_proof: None,
            })
        );
        assert_eq!(
            entry_with([
                "--allow-sorry".to_string(),
                "--changed-since".to_string(),
                "HEAD".to_string(),
                "example.click".to_string(),
            ]),
            Err("`--allow-sorry` cannot be combined with `--changed-since`".to_string())
        );
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
                allow_sorry: false,
                trace_proof: None,
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
                allow_sorry: false,
                trace_proof: None,
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
                allow_sorry: false,
                trace_proof: None,
            })
        );
    }

    #[test]
    fn imported_projects_force_the_documented_selected_scope_rebuild() {
        let project = ClickProject::new(
            "entry.click",
            [
                click::surface::ClickModuleSource::new("library.click", "", []),
                click::surface::ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\";",
                    ["library.click".to_string()],
                ),
            ],
        );
        assert!(
            imported_project_rebuild_reason(&project)
                .unwrap()
                .contains("selected entry scope")
        );
        assert!(
            imported_project_rebuild_reason(&ClickProject::new(
                "entry.click",
                [click::surface::ClickModuleSource::new(
                    "entry.click",
                    "",
                    []
                )]
            ))
            .is_none()
        );
    }

    #[test]
    fn marker_contents_include_environment_switches() {
        let relative = Path::new("examples/tiny/tiny.click");
        let plain = marker_contents("abc", relative, "fp", "", CTarget::SUPPORTED);
        assert!(plain.contains("\ntarget=x86_64-linux-kernel\n"));
        let switches = environment_switches_from([(
            "CLICK_DISABLE_TACTIC_BUDGETS".to_string(),
            "1".to_string(),
        )]);
        let budgets_off = marker_contents("abc", relative, "fp", &switches, CTarget::SUPPORTED);
        assert_ne!(plain, budgets_off);
        assert!(budgets_off.ends_with("env=CLICK_DISABLE_TACTIC_BUDGETS=1\n"));
    }

    #[test]
    fn environment_switches_are_sorted_and_limited_to_click_variables() {
        let switches = environment_switches_from([
            ("PATH".to_string(), "x".to_string()),
            ("CLICK_TIMINGS".to_string(), "1".to_string()),
            ("CLICK_DISABLE_TACTIC_BUDGETS".to_string(), "1".to_string()),
        ]);
        assert_eq!(
            switches,
            "env=CLICK_DISABLE_TACTIC_BUDGETS=1\nenv=CLICK_TIMINGS=1\n"
        );
    }

    #[test]
    fn a_baseline_is_attested_only_when_its_sources_match_the_current_ones() {
        let current: LoadedSidecar = (
            "verifying \"a.c\";".to_string(),
            vec![("a.c".to_string(), "int32 f() { return 0; }".to_string())],
        );
        assert!(baseline_matches_verified(&current, &current.0, &current.1));
        let edited: LoadedSidecar = (
            current.0.clone(),
            vec![("a.c".to_string(), "int32 f() { return 1; }".to_string())],
        );
        assert!(!baseline_matches_verified(&edited, &current.0, &current.1));
    }

    #[test]
    fn baseline_sources_include_transitive_local_headers() {
        let files = BTreeMap::from([
            (
                PathBuf::from("project/m.c"),
                "#include \"cap.h\"\nint32 m() { return 0; }".to_string(),
            ),
            (
                PathBuf::from("project/cap.h"),
                "#include \"limits.h\"\ntypedef int32 cap_t;".to_string(),
            ),
            (
                PathBuf::from("project/limits.h"),
                "#define CAP_LIMIT 4".to_string(),
            ),
        ]);
        let loaded = load_baseline_sources(Path::new("project"), "verifying \"m.c\";", |path| {
            Ok(files.get(path).cloned())
        })
        .expect("baseline sources should load")
        .expect("all baseline sources should be present");
        assert_eq!(
            loaded,
            vec![
                (
                    "m.c".to_string(),
                    "#include \"cap.h\"\nint32 m() { return 0; }".to_string()
                ),
                (
                    "cap.h".to_string(),
                    "#include \"limits.h\"\ntypedef int32 cap_t;".to_string()
                ),
                ("limits.h".to_string(), "#define CAP_LIMIT 4".to_string()),
            ]
        );
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
    fn verify_accepts_realloc_as_a_builtin() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "click-verify-realloc-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("temporary verification directory should be creatable");
        fs::write(
            root.join("realloc.c"),
            "int32 realloc_preserves_calloc_prefix() {\n\
                int32* p = calloc(2, sizeof(int32));\n\
                if (p == 0) { return -1; }\n\
                int32* q = realloc(p, 3 * sizeof(int32));\n\
                if (q == 0) { free(p); return -1; }\n\
                int32 result = q[1];\n\
                free(q);\n\
                return result;\n\
            }\n",
        )
        .expect("C source should be writable");
        let click_path = root.join("realloc.click");
        fs::write(
            &click_path,
            "verifying \"realloc.c\";\n\
                int32 realloc_preserves_calloc_prefix() {\n\
                    ensures result == 0 or result == -1 by auto;\n\
                }\n",
        )
        .expect("Click sidecar should be writable");

        let result = entry_with([click_path.display().to_string()]);
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        assert!(
            result.is_ok(),
            "click verify should accept realloc: {result:?}"
        );
    }

    #[test]
    fn corrupted_or_mismatched_incremental_markers_are_cache_misses() {
        let path = Path::new("examples/sample.click");
        let valid = marker_contents(
            "abc123",
            path,
            "verifier-a",
            &environment_switches(),
            CTarget::SUPPORTED,
        );
        assert!(valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        let other_target = valid.replace("target=x86_64-linux-kernel", "target=another-target");
        assert!(!valid_marker(
            &other_target,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        // The same sources under another selected target are a cache miss.
        assert!(!valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-a",
            CTarget::X86_64LinuxUserspace
        ));
        assert!(!valid_marker(
            "truncated",
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "different",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-b",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "abc123",
            Path::new("examples/other.click"),
            "verifier-a",
            CTarget::SUPPORTED
        ));
        // A marker written under a verifier switch this process does not have
        // set is a cache miss as well.
        let other_switches = format!(
            "{}env=CLICK_DISABLE_TACTIC_BUDGETS=1\n",
            environment_switches()
        );
        let attested_elsewhere = marker_contents(
            "abc123",
            path,
            "verifier-a",
            &other_switches,
            CTarget::SUPPORTED,
        );
        assert!(!valid_marker(
            &attested_elsewhere,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
    }
}
