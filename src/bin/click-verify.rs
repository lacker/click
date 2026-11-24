use click::surface::ProgramInputs;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use crate::git::{git_commit_id, git_repo_root, git_show};
#[cfg(test)]
use click::cli::load_target_inputs;
use click::cli::{
    LoadedTarget, RunLimits, SelectedProject, VerificationInput, containing_directory,
    load_sidecar_inputs, load_sidecar_inputs_for_verify, load_target_inputs_for_verify,
    looks_like_mdtest, looks_like_source_location, parse_duration, parse_source_location,
    parse_work_limit, select_sidecars, sidecar_project_root, source_refs, with_run_limits,
};
use click::instrumentation::VerificationPhase;
use click::languages::c::source as c_source;
use click::languages::c::target::CTarget;
use click::surface::source_display_name;
#[cfg(test)]
use click::surface::verify_c_sources;
use click::surface::{
    ClickError, ClickErrorKind, ClickProject, ProofRefusal, ProofSourceIndex,
    VerificationDiagnostic, VerificationOutcome, VerifiedProgramTheorem, accepted_proof_trace,
    c_incremental_selection, project_selected_proof_names, project_summary, selected_c_target,
    verify_c_project, verify_project_at, verify_project_functions, verify_project_theorem,
    verify_project_with_summary, verifying_source_paths, with_proof_trace,
};

const USAGE: &str = "\
usage: click verify [--checked-only] [--locked] [--work-limit <UNITS>] [--time-limit <DURATION>] <sidecar.click|mdtest.md>[:<line>:<column>]
       click verify [--checked-only] [--locked] --trace-proof <PROOF|PATH:LINE[:COLUMN]> [--trace-to <LINE[:COLUMN]>] <sidecar.click|mdtest.md>
       click verify [--checked-only] [--locked] [--work-limit <UNITS>] [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>

Compiler captures are refreshed when missing or stale. `--locked` uses
existing captures only and refuses missing or stale inputs.

Verifies proofs owned by the selected sidecar, or, when a one-based
:LINE:COLUMN suffix is supplied, only the proof unit containing that source
location. Imported declarations and unselected C function contracts are
assumptions; their proof bodies are not recursively selected.

`--checked-only` verifies with proof search disabled. Write the execution
steps and every obligation proof explicitly, as in a whole claim emitted by
`click expand`.

An mdtest is verified from its embedded ```c or ```cpp and ```click blocks,
prepared exactly as the mdtests gate prepares them. Locations are lines of
the markdown file. Verify reports the proof outcome itself; it does not
consult the ```expect block, so an expected-failure mdtest exits nonzero.

Given a directory, verifies every sidecar in it: either the project directory
itself when it holds sidecars, or each immediate subdirectory that does. This
is the command to run after applying an expansion emitted by `click expand`.

Verdicts are deterministic: every tactic has a per-class work budget, and each
selected sidecar, mdtest, or proof unit has a whole-run budget of
`--work-limit` units (default 50000000). The same source spends the same
units on any machine under any load. `--time-limit` (default 10m) is only a
wall-clock crash-containment bound for a hung or CPU-starved run; a run it
stops says so, and that is not a verdict about the proof.

`--trace-proof PROOF` verifies one C function, theorem, or user-defined tactic of the
sidecar (or `program.termination` for program closing), by name or by a PATH:LINE[:COLUMN] of the sidecar that a claim of
it covers, and shows checked fact and resource changes on the path to
the failing tactic, or an accepted path when the proof succeeds. `--trace-to`
selects a written tactic by source line (and column when the line has several
tactics) within the selected proof.
A verification refusal suggests this command when Click can locate the failing proof.

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
    locked: bool,
    limits: RunLimits,
    changed_since: Option<String>,
    explain: bool,
    allow_sorry: bool,
    checked_only: bool,
    trace_proof: Option<String>,
    trace_to: Option<TraceTo>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TraceTo {
    line: usize,
    column: Option<usize>,
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
    if arguments.trace_to.is_some() && arguments.trace_proof.is_none() {
        return Err("`--trace-to` requires `--trace-proof`".to_string());
    }
    if arguments.checked_only {
        if arguments.allow_sorry || arguments.changed_since.is_some() {
            return Err("`--checked-only` requires fresh verification without `--allow-sorry` or `--changed-since`".to_string());
        }
        if !looks_like_source_location(&arguments.target) {
            return click::surface::without_proof_search(|| run(arguments));
        }
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
        return verify_changed(path, revision, arguments.limits, arguments.explain);
    }
    if arguments.explain {
        return Err("`--explain` requires `--changed-since`".to_string());
    }
    if looks_like_source_location(&arguments.target) {
        let (click_path, line, column) = parse_source_location(&arguments.target)?;
        return verify_location(
            &click_path,
            line,
            column,
            arguments.limits,
            arguments.locked,
            arguments.checked_only,
        );
    }
    let path = Path::new(&arguments.target);
    if path.is_dir() {
        verify_directory(path, arguments.limits, arguments.locked)
    } else {
        let project_root = sidecar_project_root(path)?;
        verify_file(
            path,
            arguments.limits,
            Some(&project_root),
            arguments.trace_proof.as_deref(),
            arguments.trace_to.as_ref(),
            arguments.locked,
        )
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut target = None;
    let mut locked = false;
    let mut limits = RunLimits::verify();
    let mut changed_since = None;
    let mut explain = false;
    let mut allow_sorry = false;
    let mut checked_only = false;
    let mut trace_proof = None;
    let mut trace_to = None;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if parse_options && argument == "--locked" {
            locked = true;
        } else if parse_options && argument == "--time-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            limits.time = parse_duration(&value)?;
        } else if parse_options && argument == "--work-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing unit count after `--work-limit`\n{USAGE}"))?;
            limits.work = parse_work_limit(&value)?;
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
        } else if parse_options && argument == "--checked-only" {
            checked_only = true;
        } else if parse_options && argument == "--allow-sorry" {
            allow_sorry = true;
        } else if parse_options && argument == "--trace-proof" {
            if trace_proof.is_some() {
                return Err("`--trace-proof` may only be supplied once".to_string());
            }
            trace_proof = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing proof name after `--trace-proof`\n{USAGE}"))?,
            );
        } else if parse_options && argument == "--trace-to" {
            if trace_to.is_some() {
                return Err("`--trace-to` may only be supplied once".to_string());
            }
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing source location after `--trace-to`\n{USAGE}"))?;
            let (line, column) = value
                .split_once(':')
                .map_or((value.as_str(), None), |(line, column)| {
                    (line, Some(column))
                });
            let line = line
                .parse::<usize>()
                .ok()
                .filter(|line| *line > 0)
                .ok_or_else(|| "`--trace-to` needs a positive LINE[:COLUMN]".to_string())?;
            let column = column
                .map(|column| {
                    column
                        .parse::<usize>()
                        .ok()
                        .filter(|column| *column > 0)
                        .ok_or_else(|| "`--trace-to` needs a positive LINE[:COLUMN]".to_string())
                })
                .transpose()?;
            trace_to = Some(TraceTo { line, column });
        } else if parse_options && argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else if target.replace(argument).is_some() {
            return Err(USAGE.to_string());
        }
    }
    Ok(Arguments {
        locked,
        target: target.ok_or_else(|| USAGE.to_string())?,
        limits,
        changed_since,
        explain,
        allow_sorry,
        checked_only,
        trace_proof,
        trace_to,
    })
}

fn resolve_trace_target(
    index: &ProofSourceIndex,
    line_offset: usize,
    target: &TraceTo,
) -> Result<click::surface::SourcePosition, String> {
    let line = target
        .line
        .checked_sub(line_offset)
        .filter(|line| *line > 0)
        .ok_or_else(|| format!("tactic@{} is outside the Click source", target.line))?;
    let starts = index.starts_on_line(line);
    let selected = match target.column {
        Some(column) => starts
            .into_iter()
            .find(|position| position.column == column)
            .ok_or_else(|| {
                format!(
                    "no written tactic starts at tactic@{}:{column}",
                    target.line
                )
            })?,
        None => match starts.as_slice() {
            [position] => position.clone(),
            [] => {
                return Err(format!(
                    "no written tactic starts at tactic@{}",
                    target.line
                ));
            }
            _ => {
                let outer = starts
                    .iter()
                    .filter(|position| !index.line_has_multiple_starts(position).unwrap_or(true))
                    .collect::<Vec<_>>();
                match outer.as_slice() {
                    [position] => (*position).clone(),
                    _ => {
                        return Err(format!(
                            "several tactics start on line {}; use --trace-to LINE:COLUMN",
                            target.line
                        ));
                    }
                }
            }
        },
    };
    Ok(selected)
}

/// Verifies every sidecar under a project or examples directory, reporting
/// each one as it passes so a long run shows progress.
fn verify_directory(path: &Path, limits: RunLimits, locked: bool) -> Result<(), String> {
    let selection = select_sidecars(path)?;
    let sidecars = selection.sidecars().count();
    let projects = &selection.projects;
    for project in projects {
        reconcile_project_externs(project, path, limits, locked)?;
    }
    for project in projects {
        for sidecar in &project.sidecars {
            verify_file(sidecar, limits, Some(&project.root), None, None, locked)?;
            println!("verified {}", display_path(sidecar, path));
        }
    }
    println!(
        "verified {} sidecar{} in {} project{}",
        sidecars,
        plural(sidecars),
        projects.len(),
        plural(projects.len())
    );
    Ok(())
}

/// Refuses a project in which one sidecar assumes, through an `extern`
/// declaration, a function that a sibling sidecar's `verifying` source
/// defines.
///
/// Each sidecar is verified on its own, so nothing else compares the assumed
/// contract with the one the sibling verifies, and termination certification
/// ranks only calls whose callee has a body in the same sidecar: two sidecars
/// assuming each other's contracts would certify a pair of functions that
/// never return. Within one sidecar the same declaration is refused when the
/// sources are resolved ("external function `g` is also defined by a
/// `verifying` source"); this is that rule across the project's sidecars.
/// The remedy is the one the single-sidecar rule leaves: verify the defining
/// source in the declaring sidecar too, or put both in one sidecar. Only the
/// sources are read here; no proof runs before the project is known to be
/// reconcilable.
fn reconcile_project_externs(
    project: &SelectedProject,
    target: &Path,
    limits: RunLimits,
    locked: bool,
) -> Result<(), String> {
    if project.sidecars.len() < 2 {
        return Ok(());
    }
    let mut summaries = Vec::with_capacity(project.sidecars.len());
    for sidecar in &project.sidecars {
        let summary = with_run_limits("click verify", limits, || {
            let (_, project, inputs) = {
                let _phase = VerificationPhase::new("project loading");
                load_sidecar_inputs_for_verify(sidecar, Some(&project.root), locked)?
            };
            sidecar_summary(sidecar, &project, &inputs, 0)
        })?;
        summaries.push((sidecar.as_path(), summary));
    }
    for (sidecar, summary) in &summaries {
        for external in &summary.external_declarations {
            let Some((defining, source)) = summaries.iter().find_map(|(other, other_summary)| {
                (other != sidecar)
                    .then(|| other_summary.defined_functions.get(external))
                    .flatten()
                    .map(|source| (*other, source))
            }) else {
                continue;
            };
            return Err(format!(
                "`{}` declares `extern {external}`, but `{}` defines `{external}` in its verifying source `{source}`: a sidecar cannot assume a contract for a function this project verifies, because nothing reconciles the assumed contract with the verified one and a call into a sibling sidecar is not ranked for termination; verify `{source}` in `{}` as well, or move both into one sidecar",
                display_path(sidecar, target),
                display_path(defining, target),
                display_path(sidecar, target),
            ));
        }
    }
    Ok(())
}

fn verify_changed(
    path: &Path,
    revision: &str,
    limits: RunLimits,
    explain_only: bool,
) -> Result<(), String> {
    if looks_like_mdtest(path) {
        return Err(format!(
            "`--changed-since` selects sidecars from a git baseline and does not take an mdtest; run `click verify {}` without it",
            path.display()
        ));
    }
    let selection = select_sidecars(path)?;
    for project in &selection.projects {
        reconcile_project_externs(project, path, limits, true)?;
    }
    let mut sidecars = selection
        .projects
        .iter()
        .flat_map(|project| {
            project
                .sidecars
                .iter()
                .map(|sidecar| (sidecar.clone(), project.root.clone()))
        })
        .collect::<Vec<_>>();
    sidecars.sort();
    let repo = git_repo_root(path)?;
    let baseline_commit = git_commit_id(&repo, revision)?;

    let mut verified = 0usize;
    let mut skipped = 0usize;
    for (sidecar, project_root) in sidecars {
        let sidecar = fs::canonicalize(&sidecar)
            .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
        // Loading, selection, the dependency summary, and verification of
        // one sidecar all run inside that sidecar's limits.
        let outcome = with_run_limits("click verify", limits, || {
            verify_changed_sidecar(
                &sidecar,
                &project_root,
                &repo,
                &baseline_commit,
                revision,
                explain_only,
            )
        })?;
        match outcome {
            ChangedSidecar::Explained => {}
            ChangedSidecar::Skipped => skipped += 1,
            ChangedSidecar::Verified => {
                verified += 1;
                println!("  result: verified");
            }
        }
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

/// What `--changed-since` did with one sidecar.
enum ChangedSidecar {
    Explained,
    Skipped,
    Verified,
}

fn verify_changed_sidecar(
    sidecar: &Path,
    project_root: &Path,
    repo: &Path,
    baseline_commit: &str,
    revision: &str,
    explain_only: bool,
) -> Result<ChangedSidecar, String> {
    let (click_source, project, inputs) = {
        let _phase = VerificationPhase::new("project loading");
        load_sidecar_inputs(sidecar, Some(project_root))?
    };
    if inputs.is_prepared() {
        return Err(
            "`--changed-since` is not supported for compiler-prepared projects".to_string(),
        );
    }
    let sources = match &inputs {
        VerificationInput::Bundle(sources) => sources.clone(),
        VerificationInput::Prepared(_) | VerificationInput::PreparedProgram(_) => unreachable!(),
    };
    let refs = source_refs(&sources);
    let baseline_attested = has_full_verification_marker(
        repo,
        baseline_commit,
        sidecar,
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
            project_selected_proof_names(&project, &ProgramInputs::Bundle(refs.to_vec()))
                .map_err(|error| located_click_message(error, sidecar, &project, 0))?,
            Vec::new(),
        )
    } else if let Some((baseline_click, baseline_sources)) =
        load_baseline_sidecar(repo, baseline_commit, sidecar)?
    {
        let baseline_refs = source_refs(&baseline_sources);
        let selection =
            c_incremental_selection(&click_source, &refs, &baseline_click, &baseline_refs)
                .map_err(click_message)?;
        full_rebuild = selection.full_rebuild;
        reasons = selection.reasons;
        (selection.selected_functions, selection.reused_functions)
    } else {
        full_rebuild = true;
        reasons
            .push("sidecar or one of its declared C sources is absent at the baseline".to_string());
        (
            project_selected_proof_names(&project, &ProgramInputs::Bundle(refs.to_vec()))
                .map_err(|error| located_click_message(error, sidecar, &project, 0))?,
            Vec::new(),
        )
    };

    print_incremental_selection(
        sidecar,
        revision,
        &selected,
        &reused,
        &reasons,
        full_rebuild,
    );
    if explain_only {
        return Ok(ChangedSidecar::Explained);
    }
    if !full_rebuild && selected.is_empty() {
        return Ok(ChangedSidecar::Skipped);
    }
    let summary = {
        let _phase = VerificationPhase::new("external dependency summary");
        project_summary(&project, &ProgramInputs::Bundle(refs.to_vec()))
            .map_err(|error| located_click_message(error, sidecar, &project, 0))?
    };
    let verified_theorems = if full_rebuild {
        verify_c_project(&project, &refs)
    } else {
        verify_project_functions(
            &project,
            &ProgramInputs::Bundle(refs.to_vec()),
            selected.clone(),
        )
    }
    .map_err(|error| {
        verification_error_report(
            error.verification_diagnostic(),
            sidecar,
            false,
            &project,
            &inputs,
            0,
            None,
        )
    })?;
    print_assumptions(&summary.assumptions, &verified_theorems);
    if full_rebuild
        && project.modules().len() == 1
        && project.c_profile().is_none()
        && let Err(message) = record_full_verification(
            sidecar,
            &click_source,
            &sources,
            &[baseline_commit.to_string()],
        )
    {
        eprintln!("click-verify: warning: could not record incremental baseline: {message}");
    }
    Ok(ChangedSidecar::Verified)
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
    label_tactic_evidence(
        error.verification_diagnostic().outcome(),
        error.concise_report(),
    )
}

fn label_tactic_evidence(outcome: VerificationOutcome, report: String) -> String {
    if outcome != VerificationOutcome::TacticError {
        return report;
    }
    let mut result = String::with_capacity(report.len());
    for line in report.split_inclusive('\n') {
        let content = line.trim_start_matches(' ');
        if let Some(evidence) = content.strip_prefix("goal: ") {
            result.push_str(&line[..line.len() - content.len()]);
            result.push_str("required evidence: ");
            result.push_str(evidence);
        } else {
            result.push_str(line);
        }
    }
    result
}

/// Where the declaration a failure is about is written: the one the failure
/// records, or else the last name its message quotes that the source
/// declares. A check that fails outside the per-declaration pass still names
/// what it refused (``resource `cell` has fields``, ``in theorem `t` ``), and
/// the declaration it names is the source to show.
fn failure_declaration_position(
    error: &ClickError,
    report: &str,
    source: &str,
) -> Option<click::surface::SourcePosition> {
    let recorded = || {
        error.proof_declaration().and_then(|declaration| {
            click::surface::click_declaration_source_position(source, declaration)
        })
    };
    // A proof failure records the declaration it arose in. A declaration
    // check records only which declaration was being visited, which a check
    // made between visits does not update, so what its message names wins.
    if matches!(
        error.kind(),
        ClickErrorKind::Proof | ClickErrorKind::Unsupported
    ) && let Some(position) = recorded()
    {
        return Some(position);
    }
    report
        .split('`')
        .skip(1)
        .step_by(2)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .filter(|quoted| {
            !quoted.is_empty()
                && quoted
                    .chars()
                    .all(|character| character.is_alphanumeric() || character == '_')
        })
        .find_map(|name| click::surface::click_declaration_source_position(source, name))
        .or_else(recorded)
}

/// [`click_message`], followed by where the declaration the failure is about
/// is written when the failure records one. A declaration that fails its
/// checks is reported before any proof runs, so it has no tactic to show.
fn located_click_message(
    error: click::surface::ClickError,
    sidecar: &Path,
    project: &ClickProject,
    line_offset: usize,
) -> String {
    let mut report = error.concise_report();
    // A syntax error names its own line; a declaration its message quotes,
    // such as the contract a call map names, is not where it is.
    if error.kind() != ClickErrorKind::Syntax
        && let Some(source) = project.entry_source()
        && let Some(position) = failure_declaration_position(&error, &report, source)
        && let Some(excerpt) = source_excerpt(sidecar, source, &position, line_offset)
    {
        report.push_str("\n\n");
        report.push_str(&excerpt);
    }
    label_tactic_evidence(error.verification_diagnostic().outcome(), report)
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

fn verification_error_report(
    diagnostic: VerificationDiagnostic<'_>,
    sidecar: &Path,
    show_trace: bool,
    project: &ClickProject,
    inputs: &VerificationInput,
    line_offset: usize,
    trace_target: Option<&click::surface::SourcePosition>,
) -> String {
    let error = diagnostic.error();
    let outcome = diagnostic.outcome();
    let (mut report, mut context) = diagnostic.concise_report_parts();
    let source_locations = ProofSourceLocations::new(project, inputs);
    let implicit_tactic_error = error.implicit_tactic_step().is_some();
    let failure_position = if implicit_tactic_error {
        None
    } else {
        error
            .proof_source_site()
            .and_then(|(claim, path)| source_locations.position(claim, path))
    };
    let written_tactic = project
        .entry_source()
        .zip(failure_position.as_ref())
        .and_then(|(source, position)| {
            source_locations
                .with_index(|index| {
                    index
                        .tactic_text(source, position)
                        .ok()
                        .map(|(tactic, _)| tactic.to_owned())
                })
                .flatten()
        });
    if let Some(source) = project.entry_source()
        && let Some(position) = failure_position.as_ref()
    {
        let mut has_full_tactic = false;
        if let Some(formatted) = source_locations.format_tactic(source, position, line_offset) {
            if let Some(index) = context.iter().position(|line| line.starts_with("tactic: ")) {
                context[index] = formatted;
            } else {
                context.insert(0, formatted);
            }
            has_full_tactic = true;
        }
        if !has_full_tactic
            && let Some(excerpt) = source_excerpt(sidecar, source, position, line_offset)
        {
            // The excerpt locates the tactic line it follows, ahead of the goal.
            match context.iter().position(|line| line.starts_with("tactic: ")) {
                Some(index) => context.insert(index + 1, excerpt),
                None => context.push(excerpt),
            }
        }
    }
    if context.is_empty()
        || !context
            .iter()
            .any(|line| line.starts_with("tactic@") || line.starts_with("  --> "))
    {
        // No tactic of the proof could be shown. A failure that knows its
        // declaration, or at least its claim, shows where that is written.
        let declaration = error.proof_declaration().or_else(|| {
            error
                .proof_claim_label()
                .and_then(|claim| claim.split_once('.'))
                .map(|(declaration, _)| declaration)
        });
        if matches!(
            error.kind(),
            ClickErrorKind::Proof | ClickErrorKind::Type | ClickErrorKind::Unsupported
        ) && let Some(source) = project.entry_source()
            && let Some(position) = declaration
                .filter(|_| {
                    matches!(
                        error.kind(),
                        ClickErrorKind::Proof | ClickErrorKind::Unsupported
                    )
                })
                .and_then(|declaration| {
                    click::surface::click_declaration_source_position(source, declaration)
                })
                // A failure that names a C statement is located already; one
                // that names nothing else shows the declaration it quotes.
                .or_else(|| {
                    (!report.contains("C statement at"))
                        .then(|| failure_declaration_position(error, &report, source))
                        .flatten()
                })
            && let Some(excerpt) = source_excerpt(sidecar, source, &position, line_offset)
        {
            context.push(excerpt);
        }
    }
    if error.kind() == ClickErrorKind::Proof && !implicit_tactic_error {
        context.extend(refusal_class_lines(
            written_tactic.as_deref(),
            error.proof_refusal(),
        ));
    }
    if !context.is_empty() {
        report.push_str("\n\n");
        report.push_str(&context.join("\n"));
    }
    if show_trace {
        let target = trace_target.cloned().or(failure_position);
        let positions = RefCell::new(HashMap::<
            Vec<usize>,
            Option<(String, click::surface::SourcePosition)>,
        >::new());
        let tactic_location = |path: &[usize]| {
            if let Some(cached) = positions.borrow().get(path) {
                return cached.clone();
            }
            let label = error.proof_claim_label().and_then(|claim| {
                let position = source_locations.position(claim, path)?;
                let multiple = source_locations
                    .with_index(|index| index.line_has_multiple_starts(&position).unwrap_or(true))
                    .unwrap_or(true);
                let line = position.line + line_offset;
                let label = if multiple {
                    format!("tactic@{line}:{}", position.column)
                } else {
                    format!("tactic@{line}")
                };
                Some((label, position))
            });
            positions.borrow_mut().insert(path.to_vec(), label.clone());
            label
        };
        let branch_arm = |path: &[usize], target: &click::surface::SourcePosition| {
            let claim = error.proof_claim_label()?;
            let branch = source_locations.position(claim, path)?;
            source_locations
                .with_index(|index| index.arm_containing(&branch, target).ok().flatten())
                .flatten()
        };
        let have_body_contains = |path: &[usize], target: &click::surface::SourcePosition| {
            let Some(claim) = error.proof_claim_label() else {
                return false;
            };
            let Some(have) = source_locations.position(claim, path) else {
                return false;
            };
            source_locations
                .with_index(|index| index.have_body_contains(&have, target).unwrap_or(false))
                .unwrap_or(false)
        };
        if let Some(trace) = error.trace_context_report_with_tactic_locations(
            &tactic_location,
            &branch_arm,
            &have_body_contains,
            target.as_ref(),
        ) {
            report.push_str("\n\n");
            report.push_str(&trace);
            if let Some(formatted) = target.as_ref().and_then(|position| {
                project.entry_source().and_then(|source| {
                    source_locations.format_tactic(source, position, line_offset)
                })
            }) {
                report.push_str("\n\n");
                report.push_str(&formatted);
            }
        } else {
            report.push_str(
                "\n\nproof trace unavailable: no checked path was retained for this failure",
            );
        }
        return label_tactic_evidence(outcome, report);
    }
    // The hint is printed only for a command that `--trace-proof` accepts:
    // both resolve the name through `trace_unit`.
    if matches!(
        error.kind(),
        ClickErrorKind::Proof | ClickErrorKind::Unsupported | ClickErrorKind::Internal
    ) && let Some(declaration) = error.proof_claim_label().and_then(|claim| {
        if claim == "program.termination" {
            Some(claim)
        } else {
            claim.split_once('.').map(|(declaration, _)| declaration)
        }
    }) && let Ok(unit) = trace_unit(declaration, project, inputs)
    {
        report.push_str(&format!(
            "\n\nTo get a trace:\n  click verify --trace-proof {} {}",
            shell_word(unit.name()),
            shell_word(&sidecar.display().to_string())
        ));
    }
    click::surface::bound_diagnostic_message(label_tactic_evidence(outcome, report))
}

/// What refused a proof step, by class, and the `click docs` entry that
/// documents it. A C statement's open requirement is proved by the implicit
/// `solve` when no smart tactic reached the statement, so its refusal is a
/// smart miss even under a written `step()`. A smart form that elides an
/// argument, such as `apply(t(x))`, refuses by a search miss: the fix is to
/// write the argument. An incomplete proof reports the open requirement so
/// the proof author can finish the script.
fn refusal_class_lines(written: Option<&str>, refusal: Option<ProofRefusal>) -> Vec<String> {
    if refusal == Some(ProofRefusal::IncompleteProof) {
        return vec![
            "help: establish the reported requirement before the proof closes".to_owned(),
            "see: click docs tracing".to_owned(),
        ];
    }
    let written_text = written;
    let written = written.and_then(click::docs::written_tactic_class);
    if refusal == Some(ProofRefusal::ImplicitStatementSearch) {
        let smart = click::docs::TacticClass::Smart;
        return vec![
            format!(
                "refused by: the implicit closer that proves this statement's requirements ({}: {})",
                smart.label(),
                smart.refusal_meaning()
            ),
            "see: click docs tracing".to_owned(),
        ];
    }
    let Some((name, class)) = written else {
        return Vec::new();
    };
    use click::docs::TacticClass::{Simple, Smart};
    let meaning = match (refusal, class) {
        (Some(ProofRefusal::UnsuccessfulSearch), _)
            if written_text.is_some_and(click::docs::written_tactic_elides_argument) =>
        {
            Some(click::docs::SEARCH_MISS_MEANING)
        }
        (Some(ProofRefusal::Tactic), Simple) | (Some(ProofRefusal::UnsuccessfulSearch), Smart) => {
            Some(class.refusal_meaning())
        }
        _ => None,
    };
    let mut lines = Vec::new();
    if let Some(meaning) = meaning {
        lines.push(format!(
            "refused by: `{name}` ({}: {meaning})",
            class.label()
        ));
    }
    lines.push(format!("see: click docs {name}"));
    lines
}

/// The one proof unit `--trace-proof` verifies and traces.
enum TraceUnit {
    Function(String),
    Theorem(String),
    Tactic(String),
    ProgramTermination,
}

impl TraceUnit {
    fn name(&self) -> &str {
        match self {
            Self::Function(name) | Self::Theorem(name) | Self::Tactic(name) => name,
            Self::ProgramTermination => "program.termination",
        }
    }
}

/// Resolves a `--trace-proof` argument against the proofs the sidecar
/// selects: a function, theorem, or user-defined tactic, by name. Validation
/// refuses duplicate proof names, so the name alone identifies the proof.
/// The error says why the name cannot be traced.
fn trace_unit(
    requested: &str,
    project: &ClickProject,
    inputs: &VerificationInput,
) -> Result<TraceUnit, String> {
    let names =
        project_selected_proof_names(project, &inputs.program_inputs()).map_err(click_message)?;
    select_trace_unit(requested, &names)
}

/// Selects `requested` among the sidecar's selected proof names.
fn select_trace_unit(requested: &str, names: &[String]) -> Result<TraceUnit, String> {
    if requested == "program.termination" {
        return Ok(TraceUnit::ProgramTermination);
    }
    // A Rust item or a C++ declaration is named by its path, `quad::walk` or
    // `Square::area`, or by the name the importer gives it.
    let selects = |kind: &str, name: &str| {
        names.iter().find_map(|selected| {
            let selected = selected.strip_prefix(kind)?.strip_prefix(':')?;
            (selected == name || source_display_name(selected).as_deref() == Some(name))
                .then(|| selected.to_owned())
        })
    };
    if let Some(function) = selects("function", requested) {
        Ok(TraceUnit::Function(function))
    } else if let Some(theorem) = selects("theorem", requested) {
        Ok(TraceUnit::Theorem(theorem))
    } else if let Some(tactic) = selects("tactic", requested) {
        Ok(TraceUnit::Tactic(tactic))
    } else {
        Err(format!("`{requested}` is not a selected proof"))
    }
}

fn format_source_tactic(
    tactic: &str,
    source_indent: &str,
    line: usize,
    column: Option<usize>,
) -> String {
    let location = column.map_or_else(
        || format!("tactic@{line}"),
        |column| format!("tactic@{line}:{column}"),
    );
    let mut report = format!("{location}:");
    let line_count = tactic.lines().count();
    for (index, line) in tactic.lines().enumerate() {
        if line_count > 10 && (8..line_count - 2).contains(&index) {
            if index == 8 {
                report.push_str(&format!("\n  … {} source lines omitted", line_count - 10));
            }
            continue;
        }
        report.push_str("\n  ");
        let line = if index == 0 {
            line
        } else {
            line.strip_prefix(source_indent).unwrap_or(line)
        };
        let mut characters = line.chars();
        report.extend(characters.by_ref().take(160));
        if characters.next().is_some() {
            report.push('…');
        }
    }
    report
}

fn format_source_tactic_at_position(
    index: &ProofSourceIndex,
    source: &str,
    position: &click::surface::SourcePosition,
    line_offset: usize,
) -> Option<String> {
    let (tactic, indent) = index.tactic_text(source, position).ok()?;
    let multiple = index.line_has_multiple_starts(position).unwrap_or(true);
    Some(format_source_tactic(
        tactic,
        indent,
        position.line + line_offset,
        multiple.then_some(position.column),
    ))
}

/// Resolve a claim's enclosing tactic locations together. A trace walks
/// many distinct steps in the same proof; neither valid nor missing indices
/// should parse and resolve the project again.
struct ProofSourceLocations<'a> {
    project: &'a ClickProject,
    inputs: &'a VerificationInput,
    outer: RefCell<HashMap<String, Option<Vec<click::surface::SourcePosition>>>>,
    index: RefCell<Option<Option<ProofSourceIndex>>>,
}

impl<'a> ProofSourceLocations<'a> {
    fn format_tactic(
        &self,
        source: &str,
        position: &click::surface::SourcePosition,
        line_offset: usize,
    ) -> Option<String> {
        self.with_index(|index| {
            format_source_tactic_at_position(index, source, position, line_offset)
        })
        .flatten()
    }

    /// Queries the entry module's index, built once from its verification
    /// parse.
    fn with_index<T>(&self, query: impl FnOnce(&ProofSourceIndex) -> T) -> Option<T> {
        if self.index.borrow().is_none() {
            *self.index.borrow_mut() = Some(
                ProofSourceIndex::for_project(self.project, &self.inputs.program_inputs()).ok(),
            );
        }
        self.index.borrow().as_ref()?.as_ref().map(query)
    }

    fn new(project: &'a ClickProject, inputs: &'a VerificationInput) -> Self {
        Self {
            project,
            inputs,
            outer: RefCell::new(HashMap::new()),
            index: RefCell::new(None),
        }
    }

    fn position(&self, claim: &str, path: &[usize]) -> Option<click::surface::SourcePosition> {
        let source_index = *path.first()?;
        let key = claim.to_owned();
        if !self.outer.borrow().contains_key(&key) {
            let outer = self
                .with_index(|index| index.project_tactic_positions(self.project, claim).ok())
                .flatten();
            self.outer.borrow_mut().insert(key.clone(), outer);
        }
        let outer = self
            .outer
            .borrow()
            .get(&key)?
            .as_ref()?
            .get(source_index)?
            .clone();
        // A nested tactic that is not written (the omitted body of
        // `have P;`) has no source; its failure is located at the nearest
        // enclosing tactic that is.
        (2..=path.len())
            .rev()
            .find_map(|end| {
                self.with_index(|index| index.nested_position(&outer, &path[1..end]).ok())
                    .flatten()
            })
            .or(Some(outer))
    }
}

fn source_excerpt(
    sidecar: &Path,
    source: &str,
    position: &click::surface::SourcePosition,
    line_offset: usize,
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
    // An mdtest reports lines of the markdown file, not of its Click block.
    let file_line = position.line + line_offset;
    let width = file_line.to_string().len();
    Some(format!(
        "  --> {}:{}:{}\n  {:width$} | {}{}{}\n  {:width$} | {}{}",
        sidecar.display(),
        file_line,
        position.column,
        file_line,
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
            let failed = |error: std::io::Error| {
                format!(
                    "failed to fingerprint Click executable `{}`: {error}",
                    executable.display()
                )
            };
            // Stream the executable through the hasher: a debug or profiling
            // build is hundreds of megabytes, and reading it whole made it
            // the largest allocation of a directory verification.
            let mut file = fs::File::open(&executable).map_err(failed)?;
            let mut hasher = DefaultHasher::new();
            let mut chunk = vec![0; 1 << 20];
            loop {
                let read = file.read(&mut chunk).map_err(failed)?;
                if read == 0 {
                    break;
                }
                hasher.write(&chunk[..read]);
            }
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

/// Compare the commit's complete input bundle with the state that was
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
/// state. Re-reading the working tree here could certify a different
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

fn load_baseline_sidecar(
    repo: &Path,
    revision: &str,
    click_path: &Path,
) -> Result<Option<LoadedSidecar>, String> {
    let Some(click_source) = git_show(repo, revision, click_path)? else {
        return Ok(None);
    };
    let parent = containing_directory(click_path);
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
    limits: RunLimits,
    project_root: Option<&Path>,
    trace_proof: Option<&str>,
    trace_to: Option<&TraceTo>,
    locked: bool,
) -> Result<(), String> {
    // A previous failed sidecar may have left admissions behind; each file
    // reports only its own.
    let _ = click::surface::take_sorry_admissions();
    // Every phase of the run, from loading its sources and building the
    // external-dependency summary to counting its selected proofs, runs
    // inside the run's work budget and crash-containment bound.
    with_run_limits("click verify", limits, || {
        verify_file_within_limits(click_path, project_root, trace_proof, trace_to, locked)
    })
}

/// The external-dependency summary of one loaded sidecar, from one resolution
/// of its sources.
fn sidecar_summary(
    click_path: &Path,
    project: &ClickProject,
    inputs: &VerificationInput,
    line_offset: usize,
) -> Result<click::surface::ProjectVerificationSummary, String> {
    let _phase = VerificationPhase::new("external dependency summary");
    project_summary(project, &inputs.program_inputs())
        .map_err(|error| located_click_message(error, click_path, project, line_offset))
}

fn verify_file_within_limits(
    click_path: &Path,
    project_root: Option<&Path>,
    trace_proof: Option<&str>,
    trace_to: Option<&TraceTo>,
    locked: bool,
) -> Result<(), String> {
    let target = {
        let _phase = VerificationPhase::new("project loading");
        load_target_inputs_for_verify(click_path, project_root, locked)?
    };
    let line_offset = target.line_offset();
    let LoadedTarget {
        click_source,
        project,
        inputs,
        mdtest,
    } = target;
    // `--trace-proof FILE:LINE[:COLUMN]` traces the proof unit that owns the
    // claim covering that line.
    let trace_proof = trace_proof
        .map(|requested| {
            match click::cli::claim_at_argument(
                requested,
                click_path,
                line_offset,
                Some(&project),
                &click_source,
                &inputs,
                // Only the owner is traced, so no loop phase is resolved.
                click::surface::ClaimLocationScope::ProofUnit,
            ) {
                Some(claim) => claim.map(|claim| claim.owner),
                None => Ok(requested.to_string()),
            }
        })
        .transpose()?;
    let trace_proof = trace_proof.as_deref();
    let trace_unit = trace_proof
        .map(|requested| {
            // A sidecar that fails to load reports that failure as an
            // untraced run would; only an unknown name gets the usage hint.
            let names = project_selected_proof_names(&project, &inputs.program_inputs())
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?;
            select_trace_unit(requested, &names).map_err(|message| {
                format!(
                    "{message} in `{}`; `--trace-proof` takes the name of a function, theorem, or user-defined tactic the sidecar proves",
                    click_path.display()
                )
            })
        })
        .transpose()?;
    let trace_target = trace_to
        .map(|target| {
            let index = ProofSourceIndex::for_project(&project, &inputs.program_inputs())
                .map_err(click_message)?;
            resolve_trace_target(&index, line_offset, target)
        })
        .transpose()?;
    // An untraced run takes its summary from the verification's own
    // resolution of the sources; a traced one summarizes separately.
    let (summary, untraced) = match &trace_unit {
        Some(_) => (
            sidecar_summary(click_path, &project, &inputs, line_offset)?,
            None,
        ),
        None => {
            let summarized = verify_project_with_summary(&project, &inputs.program_inputs());
            let (summary, verified) = summarized
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?;
            (summary, Some(verified))
        }
    };
    let (verified, successful_trace) = {
        let run_traced = |unit: &TraceUnit| match unit {
            TraceUnit::Function(function) | TraceUnit::Tactic(function) => {
                verify_project_functions(&project, &inputs.program_inputs(), [function.clone()])
            }
            TraceUnit::Theorem(theorem) => {
                verify_project_theorem(&project, &inputs.program_inputs(), theorem)
            }
            TraceUnit::ProgramTermination => {
                verify_project_with_summary(&project, &inputs.program_inputs())
                    .and_then(|(_, verified)| verified)
            }
        };
        let report = |error: ClickError| {
            verification_error_report(
                error.verification_diagnostic(),
                click_path,
                trace_proof.is_some(),
                &project,
                &inputs,
                line_offset,
                trace_target.as_ref(),
            )
        };
        match &trace_unit {
            Some(unit) => with_proof_trace(unit.name(), || {
                let verified = run_traced(unit).map_err(report)?;
                // The renderer asks for one step's location several times.
                let source_locations = ProofSourceLocations::new(&project, &inputs);
                let located = RefCell::new(HashMap::<
                    (String, Vec<usize>),
                    Option<(String, click::surface::SourcePosition)>,
                >::new());
                let locate = |claim: &str, path: &[usize]| {
                    let key = (claim.to_owned(), path.to_vec());
                    if let Some(cached) = located.borrow().get(&key) {
                        return cached.clone();
                    }
                    let label = (|| {
                        let position = source_locations.position(claim, path)?;
                        let multiple = source_locations
                            .with_index(|index| index.line_has_multiple_starts(&position).ok())
                            .flatten()?;
                        let line = position.line + line_offset;
                        let label = if multiple {
                            format!("tactic@{line}:{}", position.column)
                        } else {
                            format!("tactic@{line}")
                        };
                        Some((label, position))
                    })();
                    located.borrow_mut().insert(key, label.clone());
                    label
                };
                let arm = |claim: &str, path: &[usize], target: &click::surface::SourcePosition| {
                    let branch = source_locations.position(claim, path)?;
                    source_locations
                        .with_index(|index| index.arm_containing(&branch, target).ok().flatten())
                        .flatten()
                };
                let body =
                    |claim: &str, path: &[usize], target: &click::surface::SourcePosition| {
                        let Some(have) = source_locations.position(claim, path) else {
                            return false;
                        };
                        source_locations
                            .with_index(|index| {
                                index.have_body_contains(&have, target).unwrap_or(false)
                            })
                            .unwrap_or(false)
                    };
                let trace = accepted_proof_trace(&locate, &arm, &body, trace_target.as_ref()).map(
                    |mut trace| {
                        if let Some(formatted) = trace_target.as_ref().and_then(|position| {
                            source_locations.format_tactic(&click_source, position, line_offset)
                        }) {
                            trace.push_str("\n\n");
                            trace.push_str(&formatted);
                        }
                        trace
                    },
                );
                Ok((verified, trace))
            }),
            None => untraced
                .expect("an untraced run verified with its summary")
                .map(|verified| (verified, None))
                .map_err(report),
        }
    }?;
    if trace_proof.is_some() {
        let trace = successful_trace.ok_or_else(|| {
            trace_to.map_or_else(
                || "verified proof has no retained checked path to trace".to_owned(),
                |target| {
                    format!(
                        "tactic@{} has no recorded checked step on an accepted path",
                        target.line
                    )
                },
            )
        })?;
        println!("{trace}\n");
    }
    print_assumptions(&summary.assumptions, &verified);
    // The count comes from the summary's resolution of the sources, so
    // reporting it does not parse every source again after verification.
    let selected = if trace_proof.is_some() {
        1
    } else {
        summary.selected_proof_count
    };
    println!("{selected} selected proof{} verified", plural(selected));
    let admissions = click::surface::take_sorry_admissions();
    if admissions.is_empty() {
        if let VerificationInput::Bundle(sources) = &inputs
            && trace_proof.is_none()
            && mdtest.is_none()
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
    limits: RunLimits,
    locked: bool,
    checked_only: bool,
) -> Result<(), String> {
    // As in `verify_file`, loading is inside the run's limits.
    with_run_limits("click verify", limits, || {
        verify_location_within_limits(click_path, line, column, locked, checked_only)
    })
}

fn verify_location_within_limits(
    click_path: &Path,
    line: usize,
    column: usize,
    locked: bool,
    checked_only: bool,
) -> Result<(), String> {
    let project_root = sidecar_project_root(click_path)?;
    let target = {
        let _phase = VerificationPhase::new("project loading");
        load_target_inputs_for_verify(click_path, Some(&project_root), locked)?
    };
    let line_offset = target.line_offset();
    // An mdtest location names a line of the markdown file; the verifier
    // selects by lines of the extracted Click block.
    let line = match &target.mdtest {
        Some(mdtest) => mdtest
            .click_line(line)
            .map_err(|error| format!("`{}:{line}:{column}`: {error}", click_path.display()))?,
        None => line,
    };
    let LoadedTarget {
        click_source,
        project,
        inputs,
        ..
    } = target;
    let summary = {
        let _phase = VerificationPhase::new("external dependency summary");
        project_summary(&project, &inputs.program_inputs())
            .map_err(|error| located_click_message(error, click_path, &project, line_offset))?
    };
    let verify = || {
        let result = verify_project_at(&project, &inputs.program_inputs(), line, column);
        result.map_err(|error| {
            verification_error_report(
                error.verification_diagnostic(),
                click_path,
                false,
                &project,
                &inputs,
                line_offset,
                None,
            )
        })
    };
    let verified = if checked_only {
        let selected = click::surface::claim_at(
            Some(&project),
            &click_source,
            &inputs.program_inputs(),
            line,
            Some(column),
            click::surface::ClaimLocationScope::ProofUnit,
        )
        .map_err(|error| error.reason)?;
        click::surface::without_proof_search_for_claim(&selected.label, verify)?
    } else {
        verify()?
    };
    print_assumptions(&summary.assumptions, &verified);
    println!("1 selected proof verified");
    Ok(())
}

/// The one assumption report: each verified function's library interfaces and
/// `extern` contracts, by family, after the thread runtime the whole
/// verification assumes.
fn print_assumptions(
    assumptions: &BTreeMap<String, Vec<click::surface::ModelAssumption>>,
    verified: &[VerifiedProgramTheorem],
) {
    if let Some(selection) = verified
        .first()
        .and_then(|theorem| theorem.selection.as_ref())
    {
        for assumption in &selection.runtime_assumptions {
            println!("assumptions: every function -> runtime: {assumption}");
        }
    }
    let verified_functions = verified
        .iter()
        .map(|theorem| theorem.function_block.signature().name())
        .collect::<std::collections::BTreeSet<_>>();
    for (function, assumed) in assumptions {
        if verified_functions.contains(function.as_str()) {
            // An imported name reads as its source language spells it.
            let line = format!("assumptions: {function} -> {}", render_assumptions(assumed));
            println!("{}", click::surface::display_source_names(&line));
        }
    }
}

/// `C library: strlen; allocator: free, malloc`: the names of each family,
/// in the order the summary sorted them.
fn render_assumptions(assumed: &[click::surface::ModelAssumption]) -> String {
    let mut groups = Vec::<(click::surface::ModelFamily, Vec<String>)>::new();
    for assumption in assumed {
        match groups.last_mut() {
            Some((family, names)) if *family == assumption.family => {
                names.push(assumption.display());
            }
            _ => groups.push((assumption.family, vec![assumption.display()])),
        }
    }
    groups
        .iter()
        .map(|(family, names)| format!("{}: {}", family.label(), names.join(", ")))
        .collect::<Vec<_>>()
        .join("; ")
}

#[cfg(test)]
#[path = "click-verify/incremental_tests.rs"]
mod incremental_tests;

#[cfg(test)]
#[path = "click-verify/directory_tests.rs"]
mod directory_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn program_termination_trace_selects_the_ordinary_root() {
        let (root, path) = temporary_project(
            "termination-trace",
            "int32 leaf(void) { return 7; }",
            "verifying \"program.c\"; int32 leaf() { ensures result == 7; }",
        );
        entry_with([
            "--trace-proof".to_string(),
            "program.termination".to_string(),
            path.display().to_string(),
        ])
        .expect("program termination retains its checked path for CLI tracing");
        fs::write(&path, "verifying \"program.c\"; int32 leaf() { ensures result == 7; } termination by { check_termination_component(\"leaf\", normal); close(); }").unwrap();
        let error = entry_with([path.display().to_string()]).unwrap_err();
        assert!(
            error.contains("--trace-proof program.termination"),
            "{error}"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn ordinary_cli_diagnostics_bound_late_source_and_trace_hint() {
        let name = format!(
            "oversized_{}",
            "n".repeat(click::surface::DEFAULT_DIAGNOSTIC_BYTE_LIMIT)
        );
        let source = format!("theorem {name}(x: Integer) {{ ensures x == 0 by {{ close(); }} }}");
        let (_root, path) = temporary_project("ordinary-byte-limit", "void f() {}", &source);
        let report = entry_with([path.display().to_string()]).expect_err("false theorem");
        assert!(report.len() <= click::surface::DEFAULT_DIAGNOSTIC_BYTE_LIMIT);
        assert!(report.starts_with("tactic error:"));
        assert!(report.contains("diagnostic truncated"));
    }

    #[test]
    fn source_tactic_excerpt_bounds_lines_and_unicode_width() {
        assert_eq!(
            format_source_tactic("loop {\n    step();\n  }", "  ", 7, Some(3)),
            "tactic@7:3:\n  loop {\n    step();\n  }"
        );
        let source = format!("loop {{\n{}\n}}", ("λ".repeat(400) + "\n").repeat(300));
        let report = format_source_tactic(&source, "", 7, None);
        assert!(report.contains("source lines omitted"));
        assert!(report.lines().count() <= 12);
        assert!(report.lines().all(|line| line.chars().count() <= 163));
        assert!(report.ends_with("\n  }"));
    }

    #[test]
    fn loop_entry_refusal_bounds_unexecuted_preservation_source() {
        let source = format!(
            "verifying \"program.c\";\nvoid loop_wall() {{ ensures 0 == 0; }} by {{\nstep_until(loop(0).entry);\nloop {{ invariant i == 1; maintain by {{\n{}step();\n}} }}\nstep_until(function.exit);\n}}",
            "have 0 == 0 by { normalize(); }\n".repeat(300)
        );
        let (root, path) = temporary_project(
            "loop-entry-excerpt",
            "void loop_wall() { int32 i = 0; while (i < 1) { i++; } }",
            &source,
        );
        let report = entry_with([path.display().to_string()])
            .expect_err("the false entry invariant must still be rejected");
        fs::remove_dir_all(root).unwrap();
        assert!(report.contains("loop 0 invariant 0 entry"), "{report}");
        assert!(report.contains("tactic@"), "{report}");
        assert!(report.contains("invariant i == 1"), "{report}");
        assert!(report.contains("source lines omitted"), "{report}");
        assert!(report.lines().count() <= 40, "{report}");
    }

    /// `have P;` has no written proof, so its search's site, the `have`'s
    /// body, is not in the source; the miss is located at the `have`, not
    /// at the function.
    #[test]
    fn an_omitted_have_proof_miss_is_located_at_the_have() {
        let (root, path) = temporary_project(
            "omitted-have-location",
            "int helper(void) { return 1; }\nint f(void) { int x; x = helper(); return x; }",
            "verifying \"program.c\";\nint32 helper() { ensures result == 1; }\nint32 f() { ensures result == 1; } by {\n    step();\n    step_until(statement(2).entry);\n    have x == 2;\n}",
        );
        let report = entry_with([path.display().to_string()]).expect_err("x is 1, not 2");
        fs::remove_dir_all(root).unwrap();
        assert!(report.contains("could not establish `x == 2`"), "{report}");
        assert!(report.contains("tactic@6:\n  have x == 2;"), "{report}");
        assert!(!report.contains("int32 f() { ensures"), "{report}");
    }

    fn assert_source_diagnostic(report: &str) {
        for internal in ["state#", "state<", "load A=", "pointer(pointer "] {
            assert!(!report.contains(internal), "{report}");
        }
        assert!(
            !report
                .split("value ")
                .skip(1)
                .any(|tail| { tail.as_bytes().first().is_some_and(u8::is_ascii_uppercase) }),
            "{report}"
        );
    }

    #[test]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn refused_transport_names_the_cell_and_prints_checked_effects() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_binder_instance_footprint_includes_its_memory.md");
        let report =
            entry_with([fixture.display().to_string()]).expect_err("the loop may write the cell");
        assert!(
            report.contains("effect facts relating states at this frontier"),
            "{report}"
        );
        assert!(report.contains("checked source (holds)"), "{report}");
        assert!(report.contains("checked target (wanted)"), "{report}");
        assert!(
            report.contains(
                "transport label definitions (shared by checked source, target, and effects)"
            ),
            "{report}"
        );
        assert!(report.contains("loop effect: may write"), "{report}");
        assert!(report.contains("store to occupied[start]"), "{report}");
        assert!(report.contains("i >= end"), "{report}");
        assert!(report.contains("at(pre, occupied[start])"), "{report}");
        assert!(!report.contains("lowered target"), "{report}");
        assert_eq!(
            report
                .matches("some effect facts have no exact Click spelling")
                .count(),
            0,
            "{report}"
        );
    }

    #[test]
    fn refused_call_result_fact_uses_the_proof_binding() {
        let (root, path) = temporary_project(
            "call-result-diagnostic",
            r#"
            extern int32 child(int32 x);
            int32 parent(int32 x) { return child(x); }
        "#,
            r#"
            verifying "program.c";
            theorem negative(n: int32) {
                requires n < 0;
                ensures n < 1 by { close(); }
            }
            extern int32 child(int32 x) {
                requires 0 <= x;
                ensures 0 <= result;
            }
            int32 parent(int32 x) {
                requires 0 <= x;
                ensures 0 <= result;
            } by {
                let { result: r } = step(child);
                have r < 1 by {
                    apply(negative(r));
                }
                step();
                close();
            }
        "#,
        );
        let result = entry_with([path.display().to_string()]);
        fs::remove_dir_all(root).unwrap();
        let report = result.expect_err("a nonnegative call result is not negative");
        assert_source_diagnostic(&report);
        assert!(report.contains("r < 0"), "{report}");
        assert!(
            report.contains("with n = r instantiates to r < 0"),
            "{report}"
        );
    }

    #[test]
    fn refused_match_arm_contradiction_reports_its_own_tactic() {
        for name in [
            "arm_contradiction_reports_its_source",
            "nested_arm_contradiction_reports_its_source",
            "bridged_arm_contradiction_reports_its_source",
            "arm_contradiction_after_loop_reports_its_source",
        ] {
            let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("mdtests/{name}.md"));
            let source = fs::read_to_string(&fixture).unwrap();
            let (line, tactic) = source
                .lines()
                .enumerate()
                .find(|(_, line)| {
                    line.trim()
                        .starts_with("contradiction(x.model == Cell::Present(")
                })
                .map(|(line, tactic)| (line + 1, tactic.trim()))
                .unwrap();
            let report = entry_with([fixture.display().to_string()])
                .expect_err("the constructor is not refuted");
            assert!(
                report.contains(&format!("tactic@{line}:")),
                "{name}: {report}"
            );
            assert!(report.contains(tactic), "{name}: {report}");
            assert!(
                report.contains("requires an exact fact and its negation"),
                "{name}: {report}"
            );
            assert!(
                report.contains("in match arm `Cell::Present`"),
                "{name}: {report}"
            );
        }
    }

    #[test]
    fn user_defined_tactic_trace_selects_its_own_checked_path() {
        let source = "verifying \"program.c\";\ntactic keep(x: int32) {\n    requires x == 3;\n    ensures x == 3;\n} by {\n    have x == 3 by { close(); }\n}\ntactic broken(x: int32) { ensures x == 4; } by { have x == 4 by { close(); } }\n";
        let (root, path) = temporary_project("tactic-trace", "void unused() {}", source);
        let loaded = load_target_inputs(&path, None).unwrap();
        assert!(matches!(
            trace_unit("keep", &loaded.project, &loaded.inputs).unwrap(),
            TraceUnit::Tactic(_)
        ));
        // Selection must not check the unrelated, invalid tactic.
        for selector in ["keep".to_owned(), format!("{}:6", path.display())] {
            entry_with([
                "--trace-proof".to_owned(),
                selector,
                "--trace-to".to_owned(),
                "6".to_owned(),
                path.display().to_string(),
            ])
            .expect("the selected tactic has an accepted trace at its written step");
        }
        let report = entry_with([
            "--trace-proof".to_owned(),
            "broken".to_owned(),
            path.display().to_string(),
        ])
        .expect_err("the selected tactic's false postcondition must fail");
        assert!(
            report.contains("proof trace (checked tactics and branch facts):"),
            "{report}"
        );
        assert!(report.contains("tactic@8"), "{report}");
        let ordinary = entry_with([path.display().to_string()]).unwrap_err();
        assert!(ordinary.contains("--trace-proof broken"), "{ordinary}");
        fs::write(root.join("library.click"),
            "tactic imported(x: int32) { requires x == 3; ensures x == 3; } by { have x == 3 by { close(); } }")
            .unwrap();
        fs::write(&path, format!("import \"library.click\";\n{source}")).unwrap();
        let imported = entry_with([
            "--trace-proof".to_owned(),
            "imported".to_owned(),
            path.display().to_string(),
        ])
        .expect_err("imported tactic bodies belong to the module that declares them");
        assert!(imported.contains("not a selected proof"), "{imported}");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn user_defined_tactic_trace_retains_constructor_arms() {
        let source = r#"verifying "program.c";
spec enum Choice { First, Second, Third }
resource choice() { field model: Choice; }
tactic choose() { owns x: choice(); ensures 0 == 0; } by {
    match x.model {
        Choice::First => {
            have 0 == 0 by { normalize(); }
        },
        Choice::Second => {
            have 0 == 0 by { normalize(); }
        },
        Choice::Third => {
            have 0 == 0 by { normalize(); }
        },
    }
}
"#;
        let (root, path) = temporary_project("tactic-match-trace", "void unused() {}", source);
        for line in [7, 10, 13] {
            entry_with([
                "--trace-proof".to_owned(),
                "choose".to_owned(),
                "--trace-to".to_owned(),
                line.to_string(),
                path.display().to_string(),
            ])
            .expect("every checked constructor arm retains its written steps");
        }
        fs::write(
            &path,
            source.replace(
                "Choice::Third => {\n            have 0 == 0",
                "Choice::Third => {\n            have 0 == 1",
            ),
        )
        .unwrap();
        let report = entry_with([
            "--trace-proof".to_owned(),
            "choose".to_owned(),
            path.display().to_string(),
        ])
        .unwrap_err();
        assert!(report.contains("Choice::Third arm"), "{report}");
        assert!(
            report.contains("proof trace (checked tactics and branch facts):"),
            "{report}"
        );
        let (_, trace) = report
            .split_once("proof trace (checked tactics and branch facts):")
            .unwrap();
        assert!(trace.contains("Choice::Third"), "{trace}");
        assert!(
            !trace.contains("Choice::First") && !trace.contains("Choice::Second"),
            "{trace}"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn declined_theorem_application_preserves_checked_trace() {
        let source = r#"verifying "program.c";
theorem positive(x: int32) { requires x > 0; ensures x > 0 by { close(); } }
void walk(int32 n) { requires n >= 0; ensures 0 == 0; } by {
    step(); step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        initialize by close();
        maintain by {
            have i >= 0 by { close(); }
            apply(positive(0));
            step();
        }
    }
    step(); normalize();
}
void plain(int32 n) { requires n >= 0; ensures 0 == 0; } by {
    have n >= 0 by { close(); }
    apply(positive(0));
    step_until(function.exit); normalize();
}
"#;
        let (root, path) = temporary_project(
            "declined-apply-trace",
            "void walk(int n) { int i = 0; while (i < n) { i++; } } void plain(int n) {}",
            source,
        );
        for (name, prior) in [("walk", "have i >= 0"), ("plain", "have n >= 0")] {
            let report = entry_with([
                "--trace-proof".to_owned(),
                name.to_owned(),
                path.display().to_string(),
            ])
            .expect_err("the false theorem premise remains rejected");
            assert!(
                report.contains("theorem `positive` has an unproved obligation")
                    && report.contains("`0 > 0`"),
                "{report}"
            );
            let (_, trace) = report
                .split_once("proof trace (checked tactics and branch facts):")
                .unwrap_or_else(|| panic!("missing checked prefix: {report}"));
            assert!(trace.contains(prior), "{trace}");
            assert!(!report.contains("proof trace unavailable"), "{report}");
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn completed_loop_trace_records_exported_facts_and_supports_trace_to() {
        let mut source = String::from(
            r#"verifying "program.c";
void walk(int32 n) { requires n == 12; ensures 0 == 0; } by {
    step(); step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
"#,
        );
        // The two base facts plus seven bounds export nine facts: the
        // smallest delta that detects the old eight-fact trace truncation.
        for bound in 1..=7 {
            source.push_str(&format!("        invariant i >= -{bound};\n"));
        }
        source.push_str(
            r#"        initialize by close();
        maintain by { step(); }
    }
    have 0 == 1 by { normalize(); }
    step_until(function.exit); close();
}
"#,
        );
        let (root, path) = temporary_project(
            "completed-loop-trace",
            "void walk(int n) { int i = 0; while (i < n) { i++; } }",
            &source,
        );
        for targeted in [false, true] {
            let mut args = vec!["--trace-proof".to_string(), "walk".to_string()];
            if targeted {
                args.extend(["--trace-to".to_string(), "4".to_string()]);
            }
            args.push(path.display().to_string());
            let report = entry_with(args).expect_err("the false post-loop fact remains rejected");
            assert!(report.contains("tactic@4: loop"), "{report}");
            let (_, loop_trace) = report.split_once("tactic@4: loop").unwrap();
            assert!(loop_trace.matches("adds:").count() > 8, "{loop_trace}");
            assert!(!loop_trace.contains("more added facts"), "{loop_trace}");
            if targeted {
                assert!(
                    !report.contains("target tactic has no recorded checked step"),
                    "{report}"
                );
            }
        }
        fs::remove_dir_all(root).unwrap();
    }

    const HEAP_READ_C: &str = "int read_first(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) { return 0; }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
";

    /// A proof `if` in an execution proof is a tactic of its own: the split
    /// is recorded at the `if`, so `--trace-to` a line inside either arm of
    /// an accepted proof selects that arm's checked steps. It used to be
    /// recorded at the previous tactic, and no line in an arm was found.
    #[test]
    fn trace_to_selects_a_line_inside_a_proof_if_arm() {
        let (root, path) = temporary_project(
            "proof-if-arm-trace",
            HEAP_READ_C,
            r#"verifying "program.c";

int32 read_first(int32 m) {
    requires 2 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7 by {
        step(); step();
        if q == 0 {
            step_until(function.exit);
        } else {
            step_until(statement(3).entry);
            have q[0] == 7 by close();
            step_until(function.exit);
        }
    }
}
"#,
        );
        for (line, arm) in [(9, "then"), (11, "else"), (12, "else"), (13, "else")] {
            let arguments = [
                "--trace-proof",
                "read_first",
                "--trace-to",
                &line.to_string(),
                &path.display().to_string(),
            ]
            .map(str::to_string);
            entry_with(arguments).unwrap_or_else(|error| {
                panic!("tactic@{line} in the {arm} arm has a checked step: {error}")
            });
        }
        fs::remove_dir_all(root).unwrap();
    }

    /// The trace shows a store dropping a cached cell, with the index
    /// comparison it lacked, and a later read whose history stops at the
    /// store. The report names the store's statement and the fact the
    /// store search spelled and could not prove before it.
    #[test]
    fn trace_shows_a_dropped_cell_and_the_read_history_stop() {
        let (root, path) = temporary_project(
            "store-forget-trace",
            HEAP_READ_C,
            r#"verifying "program.c";

int32 read_first(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7 or result == 1 by {
        step(); step();
        if q == 0 {
            step_until(function.exit);
        } else {
            step_until(statement(4).entry);
            step();
            if 0 == to_integer(m - 1) {
                step();
                step_until(function.exit);
            } else {
                step();
                step_until(function.exit);
            }
        }
    }
}
"#,
        );
        let arguments = [
            "--trace-proof",
            "read_first",
            "--trace-to",
            "17",
            &path.display().to_string(),
        ]
        .map(str::to_string);
        let report = entry_with(arguments).expect_err("the cell `q[0]` was dropped");
        let statement = "statement(3) may have overwritten `q[0]`; it is kept if you state \
                         `have ((m - 1) as int32) != 0 by { ... };` before statement(3)";
        assert!(report.contains(statement), "{report}");
        let (_, trace) = report
            .split_once("proof trace (checked tactics and branch facts):")
            .unwrap_or_else(|| panic!("missing proof trace: {report}"));
        let (store, read) = trace
            .split_once("steps through: r = q[0]")
            .unwrap_or_else(|| panic!("the read is traced: {trace}"));
        let (_, store) = store
            .split_once("steps through: q[(m - 1)] = 1\n")
            .unwrap_or_else(|| panic!("the store is traced: {trace}"));
        assert!(
            store.trim_start().starts_with(
                "forgets cached `q[0]` beside the store to `q[(m - 1)]`: the store keeps it only on the stated fact "
            ),
            "{trace}"
        );
        assert!(
            read.contains("read history stopped after crossing 0 recorded transitions (a read follows at most one)"),
            "{trace}"
        );
        assert!(
            trace.contains(&format!("store search: {statement}")),
            "{trace}"
        );
        fs::remove_dir_all(root).unwrap();
    }

    fn loop_frontier_trace_report(target: Option<usize>) -> String {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_preserve_frontier_report_multi_exit.md");
        let mut arguments = vec!["--trace-proof".to_owned(), "scan".to_owned()];
        if let Some(line) = target {
            arguments.extend(["--trace-to".to_owned(), line.to_string()]);
        }
        arguments.push(fixture.display().to_string());
        entry_with(arguments).expect_err("the loop proof remains unfinished")
    }

    #[test]
    fn loop_frontier_trace_reports_the_unfinished_path() {
        let report = loop_frontier_trace_report(None);
        assert!(report.contains("stopped inside the loop body"), "{report}");
        let (_, trace) = report
            .split_once("proof trace (checked tactics and branch facts):")
            .unwrap_or_else(|| panic!("missing proof trace: {report}"));
        for line in [51, 52, 62] {
            assert!(trace.contains(&format!("tactic@{line}: step\n")), "{trace}");
        }
        assert!(!trace.contains("tactic@60:"), "{trace}");
    }

    #[test]
    fn loop_frontier_trace_to_selects_checked_tactics() {
        for target in [51, 60, 62] {
            let report = loop_frontier_trace_report(Some(target));
            let (_, trace) = report
                .split_once("proof trace (checked tactics and branch facts):")
                .unwrap_or_else(|| panic!("missing proof trace at {target}: {report}"));
            assert!(
                trace.contains(&format!("tactic@{target}: step\n")),
                "{trace}"
            );
            if target == 51 {
                assert!(!trace.contains("tactic@52:"), "{trace}");
            } else if target == 60 {
                assert!(!trace.contains("tactic@62:"), "{trace}");
            } else {
                assert!(!trace.contains("tactic@60:"), "{trace}");
            }
        }
    }

    #[test]
    fn loop_frontier_trace_to_an_unreached_tactic_explains_the_missing_step() {
        let report = loop_frontier_trace_report(Some(66));
        assert!(
            report.contains("target tactic has no recorded checked step on a retained path"),
            "{report}"
        );
        assert!(!report.contains("tactic@66: step\n"), "{report}");
    }

    #[test]
    fn loop_frontier_trace_to_selects_another_unfinished_arm() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_preserve_frontier_report_multi_exit.md");
        let mut loaded = load_target_inputs(&fixture, None).unwrap();
        let line_offset = loaded.line_offset();
        // Leave both arms unfinished, preserving physical source line numbers.
        loaded.click_source = loaded.click_source.replace(
            "                step();\n                step();",
            "                step();\n                ",
        );
        loaded.project = loaded
            .project
            .with_entry_source(loaded.click_source.clone());
        let VerificationInput::Bundle(sources) = &loaded.inputs else {
            panic!("expected C fixture")
        };
        let index = ProofSourceIndex::for_project(
            &loaded.project,
            &ProgramInputs::Bundle(source_refs(sources)),
        )
        .unwrap();
        let target = resolve_trace_target(
            &index,
            line_offset,
            &TraceTo {
                line: 62,
                column: None,
            },
        )
        .unwrap();
        let report = with_proof_trace("scan", || {
            let error = verify_project_functions(
                &loaded.project,
                &ProgramInputs::Bundle(source_refs(sources)),
                ["scan".to_owned()],
            )
            .expect_err("both preservation arms remain unfinished");
            verification_error_report(
                error.verification_diagnostic(),
                &fixture,
                true,
                &loaded.project,
                &loaded.inputs,
                line_offset,
                Some(&target),
            )
        });
        assert!(report.contains("tactic@62: step\n"), "{report}");
        assert!(
            !report.contains("target tactic has no recorded checked step"),
            "{report}"
        );
    }

    #[test]
    fn trace_target_uses_a_unique_line_or_an_explicit_column() {
        let index = |source: &str| {
            ProofSourceIndex::for_sidecar(source, &ProgramInputs::Bundle(Vec::new())).unwrap()
        };
        let target = |index: &ProofSourceIndex, line, column| {
            resolve_trace_target(index, 8, &TraceTo { line, column })
        };
        let source = "theorem shared() {\n    ensures true by { close(); close(); }\n}\ntheorem alone() {\n    ensures true by {\n        close();\n    }\n}\n";
        let shared = index(source);
        assert_eq!(
            target(&shared, 14, None).unwrap(),
            click::surface::SourcePosition::new(6, 9),
        );
        assert!(
            target(&shared, 10, None)
                .unwrap_err()
                .contains("several tactics")
        );
        for column in [23, 32] {
            assert_eq!(
                target(&shared, 10, Some(column)).unwrap(),
                click::surface::SourcePosition::new(2, column),
            );
        }
        assert!(target(&shared, 10, Some(31)).is_err());

        // A `cases` arm's block follows `=>`; its tactics are targets too.
        let arm = "theorem arm() {\n    ensures true by {\n        cases {\n            true => {\n                close();\n            }\n            false => {\n                close();\n            }\n        }\n    }\n}\n";
        assert_eq!(
            target(&index(arm), 13, None).unwrap(),
            click::surface::SourcePosition::new(5, 17),
        );

        // A `have` with its proof on the same line is that line's target.
        let nested = "theorem nested() {\n    ensures true by {\n        have true by { close(); }\n    }\n}\n";
        assert_eq!(
            target(&index(nested), 11, None).unwrap(),
            click::surface::SourcePosition::new(3, 9),
        );
    }

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
                locked: false,
                target: "example.click".to_string(),
                limits: RunLimits::verify(),
                changed_since: None,
                explain: false,
                allow_sorry: true,
                checked_only: false,
                trace_proof: None,
                trace_to: None,
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
    fn parses_default_and_overridden_run_limits() {
        assert_eq!(
            parse_arguments(["example.click".to_string()]),
            Ok(Arguments {
                locked: false,
                target: "example.click".to_string(),
                limits: RunLimits::verify(),
                changed_since: None,
                explain: false,
                allow_sorry: false,
                checked_only: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert_eq!(
            parse_arguments([
                "--time-limit".to_string(),
                "250ms".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                locked: false,
                target: "example.click".to_string(),
                limits: RunLimits {
                    time: Duration::from_millis(250),
                    ..RunLimits::verify()
                },
                changed_since: None,
                explain: false,
                allow_sorry: false,
                checked_only: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert_eq!(
            parse_arguments([
                "--work-limit".to_string(),
                "1_000".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                locked: false,
                target: "example.click".to_string(),
                limits: RunLimits {
                    work: 1_000,
                    ..RunLimits::verify()
                },
                changed_since: None,
                explain: false,
                allow_sorry: false,
                checked_only: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert!(
            parse_arguments([
                "--work-limit".to_string(),
                "0".to_string(),
                "example.click".to_string(),
            ])
            .is_err()
        );
        assert_eq!(
            parse_arguments([
                "--changed-since".to_string(),
                "HEAD~1".to_string(),
                "--explain".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                locked: false,
                target: "examples".to_string(),
                limits: RunLimits::verify(),
                changed_since: Some("HEAD~1".to_string()),
                explain: true,
                allow_sorry: false,
                checked_only: false,
                trace_proof: None,
                trace_to: None,
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
        assert!(plain.contains("\ntarget=x86_64-unknown-linux-gnu (userspace)\n"));
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
        let selection = select_sidecars(Path::new("examples/input-cursor"))
            .expect("the project should resolve");
        assert_eq!(selection.projects.len(), 1);
        assert!(!selection.projects[0].sidecars.is_empty());
        assert_eq!(
            selection.projects[0].root,
            fs::canonicalize("examples/input-cursor").unwrap()
        );
    }

    /// Writes one sidecar project into a fresh temporary directory and
    /// returns the directory and the sidecar path.
    fn temporary_project(label: &str, c_source: &str, click_source: &str) -> (PathBuf, PathBuf) {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "click-verify-{label}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("temporary verification directory should be creatable");
        fs::write(root.join("program.c"), c_source).expect("C source should be writable");
        let click_path = root.join("program.click");
        fs::write(&click_path, click_source).expect("Click sidecar should be writable");
        (root, click_path)
    }

    /// One report line names every library interface family a C function
    /// relies on, each tagged, from the summary's one closure walk.
    #[test]
    fn the_assumption_report_tags_each_c_library_model_family() {
        let (root, click_path) = temporary_project(
            "assumption-families",
            "unsigned long strlen(const char *s);\n\
             int snprintf(char *buf, unsigned long size, const char *fmt, ...);\n\
             int helper(int x);\n\
             int f(char *buf, int x) {\n\
                 int *p = malloc(sizeof(int));\n\
                 if (p != 0) { free(p); }\n\
                 unsigned long n = strlen(\"abc\");\n\
                 int w = snprintf(buf, 8, \"%s\", \"kB\");\n\
                 return helper(x);\n\
             }\n",
            "target \"x86_64-unknown-linux-gnu\";\n\
             verifying \"program.c\";\n\
             extern int32 helper(int32 x) { ensures result == x; }\n\
             int32 f(char buf[], int32 x) { owns buf[0..8]; ensures result == x; }\n",
        );
        let LoadedTarget {
            project, inputs, ..
        } = load_target_inputs(&click_path, Some(&root)).expect("the project loads");
        let summary = project_summary(&project, &inputs.program_inputs());
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        let summary = summary.expect("the summary resolves");
        assert_eq!(
            render_assumptions(&summary.assumptions["f"]),
            "extern: helper; C library: strlen; allocator: free, malloc; snprintf: \"%s\""
        );
    }

    /// The project summary (external dependencies and the selected proof
    /// count) reads function names, signatures, and call graphs. It once
    /// built `main`'s whole program-entry storage too and dropped it, which
    /// doubled the setup cost of a program with large static objects. It now
    /// enters no program-entry storage phase, and beyond resolving the
    /// sources it spends the same work whatever a static array's
    /// initializer holds, while verification still builds that storage.
    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn the_project_summary_builds_no_program_entry_storage() {
        use click::instrumentation::{VerificationEvent, collect, measure_deterministic_work};
        let costs = [100usize, 2000].map(|elements| {
            let initializers = (0..elements)
                .map(|index| format!("{{{}, 0}}", index % 97))
                .collect::<Vec<_>>()
                .join(", ");
            let (root, click_path) = temporary_project(
                "summary-entry",
                &format!(
                    "struct node {{ int32 key; struct node *next; }};\n\
                     struct node pool[{elements}] = {{{initializers}}};\n\
                     int main(void) {{ return pool[0].key; }}\n"
                ),
                "verifying \"program.c\";\n\
                 int main() {\n\
                     ensures result == 0;\n\
                 } by {\n\
                     step_until(function.exit);\n\
                     close();\n\
                 }\n",
            );
            let LoadedTarget {
                project, inputs, ..
            } = load_target_inputs(&click_path, Some(&root)).expect("the project loads");
            let VerificationInput::Bundle(sources) = &inputs else {
                panic!("a plain C project is a source bundle");
            };
            let refs = source_refs(sources);
            // Warm the process-wide caches so both sizes are measured alike.
            click::surface::c_project_function_names(&project, &refs).expect("the sources resolve");
            let ((summary, summary_events), summary_work) = measure_deterministic_work(|| {
                collect(|| project_summary(&project, &ProgramInputs::Bundle(refs.to_vec())))
            });
            let (resolution, resolution_work) = measure_deterministic_work(|| {
                click::surface::c_project_function_names(&project, &refs)
            });
            let (verified, verify_events) = collect(|| verify_c_project(&project, &refs));
            fs::remove_dir_all(&root)
                .expect("temporary verification directory should be removable");
            let summary = summary.expect("the summary resolves");
            resolution.expect("the sources resolve");
            verified.expect("the program verifies");
            let builds_storage = |events: &[VerificationEvent]| {
                events.iter().any(|event| {
                    matches!(
                        event,
                        VerificationEvent::PhaseStarted("program-entry storage")
                    )
                })
            };
            assert!(
                !builds_storage(&summary_events),
                "the summary built entry storage"
            );
            assert!(
                builds_storage(&verify_events),
                "verification builds entry storage"
            );
            assert_eq!(summary.selected_proof_count, 1);
            assert!(summary.assumptions.is_empty());
            summary_work as i64 - resolution_work as i64
        });
        assert_eq!(
            costs[0], costs[1],
            "beyond resolution, the summary's work grew with the initializer: {costs:?}"
        );
    }

    /// An untraced run reports its external-dependency summary from the
    /// verification's own resolution of the sources. Resolving validates every
    /// declaration, the standard library's included, and once cost about a
    /// tenth of a small run when the summary resolved the sources again.
    #[test]
    fn an_untraced_verification_resolves_its_sources_once() {
        use click::instrumentation::{VerificationEvent, collect};
        let (root, click_path) = temporary_project(
            "one-resolution",
            "int32 identity(int32 x) { return x; }\n",
            "verifying \"program.c\";\n\
             int32 identity(int32 x) {\n\
                 ensures result == x;\n\
             } by {\n\
                 step_until(function.exit);\n\
                 close();\n\
             }\n",
        );
        let (result, events) = collect(|| entry_with([click_path.display().to_string()]));
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        result.expect("the program verifies");
        let resolutions = events
            .iter()
            .filter(|event| matches!(event, VerificationEvent::PhaseStarted("source resolution")))
            .count();
        assert_eq!(resolutions, 1);
    }

    #[test]
    fn c_parsing_reports_the_whole_run_work_limit() {
        let c_source = "int identity(int x) { return x; }";
        let click_source = "verifying \"program.c\";\n\
            int identity(int x) { ensures result == x; }\n";
        let (root, click_path) = temporary_project("parsing-work-limit", c_source, click_source);
        let error = entry_with([
            "--work-limit".to_string(),
            "1".to_string(),
            click_path.display().to_string(),
        ])
        .expect_err("one work unit stops while parsing valid C");
        fs::remove_dir_all(&root).unwrap();
        assert!(error.starts_with("work limit reached:"), "{error}");
        assert!(!error.contains("syntax error"), "{error}");
        assert!(error.contains("C parsing stopped"), "{error}");
        assert!(
            error.contains("deterministic whole-run work budget"),
            "{error}"
        );
        assert!(
            error.contains("external dependency summary > source resolution phase"),
            "{error}"
        );

        let error = click::instrumentation::with_run_work_limit(1, || {
            verify_c_sources(click_source, &[("program.c", c_source)])
        })
        .expect_err("the API preserves the parser's stop kind too");
        assert_eq!(error.kind(), ClickErrorKind::WorkLimitReached);
        assert!(error.report().contains("error kind: work limit reached"));

        let syntax_error = verify_c_sources(click_source, &[("program.c", "int identity( {")])
            .expect_err("malformed C still reports a syntax error");
        assert_eq!(syntax_error.kind(), ClickErrorKind::Syntax);
        assert!(syntax_error.concise_report().starts_with("syntax error:"));
    }

    #[test]
    fn solve_work_exhaustion_reports_unsuccessful_search() {
        let (root, click_path) = temporary_project(
            "solve-work-limit",
            "int32 f(int32 x) { return x; }",
            r#"verifying "program.c";
               int32 f(int32 x) { ensures result == x; } by {
                   step();
                   close();
               }
            "#,
        );
        let verify = |options: &[&str]| {
            click::instrumentation::with_tactic_work_limits(
                click::instrumentation::TacticWorkLimits {
                    smart: 0,
                    ..Default::default()
                },
                || {
                    let arguments = options
                        .iter()
                        .map(|option| (*option).to_string())
                        .chain(std::iter::once(click_path.display().to_string()));
                    entry_with(arguments)
                },
            )
            .expect_err("the written solve has no work allowance")
        };
        let error = verify(&[]);
        let trace = verify(&["--trace-proof", "f"]);
        fs::remove_dir_all(&root).unwrap();
        assert!(error.starts_with("unsuccessful search"), "{error}");
        assert!(
            error.contains("tactic `solve`") && error.contains("smart work budget"),
            "{error}"
        );
        assert!(error.contains("goal: result == x"), "{error}");
        assert!(trace.contains("steps through: return x"), "{trace}");
    }

    /// The crash-containment bound is installed before the run loads its
    /// sources, so even the first C parse, for the external-dependency
    /// summary, stops at a checkpoint once the bound has expired.
    #[test]
    fn the_crash_bound_covers_source_loading_and_parsing() {
        let functions = (0..4000)
            .map(|index| format!("int32 f{index}(int32 x) {{ return x; }}\n"))
            .collect::<String>();
        let (root, click_path) = temporary_project(
            "slow-frontend",
            &functions,
            "verifying \"program.c\";\n\
             int32 f0(int32 x) {\n\
                 ensures result == x;\n\
             } by {\n\
                 step_until(function.exit);\n\
                 close();\n\
             }\n",
        );
        let error = entry_with([
            "--time-limit".to_string(),
            "1ms".to_string(),
            click_path.display().to_string(),
        ])
        .expect_err("one millisecond cannot parse four thousand functions");
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        assert!(
            error.starts_with("timed out:\n  click verify was stopped after")
                && error.contains("by the 1ms wall-clock crash-containment bound")
                && error.contains("C parsing stopped")
                && error.contains(
                    "external dependency summary > source resolution phase, stopped by the 1ms"
                ),
            "{error}"
        );
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
                    ensures result == 0 or result == -1;\n\
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
        let other_target = valid.replace(
            "target=x86_64-unknown-linux-gnu (userspace)",
            "target=another-target",
        );
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
            CTarget::X86_64LinuxKernel
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/bin/click-verify/tests.rs");
    }
}
