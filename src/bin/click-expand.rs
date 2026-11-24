#[path = "click-expand/migrate_normalize.rs"]
mod migrate_normalize;

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use click::cli::{
    self, RunLimits, VerificationInput, containing_directory, looks_like_mdtest, parse_duration,
    parse_source_line_location, prepare_mdtest_inputs, read_lone_sidecar_inputs, read_mdtest,
    read_mdtest_project_if_needed, source_refs,
};
use click::surface::{
    ClickProject, SmartTacticCandidate, SmartTacticSelectionError,
    expand_c_prepared_tactic_source_at, expand_c_tactic_source_at,
    expand_program_prepared_tactic_source_at, expand_project_tactic_source_at,
    project_select_smart_tactic, project_tactic_source_position, tactic_source_position,
    verify_project_at, verify_sources_at,
};

const USAGE: &str = "usage: click expand [--work-limit <UNITS>] [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>:<line>[:<column>]\n       click expand --claim <LABEL|PATH:LINE[:COLUMN]> [--work-limit <UNITS>] [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>\n       click expand --migrate-normalize [--claim <LABEL>] <sidecar.click|mdtest.md>\n\n--migrate-normalize proposes checked substitutions for written normalize calls. The expanded proof is used as validation and the output keeps the short substitutions.\n\n--claim selects a claim by its label or by a line its clause or proof covers. Expansion is checked before output. Whole-claim expansions are checked with proof search disabled. With --output, write the rewrite beside the input. With --in-place, atomically replace the input after targeted verification succeeds.\n\nThe whole command, generating the expansion and checking it, has a deterministic budget of --work-limit units (default 50000000), beside every tactic's own work budget. --time-limit (default 10m) is only a wall-clock crash-containment bound for a hung or CPU-starved run, not a verdict about the proof.";

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    click_path: PathBuf,
    selection: Selection,
    limits: RunLimits,
    output: Option<PathBuf>,
    in_place: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Selection {
    /// A source location; without a column the line must start exactly one
    /// smart tactic.
    Tactic {
        line: usize,
        column: Option<usize>,
    },
    Claim(String),
    MigrateNormalize(Option<String>),
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let raw = arguments.into_iter().collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    cli::with_run_limits("click expand", arguments.limits, || {
        let expanded = run_bounded(&arguments)?;
        check_expansion_deadline("writing the verified expansion")?;
        let destination = if arguments.in_place {
            Some(arguments.click_path.as_path())
        } else {
            arguments.output.as_deref()
        };
        if let Some(destination) = destination {
            atomic_replace(destination, expanded.as_bytes())
        } else {
            print!("{expanded}");
            Ok(())
        }
    })
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut work_limit = None;
    let mut output = None;
    let mut in_place = false;
    let mut claim = None;
    let mut migrate = false;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if !parse_options {
            positional.push(argument);
        } else if argument == "--output" {
            if output.is_some() {
                return Err("`--output` may only be supplied once".to_string());
            }
            output =
                Some(PathBuf::from(arguments.next().ok_or_else(|| {
                    format!("missing path after `--output`\n{USAGE}")
                })?));
        } else if argument == "--in-place" {
            in_place = true;
        } else if argument == "--time-limit" {
            if time_limit.is_some() {
                return Err("`--time-limit` may only be supplied once".to_string());
            }
            let duration = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            time_limit = Some(parse_duration(&duration)?);
        } else if argument == "--work-limit" {
            if work_limit.is_some() {
                return Err("`--work-limit` may only be supplied once".to_string());
            }
            let units = arguments
                .next()
                .ok_or_else(|| format!("missing unit count after `--work-limit`\n{USAGE}"))?;
            work_limit = Some(cli::parse_work_limit(&units)?);
        } else if argument == "--migrate-normalize" {
            migrate = true;
        } else if argument == "--claim" {
            if claim.is_some() {
                return Err("`--claim` may only be supplied once".to_string());
            }
            claim = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing label after `--claim`\n{USAGE}"))?,
            );
        } else if argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else {
            positional.push(argument);
        }
    }
    let (click_path, selection) = match (migrate, claim, positional.as_slice()) {
        (true, claim, [path]) => (PathBuf::from(path), Selection::MigrateNormalize(claim)),
        (false, Some(claim), [path]) => (PathBuf::from(path), Selection::Claim(claim)),
        (false, None, [location]) => {
            let (path, line, column) = parse_source_line_location(location)?;
            (path, Selection::Tactic { line, column })
        }
        _ => return Err(USAGE.to_string()),
    };
    if in_place && output.is_some() {
        return Err("`--output` and `--in-place` cannot be combined".to_string());
    }
    Ok(Arguments {
        click_path,
        selection,
        limits: RunLimits {
            work: work_limit.unwrap_or(RunLimits::expand().work),
            time: time_limit.unwrap_or(RunLimits::expand().time),
        },
        output,
        in_place,
    })
}

#[cfg(test)]
fn run(arguments: &Arguments) -> Result<String, String> {
    cli::with_run_limits("click expand", arguments.limits, || run_bounded(arguments))
}

fn run_bounded(arguments: &Arguments) -> Result<String, String> {
    if let Some(output) = &arguments.output {
        check_output_directory(&arguments.click_path, output)?;
    }
    if looks_like_mdtest(&arguments.click_path) {
        return run_mdtest(arguments);
    }
    let click_source = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let (project, inputs) = read_lone_sidecar_inputs(&arguments.click_path, &click_source)?;
    if let Some(output) = &arguments.output {
        check_sidecar_output(&arguments.click_path, output, &inputs)?;
    }
    if let Selection::MigrateNormalize(claim) = &arguments.selection {
        return migrate_normalize::run(
            Some(&project),
            &click_source,
            &inputs,
            claim.as_deref(),
            &arguments.click_path,
            0,
        );
    }
    let selected = generate_expansion(|| {
        expand_selection(
            Some(&project),
            &click_source,
            &inputs,
            &arguments.selection,
            &SelectionReport {
                path: &arguments.click_path,
                line_offset: 0,
            },
        )
    })?;
    verified_expansion(Some(&project), &click_source, selected, &inputs, arguments)
}

fn check_output_directory(input: &Path, output: &Path) -> Result<(), String> {
    let input_dir = containing_directory(input);
    let output_dir = containing_directory(output);
    let canonical_directory = |directory: &Path| {
        fs::canonicalize(directory).map_err(|error| {
            format!(
                "failed to resolve directory `{}`: {error}",
                directory.display()
            )
        })
    };
    if canonical_directory(input_dir)? != canonical_directory(output_dir)? {
        return Err(format!(
            "`--output` must be in the input's directory `{}`, got `{}`",
            input_dir.display(),
            output.display()
        ));
    }
    Ok(())
}

fn check_sidecar_output(
    input: &Path,
    output: &Path,
    inputs: &VerificationInput,
) -> Result<(), String> {
    if inputs.is_prepared() && output.file_name() != input.file_name() {
        return Err(
            "use `--in-place` to write an expansion of a prepared import sidecar".to_string(),
        );
    }
    let name = output
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("output path `{}` has no valid filename", output.display()))?;
    let config = output.with_file_name(format!("{name}.import.json"));
    match fs::symlink_metadata(&config) {
        Ok(_) => Err(cli::per_sidecar_config_refusal(&config)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("failed to inspect `{}`: {error}", config.display())),
    }
}

/// Expands a tactic inside an mdtest's ```click block. The location is given
/// in `.md` file coordinates — the same coordinates `click profile` reports —
/// and the output is the whole markdown file with the block's body replaced,
/// so the same redirect workflow as sidecar expansion applies.
fn run_mdtest(arguments: &Arguments) -> Result<String, String> {
    let markdown = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let mdtest = read_mdtest(&arguments.click_path)?;
    if matches!(arguments.selection, Selection::MigrateNormalize(_))
        && mdtest.expectation != Some(cli::MdTestExpectation::Pass)
    {
        eprintln!(
            "{}: skipping mdtest without a passing expectation",
            arguments.click_path.display()
        );
        return Ok(markdown);
    }
    let click_source = mdtest.click_source.as_deref().ok_or_else(|| {
        format!(
            "mdtest `{}` has no ```click block",
            arguments.click_path.display()
        )
    })?;
    let inputs = prepare_mdtest_inputs(&mdtest)?;
    let project = read_mdtest_project_if_needed(&arguments.click_path, click_source, &inputs)?;
    if let Selection::MigrateNormalize(claim) = &arguments.selection {
        let migrated = migrate_normalize::run(
            project.as_ref(),
            click_source,
            &inputs,
            claim.as_deref(),
            &arguments.click_path,
            mdtest.click_start_line.saturating_sub(1),
        )?;
        return if migrated == click_source {
            Ok(markdown)
        } else {
            mdtest.replace_click_source(&markdown, &migrated)
        };
    }
    let selected = generate_expansion(|| {
        let selection = match &arguments.selection {
            Selection::Tactic { line, column } => Selection::Tactic {
                line: mdtest.click_line(*line)?,
                column: *column,
            },
            Selection::Claim(claim) => Selection::Claim(claim.clone()),
            Selection::MigrateNormalize(_) => unreachable!("migration handled above"),
        };
        let location = SelectionReport {
            path: &arguments.click_path,
            line_offset: mdtest.click_start_line.saturating_sub(1),
        };
        expand_selection(
            project.as_ref(),
            click_source,
            &inputs,
            &selection,
            &location,
        )
    })?;
    let expanded =
        verified_expansion(project.as_ref(), click_source, selected, &inputs, arguments)?;
    mdtest.replace_click_source(&markdown, &expanded)
}

/// How a selection failure names file positions: the input path, and the
/// line of the input file where the Click source's first line sits.
struct SelectionReport<'a> {
    path: &'a Path,
    line_offset: usize,
}

impl SelectionReport<'_> {
    fn describe(
        &self,
        line: usize,
        column: Option<usize>,
        error: SmartTacticSelectionError,
    ) -> String {
        let location = |line: usize, column: Option<usize>| {
            let line = line + self.line_offset;
            column.map_or_else(
                || format!("{}:{line}", self.path.display()),
                |column| format!("{}:{line}:{column}", self.path.display()),
            )
        };
        let mut message = format!("{}: {}", location(line, column), error.reason);
        for candidate in &error.candidates {
            message.push_str(&format!(
                "\n  {} `{}` in `{}`",
                location(candidate.position.line, Some(candidate.position.column)),
                candidate.tactic_name,
                candidate.claim_label
            ));
        }
        message
    }
}

struct SelectedExpansion {
    claim: String,
    source: String,
    whole_claim: bool,
}

fn expand_selection(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &VerificationInput,
    selection: &Selection,
    report: &SelectionReport<'_>,
) -> Result<SelectedExpansion, String> {
    match selection {
        Selection::Tactic { line, column } => {
            let selected = select_smart_tactic(project, click_source, inputs, *line, *column)
                .map_err(|error| report.describe(*line, *column, error))?;
            let claim = selected.claim_label;
            let (line, column) = (&selected.position.line, &selected.position.column);
            let expanded = match (project, inputs) {
                (Some(project), _) => expand_project_tactic_source_at(
                    project,
                    &inputs.program_inputs(),
                    *line,
                    *column,
                ),
                (None, VerificationInput::Bundle(sources)) => {
                    expand_c_tactic_source_at(click_source, &source_refs(sources), *line, *column)
                }
                (None, VerificationInput::Prepared(imports)) => {
                    expand_c_prepared_tactic_source_at(click_source, imports, *line, *column)
                }
                (None, VerificationInput::PreparedProgram(import)) => {
                    expand_program_prepared_tactic_source_at(click_source, import, *line, *column)
                }
            }
            .map_err(|error| {
                format!(
                    "{}\nOriginal tactic `{}` at {}:{}:{}",
                    error.report(),
                    selected.tactic_name,
                    report.path.display(),
                    line + report.line_offset,
                    column,
                )
            })?;
            Ok(SelectedExpansion {
                claim,
                source: expanded,
                whole_claim: false,
            })
        }
        Selection::MigrateNormalize(_) => unreachable!("migration handled before expansion"),
        Selection::Claim(requested) => {
            // `--claim FILE:LINE[:COLUMN]` names the claim covering that line.
            // Its position tells apart `loop` tactics proving one loop phase.
            let (claim, at) = match cli::claim_at_argument(
                requested,
                report.path,
                report.line_offset,
                project,
                click_source,
                inputs,
                click::surface::ClaimLocationScope::Innermost,
            ) {
                Some(selected) => {
                    let selected = selected?;
                    (selected.label, Some(selected.position))
                }
                None => (requested.clone(), None),
            };
            // A loop phase proved inside a claim's proof script is checked
            // by verifying that claim.
            let expansion = click::surface::expand_claim_by_label(
                project,
                click_source,
                &inputs.program_inputs(),
                &claim,
                at,
            )
            .map_err(|error| {
                format!(
                    "{}\nOriginal selection `{requested}` in `{}`",
                    error.report(),
                    report.path.display()
                )
            })?;
            // A loop phase inside its owner's proof rewrites only part of
            // that proof. Compare resolved labels even for FILE:LINE input.
            Ok(SelectedExpansion {
                whole_claim: claim == expansion.proof_unit,
                claim: expansion.proof_unit,
                source: expansion.source,
            })
        }
    }
}

fn generate_expansion<R>(operation: impl FnOnce() -> Result<R, String>) -> Result<R, String> {
    let (result, events) = click::instrumentation::collect(operation);
    if click::instrumentation::deadline_exceeded() {
        return Err(expansion_limit_error(
            "generating the selected tactic certificate",
            &events,
        ));
    }
    result
}

fn check_expansion_deadline(stage: &str) -> Result<(), String> {
    if click::instrumentation::deadline_exceeded() {
        Err(format!(
            "expansion stopped while {stage}: {}",
            click::instrumentation::deadline_context()
        ))
    } else {
        Ok(())
    }
}

/// Why expansion stopped at `stage`: the deterministic whole-run work
/// budget, whose message names what was running, or the crash-containment
/// bound, named with the work it interrupted.
fn expansion_limit_error(
    stage: &str,
    events: &[click::instrumentation::VerificationEvent],
) -> String {
    let interrupted = events.iter().rev().find_map(|event| match event {
        click::instrumentation::VerificationEvent::DeadlineExceeded(
            click::instrumentation::ActiveVerificationWork::Tactic(tactic),
        ) => Some(format!(
            "tactic `{}` in `{}` (class {}, statement {}, source tactic {})",
            tactic.tactic_name,
            tactic.claim,
            tactic.class,
            tactic.statement_index,
            tactic.source_index
        )),
        click::instrumentation::VerificationEvent::DeadlineExceeded(
            click::instrumentation::ActiveVerificationWork::Phase(phase),
        ) => Some(format!("{phase} phase")),
        click::instrumentation::VerificationEvent::DeadlineExceeded(
            click::instrumentation::ActiveVerificationWork::Driver,
        ) => Some("verification driver".to_string()),
        _ => None,
    });
    match click::instrumentation::expired_containment_bound() {
        Some(limit) => format!(
            "expansion stopped while {stage} in {}, by {}",
            interrupted.unwrap_or_else(|| "verification driver".to_string()),
            click::instrumentation::containment_bound_description(limit)
        ),
        None => format!(
            "expansion stopped while {stage}: {}",
            click::instrumentation::deadline_context()
        ),
    }
}

fn select_smart_tactic(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &VerificationInput,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    match (project, inputs) {
        (Some(project), _) => {
            project_select_smart_tactic(project, &inputs.program_inputs(), line, column)
        }
        (None, inputs) => click::surface::select_smart_tactic(
            click_source,
            &inputs.program_inputs(),
            line,
            column,
        ),
    }
}

fn verified_expansion(
    project: Option<&ClickProject>,
    click_source: &str,
    selected: SelectedExpansion,
    inputs: &VerificationInput,
    arguments: &Arguments,
) -> Result<String, String> {
    let SelectedExpansion {
        claim,
        source: expanded,
        whole_claim,
    } = selected;
    verify_expansion(
        project,
        click_source,
        &expanded,
        inputs,
        &claim,
        whole_claim,
    )
    .map_err(|error| {
        let path = arguments.click_path.display();
        let selection = match &arguments.selection {
            Selection::MigrateNormalize(_) => unreachable!("migration checks directly"),
            Selection::Claim(label) => format!("`{label}` in `{path}`"),
            Selection::Tactic { line, column } => match column {
                Some(column) => format!("`{path}:{line}:{column}` in `{claim}`"),
                None => format!("`{path}:{line}` in `{claim}`"),
            },
        };
        format!("{error}\nOriginal selection {selection}")
    })?;
    Ok(expanded)
}

/// Checks the expansion before it is written. A whole claim's expansion has
/// nothing smart left, so that claim is checked with proof search disabled
/// and so shown self-contained, while the proofs around it keep the closer
/// they were written against, as in `click audit`. A single site's
/// expansion leaves the claim's other steps and smart tactics, which still
/// use it.
fn verify_expansion(
    project: Option<&ClickProject>,
    original: &str,
    expanded: &str,
    inputs: &VerificationInput,
    claim: &str,
    whole_claim: bool,
) -> Result<(), String> {
    if whole_claim {
        click::surface::without_proof_search_for_claim(claim, || {
            verify_expansion_now(project, original, expanded, inputs, claim)
        })
    } else {
        verify_expansion_now(project, original, expanded, inputs, claim)
    }
}

fn verify_expansion_now(
    project: Option<&ClickProject>,
    original: &str,
    expanded: &str,
    inputs: &VerificationInput,
    claim: &str,
) -> Result<(), String> {
    let (result, events) =
        click::instrumentation::collect(|| verify_proof_unit(project, expanded, inputs, claim));
    if click::instrumentation::deadline_exceeded() {
        return Err(expansion_limit_error(
            "checking the generated certificate",
            &events,
        ));
    }
    result.map_err(|error| {
        if error.verification_stopped() {
            return error.report();
        }
        let start: usize = original
            .split_inclusive('\n')
            .zip(expanded.split_inclusive('\n'))
            .take_while(|(before, after)| before == after)
            .map(|(_, line)| line.len())
            .sum();
        let fragment: String = expanded[start..].chars().take(400).collect();
        format!(
            "expanded proof did not verify (report this as a bug)\nGenerated fragment starts with {fragment:?}\n{}",
            error.report()
        )
    })
}

fn verify_proof_unit(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &VerificationInput,
    claim: &str,
) -> Result<(), click::surface::ClickError> {
    let rewritten = project.map(|project| project.with_entry_source(source.to_string()));
    let position = match (&rewritten, inputs) {
        (Some(project), _) => {
            project_tactic_source_position(project, &inputs.program_inputs(), claim, 0)
        }
        (None, inputs) => tactic_source_position(source, &inputs.program_inputs(), claim, 0),
    }?;
    let result = match (&rewritten, inputs) {
        (Some(project), _) => verify_project_at(
            project,
            &inputs.program_inputs(),
            position.line,
            position.column,
        ),
        (None, inputs) => verify_sources_at(
            source,
            &inputs.program_inputs(),
            position.line,
            position.column,
        ),
    };
    result.map(|_| ())
}

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn atomic_replace(path: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = containing_directory(path);
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("click-source");
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(
        ".{name}.click-expand-{}-{sequence}",
        std::process::id()
    ));
    let result = (|| {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|error| format!("failed to create `{}`: {error}", temporary.display()))?;
        file.write_all(contents)
            .and_then(|_| file.sync_all())
            .map_err(|error| format!("failed to write `{}`: {error}", temporary.display()))?;
        fs::rename(&temporary, path).map_err(|error| {
            format!(
                "failed to atomically replace `{}` from `{}`: {error}",
                path.display(),
                temporary.display()
            )
        })
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use click::surface::c_tactic_source_position;
    use std::env;
    use std::time::Duration;

    #[test]
    fn program_termination_claim_expands_and_rechecks() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/termination_ordinary_proof_steps.md");
        let arguments = parse_arguments(
            ["--claim", "program.termination", path.to_str().unwrap()].map(str::to_string),
        )
        .unwrap();
        let expanded = run(&arguments)
            .expect("ordinary termination certificate replays with implicit solving disabled");
        assert!(expanded.contains("termination by {"));
        assert!(expanded.contains("check_termination_component(\"caller\", normal)"));
    }

    #[test]
    #[ignore = "nightly: 1.2s in the parallel gate"]
    fn symbolic_borrowed_range_expansion_rechecks_without_serializing_graph_ids() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/views_a_byte_range_makes_an_index_readable.md");
        for label in [
            "read_byte.contract",
            "read_byte_from.contract",
            "read_half.contract",
        ] {
            let arguments =
                parse_arguments(["--claim", label, path.to_str().unwrap()].map(str::to_string))
                    .unwrap();
            let expanded =
                run(&arguments).expect("symbolic supplier evidence must expand and recheck");
            let parsed = click::cli::parse_mdtest(&path, &expanded).unwrap();
            let sources = source_refs(&parsed.c_sources);
            click::surface::verify_c_sources(parsed.click_source.as_deref().unwrap(), &sources)
                .expect("fresh ordinary verification must reconstruct supplier evidence");
        }
    }

    #[test]
    fn cpp_mdtest_expansion_rechecks_the_imported_source() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/cpp_scalar_catch.md");
        let arguments = parse_arguments(
            ["--claim", "caller.ensures_0", path.to_str().unwrap()].map(str::to_string),
        )
        .unwrap();
        let expanded = run(&arguments).expect("expand and reverify C++ mdtest");
        assert!(expanded.contains("outcomes {"));
        let parsed = click::cli::parse_mdtest(&path, &expanded).unwrap();
        assert_eq!(parsed.cpp_source.unwrap().filename, "caller.cpp");
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn c_mdtest_expansion_sees_an_imported_local_module() {
        // `unmarked` is declared only in the imported `unmarked_count_lemmas.click`.
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/sweep_prefix_survives_its_endpoint_store_by_solve.md");
        let arguments = parse_arguments(
            ["--claim", "sweep.contract", path.to_str().unwrap()].map(str::to_string),
        )
        .unwrap();
        let expanded = run(&arguments).expect("expand and reverify an importing C mdtest");
        assert!(expanded.contains("transport("), "{expanded}");
    }

    #[test]
    fn resource_pattern_exit_solve_expansion_checks() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/resource_pattern_counts_cross_contracts.md");
        let mdtest = read_mdtest(&path).expect("fixture should parse");
        let click_source = mdtest
            .click_source
            .as_deref()
            .expect("fixture should have Click");
        let (line_index, line) = click_source
            .lines()
            .enumerate()
            .find(|(_, line)| *line == "    close();")
            .expect("fixture should contain an exit solve");
        let markdown_line = mdtest.click_start_line + line_index;
        let column = line.find("close()").unwrap() + 1;
        let selection = format!("{}:{markdown_line}:{column}", path.display());
        let arguments = parse_arguments([selection]).expect("fixture selection should parse");
        // Use the artifact loader so the C inputs survive both expansion and
        // certificate verification.
        let expanded = run(&arguments).expect("exit solve should generate a checked certificate");
        cli::parse_mdtest(&path, &expanded).expect("the expanded mdtest should parse");
    }

    #[test]
    fn parses_time_limit_before_or_after_positionals() {
        let before =
            parse_arguments(["--time-limit", "30s", "example.click:12:5"].map(str::to_string))
                .expect("leading time limit should parse");
        let after =
            parse_arguments(["example.click:12:5", "--time-limit", "30s"].map(str::to_string))
                .expect("trailing time limit should parse");

        assert_eq!(before, after);
        assert_eq!(before.limits.time, Duration::from_secs(30));
        assert_eq!(before.limits.work, RunLimits::expand().work);
        assert_eq!(before.output, None);
        assert!(!before.in_place);
        let default = parse_arguments(["example.click:12:5".to_string()])
            .expect("the default expansion should be bounded");
        assert_eq!(default.limits, RunLimits::expand());
        let work =
            parse_arguments(["--work-limit", "12,000", "example.click:12:5"].map(str::to_string))
                .expect("a work limit should parse");
        assert_eq!(work.limits.work, 12_000);
        assert_eq!(work.limits.time, RunLimits::expand().time);
    }

    #[test]
    fn reports_an_expired_expansion_deadline_directly() {
        let error = click::instrumentation::with_deadline(Duration::ZERO, || {
            check_expansion_deadline("checking a generated certificate")
        })
        .expect_err("an expired expansion deadline should fail directly");

        assert!(
            error.starts_with("expansion stopped while checking a generated certificate:")
                && error.contains("crash-containment bound")
                && error.contains("not a verdict about the proof"),
            "{error}"
        );
    }

    #[test]
    fn exhausted_command_deadline_writes_no_artifact() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-deadline-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        let click_path = directory.join("project.click");
        let output_path = directory.join("expanded.click");
        fs::write(directory.join("identity.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let position = c_tactic_source_position(
            click_source,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            0,
        )
        .unwrap();
        let location = format!(
            "{}:{}:{}",
            click_path.display(),
            position.line,
            position.column
        );

        let error = entry_with([
            "--time-limit".to_string(),
            "1ms".to_string(),
            "--output".to_string(),
            output_path.display().to_string(),
            location,
        ])
        .expect_err("an exhausted command deadline must fail before output");

        assert!(
            error.starts_with("timed out:\n  click expand was stopped after")
                && error.contains("1ms wall-clock crash-containment bound")
                && error.contains("not a verdict about the proof"),
            "{error}"
        );
        assert!(
            !output_path.exists(),
            "a failed expansion wrote an artifact"
        );
        assert_eq!(fs::read_to_string(&click_path).unwrap(), click_source);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn translates_md_lines_into_the_click_block_and_rejects_outsiders() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        // Block body is md lines 4..6.
        assert_eq!(mdtest.click_line(4), Ok(1));
        assert_eq!(mdtest.click_line(5), Ok(2));
        assert_eq!(mdtest.click_line(6), Ok(3));
        assert!(mdtest.click_line(3).is_err());
        assert!(mdtest.click_line(7).is_err());
    }

    #[test]
    fn splices_the_expanded_block_back_into_the_markdown() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        let expanded = "proof p {\n  step one;\n  step two;\n}\n";
        assert_eq!(
            mdtest.replace_click_source(markdown, expanded).unwrap(),
            "# title\n\n```click\nproof p {\n  step one;\n  step two;\n}\n```\n\ndone\n"
        );
    }

    #[test]
    fn parses_source_location_with_colons_in_path() {
        let arguments = parse_arguments(
            ["volume:name/example.click:12:7", "--time-limit", "30s"].map(str::to_string),
        )
        .expect("source location should parse");

        assert_eq!(
            arguments.click_path,
            PathBuf::from("volume:name/example.click")
        );
        assert_eq!(
            arguments.selection,
            Selection::Tactic {
                line: 12,
                column: Some(7)
            }
        );
        assert_eq!(arguments.limits.time, Duration::from_secs(30));
    }

    #[test]
    fn claim_expansion_proves_its_normalized_claims_in_goal_order() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-closers-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let example = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/vector-push");
        let sidecar = fs::read_to_string(example.join("vector_push.click")).unwrap();
        // The contract without its proof, left to the implicit `solve`.
        let unproved = format!("{}}}\n", &sidecar[..sidecar.find("} by {").unwrap()]);
        fs::copy(
            example.join("vector_push.c"),
            directory.join("vector_push.c"),
        )
        .unwrap();
        let click_path = directory.join("vector_push.click");
        fs::write(&click_path, &unproved).unwrap();
        let expanded = run(&Arguments {
            click_path,
            selection: Selection::Claim("vector_push.contract".to_string()),
            limits: RunLimits::expand(),
            output: None,
            in_place: false,
        })
        .expect("the contract should expand and recheck");
        let _ = fs::remove_dir_all(&directory);

        // These top-level facts establish the postconditions in declaration
        // order. The tactics used to close the resulting goals may vary.
        let proved_claims = expanded
            .lines()
            .filter_map(|line| line.strip_prefix("    have ")?.strip_suffix(" by {"))
            .collect::<Vec<_>>();
        assert_eq!(
            proved_claims,
            [
                "to_integer(result) == (to_integer(old(owner->len)) + 1)",
                "to_integer(owner->len) == (to_integer(old(owner->len)) + 1)",
                "owner->data[old(owner->len)] == value",
                "owner->cap == old(owner->cap)",
                "owner->data == old(owner->data)",
            ]
        );
    }

    #[test]
    fn parses_claim_selection_with_a_plain_path() {
        let arguments =
            parse_arguments(["--claim", "identity.contract", "example.click"].map(str::to_string))
                .expect("claim selection should parse");

        assert_eq!(arguments.click_path, PathBuf::from("example.click"));
        assert_eq!(
            arguments.selection,
            Selection::Claim("identity.contract".to_string())
        );
    }

    #[test]
    fn end_of_options_accepts_a_dash_prefixed_location() {
        let arguments = parse_arguments(["--", "-example.click:2:3"].map(str::to_string)).unwrap();
        assert_eq!(arguments.click_path, PathBuf::from("-example.click"));
    }

    #[test]
    fn run_expands_selected_unit_despite_unrelated_broken_proof() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-isolation-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let good_c = "int32 good(int32 x) { return x; }";
        let bad_c = "int32 bad(int32 x) { return x; }";
        let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x;
}
int32 bad(int32 x) {
    ensures result == x + 1 by close();
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("good.c"), good_c).unwrap();
        fs::write(directory.join("bad.c"), bad_c).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let sources = [("good.c", good_c), ("bad.c", bad_c)];
        let position = c_tactic_source_position(click_source, &sources, "good.ensures_0", 0)
            .expect("selected tactic should have a source position");
        let arguments = Arguments {
            click_path,
            selection: Selection::Tactic {
                line: position.line,
                column: Some(position.column),
            },
            limits: RunLimits::expand(),
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments)
            .expect("the command should ignore an unrelated broken proof during expansion");

        assert_ne!(expanded, click_source);
        assert!(
            expanded
                .ends_with("int32 bad(int32 x) {\n    ensures result == x + 1 by close();\n}\n")
        );
        fs::remove_dir_all(directory).unwrap();
    }

    /// A smart `have` nested in a proof `branch` arm is one site, selected by
    /// its `have` keyword or by the `solve` written in its body; both select
    /// the same checked expansion.
    #[test]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn a_smart_tactic_inside_a_nested_have_body_selects_the_have() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/guarded_postcondition_closes_after_call.md");
        let markdown = fs::read_to_string(&path).unwrap();
        let have_line = markdown
            .lines()
            .position(|line| line == "            have st.live == 1 by {")
            .expect("fixture should contain the nested smart have")
            + 1;
        let solve = markdown.lines().nth(have_line).unwrap();
        assert_eq!(solve.trim(), "close() using {", "{solve}");
        let run_at = |line: usize, column: usize| {
            run(&Arguments {
                click_path: path.clone(),
                selection: Selection::Tactic {
                    line,
                    column: Some(column),
                },
                limits: RunLimits::expand(),
                output: None,
                in_place: false,
            })
        };

        let from_solve = run_at(have_line + 1, solve.find("close").unwrap() + 1)
            .expect("the nested solve should select its smart have");
        let from_have = run_at(have_line, 13).expect("the have keyword should select it");

        assert_eq!(from_solve, from_have);
        // The selected have's `close() using` becomes an explicit closer.
        assert!(
            from_solve
                .lines()
                .zip(from_solve.lines().skip(1))
                .any(|(have, body)| have.trim() == "have st.live == 1 by {"
                    && body.trim() == "close();"),
            "{from_solve}"
        );
        // The written `close() using` is replaced, at whatever indentation.
        assert!(
            !from_solve
                .lines()
                .zip(from_solve.lines().skip(1))
                .any(|(solve, premise)| {
                    solve.trim() == "close() using {"
                        && premise.trim()
                            == "to_integer(st.live) == to_integer(at(m, st.live) + got);"
                }),
            "{from_solve}"
        );
    }

    fn mdtest_path(name: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(name)
    }

    /// Runs one location selection end to end, including the ordinary
    /// verification of the rewritten source that `run` performs.
    fn run_location(path: &Path, location: &str) -> Result<String, String> {
        let arguments = parse_arguments([format!("{}:{location}", path.display())])?;
        run(&arguments)
    }

    fn markdown_line(path: &Path, line: usize) -> String {
        fs::read_to_string(path)
            .unwrap()
            .lines()
            .nth(line - 1)
            .unwrap()
            .to_string()
    }

    #[test]
    fn parses_a_location_without_a_column() {
        let arguments = parse_arguments(["volume:name/example.click:12".to_string()])
            .expect("a line-only location should parse");
        assert_eq!(
            arguments.click_path,
            PathBuf::from("volume:name/example.click")
        );
        assert_eq!(
            arguments.selection,
            Selection::Tactic {
                line: 12,
                column: None
            }
        );
        assert!(parse_arguments(["example.click".to_string()]).is_err());
        assert!(parse_arguments(["example.click:0".to_string()]).is_err());
    }

    /// Inside a proof `branch` arm: the line of the `solve` in a smart
    /// `have` body selects that `have`, as its keyword and any column
    /// inside it do; a line that starts no smart tactic selects nothing.
    #[test]
    #[ignore = "nightly: 0.9s in the parallel gate"]
    fn a_line_inside_a_branch_arm_selects_its_one_smart_tactic() {
        let path = mdtest_path("guarded_postcondition_closes_after_call.md");
        let markdown = fs::read_to_string(&path).unwrap();
        let have_line = markdown
            .lines()
            .position(|line| line == "            have st.live == 1 by {")
            .unwrap()
            + 1;
        let from_have = run_location(&path, &format!("{have_line}:13")).unwrap();
        assert_eq!(
            run_location(&path, &format!("{}", have_line + 1)).unwrap(),
            from_have
        );
        let premise_line = have_line + 2;
        assert!(
            markdown_line(&path, premise_line)
                .contains("to_integer(st.live) == to_integer(at(m, st.live) + got)")
        );
        assert_eq!(
            run_location(&path, &format!("{premise_line}:24")).unwrap(),
            from_have
        );
        let error = run_location(&path, &format!("{premise_line}"))
            .expect_err("a premise line starts no smart tactic");
        assert!(
            error.contains(&format!(
                "{}:{premise_line}: no smart tactic starts on this line",
                path.display()
            )),
            "{error}"
        );
    }

    /// A tactic in a `cases` arm and one inside a nested smart `have` are
    /// addressed by line: expansion rewrites only the selected tactic's lines.
    #[test]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn lines_in_cases_arms_inside_a_have_body_select() {
        let path = mdtest_path("proof_cases_after_c_branch_expands.md");
        let original = fs::read_to_string(&path).unwrap();
        let original_lines = original.lines().collect::<Vec<_>>();
        let line_of = |text: &str| {
            original_lines
                .iter()
                .position(|line| line.trim() == text)
                .unwrap()
                + 1
        };
        let direct = line_of("result == 18 => {") + 1;
        let have = line_of("have result < 0 by {");
        assert_eq!(original_lines[direct - 1].trim(), "close();");
        assert_eq!(original_lines[have].trim(), "close();");
        assert_eq!(original_lines[have + 1].trim(), "}");
        // (selected line, first and last rewritten line): selecting the
        // `solve` in the smart `have` selects that whole `have`.
        for (line, first, last) in [(direct, direct, direct), (have + 1, have, have + 2)] {
            let expanded = run_location(&path, &line.to_string())
                .unwrap_or_else(|error| panic!("line {line}: {error}"));
            assert_ne!(expanded, original);
            let expanded_lines = expanded.lines().collect::<Vec<_>>();
            // Every other line of the proof is kept as written.
            assert_eq!(
                expanded_lines[..first - 1],
                original_lines[..first - 1],
                "line {line}:\n{expanded}"
            );
            let kept_after = original_lines.len() - last;
            assert_eq!(
                expanded_lines[expanded_lines.len() - kept_after..],
                original_lines[last..],
                "line {line}:\n{expanded}"
            );
        }
    }

    /// Loop phases: the smart `initialize by close()` of a frontier-local
    /// loop is selected by line.
    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn lines_in_loop_phases_select_their_smart_tactics() {
        let path = mdtest_path("c_decreases_count_up.md");
        let (line, text) = (27, "initialize by close();");
        assert_eq!(markdown_line(&path, line).trim(), text);
        let expanded = run_location(&path, &line.to_string())
            .unwrap_or_else(|error| panic!("line {line}: {error}"));
        assert!(!expanded.contains(text), "{expanded}");
    }

    /// Call outcomes: the `solve` closing the `returned` arm is selected by
    /// its line, and only that arm is rewritten.
    #[test]
    #[ignore = "nightly: 1.1s in the parallel gate"]
    fn a_line_in_a_call_outcome_arm_selects_its_smart_tactic() {
        let path = mdtest_path("cpp_single_guard_throw_step.md");
        assert_eq!(
            markdown_line(&path, 81).trim(),
            "step_until(function.exit);"
        );
        let expanded = run_location(&path, "81").unwrap();
        let tail = expanded
            .split_once("        threw(error) => {\n")
            .expect("the threw arm is kept")
            .1;
        // The arm keeps its written `have`, and the selected `step_until`
        // becomes the explicit steps to the exit.
        let arm = tail
            .lines()
            .map(str::trim)
            .take_while(|line| !line.is_empty() && *line != "outcomes {")
            .collect::<Vec<_>>();
        assert_eq!(
            arm[..6],
            [
                "have error == 7 by close();",
                "step() by {",
                "close();",
                "}",
                "step();",
                "step();",
            ],
            "{expanded}"
        );
        assert!(
            !arm.iter()
                .take(8)
                .any(|line| line.starts_with("step_until(")),
            "{expanded}"
        );
    }

    /// Through the CLI on a sidecar: a smart tactic in a mixed `have` body
    /// is selected by its line, an ambiguous line lists its candidates as
    /// copy-pasteable locations, and a location between tactics is refused.
    #[test]
    fn line_selection_on_a_sidecar_lists_ambiguous_candidates() {
        let directory = env::temp_dir().join(format!(
            "click-expand-lines-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        fs::write(
            directory.join("identity.c"),
            "int32 identity(int32 x) { return x; }",
        )
        .unwrap();
        let click_path = directory.join("identity.click");
        let click_source = "verifying \"identity.c\";\n\
            int32 identity(int32 x) {\n\
            \x20   ensures result == x;\n\
            } by {\n\
            \x20   have x <= x by {\n\
            \x20       have x == x by { close(); }\n\
            \x20       close();\n\
            \x20   }\n\
            \x20   have x >= x by { have x == x by close(); close(); }\n\
            \x20   step_until(function.exit);\n\
            \x20   close();\n\
            }\n";
        fs::write(&click_path, click_source).unwrap();

        // Selection controls the rewritten span, not the closer's strategy.
        let assert_selected_solve_changed = |expanded: &str, offset: usize| {
            let suffix = &click_source[offset + "close();".len()..];
            assert!(expanded.starts_with(&click_source[..offset]), "{expanded}");
            assert!(expanded.ends_with(suffix), "{expanded}");
            let replacement = &expanded[offset..expanded.len() - suffix.len()];
            assert!(!replacement.contains("solve()"), "{expanded}");
            assert_ne!(expanded, click_source);
        };
        let expanded = run_location(&click_path, "7").unwrap();
        let selected = click_source.find("        close();\n").unwrap() + 8;
        assert_selected_solve_changed(&expanded, selected);
        let ambiguous = run_location(&click_path, "9").expect_err("line 9 is ambiguous");
        let path = click_path.display();
        assert!(
            ambiguous.contains(&format!(
                "{path}:9: 2 smart tactics start on this line; add the column of one of them:\n  {path}:9:22 `have` in `identity.contract`\n  {path}:9:46 `solve` in `identity.contract`"
            )),
            "{ambiguous}"
        );
        let expanded = run_location(&click_path, "9:46").unwrap();
        let selected = click_source.rfind("close(); }").unwrap();
        assert_selected_solve_changed(&expanded, selected);
        let between =
            run_location(&click_path, "8:5").expect_err("a closing brace selects nothing");
        assert!(
            between.contains(&format!(
                "{path}:8:5: no smart tactic's source contains this location"
            )),
            "{between}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn run_expands_an_entire_claim_by_label() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-claim-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("identity.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let arguments = Arguments {
            click_path,
            selection: Selection::Claim("identity.ensures_0".to_string()),
            limits: RunLimits::expand(),
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments).expect("the whole claim should expand and check");

        assert_ne!(expanded, click_source);
        assert!(!expanded.contains("step_until(function.exit);"));
        assert!(!expanded.contains("solve();"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn run_expands_a_pure_theorem_claim_by_label() {
        let directory = env::temp_dir().join(format!(
            "click-expand-pure-claim-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let click_path = directory.join("project.click");
        let click_source = r#"theorem successor(x: int32) {
    ensures x == x by { close(); }
}
"#;
        fs::write(&click_path, click_source).unwrap();
        let arguments = Arguments {
            click_path,
            selection: Selection::Claim("successor.ensures_0".to_string()),
            limits: RunLimits::expand(),
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments).expect("pure theorem claims should expand by label");

        assert_ne!(expanded, click_source);
        assert!(!expanded.contains("solve();"));
        let by_location = Selection::Claim(format!("{}:2:5", arguments.click_path.display()));
        let selection = expand_selection(
            None,
            click_source,
            &VerificationInput::Bundle(Vec::new()),
            &by_location,
            &SelectionReport {
                path: &arguments.click_path,
                line_offset: 0,
            },
        )
        .unwrap();
        assert_eq!(selection.claim, "successor.ensures_0");
        assert!(selection.whole_claim);
        fs::remove_dir_all(directory).unwrap();
    }

    /// A loop phase written in a `loop` tactic of a contract proof is
    /// selected by its label or by a line of its proof. Only the phase is
    /// rewritten, an omitted phase is written out, and each result is
    /// checked by verifying the contract proof that writes the phase.
    #[test]
    fn run_expands_a_loop_phase_by_label_and_by_line() {
        let directory = env::temp_dir().join(format!(
            "click-expand-loop-phase-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let c_source = "int32 f(int32 a, int32 b) {
    while (a > 0) {
        a = 0;
        b = 0;
    }
    return a;
}
";
        let click_source = r#"verifying "phase.c";

int32 f(int32 a, int32 b) {
    requires a <= 0;
    ensures result <= 0;
} by {
    loop {
        decreases a + 1;
        invariant a <= 0;
        initialize by close();
    }
    step();
    close();
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("phase.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let expand = |claim: String| {
            run(&Arguments {
                click_path: click_path.clone(),
                selection: Selection::Claim(claim),
                limits: RunLimits::expand(),
                output: None,
                in_place: false,
            })
        };

        let written = "initialize by close();";
        let start = click_source.find(written).unwrap();
        let end = start + written.len();
        let by_label = expand("f.loop(0).initialize".to_string())
            .expect("the written phase should expand and check");
        assert!(by_label.starts_with(&click_source[..start]), "{by_label}");
        assert!(by_label.ends_with(&click_source[end..]), "{by_label}");
        let phase = &by_label[start..by_label.len() - (click_source.len() - end)];
        assert!(phase.starts_with("initialize by {"), "{phase}");
        assert!(!phase.contains("solve"), "{phase}");
        let line = click_source[..start].lines().count();
        let output = directory.join("project.expanded.click");
        entry_with([
            "--claim".to_string(),
            format!("{}:{line}", click_path.display()),
            "--output".to_string(),
            output.display().to_string(),
            click_path.display().to_string(),
        ])
        .expect("a loop phase selected by line can be written beside the input");
        assert_eq!(fs::read_to_string(output).unwrap(), by_label);

        let insertion = click_source.find("}\n    step();").unwrap();
        let omitted = expand("f.loop(0).maintain".to_string())
            .expect("the omitted phase should expand and check");
        assert!(omitted.starts_with(&click_source[..insertion]), "{omitted}");
        assert!(omitted.ends_with(&click_source[insertion..]), "{omitted}");
        assert!(
            omitted[insertion..].starts_with("    maintain by {\n"),
            "{omitted}"
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn run_expands_and_rechecks_an_integer_theorem_application_by_label() {
        let directory = env::temp_dir().join(format!(
            "click-expand-integer-claim-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let click_path = directory.join("project.click");
        let click_source = r#"theorem add_one(x: Integer) {
    requires x == x;
    ensures x + 1 > x by { close(); }
}

theorem use_add_one(x: Integer) {
    requires x == x;
    ensures x + 1 > x by { apply(add_one(x)); }
}
"#;
        fs::write(&click_path, click_source).unwrap();
        let arguments = Arguments {
            click_path,
            selection: Selection::Claim("use_add_one.ensures_0".to_string()),
            limits: RunLimits::expand(),
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments)
            .expect("Integer theorem applications should expand and independently recheck");

        assert_ne!(expanded, click_source);
        // Bare application is itself a checked step with these premises.
        assert!(expanded.contains("apply(add_one(x));"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn invalid_generated_proof_replay_asks_for_a_bug_report() {
        let original = "theorem reflexive(x: Integer) { ensures x == x by close(); }";
        let inputs = VerificationInput::Bundle(Vec::new());
        let claim = "reflexive.ensures_0";
        verify_expansion(None, original, original, &inputs, claim, false).unwrap();

        for generated in [
            "theorem reflexive(x: Integer) { ensures x == x by { have x == x + 1 by close(); } }",
            "theorem reflexive(x: Integer) { ensures x == x by { ??? } }",
        ] {
            let error =
                verify_expansion(None, original, generated, &inputs, claim, false).unwrap_err();
            assert!(
                error.contains("report this as a bug") && error.contains(generated),
                "{error}"
            );
        }
    }

    #[test]
    fn close_replays_direct_hits_and_expands_its_search() {
        let source = r#"
theorem written(x: int32) {
    requires x == 0;
    ensures x == 0 by close();
}
theorem direct(x: int32) {
    requires x == 0;
    ensures x == 0 by close();
}
theorem fallback(x: int32) {
    ensures x == 0 implies x == 0 by close();
}
"#;
        let inputs = VerificationInput::Bundle(Vec::new());
        verify_expansion(None, source, source, &inputs, "direct.ensures_0", true).unwrap();

        let claim = "fallback.ensures_0";
        verify_expansion(None, source, source, &inputs, claim, false).unwrap();
        assert!(verify_expansion(None, source, source, &inputs, claim, true).is_err());
        let expanded = generate_expansion(|| {
            click::surface::expand_c_claim_source_by_label(source, &[], claim)
                .map_err(|error| error.report())
        })
        .unwrap();
        assert!(expanded.contains("ensures x == 0 by close();"));
        let fallback = expanded.split("theorem fallback").nth(1).unwrap();
        assert!(fallback.contains("intro();") && fallback.contains("close();"));
        assert!(!fallback.contains("known();") && !fallback.contains("solve();"));
        verify_expansion(None, source, &expanded, &inputs, claim, true).unwrap();
        // If a step goes missing, ordinary verification can still recover
        // at the new spelling. The whole-claim replay must refuse it.
        let incomplete = expanded.replace("intro();", "");
        verify_expansion(None, source, &incomplete, &inputs, claim, false).unwrap();
        assert!(verify_expansion(None, source, &incomplete, &inputs, claim, true).is_err());
    }

    #[test]
    fn whole_claim_replay_refuses_search_even_in_nested_proofs() {
        let source = r#"
theorem neighbor(x: int32) {
    ensures x == 0 implies x == 0 by close();
}
theorem selected(x: int32) {
    ensures x == 0 implies x == 0 by {
        intro();
        have x == 0 by { close(); }
        close();
    }
}
"#;
        let inputs = VerificationInput::Bundle(Vec::new());
        let claim = "selected.ensures_0";
        verify_expansion(None, source, source, &inputs, claim, true).unwrap();
        for body in [
            "close();",
            "intro(); have x == 0 by { close(); } close();",
            "intro();",
        ] {
            let incomplete = source.replace(
                "intro();\n        have x == 0 by { close(); }\n        close();",
                body,
            );
            assert_ne!(source, incomplete);
            verify_expansion(None, source, &incomplete, &inputs, claim, false).unwrap();
            let error =
                verify_expansion(None, source, &incomplete, &inputs, claim, true).unwrap_err();
            assert!(error.contains(claim), "{error}");
        }
    }

    #[test]
    fn generated_proof_check_stops_at_the_whole_run_work_budget() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        let inputs =
            VerificationInput::Bundle(vec![("identity.c".to_string(), c_source.to_string())]);
        let check = || {
            verify_expansion(
                None,
                click_source,
                click_source,
                &inputs,
                "identity.ensures_0",
                false,
            )
        };

        check().expect("the generated proof verifies within the default budgets");
        let first = click::instrumentation::with_run_work_limit(10, check)
            .expect_err("ten units cannot check a generated proof");
        let second = click::instrumentation::with_run_work_limit(10, check)
            .expect_err("ten units cannot check a generated proof");
        assert!(
            first.starts_with("expansion stopped while checking the generated certificate:")
                && first.contains(
                    "exhausted its deterministic whole-run work budget after 11 units (10 limit)"
                ),
            "{first}"
        );
        assert_eq!(first, second, "a work-budget verdict is deterministic");
        assert!(!first.contains("report this as a bug"), "{first}");
    }

    #[test]
    fn an_exhausted_whole_run_work_budget_writes_no_artifact() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-work-limit-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        let click_path = directory.join("project.click");
        let output_path = directory.join("expanded.click");
        fs::write(directory.join("identity.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let position = c_tactic_source_position(
            click_source,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            0,
        )
        .unwrap();
        let location = format!(
            "{}:{}:{}",
            click_path.display(),
            position.line,
            position.column
        );

        let error = entry_with([
            "--work-limit".to_string(),
            "20".to_string(),
            "--output".to_string(),
            output_path.display().to_string(),
            location,
        ])
        .expect_err("an exhausted work budget must fail before output");

        assert!(
            error.contains("exhausted its deterministic whole-run work budget")
                && error.contains("(20 limit)")
                && !error.contains("crash-containment"),
            "{error}"
        );
        assert!(
            !output_path.exists(),
            "a failed expansion wrote an artifact"
        );
        assert_eq!(fs::read_to_string(&click_path).unwrap(), click_source);
        fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod output_context_tests {
    use super::*;
    use click::cli::read_verification_inputs;
    use click::surface::verify_c_sources;
    use std::env;

    fn setup_source_bundle(sequence: u64) -> (PathBuf, PathBuf, PathBuf) {
        let directory = env::temp_dir().join(format!(
            "click-expand-context-{}-{sequence}",
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir_all(directory.join("source")).unwrap();
        fs::create_dir_all(directory.join("out")).unwrap();
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        fs::write(directory.join("source/identity.c"), c_source).unwrap();
        let click_path = directory.join("source/identity.click");
        fs::write(&click_path, click_source).unwrap();
        let source_c = directory.join("source/identity.c");
        (directory, click_path, source_c)
    }

    fn assert_emitted_verifies(output: &Path) {
        let emitted = fs::read_to_string(output).expect("the expansion artifact exists");
        let inputs = read_verification_inputs(output, &emitted)
            .expect("the emitted artifact must load its inputs at the output path");
        let sources = match inputs {
            VerificationInput::Bundle(sources) => sources,
            _ => panic!("a source-bundle expansion must select a source bundle"),
        };
        verify_c_sources(&emitted, &[(&sources[0].0, sources[0].1.as_str())])
            .expect("the emitted artifact must verify through the output-path loading rules");
    }

    #[test]
    fn output_in_another_directory_is_rejected_before_writing() {
        let (directory, click_path, _) =
            setup_source_bundle(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let output = directory.join("out/identity.click");

        let error = entry_with([
            "--claim".to_string(),
            "identity.ensures_0".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            click_path.display().to_string(),
        ])
        .expect_err("output must stay beside the input");

        assert!(
            error.contains("must be in the input's directory"),
            "{error}"
        );
        assert_eq!(fs::read_dir(directory.join("out")).unwrap().count(), 0);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn markdown_output_in_another_directory_is_rejected() {
        let input = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/termination_ordinary_proof_steps.md");
        let directory = tempfile::tempdir().unwrap();
        let output = directory.path().join("expanded.md");
        let error = entry_with([
            "--claim".to_string(),
            "program.termination".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            input.display().to_string(),
        ])
        .expect_err("Markdown output must stay beside the input");

        assert!(
            error.contains("must be in the input's directory"),
            "{error}"
        );
        assert!(!output.exists());
    }

    #[test]
    fn output_in_the_same_directory_preserves_declared_sources() {
        let (directory, click_path, _) =
            setup_source_bundle(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let output = directory.join("source/../source/expanded.click");

        entry_with([
            "--claim".to_string(),
            "identity.ensures_0".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            click_path.display().to_string(),
        ])
        .expect("equivalent paths name the same source directory");

        let emitted = fs::read_to_string(&output).unwrap();
        assert!(
            emitted.starts_with("verifying \"identity.c\";\n"),
            "{emitted}"
        );
        assert_emitted_verifies(&output);
        fs::remove_dir_all(directory).unwrap();
    }
}

// Prepared-import behavior mirrors `tests/compiler_import.rs`, which only
// runs where GNU GCC exists.
#[cfg(all(test, not(target_os = "macos")))]
mod prepared_output_tests {
    use super::*;
    use click::cli::read_verification_inputs;
    use std::env;

    fn setup_prepared(sequence: u64) -> PathBuf {
        // The import loader rejects symlinked root components, so the
        // fixture runs from the canonical temporary tree.
        let directory = fs::canonicalize(env::temp_dir())
            .unwrap_or_else(|_| env::temp_dir())
            .join(format!(
                "click-expand-prepared-{}-{sequence}",
                std::process::id()
            ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir_all(&directory).unwrap();
        fs::create_dir_all(directory.join("configured")).unwrap();
        for (path, contents) in [
            (
                "main.c",
                include_str!("../../tests/fixtures/compiler-import/main.c"),
            ),
            (
                "context.h",
                include_str!("../../tests/fixtures/compiler-import/context.h"),
            ),
            (
                "main.click",
                include_str!("../../tests/fixtures/compiler-import/main.click"),
            ),
            (
                "configured/configured.h",
                include_str!("../../tests/fixtures/compiler-import/configured/configured.h"),
            ),
        ] {
            fs::write(directory.join(path), contents).unwrap();
        }
        assert!(
            Path::new("/usr/bin/gcc").is_file(),
            "prepared-import fixture requires GCC at /usr/bin/gcc; provision it before scripts/check.sh"
        );
        let project = serde_json::json!({
            "target": "x86_64-unknown-linux-gnu",
                "mode": "kernel",
            "units": {"main": {
                "language": "c",
                "compiler": "/usr/bin/gcc",
                "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "SOURCE_DATE_EPOCH": "0"},
                "args": ["-DVARIANT=1", "-isystem", "configured"],
                "sources": {"main.c": {}}
            }}
        });
        let project_file = directory.join(click::project::FILE_NAME);
        fs::write(&project_file, serde_json::to_vec_pretty(&project).unwrap()).unwrap();
        click::project::Project::load(&project_file)
            .and_then(|project| project.lock())
            .expect("lock the prepared import");
        directory
    }

    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn a_prepared_import_sidecar_refuses_a_renamed_output() {
        let directory = setup_prepared(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let renamed = directory.join("renamed.click");
        let rename_error = entry_with([
            "--claim".to_string(),
            "from_header.ensures_0".to_string(),
            "--output".to_string(),
            renamed.display().to_string(),
            directory.join("main.click").display().to_string(),
        ])
        .expect_err("prepared sidecars use in-place expansion");
        assert!(rename_error.contains("prepared import"), "{rename_error}");
        assert!(
            !renamed.exists(),
            "a rejected rename must not write the artifact"
        );
        fs::remove_dir_all(directory).unwrap();
    }
    /// Confirms the fixture drives the exact prepared-input path the reject
    /// protects: loading the manifest yields one prepared C import.
    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn the_prepared_fixture_selects_the_prepared_input_route() {
        let directory = setup_prepared(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let click_path = directory.join("main.click");
        let inputs =
            read_verification_inputs(&click_path, &fs::read_to_string(&click_path).unwrap())
                .expect("a locked manifest must select the prepared route");
        assert!(inputs.is_prepared(), "the fixture must be prepared");
        fs::remove_dir_all(directory).unwrap();
    }
}
