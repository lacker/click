use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use click::cli::{
    CInput, DEFAULT_EXPANSION_TIME_LIMIT, containing_directory, looks_like_mdtest, parse_duration,
    parse_source_location, prepare_mdtest_inputs, read_c_inputs, read_click_project, read_mdtest,
    source_refs,
};
use click::surface::{
    ClickProject, c0_prepared_project_smart_tactic_source_sites,
    c0_prepared_project_tactic_source_position, c0_prepared_smart_tactic_source_sites,
    c0_prepared_tactic_source_position, c0_project_smart_tactic_source_sites,
    c0_project_tactic_source_position, c0_smart_tactic_source_sites, c0_tactic_source_position,
    cpp_prepared_project_smart_tactic_source_sites, cpp_prepared_project_tactic_source_position,
    cpp_prepared_smart_tactic_source_sites, cpp_prepared_tactic_source_position,
    expand_c0_claim_source_by_label, expand_c0_prepared_claim_source_by_label,
    expand_c0_prepared_project_claim_source_by_label, expand_c0_prepared_project_tactic_source_at,
    expand_c0_prepared_tactic_source_at, expand_c0_project_claim_source_by_label,
    expand_c0_project_tactic_source_at, expand_c0_tactic_source_at,
    expand_cpp_prepared_claim_source_by_label, expand_cpp_prepared_project_claim_source_by_label,
    expand_cpp_prepared_project_tactic_source_at, expand_cpp_prepared_tactic_source_at,
    map_verifying_source_paths, verify_c0_prepared_project_at, verify_c0_prepared_sources_at,
    verify_c0_project_at, verify_c0_sources_at, verify_cpp_prepared_project_at,
    verify_cpp_prepared_sources_at,
};

const USAGE: &str = "usage: click expand [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>:<line>:<column>\n       click expand --claim <LABEL> [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>\n\nExpansion is checked before output. With --in-place, the original is atomically replaced only after targeted verification succeeds.";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-expand: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    click_path: PathBuf,
    selection: Selection,
    time_limit: Duration,
    output: Option<PathBuf>,
    in_place: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Selection {
    Tactic { line: usize, column: usize },
    Claim(String),
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
    click::instrumentation::with_deadline(arguments.time_limit, || {
        let artifact = run_bounded(&arguments)?;
        check_expansion_deadline("writing the verified expansion")?;
        if arguments.in_place {
            atomic_replace(&arguments.click_path, artifact.source.as_bytes())
        } else if let Some(output) = &arguments.output {
            write_context_preserved(&arguments, output, &artifact)
        } else {
            print!("{}", artifact.source);
            Ok(())
        }
    })
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut output = None;
    let mut in_place = false;
    let mut claim = None;
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
    let (click_path, selection) = match (claim, positional.as_slice()) {
        (Some(claim), [path]) => (PathBuf::from(path), Selection::Claim(claim)),
        (None, [location]) => {
            let (path, line, column) = parse_source_location(location)?;
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
        time_limit: time_limit.unwrap_or(DEFAULT_EXPANSION_TIME_LIMIT),
        output,
        in_place,
    })
}

#[cfg(test)]
fn run(arguments: &Arguments) -> Result<String, String> {
    click::instrumentation::with_deadline(arguments.time_limit, || {
        run_bounded(arguments).map(|artifact| artifact.source)
    })
}

/// One verified artifact. `claim` is the proof unit label whose expansion the
/// output-context check re-verifies.
struct ExpandedArtifact {
    source: String,
    claim: String,
}

fn run_bounded(arguments: &Arguments) -> Result<ExpandedArtifact, String> {
    if looks_like_mdtest(&arguments.click_path) {
        return run_mdtest(arguments);
    }
    let click_source = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let inputs = read_c_inputs(&arguments.click_path, &click_source)?;
    let project = read_click_project(&arguments.click_path, &click_source)?;
    let (claim, expanded) = generate_expansion(arguments.time_limit, || {
        expand_selection(Some(&project), &click_source, &inputs, &arguments.selection)
    })?;
    verify_expansion(
        Some(&project),
        &expanded,
        &inputs,
        &claim,
        arguments.time_limit,
    )?;
    Ok(ExpandedArtifact {
        source: expanded,
        claim,
    })
}

/// Prepares the exact bytes that `--output` may write.
///
/// A source-bundle sidecar relocated into another directory keeps its
/// `verifying` declarations' meaning through one consistent rebasing: each
/// relative declaration is respelled relative to the output directory so it
/// selects the same file, and the rebased artifact is re-verified through the
/// output path's own loading rules before anything is written. A prepared
/// import anchors its manifest, roots, and locked artifacts next to the
/// sidecar, so a `--output` that moves or renames it cannot preserve that
/// identity and is rejected before writing. In-place output and mdtest output
/// keep context unchanged.
fn write_context_preserved(
    arguments: &Arguments,
    output: &Path,
    artifact: &ExpandedArtifact,
) -> Result<(), String> {
    let write_artifact = |content: &str| {
        fs::write(output, content.as_bytes())
            .map_err(|error| format!("failed to write `{}`: {error}", output.display()))
    };
    if looks_like_mdtest(&arguments.click_path) {
        return write_artifact(&artifact.source);
    }
    let source_dir = containing_directory(&arguments.click_path).to_path_buf();
    let output_dir = containing_directory(output);
    let original_inputs = read_c_inputs(&arguments.click_path, &artifact.source)?;
    let same_directory = same_path(&source_dir, output_dir);
    let same_name = output.file_name() == arguments.click_path.file_name();
    if original_inputs.is_prepared() {
        if same_directory && same_name {
            return write_artifact(&artifact.source);
        }
        let what = if same_name { "location" } else { "name" };
        return Err(format!(
            "`--output` would relocate the prepared import sidecar's {what}; its import manifest and locked artifacts are anchored beside the sidecar, so an expansion must be written in place"
        ));
    }
    if same_directory {
        return write_artifact(&artifact.source);
    }
    if !output_dir.is_dir() {
        return Err(format!(
            "`--output` directory `{}` does not exist; an relocated sidecar cannot resolve its sources without it",
            output_dir.display()
        ));
    }
    let rebased = map_verifying_source_paths(&artifact.source, |declared| {
        rebase_verifying_declaration(&source_dir, output_dir, declared)
    })
    .map_err(|error| error.report())?;
    // The rebased artifact is verified through the rules the requested path
    // will actually use, including a manifest hijacking the destination name,
    // before the final bytes are promoted. The staged entry shares the output
    // directory so `verifying` resolution and project rooting match exactly.
    let hijacking_manifest = output.with_file_name(format!(
        "{}.import.json",
        output
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("output path `{}` has no valid filename", output.display()))?
    ));
    if fs::symlink_metadata(&hijacking_manifest).is_ok() {
        return Err(format!(
            "`--output` destination `{}` would be loaded as a prepared import through its adjacent import manifest; relocating a source-bundle sidecar there is refused",
            output.display()
        ));
    }
    let staged = temp_entry_for(output);
    fs::write(&staged, rebased.as_bytes())
        .map_err(|error| format!("failed to stage `{}`: {error}", staged.display()))?;
    let verification = (|| -> Result<(), String> {
        let verified_inputs = read_c_inputs(&staged, &rebased)?;
        let verified_project = read_click_project(&staged, &rebased)?;
        let original_project = read_click_project(&arguments.click_path, &artifact.source)?;
        if original_project.c_profile() != verified_project.c_profile() {
            return Err("`--output` would change the Click project C configuration; place the output in the same project directory".to_string());
        }
        verify_expansion(
            Some(&verified_project),
            &rebased,
            &verified_inputs,
            &artifact.claim,
            arguments.time_limit,
        )
    })();
    if let Err(verification) = verification {
        let _ = fs::remove_file(&staged);
        return Err(verification);
    }
    if let Err(error) = fs::rename(&staged, output) {
        let _ = fs::remove_file(&staged);
        return Err(format!(
            "failed to promote the verified expansion to `{}`: {error}",
            output.display()
        ));
    }
    Ok(())
}

fn temp_entry_for(output: &Path) -> PathBuf {
    let name = output
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("expanded.click");
    output.with_file_name(format!(
        ".click-expand-{}-{}",
        TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed),
        name
    ))
}

/// Rebases one relative `verifying` declaration from the source directory to
/// the output directory, keeping the same selected file. Absolute declarations
/// need no rebasing.
fn rebase_verifying_declaration(
    source_dir: &Path,
    output_dir: &Path,
    declared: &str,
) -> Option<String> {
    let declared_path = Path::new(declared);
    if declared_path.is_absolute() {
        return None;
    }
    let selected = fs::canonicalize(source_dir.join(declared_path)).ok()?;
    if !selected.is_file() {
        return None;
    }
    let output_root = fs::canonicalize(output_dir).ok()?;
    let selected = selected.components().collect::<Vec<_>>();
    let output = output_root.components().collect::<Vec<_>>();
    let shared = selected
        .iter()
        .zip(output.iter())
        .take_while(|(left, right)| left == right)
        .count();
    let mut rebased = std::path::PathBuf::new();
    for component in &output[shared..] {
        if let std::path::Component::Normal(_) = component {
            rebased.push("..");
        }
    }
    for component in &selected[shared..] {
        if let std::path::Component::Normal(component) = component {
            rebased.push(component);
        }
    }
    let rebased = rebased.to_string_lossy().into_owned();
    (rebased != declared).then_some(rebased)
}

fn same_path(left: &Path, right: &Path) -> bool {
    absolute_lexical(left) == absolute_lexical(right)
}

fn absolute_lexical(path: &Path) -> PathBuf {
    if path.is_absolute() {
        return path.to_path_buf();
    }
    std::env::current_dir()
        .map(|current| current.join(path))
        .unwrap_or_else(|_| path.to_path_buf())
}

/// Expands a tactic inside an mdtest's ```click block. The location is given
/// in `.md` file coordinates — the same coordinates `click profile` reports —
/// and the output is the whole markdown file with the block's body replaced,
/// so the same redirect workflow as sidecar expansion applies.
fn run_mdtest(arguments: &Arguments) -> Result<ExpandedArtifact, String> {
    let markdown = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let mdtest = read_mdtest(&arguments.click_path)?;
    let click_source = mdtest.click_source.as_deref().ok_or_else(|| {
        format!(
            "mdtest `{}` has no ```click block",
            arguments.click_path.display()
        )
    })?;
    let inputs = prepare_mdtest_inputs(&mdtest)?;
    let project = if matches!(inputs, CInput::PreparedCpp(_)) {
        Some(read_click_project(&arguments.click_path, click_source)?)
    } else {
        None
    };
    let (claim, expanded) = generate_expansion(arguments.time_limit, || {
        let selection = match &arguments.selection {
            Selection::Tactic { line, column } => Selection::Tactic {
                line: mdtest.click_line(*line)?,
                column: *column,
            },
            Selection::Claim(claim) => Selection::Claim(claim.clone()),
        };
        expand_selection(project.as_ref(), click_source, &inputs, &selection)
    })?;
    verify_expansion(
        project.as_ref(),
        &expanded,
        &inputs,
        &claim,
        arguments.time_limit,
    )?;
    let source = mdtest.replace_click_source(&markdown, &expanded)?;
    Ok(ExpandedArtifact { source, claim })
}

fn expand_selection(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &CInput,
    selection: &Selection,
) -> Result<(String, String), String> {
    match selection {
        Selection::Tactic { line, column } => {
            let claim = selected_claim(project, click_source, inputs, *line, *column)?;
            let expanded = match inputs {
                CInput::Bundle(sources) => match project {
                    Some(project) => expand_c0_project_tactic_source_at(
                        project,
                        &source_refs(sources),
                        *line,
                        *column,
                    ),
                    None => expand_c0_tactic_source_at(
                        click_source,
                        &source_refs(sources),
                        *line,
                        *column,
                    ),
                },
                CInput::Prepared(imports) => match project {
                    Some(project) => expand_c0_prepared_project_tactic_source_at(
                        project, imports, *line, *column,
                    ),
                    None => {
                        expand_c0_prepared_tactic_source_at(click_source, imports, *line, *column)
                    }
                },
                CInput::PreparedCpp(import) => match project {
                    Some(project) => expand_cpp_prepared_project_tactic_source_at(
                        project, import, *line, *column,
                    ),
                    None => {
                        expand_cpp_prepared_tactic_source_at(click_source, import, *line, *column)
                    }
                },
            }
            .map_err(|error| error.report())?;
            Ok((claim, expanded))
        }
        Selection::Claim(claim) => {
            let expanded = match inputs {
                CInput::Bundle(sources) => match project {
                    Some(project) => expand_c0_project_claim_source_by_label(
                        project,
                        &source_refs(sources),
                        claim,
                    ),
                    None => {
                        expand_c0_claim_source_by_label(click_source, &source_refs(sources), claim)
                    }
                },
                CInput::Prepared(imports) => match project {
                    Some(project) => {
                        expand_c0_prepared_project_claim_source_by_label(project, imports, claim)
                    }
                    None => expand_c0_prepared_claim_source_by_label(click_source, imports, claim),
                },
                CInput::PreparedCpp(import) => match project {
                    Some(project) => {
                        expand_cpp_prepared_project_claim_source_by_label(project, import, claim)
                    }
                    None => expand_cpp_prepared_claim_source_by_label(click_source, import, claim),
                },
            }
            .map_err(|error| error.report())?;
            Ok((claim.clone(), expanded))
        }
    }
}

fn generate_expansion<R>(
    time_limit: Duration,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    let (result, events) = click::instrumentation::collect(|| {
        click::instrumentation::with_tactic_limits(
            click::instrumentation::TacticLimits {
                smart: time_limit,
                ..click::instrumentation::TacticLimits::default()
            },
            operation,
        )
    });
    if click::instrumentation::deadline_exceeded() {
        return Err(expansion_deadline_error(
            "generating the selected tactic certificate",
            &events,
        ));
    }
    result
}

fn check_expansion_deadline(stage: &str) -> Result<(), String> {
    if click::instrumentation::deadline_exceeded() {
        Err(format!(
            "expansion time limit exceeded while {stage}: {}",
            click::instrumentation::deadline_context()
        ))
    } else {
        Ok(())
    }
}

fn expansion_deadline_error(
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
    format!(
        "expansion time limit exceeded while {stage}: {}",
        interrupted.unwrap_or_else(|| "verification driver".to_string())
    )
}

fn selected_claim(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &CInput,
    line: usize,
    column: usize,
) -> Result<String, String> {
    let sites = match inputs {
        CInput::Bundle(sources) => match project {
            Some(project) => c0_project_smart_tactic_source_sites(project, &source_refs(sources)),
            None => c0_smart_tactic_source_sites(click_source, &source_refs(sources)),
        },
        CInput::Prepared(imports) => match project {
            Some(project) => c0_prepared_project_smart_tactic_source_sites(project, imports),
            None => c0_prepared_smart_tactic_source_sites(click_source, imports),
        },
        CInput::PreparedCpp(import) => match project {
            Some(project) => cpp_prepared_project_smart_tactic_source_sites(project, import),
            None => cpp_prepared_smart_tactic_source_sites(click_source, import),
        },
    }
    .map_err(|error| error.report())?;
    sites
        .into_iter()
        .find_map(|site| {
            let position = match inputs {
                CInput::Bundle(sources) => match project {
                    Some(project) => c0_project_tactic_source_position(
                        project,
                        &source_refs(sources),
                        &site.claim_label,
                        site.source_index,
                    ),
                    None => c0_tactic_source_position(
                        click_source,
                        &source_refs(sources),
                        &site.claim_label,
                        site.source_index,
                    ),
                },
                CInput::Prepared(imports) => match project {
                    Some(project) => c0_prepared_project_tactic_source_position(
                        project,
                        imports,
                        &site.claim_label,
                        site.source_index,
                    ),
                    None => c0_prepared_tactic_source_position(
                        click_source,
                        imports,
                        &site.claim_label,
                        site.source_index,
                    ),
                },
                CInput::PreparedCpp(import) => match project {
                    Some(project) => cpp_prepared_project_tactic_source_position(
                        project,
                        import,
                        &site.claim_label,
                        site.source_index,
                    ),
                    None => cpp_prepared_tactic_source_position(
                        click_source,
                        import,
                        &site.claim_label,
                        site.source_index,
                    ),
                },
            }
            .ok()?;
            (position.line == line && position.column == column).then_some(site.claim_label)
        })
        .ok_or_else(|| "source location does not select a smart tactic".to_string())
}

fn verify_expansion(
    project: Option<&ClickProject>,
    expanded: &str,
    inputs: &CInput,
    claim: &str,
    smart_limit: Duration,
) -> Result<(), String> {
    let (result, events) = click::instrumentation::collect(|| {
        click::instrumentation::with_tactic_limits(
            click::instrumentation::TacticLimits {
                smart: smart_limit,
                ..click::instrumentation::TacticLimits::default()
            },
            || {
                let position = match inputs {
                    CInput::Bundle(sources) => match project {
                        Some(project) => {
                            let rewritten = project.with_entry_source(expanded.to_string());
                            c0_project_tactic_source_position(
                                &rewritten,
                                &source_refs(sources),
                                claim,
                                0,
                            )
                        }
                        None => {
                            c0_tactic_source_position(expanded, &source_refs(sources), claim, 0)
                        }
                    },
                    CInput::Prepared(imports) => match project {
                        Some(project) => c0_prepared_project_tactic_source_position(
                            &project.with_entry_source(expanded.to_string()),
                            imports,
                            claim,
                            0,
                        ),
                        None => c0_prepared_tactic_source_position(expanded, imports, claim, 0),
                    },
                    CInput::PreparedCpp(import) => match project {
                        Some(project) => cpp_prepared_project_tactic_source_position(
                            &project.with_entry_source(expanded.to_string()),
                            import,
                            claim,
                            0,
                        ),
                        None => cpp_prepared_tactic_source_position(expanded, import, claim, 0),
                    },
                }
                .map_err(|error| error.report())?;
                let result = match inputs {
                    CInput::Bundle(sources) => match project {
                        Some(project) => verify_c0_project_at(
                            &project.with_entry_source(expanded.to_string()),
                            &source_refs(sources),
                            position.line,
                            position.column,
                        ),
                        None => verify_c0_sources_at(
                            expanded,
                            &source_refs(sources),
                            position.line,
                            position.column,
                        ),
                    },
                    CInput::Prepared(imports) => match project {
                        Some(project) => verify_c0_prepared_project_at(
                            &project.with_entry_source(expanded.to_string()),
                            imports,
                            position.line,
                            position.column,
                        ),
                        None => verify_c0_prepared_sources_at(
                            expanded,
                            imports,
                            position.line,
                            position.column,
                        ),
                    },
                    CInput::PreparedCpp(import) => match project {
                        Some(project) => verify_cpp_prepared_project_at(
                            &project.with_entry_source(expanded.to_string()),
                            import,
                            position.line,
                            position.column,
                        ),
                        None => verify_cpp_prepared_sources_at(
                            expanded,
                            import,
                            position.line,
                            position.column,
                        ),
                    },
                };
                result
                    .map(|_| ())
                    .map_err(|error| format!("expanded proof did not verify: {}", error.report()))
            },
        )
    });
    if click::instrumentation::deadline_exceeded() {
        return Err(expansion_deadline_error(
            "checking the generated certificate",
            &events,
        ));
    }
    result
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
    fn resource_pattern_exit_simp_expansion_checks() {
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
            .find(|(_, line)| *line == "    simp();")
            .expect("fixture should contain an exit simp");
        let click_line = line_index + 1;
        let column = line.find("simp()").unwrap() + 1;
        let sources = source_refs(&mdtest.c_sources);
        let expanded = expand_c0_tactic_source_at(click_source, &sources, click_line, column)
            .expect("exit simp should generate a certificate");
        click::surface::verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!(
                "resource-pattern exit simp expansion should check: {}\n{expanded}",
                error.message()
            )
        });
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
        assert_eq!(before.time_limit, Duration::from_secs(30));
        assert_eq!(before.output, None);
        assert!(!before.in_place);
        let default = parse_arguments(["example.click:12:5".to_string()])
            .expect("the default expansion should be bounded");
        assert_eq!(default.time_limit, DEFAULT_EXPANSION_TIME_LIMIT);
    }

    #[test]
    fn reports_an_expired_expansion_deadline_directly() {
        let error = click::instrumentation::with_deadline(Duration::ZERO, || {
            check_expansion_deadline("checking a generated certificate")
        })
        .expect_err("an expired expansion deadline should fail directly");

        assert!(
            error.starts_with(
                "expansion time limit exceeded while checking a generated certificate:"
            ),
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
    ensures result == x by { execute(); simp(); }
}
"#;
        let click_path = directory.join("project.click");
        let output_path = directory.join("expanded.click");
        fs::write(directory.join("identity.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let position = c0_tactic_source_position(
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

        assert!(error.contains("expansion time limit exceeded"), "{error}");
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
                column: 7
            }
        );
        assert_eq!(arguments.time_limit, Duration::from_secs(30));
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
    ensures result == x by { execute(); simp(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("good.c"), good_c).unwrap();
        fs::write(directory.join("bad.c"), bad_c).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let sources = [("good.c", good_c), ("bad.c", bad_c)];
        let position = c0_tactic_source_position(click_source, &sources, "good.ensures_0", 0)
            .expect("selected tactic should have a source position");
        let arguments = Arguments {
            click_path,
            selection: Selection::Tactic {
                line: position.line,
                column: position.column,
            },
            time_limit: DEFAULT_EXPANSION_TIME_LIMIT,
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments)
            .expect("the command should ignore an unrelated broken proof during expansion");

        assert_ne!(expanded, click_source);
        assert!(
            expanded.ends_with("int32 bad(int32 x) {\n    ensures result == x + 1 by simp;\n}\n")
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
} by {
    execute();
    simp();
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("identity.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let arguments = Arguments {
            click_path,
            selection: Selection::Claim("identity.contract".to_string()),
            time_limit: DEFAULT_EXPANSION_TIME_LIMIT,
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments).expect("the whole claim should expand and check");

        assert_ne!(expanded, click_source);
        assert!(!expanded.contains("execute();"));
        assert!(!expanded.contains("simp();"));
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
    ensures x == x by { simp(); }
}
"#;
        fs::write(&click_path, click_source).unwrap();
        let arguments = Arguments {
            click_path,
            selection: Selection::Claim("successor.ensures_0".to_string()),
            time_limit: DEFAULT_EXPANSION_TIME_LIMIT,
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments).expect("pure theorem claims should expand by label");

        assert_ne!(expanded, click_source);
        assert!(!expanded.contains("simp();"));
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
    ensures x + 1 > x by { simp(); }
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
            time_limit: DEFAULT_EXPANSION_TIME_LIMIT,
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments)
            .expect("Integer theorem applications should expand and independently recheck");

        assert_ne!(expanded, click_source);
        assert!(!expanded.contains("apply(add_one(x));"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn generated_proof_check_uses_the_command_limit_for_remaining_smart_tactics() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x by auto;
}
"#;

        let result = click::instrumentation::with_tactic_limits(
            click::instrumentation::TacticLimits {
                smart: Duration::ZERO,
                ..click::instrumentation::TacticLimits::default()
            },
            || {
                let inputs = CInput::Bundle(vec![("identity.c".to_string(), c_source.to_string())]);
                verify_expansion(
                    None,
                    click_source,
                    &inputs,
                    "identity.ensures_0",
                    Duration::from_secs(1),
                )
            },
        );

        result.expect("generated-proof verification should install its own smart limit");
    }
}

#[cfg(test)]
mod output_context_tests {
    use super::*;
    use click::cli::CInput;
    use click::surface::verify_c0_sources;

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
    ensures result == x by { execute(); simp(); }
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
        let inputs = read_c_inputs(output, &emitted)
            .expect("the emitted artifact must load its inputs at the output path");
        let sources = match inputs {
            CInput::Bundle(sources) => sources,
            _ => panic!("a source-bundle expansion must select a source bundle"),
        };
        verify_c0_sources(&emitted, &[(&sources[0].0, sources[0].1.as_str())])
            .expect("the emitted artifact must verify through the output-path loading rules");
    }

    #[test]
    fn output_in_another_directory_rebases_declared_sources_and_verifies_there() {
        let (directory, click_path, _) =
            setup_source_bundle(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        // An unrelated C file with the same name in the output directory must
        // not silently become the selected input.
        fs::write(
            directory.join("out/identity.c"),
            "int32 decoy() { return 7; }",
        )
        .unwrap();
        let output = directory.join("out/identity.click");

        entry_with([
            "--claim".to_string(),
            "identity.ensures_0".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            click_path.display().to_string(),
        ])
        .expect("expansion into another directory rebases and verifies the artifact");

        let emitted = fs::read_to_string(&output).unwrap();
        assert!(
            emitted.starts_with("verifying \"../source/identity.c\";\n"),
            "relocated declarations must select the original source: {emitted}"
        );
        assert_emitted_verifies(&output);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn output_in_the_same_directory_keeps_declared_sources_unrebased() {
        let (directory, click_path, _) =
            setup_source_bundle(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let output = directory.join("source/expanded.click");

        entry_with([
            "--claim".to_string(),
            "identity.ensures_0".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            click_path.display().to_string(),
        ])
        .expect("expansion within the source directory needs no rebasing");

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
    use click::languages::c::compiler_import::create_lock;

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
        let config = serde_json::json!({
            "schema": 1,
            "target": "x86_64-linux-kernel",
            "compiler": "/usr/bin/gcc",
            "working_directory": ".",
            "environment": {"allow": {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "SOURCE_DATE_EPOCH": "0"}},
            "sources": [{"logical_source": "main.c", "path": "main.c", "args": ["-DVARIANT=1", "-isystem", "configured"], "artifact": "main.i"}]
        });
        let config_path = directory.join("main.click.import.json");
        fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
        create_lock(&config_path).expect("lock the prepared import");
        directory
    }

    #[test]
    fn a_relocated_prepared_import_sidecar_refuses_output_and_writes_nothing() {
        let directory = setup_prepared(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let output_directory = directory.join("out");
        fs::create_dir(&output_directory).unwrap();
        let output = output_directory.join("main.click");

        let error = entry_with([
            "--claim".to_string(),
            "from_header.ensures_0".to_string(),
            "--output".to_string(),
            output.display().to_string(),
            directory.join("main.click").display().to_string(),
        ])
        .expect_err("a relocated prepared sidecar cannot preserve its context");

        assert!(error.contains("prepared import"), "{error}");
        assert!(
            !output.exists(),
            "a rejected relocation must not write the artifact"
        );
        assert!(
            fs::read_dir(&output_directory).unwrap().count() == 0,
            "a rejected relocation must not leave staged artifacts"
        );
        // A renamed sidecar beside its manifest loses manifest identity too.
        let renamed = directory.join("renamed.click");
        let rename_error = entry_with([
            "--claim".to_string(),
            "from_header.ensures_0".to_string(),
            "--output".to_string(),
            renamed.display().to_string(),
            directory.join("main.click").display().to_string(),
        ])
        .expect_err("renaming a prepared sidecar cannot preserve its manifest identity");
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
    fn the_prepared_fixture_selects_the_prepared_input_route() {
        let directory = setup_prepared(TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed));
        let click_path = directory.join("main.click");
        let inputs = read_c_inputs(&click_path, &fs::read_to_string(&click_path).unwrap())
            .expect("a locked manifest must select the prepared route");
        assert!(inputs.is_prepared(), "the fixture must be prepared");
        fs::remove_dir_all(directory).unwrap();
    }
}
