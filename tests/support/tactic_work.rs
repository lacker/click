//! Per-tactic work reports for budget calibration.
//!
//! `scripts/measure-tactic-work.sh` runs the example and mdtest harnesses
//! with `CLICK_DISABLE_TACTIC_BUDGETS=1` and `CLICK_TACTIC_WORK_REPORT=DIR`.
//! Each fixture then records the deterministic work every tactic charged and
//! writes one tab-separated file into `DIR`; the script aggregates them into
//! the per-class statistics `TacticWorkLimits::default` documents. Without
//! the variable the harnesses run exactly as the gate does.

use std::fs;
use std::path::{Path, PathBuf};

use click::instrumentation::{self, TacticWorkSample};

pub const REPORT: &str = "CLICK_TACTIC_WORK_REPORT";

/// Resolves only the heaviest tactics' source positions per fixture and
/// class: enough to name every corpus-wide top-ten entry without reparsing
/// the proof for each of thousands of cheap steps.
const LOCATED_PER_CLASS: usize = 10;

pub fn report_dir() -> Option<PathBuf> {
    std::env::var_os(REPORT).map(PathBuf::from)
}

/// Runs one fixture verification, recording its tactics when a report was
/// requested.
pub fn measure<R>(operation: impl FnOnce() -> R) -> (R, Vec<TacticWorkSample>) {
    if report_dir().is_some() {
        instrumentation::collect_tactic_work(operation)
    } else {
        (operation(), Vec::new())
    }
}

/// Writes one fixture's samples as `harness fixture class work failed
/// tactic claim statement source location` rows. `locate` maps a claim and
/// source tactic index to a one-based `line:column` in `source_path`.
pub fn write(
    harness: &str,
    fixture: &str,
    source_path: &Path,
    samples: &[TacticWorkSample],
    locate: impl Fn(&str, usize) -> Option<(usize, usize)>,
) {
    let Some(dir) = report_dir() else {
        return;
    };
    let mut located = std::collections::BTreeSet::new();
    for class in ["simple", "smart", "control"] {
        let mut indices = samples
            .iter()
            .enumerate()
            .filter(|(_, sample)| sample.tactic.class == class)
            .map(|(index, sample)| (sample.work, index))
            .collect::<Vec<_>>();
        indices.sort_by(|left, right| right.cmp(left));
        located.extend(
            indices
                .into_iter()
                .take(LOCATED_PER_CLASS)
                .map(|(_, index)| index),
        );
    }
    let clean = |text: &str| text.replace(['\t', '\n', '\r'], " ");
    let mut rows = String::new();
    for (index, sample) in samples.iter().enumerate() {
        let location = if located.contains(&index) {
            match locate(&sample.tactic.claim, sample.tactic.source_index) {
                Some((line, column)) => format!("{}:{line}:{column}", source_path.display()),
                None => format!("{}:?", source_path.display()),
            }
        } else {
            "-".to_string()
        };
        rows.push_str(&format!(
            "{harness}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{location}\n",
            clean(fixture),
            clean(&sample.tactic.class),
            sample.work,
            if sample.failed { "failed" } else { "finished" },
            clean(&sample.tactic.tactic_name),
            clean(&sample.tactic.claim),
            sample.tactic.statement_index,
            sample.tactic.source_index,
        ));
    }
    let name = fixture
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '-' || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    let path = dir.join(format!("{harness}-{name}.tsv"));
    fs::create_dir_all(&dir)
        .and_then(|()| fs::write(&path, rows))
        .unwrap_or_else(|error| panic!("failed to write `{}`: {error}", path.display()));
}
