use click::instrumentation;
use click::surface::{ClickError, ClickErrorKind};

const QUICK_SOLVE_WORK_LIMIT: usize = 50_000;

pub fn check_quick_solve(
    samples: &[instrumentation::TacticWorkSample],
    result: &Result<(), ClickError>,
) -> Result<(), String> {
    let work_limit = std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS")
        .is_none()
        .then_some(QUICK_SOLVE_WORK_LIMIT);
    check_quick_solve_with_limit(samples, result, work_limit)
}

pub fn check_quick_solve_with_limit(
    samples: &[instrumentation::TacticWorkSample],
    result: &Result<(), ClickError>,
    work_limit: Option<usize>,
) -> Result<(), String> {
    if let Err(error) = result
        && (error.verification_stopped() || error.kind() == ClickErrorKind::Internal)
    {
        return Err(format!(
            "Quick Solve Test did not finish: {}",
            error.report()
        ));
    }
    // The direct check and its fallback can both have a work sample at one
    // source site. Prefer the search sample when the tactic needed search.
    let closers = samples.iter().filter(|sample| {
        sample.tactic.tactic_name == "close" && sample.tactic.claim != "program.termination"
    });
    let class = if closers.clone().any(|sample| sample.tactic.class == "smart") {
        "smart"
    } else {
        "simple"
    };
    let mut measured = closers.filter(|sample| sample.tactic.class == class);
    let Some(closer) = measured.next() else {
        return Err("Quick Solve Test must reach one explicit `close()`".into());
    };
    if measured.next().is_some() {
        return Err("Quick Solve Test ran more than one measured `close()`".into());
    }
    let work = closer.inclusive_work;
    if let Some(limit) = work_limit
        && work > limit
    {
        return Err(format!(
            "Quick Solve Test used {work} deterministic work units (limit {limit}) in `{}`",
            closer.tactic.claim
        ));
    }
    Ok(())
}
