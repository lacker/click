use super::*;
use std::fmt::Write as _;

pub(super) fn print_profiles(
    profiles: &[ProjectProfile],
    thresholds: Thresholds,
    time_limit: Duration,
    top_attribution_rows: usize,
) {
    print!(
        "{}",
        render_profiles_with_top(profiles, thresholds, time_limit, top_attribution_rows,)
    );
}

#[cfg(test)]
pub(super) fn render_profiles(
    profiles: &[ProjectProfile],
    thresholds: Thresholds,
    time_limit: Duration,
) -> String {
    render_profiles_with_top(
        profiles,
        thresholds,
        time_limit,
        DEFAULT_TOP_ATTRIBUTION_ROWS,
    )
}

pub(super) fn render_profiles_with_top(
    profiles: &[ProjectProfile],
    thresholds: Thresholds,
    time_limit: Duration,
    top_attribution_rows: usize,
) -> String {
    let has_correctness_failure = profiles
        .iter()
        .any(|profile| profile.verification_failure.is_some() && !profile.timed_out);
    let has_timeout = profiles.iter().any(|profile| profile.timed_out);
    let blocked_expansion_sources = profiles
        .iter()
        .filter(|profile| profile.verification_failure.is_some() || profile.timed_out)
        .flat_map(|profile| {
            profile
                .slow_steps
                .iter()
                .map(|step| step.key.source_path.clone())
        })
        .collect::<BTreeSet<_>>();
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
    if has_correctness_failure {
        writeln!(
            output,
            "INCOMPLETE CORRECTNESS RUN — NOT AN OPTIMIZATION PROFILE. Fix verification failures before acting on timings or expanding tactics."
        )
        .expect("writing a String cannot fail");
    }
    if has_timeout {
        writeln!(
            output,
            "TIMEOUT DIAGNOSTIC — use these partial timings to find why verification did not complete; restore a green proof before expansion."
        )
        .expect("writing a String cannot fail");
    }

    render_category(
        &mut output,
        &slow_steps,
        CategorySection {
            category: TacticCategory::Simple,
            title: "SIMPLE — FIX THE ENGINE; DO NOT EXPAND",
            advice: "A slow simple tactic is deterministic certificate replay. Reduce its verifier path and fix that bottleneck before expanding more smart tactics.",
        },
        thresholds,
        time_limit,
        &blocked_expansion_sources,
    );
    render_category(
        &mut output,
        &slow_steps,
        CategorySection {
            category: TacticCategory::Smart,
            title: "SMART — EXPAND ONLY FROM VERIFIED PROOFS",
            advice: "A successful hotspot in a fully verified proof is an expansion candidate. In an incomplete run it is diagnostic only. A failed smart search has no certificate; use smaller or explicit simple tactics unless it missed its bound or failed unclearly.",
        },
        thresholds,
        time_limit,
        &blocked_expansion_sources,
    );
    render_category(
        &mut output,
        &slow_steps,
        CategorySection {
            category: TacticCategory::Control,
            title: "CONTROL — INSPECT NESTED STEPS",
            advice: "This is a proof container. Use its nested SMART/SIMPLE timings; do not optimize or expand it based on the container row alone.",
        },
        thresholds,
        time_limit,
        &blocked_expansion_sources,
    );

    render_accounting(&mut output, profiles);
    render_work_metrics(&mut output, profiles);
    render_attribution(&mut output, profiles, top_attribution_rows);
    render_diagnoses(&mut output, profiles);

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
        match profile.interrupted.as_ref() {
            Some(InterruptedWork::Tactic(key)) => {
                writeln!(
                    output,
                    "    [{}] {}  {}  {}  statement {}",
                    key.category.label(),
                    step_location(key),
                    key.claim,
                    key.tactic_name,
                    key.statement_index
                )
                .expect("writing a String cannot fail");
                if key.category == TacticCategory::Smart {
                    writeln!(
                        output,
                        "              interrupted before a certificate was produced; reduce the search in Click"
                    )
                    .expect("writing a String cannot fail");
                }
            }
            Some(InterruptedWork::Phase(phase)) => {
                writeln!(output, "    [PHASE] {phase}").expect("writing a String cannot fail");
            }
            Some(InterruptedWork::Driver) | None => {
                writeln!(output, "    [DRIVER] verification orchestration")
                    .expect("writing a String cannot fail");
            }
        }
    }

    let has_simple_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Simple)
        || profiles.iter().any(|profile| {
            (profile.timed_out
                && matches!(
                    profile.interrupted,
                    Some(InterruptedWork::Tactic(ref key))
                        if key.category == TacticCategory::Simple
                ))
                || {
                    let simple = profile.work.category(TacticCategory::Simple);
                    simple.count > 0 && simple.average() > SIMPLE_AVERAGE_LIMIT
                }
        });
    let has_smart_candidate = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Smart && !step.failed);
    let has_smart_failure = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Smart && step.failed)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && matches!(
                    profile.interrupted,
                    Some(InterruptedWork::Tactic(ref key))
                        if key.category == TacticCategory::Smart
                )
        });
    let has_control_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Control)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && matches!(
                    profile.interrupted,
                    Some(InterruptedWork::Tactic(ref key))
                        if key.category == TacticCategory::Control
                )
        });
    let interrupted_phase = profiles.iter().find_map(|profile| {
        if profile.timed_out {
            match profile.interrupted.as_ref() {
                Some(InterruptedWork::Phase(phase)) => Some(*phase),
                Some(InterruptedWork::Driver) | None => Some("driver"),
                Some(InterruptedWork::Tactic(_)) => None,
            }
        } else {
            None
        }
    });
    let has_certification_problem = profiles.iter().any(|profile| {
        (profile.work.claims > 0
            && average_time(profile.accounting.certification, profile.work.claims)
                > CERTIFICATION_PER_CLAIM_LIMIT)
            || (profile.work.certification_paths > 0
                && average_time(
                    profile.accounting.certification,
                    profile.work.certification_paths,
                ) > CERTIFICATION_PER_PATH_LIMIT)
    });
    let has_setup_problem = profiles.iter().any(|profile| {
        profile.work.source_files > 0
            && (average_time(profile.accounting.frontend, profile.work.source_files)
                > SETUP_PER_FILE_LIMIT
                || average_time(profile.accounting.environment, profile.work.source_files)
                    > SETUP_PER_FILE_LIMIT)
    });
    let unknown_timing = profiles
        .iter()
        .filter(|profile| !profile.unknown_timing.is_empty())
        .collect::<Vec<_>>();
    if !unknown_timing.is_empty() {
        writeln!(output, "\nUNRECOGNIZED TIMING LINES").expect("writing a String cannot fail");
        writeln!(
            output,
            "  This profile skipped verifier timing output it does not understand, so the report below may be incomplete. Teach src/bin/click-profile.rs about these kinds."
        )
        .expect("writing a String cannot fail");
    }
    for profile in &unknown_timing {
        for (kind, seen) in &profile.unknown_timing {
            writeln!(
                output,
                "  {}: {} line{} of kind `{kind}`",
                profile.project,
                seen.count,
                if seen.count == 1 { "" } else { "s" }
            )
            .expect("writing a String cannot fail");
            writeln!(output, "    {}", seen.example).expect("writing a String cannot fail");
        }
    }

    let unresolved = profiles
        .iter()
        .filter(|profile| !profile.unresolved_positions.is_empty())
        .collect::<Vec<_>>();
    if !unresolved.is_empty() {
        writeln!(output, "\nSTEPS WITHOUT A SOURCE LOCATION")
            .expect("writing a String cannot fail");
        writeln!(
            output,
            "  These steps are timed and classified, but the verifier reported a tactic index the surface proof does not have — a certificate the verifier planned itself. Their times above are real; only the location is missing."
        )
        .expect("writing a String cannot fail");
    }
    for profile in &unresolved {
        for (reason, count) in &profile.unresolved_positions {
            writeln!(
                output,
                "  {}: {count} step{} — {reason}",
                profile.project,
                if *count == 1 { "" } else { "s" }
            )
            .expect("writing a String cannot fail");
        }
    }

    let has_unknown_timing = !unknown_timing.is_empty();
    // This is independent of tactic thresholds: a material invisible
    // remainder means the profile is incomplete even if every tactic is fast.
    let materially_unattributed = profiles
        .iter()
        .any(|profile| profile.accounting.materially_unattributed());
    let has_verification_failure = profiles
        .iter()
        .any(|profile| profile.verification_failure.is_some() && !profile.timed_out);
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
    } else if has_smart_failure {
        writeln!(
            output,
            "\nNEXT: decompose the failed or interrupted SMART search into smaller or explicit simple tactics. It produced no certificate, so click-expand is not available; investigate Click only if ordinary verification missed its bound or the failure is not actionable."
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
    } else if has_certification_problem {
        writeln!(
            output,
            "\nNEXT: reduce the CERTIFICATION bottleneck; tactic expansion is not the indicated fix for this rate."
        )
        .expect("writing a String cannot fail");
    } else if has_setup_problem {
        writeln!(
            output,
            "\nNEXT: reduce the SETUP bottleneck in frontend or environment construction."
        )
        .expect("writing a String cannot fail");
    } else if let Some(phase) = interrupted_phase {
        writeln!(
            output,
            "\nNEXT: the profile is incomplete because its deadline interrupted `{phase}` work. Reduce or instrument that phase before treating aggregate volume as healthy."
        )
        .expect("writing a String cannot fail");
    } else if has_unknown_timing {
        writeln!(
            output,
            "\nNEXT: nothing crossed the configured thresholds, but unrecognized timing lines mean this green is not trustworthy. Teach the parser those kinds and rerun."
        )
        .expect("writing a String cannot fail");
    } else if materially_unattributed {
        writeln!(
            output,
            "\nNEXT: nothing crossed the configured thresholds, but a material amount of wall time is UNATTRIBUTED. Instrument that machinery before reading this profile as clean."
        )
        .expect("writing a String cannot fail");
    } else if profiles.iter().any(|profile| profile.timed_out) {
        writeln!(
            output,
            "\nNEXT: the profile is incomplete because a project deadline fired; use the interrupted operation above, not aggregate volume, as the next debugging target."
        )
        .expect("writing a String cannot fail");
    } else if profiles
        .iter()
        .any(|profile| profile.accounting.denominator() >= VOLUME_REPORT_THRESHOLD)
    {
        writeln!(
            output,
            "\nNEXT: measured cost is HEALTHY VOLUME at the current baselines; reduce proof volume or improve Click's aggregate throughput rather than expanding an arbitrary tactic."
        )
        .expect("writing a String cannot fail");
    } else {
        writeln!(
            output,
            "\nNEXT: the measured run is within the current baselines."
        )
        .expect("writing a String cannot fail");
    }

    output
}

/// Prints where each profiled run's wall-clock time actually went.
///
/// The category sections above only list steps that crossed a threshold, so
/// they answer "what should I act on" but not "is this proof smart-slow or
/// simple-slow overall". This does.
fn render_accounting(output: &mut String, profiles: &[ProjectProfile]) {
    let measured = profiles
        .iter()
        .filter(|profile| !profile.accounting.denominator().is_zero())
        .collect::<Vec<_>>();
    if measured.is_empty() {
        return;
    }
    writeln!(output, "\nTIME ACCOUNTING").expect("writing a String cannot fail");
    writeln!(
        output,
        "  The total is direct verification wall time. Tactic time is exclusive, and every row is non-overlapping. VERIFIER CORE is measured function time outside tactics and certification; INTERRUPTED is unfinished active work observed at a deadline; PROCESS/DRIVER is source I/O and driver work outside emitted verifier phases."
    )
    .expect("writing a String cannot fail");
    for profile in measured {
        let accounting = profile.accounting;
        writeln!(
            output,
            "  {}: {} total{}",
            profile.project,
            format_fractional_duration(accounting.denominator()),
            if accounting.wall_total.is_zero() && accounting.total.is_zero() {
                " measured (the run reported no function total, so this is the measured time only)"
            } else {
                ""
            }
        )
        .expect("writing a String cannot fail");
        for (label, part) in [
            ("FRONTEND", accounting.frontend),
            ("ENVIRONMENT", accounting.environment),
            ("SIMPLE", accounting.simple),
            ("SMART", accounting.smart),
            ("CONTROL", accounting.control),
            ("CERTIFICATION", accounting.certification),
            ("VERIFIER CORE", accounting.verifier_core()),
            ("INTERRUPTED", accounting.interrupted),
            ("PROCESS/DRIVER", accounting.process_driver()),
            ("UNATTRIBUTED", accounting.unattributed()),
        ] {
            writeln!(
                output,
                "    {label:>13}  {:>10}  {:>5.1}%",
                format_fractional_duration(part),
                accounting.share(part),
            )
            .expect("writing a String cannot fail");
        }
    }
}

fn render_attribution(output: &mut String, profiles: &[ProjectProfile], top: usize) {
    if profiles
        .iter()
        .all(|profile| profile.attribution.is_empty())
    {
        return;
    }
    writeln!(output, "\nTOP FUNCTIONS / CLAIMS BY EXCLUSIVE TIME")
        .expect("writing a String cannot fail");
    writeln!(
        output,
        "  Function and claim rankings are two views of the same exclusive buckets; do not add them together. Within each function, its claim rows plus `<shared verifier work>` reconcile to the function total. Showing at most {top} rows in each ranking."
    )
    .expect("writing a String cannot fail");
    for profile in profiles {
        if profile.attribution.is_empty() {
            continue;
        }
        writeln!(output, "  {}:", profile.project).expect("writing a String cannot fail");
        let mut functions = profile.attribution.iter().collect::<Vec<_>>();
        functions.sort_by(|(left_name, left), (right_name, right)| {
            right
                .buckets
                .total()
                .cmp(&left.buckets.total())
                .then_with(|| left_name.cmp(right_name))
        });
        writeln!(output, "    FUNCTIONS").expect("writing a String cannot fail");
        for (name, function) in functions.into_iter().take(top) {
            let smart_sites = function
                .claims
                .values()
                .map(|claim| claim.smart_sites.len())
                .sum::<usize>();
            render_attribution_row(output, "FUNCTION", name, function.buckets, smart_sites);
        }

        let mut claims = profile
            .attribution
            .values()
            .flat_map(|function| function.claims.iter())
            .collect::<Vec<_>>();
        claims.sort_by(|(left_name, left), (right_name, right)| {
            right
                .buckets
                .total()
                .cmp(&left.buckets.total())
                .then_with(|| left_name.cmp(right_name))
        });
        writeln!(output, "    CLAIMS").expect("writing a String cannot fail");
        for (name, claim) in claims.into_iter().take(top) {
            render_attribution_row(
                output,
                "CLAIM",
                name,
                claim.buckets,
                claim.smart_sites.len(),
            );
        }
    }
}

fn render_attribution_row(
    output: &mut String,
    kind: &str,
    name: &str,
    buckets: AttributedBuckets,
    smart_sites: usize,
) {
    writeln!(
        output,
        "      {kind:<8} {name:<36} total {:>9}  simple {:>9}  smart {:>9}  control {:>9}  cert {:>9}  core {:>9}  smart {}/{} attempts/sites",
        format_fractional_duration(buckets.total()),
        format_fractional_duration(buckets.simple),
        format_fractional_duration(buckets.smart),
        format_fractional_duration(buckets.control),
        format_fractional_duration(buckets.certification),
        format_fractional_duration(buckets.verifier_core),
        buckets.smart_attempts,
        smart_sites,
    )
    .expect("writing a String cannot fail");
}

fn render_work_metrics(output: &mut String, profiles: &[ProjectProfile]) {
    let measured = profiles
        .iter()
        .filter(|profile| {
            profile.work.source_files > 0
                || profile.work.functions > 0
                || !profile.work.tactics.is_empty()
        })
        .collect::<Vec<_>>();
    if measured.is_empty() {
        return;
    }
    writeln!(output, "\nWORK AND THROUGHPUT").expect("writing a String cannot fail");
    writeln!(
        output,
        "  Counts come from completed verifier operations, not source-line estimates. C transitions are a semantic subset of SIMPLE and are not an additional time bucket."
    )
    .expect("writing a String cannot fail");
    for profile in measured {
        let work = &profile.work;
        writeln!(
            output,
            "  {}: {} file{}, {} function{}, {} claim{}, {} certification path{}",
            profile.project,
            work.source_files,
            if work.source_files == 1 { "" } else { "s" },
            work.functions,
            if work.functions == 1 { "" } else { "s" },
            work.claims,
            if work.claims == 1 { "" } else { "s" },
            work.certification_paths,
            if work.certification_paths == 1 {
                ""
            } else {
                "s"
            },
        )
        .expect("writing a String cannot fail");
        render_operation_stats(output, "C TRANSITIONS", work.c_transitions);
        for category in [
            TacticCategory::Simple,
            TacticCategory::Smart,
            TacticCategory::Control,
        ] {
            render_operation_stats(
                output,
                &format!(
                    "{} {}",
                    category.label(),
                    if category == TacticCategory::Smart {
                        "ATTEMPTS"
                    } else {
                        "COMPLETED"
                    }
                ),
                work.category(category),
            );
        }
        let failed_smart = work
            .failed_tactics
            .iter()
            .filter(|key| key.category == TacticCategory::Smart)
            .count();
        let smart_attempts = work.category(TacticCategory::Smart).count;
        if work.smart_source_sites > 0 {
            writeln!(
                output,
                "    {:>24}  {:>6} unique source sites, {:>6} dynamic attempts",
                "SMART SITES / ATTEMPTS", work.smart_source_sites, smart_attempts,
            )
            .expect("writing a String cannot fail");
            if smart_attempts > work.smart_source_sites {
                writeln!(
                    output,
                    "                           Dynamic attempts exceed source sites when paths or repeated claim execution revisit one source occurrence."
                )
                .expect("writing a String cannot fail");
            }
        }
        if smart_attempts > 0 || failed_smart > 0 {
            writeln!(
                output,
                "    {:>24}  {:>6} succeeded, {:>6} failed",
                "SMART OUTCOMES",
                smart_attempts.saturating_sub(failed_smart),
                failed_smart,
            )
            .expect("writing a String cannot fail");
        }
        if work.source_files > 0 {
            render_rate(
                output,
                "FRONTEND / FILE",
                profile.accounting.frontend,
                work.source_files,
            );
            render_rate(
                output,
                "ENVIRONMENT / FILE",
                profile.accounting.environment,
                work.source_files,
            );
        }
        if work.claims > 0 {
            render_rate(
                output,
                "CERTIFICATION / CLAIM",
                profile.accounting.certification,
                work.claims,
            );
        }
        if work.certification_paths > 0 {
            render_rate(
                output,
                "CERTIFICATION / PATH",
                profile.accounting.certification,
                work.certification_paths,
            );
        }
        let simple_kinds = work
            .tactics
            .iter()
            .filter(|((category, _), _)| *category == TacticCategory::Simple)
            .collect::<Vec<_>>();
        if !simple_kinds.is_empty() {
            writeln!(output, "    SIMPLE BY KIND").expect("writing a String cannot fail");
            for ((_, name), stats) in simple_kinds {
                render_operation_stats(output, name, *stats);
            }
        }
    }
}

fn render_operation_stats(output: &mut String, label: &str, stats: OperationStats) {
    writeln!(
        output,
        "    {label:>24}  {:>6}  total {:>10}  avg {:>10}  max {:>10}",
        stats.count,
        format_fractional_duration(stats.total),
        format_fractional_duration(stats.average()),
        format_fractional_duration(stats.max),
    )
    .expect("writing a String cannot fail");
}

fn render_rate(output: &mut String, label: &str, total: Duration, count: usize) {
    let average = average_time(total, count);
    writeln!(
        output,
        "    {label:>24}  {:>10}",
        format_fractional_duration(average),
    )
    .expect("writing a String cannot fail");
}

fn average_time(total: Duration, count: usize) -> Duration {
    if count == 0 {
        Duration::ZERO
    } else {
        total / u32::try_from(count).unwrap_or(u32::MAX)
    }
}

fn render_diagnoses(output: &mut String, profiles: &[ProjectProfile]) {
    writeln!(output, "\nDIAGNOSES").expect("writing a String cannot fail");
    writeln!(
        output,
        "  Conservative development baselines: SIMPLE average <= {}, certification <= {}/claim and <= {}/path, frontend/environment <= {}/file. Per-tactic thresholds remain the long-tail guards.",
        format_fractional_duration(SIMPLE_AVERAGE_LIMIT),
        format_fractional_duration(CERTIFICATION_PER_CLAIM_LIMIT),
        format_fractional_duration(CERTIFICATION_PER_PATH_LIMIT),
        format_fractional_duration(SETUP_PER_FILE_LIMIT),
    )
    .expect("writing a String cannot fail");
    for profile in profiles {
        writeln!(output, "  {}:", profile.project).expect("writing a String cannot fail");
        let mut findings = 0;
        if profile.timed_out {
            findings += 1;
            let active = match profile.interrupted.as_ref() {
                Some(InterruptedWork::Tactic(key)) => format!(
                    "{} tactic `{}` in `{}`",
                    key.category.label(),
                    key.tactic_name,
                    key.claim
                ),
                Some(InterruptedWork::Phase(phase)) => format!("`{phase}` phase"),
                Some(InterruptedWork::Driver) | None => "verification driver".to_string(),
            };
            writeln!(
                output,
                "    INCOMPLETE TIMEOUT — the project deadline interrupted {active}; completed counts and exclusive timings are preserved below."
            )
            .expect("writing a String cannot fail");
        }
        let simple = profile.work.category(TacticCategory::Simple);
        let slow_simple = profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Simple);
        if slow_simple || (simple.count > 0 && simple.average() > SIMPLE_AVERAGE_LIMIT) {
            findings += 1;
            writeln!(
                output,
                "    SIMPLE ENGINE BUG — deterministic replay crossed a tail or throughput bound; reduce and fix Click."
            )
            .expect("writing a String cannot fail");
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Smart && !step.failed)
        {
            findings += 1;
            if profile.verification_failure.is_some() || profile.timed_out {
                writeln!(
                    output,
                    "    SMART HOTSPOT RECORDED — restore complete verification before expanding this successful site."
                )
                .expect("writing a String cannot fail");
            } else {
                writeln!(
                    output,
                    "    SMART HOTSPOT — expand one reported successful smart site, verify the artifact, and compare its profile."
                )
                .expect("writing a String cannot fail");
            }
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Smart && step.failed)
            || (profile.timed_out
                && matches!(
                    profile.interrupted.as_ref(),
                    Some(InterruptedWork::Tactic(key))
                        if key.category == TacticCategory::Smart
                ))
        {
            findings += 1;
            writeln!(
                output,
                "    SMART SEARCH LIMIT — no certificate exists to expand; decompose the proof with smaller or explicit simple tactics. Investigate Click only if search missed its bound or failed unclearly."
            )
            .expect("writing a String cannot fail");
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Control)
        {
            findings += 1;
            writeln!(
                output,
                "    CONTROL BOTTLENECK — inspect its exclusive bookkeeping and nested tactic findings."
            )
            .expect("writing a String cannot fail");
        }
        let certification_per_claim =
            average_time(profile.accounting.certification, profile.work.claims);
        let certification_per_path = average_time(
            profile.accounting.certification,
            profile.work.certification_paths,
        );
        if (profile.work.claims > 0 && certification_per_claim > CERTIFICATION_PER_CLAIM_LIMIT)
            || (profile.work.certification_paths > 0
                && certification_per_path > CERTIFICATION_PER_PATH_LIMIT)
        {
            findings += 1;
            writeln!(
                output,
                "    CERTIFICATION BOTTLENECK — kernel certification is expensive for its measured claims or paths."
            )
            .expect("writing a String cannot fail");
        }
        let frontend_per_file =
            average_time(profile.accounting.frontend, profile.work.source_files);
        let environment_per_file =
            average_time(profile.accounting.environment, profile.work.source_files);
        if profile.work.source_files > 0
            && (frontend_per_file > SETUP_PER_FILE_LIMIT
                || environment_per_file > SETUP_PER_FILE_LIMIT)
        {
            findings += 1;
            writeln!(
                output,
                "    SETUP BOTTLENECK — frontend or environment construction is expensive for its file count."
            )
            .expect("writing a String cannot fail");
        }
        if profile.accounting.materially_unattributed() || !profile.unknown_timing.is_empty() {
            findings += 1;
            writeln!(
                output,
                "    UNEXPLAINED — a material residual or unknown timing event prevents a complete diagnosis."
            )
            .expect("writing a String cannot fail");
        }
        if profile.verification_failure.is_some() && !profile.timed_out {
            findings += 1;
            writeln!(
                output,
                "    INCOMPLETE — verification failed, so counts and rates describe only the completed frontier."
            )
            .expect("writing a String cannot fail");
        }
        if findings == 0 {
            if profile.accounting.denominator() >= VOLUME_REPORT_THRESHOLD {
                writeln!(
                    output,
                    "    HEALTHY VOLUME — no measured operation or normalized rate crossed a bound; total cost comes from work volume at the current baselines."
                )
                .expect("writing a String cannot fail");
            } else {
                writeln!(
                    output,
                    "    WITHIN BASELINE — the measured run is small and no bound was crossed."
                )
                .expect("writing a String cannot fail");
            }
        }
    }
}

struct CategorySection {
    category: TacticCategory,
    title: &'static str,
    advice: &'static str,
}

fn render_category(
    output: &mut String,
    slow_steps: &[&SlowStep],
    section: CategorySection,
    thresholds: Thresholds,
    time_limit: Duration,
    blocked_expansion_sources: &BTreeSet<PathBuf>,
) {
    writeln!(output, "\n{}", section.title).expect("writing a String cannot fail");
    writeln!(output, "  {}", section.advice).expect("writing a String cannot fail");
    let matching = slow_steps
        .iter()
        .copied()
        .filter(|step| step.key.category == section.category)
        .collect::<Vec<_>>();
    if matching.is_empty() {
        writeln!(output, "  none completed").expect("writing a String cannot fail");
        return;
    }
    if section.category == TacticCategory::Simple {
        writeln!(
            output,
            "  WARNING: expanding an enclosing smart tactic is not a fix for the simple steps below."
        )
        .expect("writing a String cannot fail");
    }
    for step in matching {
        let status = if step.failed {
            "  FAILED — no certificate to expand"
        } else if section.category == TacticCategory::Smart
            && blocked_expansion_sources.contains(&step.key.source_path)
        {
            "  INCOMPLETE RUN — restore verification before expansion"
        } else {
            ""
        };
        writeln!(
            output,
            "  {:>10}  {}  {}  {}  statement {}{}",
            format_fractional_duration(step.elapsed),
            step_location(&step.key),
            step.key.claim,
            step.key.tactic_name,
            step.key.statement_index,
            status,
        )
        .expect("writing a String cannot fail");
        if !step.failed
            && let (TacticCategory::Smart, Some(position)) = (section.category, step.key.position)
            && !blocked_expansion_sources.contains(&step.key.source_path)
        {
            render_expansion_command(output, &step.key, position, thresholds, time_limit);
        }
    }
}

/// Renders a step's `PATH:LINE:COLUMN`, or just the path when the step has no
/// surface tactic to point at.
fn step_location(key: &StepKey) -> String {
    match key.position {
        Some(position) => format!(
            "{}:{}:{}",
            key.source_path.display(),
            position.line,
            position.column
        ),
        None => format!("{} (no source location)", key.source_path.display()),
    }
}

pub(super) fn render_expansion_command(
    output: &mut String,
    key: &StepKey,
    position: SourcePosition,
    thresholds: Thresholds,
    time_limit: Duration,
) {
    let artifact = expanded_artifact_path(&key.source_path);
    let location = format!(
        "{}:{}:{}",
        key.source_path.display(),
        position.line,
        position.column
    );
    writeln!(
        output,
        "              expand: click expand --time-limit {} --output {} {}",
        format_duration(DEFAULT_EXPANSION_TIME_LIMIT),
        shell_quote(&artifact.display().to_string()),
        shell_quote(&location),
    )
    .expect("writing a String cannot fail");
    if !looks_like_mdtest(&artifact) {
        writeln!(
            output,
            "              verify: click verify {}",
            shell_quote(&artifact.display().to_string()),
        )
        .expect("writing a String cannot fail");
    }
    writeln!(
        output,
        "           reprofile: click profile --smart-threshold {} --simple-threshold {} --control-threshold {} --time-limit {} {}",
        format_duration(thresholds.smart),
        format_duration(thresholds.simple),
        format_duration(thresholds.control),
        format_duration(time_limit),
        shell_quote(&artifact.display().to_string()),
    )
    .expect("writing a String cannot fail");
}

fn expanded_artifact_path(source: &Path) -> PathBuf {
    let extension = source
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or("click");
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("expanded");
    source.with_file_name(format!("{stem}.expanded.{extension}"))
}
