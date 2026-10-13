# Audit

Audit checks more than ordinary verification: it evaluates whether smart proof
sites remain discoverable, expandable into normally verifiable source, and
within the project's performance policy.

An audit session discovers applicable proof sites, performs bounded expansion,
verifies the resulting proof, and records performance. Each phase is judged by
the deterministic work it spends, so machine load cannot change a verdict;
wall-clock time is reported as information, a phase's time limit only
contains a hung run, and the whole-run time limit paces a long audit at a
resumable cursor. Selection
options let maintainers resume at a source location, restrict claims, or audit
only changes since a Git revision.

The stages protect different invariants:

- discovery must identify the intended smart proof sites deterministically;
- expansion must extract and render the checked operations attributed to the
  selected site;
- ordinary verification must accept the complete rewritten source;
- the expanded proof's deterministic work must remain inside the configured
  ratio and slack of the original's.

A claim whose sites are all selected is expanded once, with every site
together. Expanding one site runs its whole claim, so expanding the sites one
at a time costs the claim once per site. A failure of whole-claim expansion
fails the audit. The per-site path is used only for a partial selection of a
claim, such as resuming inside it with `--start-at` or using `--max-sites`.

`--keep-going` gathers further independent failures after a site fails. It
doesn't make the run successful. A whole-session timeout can leave only a
diagnostic frontier; never treat partial audit results as a complete pass.

For stage defaults, selection, and exit behavior, see [`click audit`](../reference/cli/audit.md).
