# Audit

Audit checks more than ordinary verification. It evaluates whether smart proof
sites remain discoverable, expandable into normally verifiable source, and
within the project's performance policy.

An audit session discovers applicable proof sites, performs bounded expansion,
verifies the resulting proof, and records performance. Site-specific deadlines
contain one operation; the session deadline bounds the complete run. Selection
options let maintainers resume at a source location, restrict claims, or audit
only changes since a Git revision.

The stages protect different invariants:

- discovery must identify the intended smart proof sites deterministically;
- expansion must extract and render the checked operations attributed to the
  selected site;
- ordinary verification must accept the complete rewritten source;
- performance comparison must remain inside the configured slack and limits.

`--keep-going` gathers further independent failures after a site fails. It
doesn't make the run successful. A whole-session timeout can leave only a
diagnostic frontier; never treat partial audit results as a complete pass.

For stage defaults, selection, and exit behavior, see [`click audit`](../reference/cli/audit.md).
