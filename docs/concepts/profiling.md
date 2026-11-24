# Profiling

Click profiling attributes verifier work to source-level proof sites. Use it
after ordinary verification succeeds, or while diagnosing an unexpected
timeout. A profile of a non-verifying target is an incomplete frontier, not a
normal optimization baseline.

The report separates smart-tactic work, simple-tactic checking, and nested
control-tactic work. Thresholds filter categories for readability; they do
not change whether a proof is valid. The total elapsed time also includes work
that can't be charged cleanly to a single displayed site.

A successful slow smart tactic is an expansion candidate because expansion can
remove its planning and search. A slow simple tactic is already direct checked
work and is therefore a verifier performance defect, not another expansion
candidate.

The implicit tail that ends every script, an omitted proof included, is smart
work charged to the smart budget at the site after the script's last tactic.
Profile rows name the tail, its execution and its closer, `implicit tail`,
and a written `close()` or `close() using` `close`. A bare closer charges
its initial check as simple work and any fallback search as smart work. The
implicit closer that proves a simple tactic's open requirement, such as a bare
`step()`'s obligation or a bare `fold`'s body fact, is reported as its own
smart row named `implicit closer` at that tactic's site and charged to the
smart budget. A bare
simple tactic is not a selectable expansion site, so the row's expansion
command expands its claim (`click expand --claim`), which writes the proof as
the tactic's `by`.

Interpret high work counts before comparing small wall-clock differences.
Deterministic work exposes repeatable algorithmic cost, while elapsed time is
affected by machine load and warm caches. For performance-sensitive changes,
use scaling regressions over multiple input sizes rather than treating one
corpus run as evidence of acceptable complexity.

If profiling shows unexpected slowness, preserve the original source and
reduce the verifier behavior. Don't raise a limit, add an arbitrary search cap,
or rewrite working C to make the measurement disappear.

For all report filters and target syntax, see [`click profile`](../reference/cli/profile.md).
