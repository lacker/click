# Performance tools

Click separates proof validity, cost diagnosis, proof expansion, and workflow
auditing into distinct operations:

1. Run `click verify` to establish ordinary correctness.
2. Run `click profile` to attribute verifier work to source proof sites.
3. Expand a successful smart hotspot when an explicit proof is preferable.
4. Run `click verify` on the rewritten source.
5. Use `click audit` to check discovery, expansion, rewritten-source
   verification, and performance policy across a larger selection.

A prompt proof failure isn't a performance target. Repair the proof first. A
profile of a timeout or unexpectedly slow failure is useful only as a partial
diagnostic frontier, and a failed smart tactic has no successful proof to
expand.

High aggregate cost can come from one expensive operation or from many healthy
operations. Profiling distinguishes those cases. Expansion can remove search
from a successful smart site, but it can't eliminate legitimate proof volume
or repair an inefficient simple checker.

For the individual models, see [Profiling](profiling.md),
[Expansion](expansion.md), and [Audit](audit.md). For the complexity contract
and scaling-regression requirements, see
[Verification efficiency](../internals/verification-efficiency.md). Command
syntax and defaults belong in the [CLI reference](../reference/cli/index.md).
