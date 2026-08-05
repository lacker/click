# Expand slow bubble-sort smart proofs

## Problem

Two bubble-sort mdtests exceed the two-second SMART budget:

- `bubble_sort3_loop_permutation.md`: the final permutation `simp` takes about
  2.3 seconds;
- `bubble_sort3_two_pass_sorted.md`: loop 1 preservation `simp` takes about 4.1
  seconds.

Both fixtures are quarantined until their searched certificates pass the full
expansion workflow.

## Work

Expand each exact profiler site separately. Verify and reprofile the generated
certificate before editing the source, then run the audit fixed-point check. If
either expansion fails, produces excessive output, or fails replay, stop and
fix the corresponding tooling issue. Do not hand-copy ambient facts out of a
failed expansion.

## Acceptance criteria

- Both smart sites are below budget or replaced with replayable simple
  certificates.
- Replacement simple tactics remain below 500ms.
- Expanded proofs remain readable enough for these mdtests to teach their loop
  and permutation claims.
- Both quarantine entries are removed together with the verified fixes.
