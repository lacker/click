# Model forward and backward `goto` edges

Found during the 2026-09-03 control-flow follow-up after commit 184b4ef2.

C0 has no labels or `goto`. This is a separate problem from structured loop
control: the current kernel executes a statement tree with a remaining-source
tail, while the proof frontier assumes that source indices advance through
that tree except for loop continuations. A `goto` can skip that tail, enter a
different source region, or create a backward edge. Treating it as `break`, a
hidden flag, or a source rewrite would lose the C control-flow semantics that
Click is meant to verify.

## Violated invariant

Every accepted C control-flow edge must be represented in the kernel semantics
and in the checked proof certificate. A jump must preserve the complete C state
at the jump and resume exactly at its target, while statements between the
jump and target execute on neither the jump path nor its proof trace.

## Intended regression

Start with the forward cleanup idiom, then add the general edge cases:

1. A conditional forward `goto cleanup;` that skips ordinary statements and
   reaches a function-scope cleanup label on both the normal and error paths.
2. A jump from inside an `if` to a later label, checking that the two paths
   retain distinct state until their checked join at the label.
3. Diagnostics for an unknown label, duplicate label, a backward jump, and a
   jump into a loop, switch, or declaration scope until those shapes are
   explicitly supported.

## Acceptance criteria

- The parser records labels and `goto` targets, rejects unknown and duplicate
  labels, and reports unsupported jump shapes without changing the C source.
- The first semantic slice supports forward jumps to function-scope labels,
  including the cleanup idiom, with no bypass of a declaration whose runtime
  initialization must execute before the target.
- The kernel represents a jump as a checked control-flow edge carrying its
  target and post-jump state; execution does not emulate the edge with a
  proof-only local or a hidden conditional flag.
- The execution frontier and source layout can resume at a target label, and
  the certificate records and validates the jump edge and all skipped source.
  Paths that converge at a label use an independently checked state/fact join.
- Backward jumps remain rejected until a termination rule handles their cycle;
  later support must include a deterministic termination regression rather than
  relying on an execution budget.
- The goto regressions and `scripts/check.sh` pass.
