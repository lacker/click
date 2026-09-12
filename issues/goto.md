# Model forward and backward `goto` edges

Found during the 2026-09-03 control-flow follow-up after commit 184b4ef2.

C0 has no labels or `goto`. This is a separate problem from structured loop
control: the current kernel executes a statement tree with a remaining-source
tail, while the proof frontier assumes that source indices advance through
that tree except for loop continuations. A `goto` can skip that tail, enter a
different source region, or create a backward edge. Treating it as `break`, a
hidden flag, or a source rewrite would lose the C control-flow semantics that
Click is meant to verify.

## Cross-language edge design

Design the execution frontier and checked edges with the future language
frontends in mind. The shared control-flow discussion is in
[Supporting more languages](../design/supporting-more-languages.md#control-flow-goto-and-implicit-cleanup).
The P1 [basic C++ slice](basic-cpp-support.md) needs implicit cleanup on
ordinary scope exits and returns; it can land before general C goto.

A target label alone is not enough for every language. An edge may need
checked scope-exit operations, object-lifetime changes, and a distinction
between normal transfer and unwinding. C++ can require destructors on scope
exit and restrict jumps across initialization. Rust MIR has block edges and
conditional drops, even though Rust has no source `goto`. Loan expiration
must remain distinct from lexical scope exit and object destruction.

Keep the edge mechanism shared and its legality/cleanup rules language-specific.
In particular, do not apply C++ initialization restrictions to every C jump,
or assume that skipped lexical statements account for all implicit effects.
Capturing a return value must precede the cleanups required before returning
to the caller. Carry source attribution for those implicit operations into
the certificate and diagnostics.

Before fixing the representation, check it against a forward C cleanup jump,
a C++ RAII early return, and a Rust conditional-drop edge. These are design
checks; this issue does not require implementing the other language frontends
or exception handling. Reuse cleanup-edge work from the basic C++ issue
without introducing a dependency cycle between the two issues.

## Violated invariant

Every accepted C control-flow edge must be represented in the kernel semantics
and in the checked proof certificate. A jump must carry the complete C state
at the jump, apply any required checked scope-exit effects, and resume exactly
at its target. Ordinary statements skipped by the jump execute on neither
the jump path nor its proof trace.

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
- The edge/scope representation has an explicit account of the C++ cleanup
  and Rust drop design checks above, with language-specific legality and
  reserved normal/unwind distinctions. It does not require a second proof
  engine or treat every scope exit as automatic loan recovery.
- Backward jumps remain rejected until a termination rule handles their cycle;
  later support must include a deterministic termination regression rather than
  relying on an execution budget.
- The goto regressions and `scripts/check.sh` pass.
