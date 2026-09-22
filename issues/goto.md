# P2: General backward and irreducible `goto`

Found during the 2026-09-03 control-flow follow-up after commit 184b4ef2.

The P1 forward-cleanup prerequisite for the selected control-flow demo landed
in commits `9e247956`,
`2e3bdcb9`, and the cleanup-chain regression linked below. Click now has
checked forward edges from function bodies and `if` arms to later
function-scope labels, exact target resumption, path joins, and chained
ordinary C cleanup. This issue now tracks only the deferred general jump
shapes.

C0 accepts the documented forward subset and one narrow reducible natural-cycle
subset: a direct function-body entry label with exactly one backward edge in
the re-entered region. That edge may be nested in an `if`, and the existing
`loop` proof supplies its invariant and termination evidence. General
general backward edges, jumps involving loops or switches, labels nested below
the function body, and edges across unsupported declaration scopes remain
rejected. Treating those shapes as
`break`, a hidden flag, or a source rewrite would lose the C control-flow
semantics that Click is meant to verify.

## Cross-language edge design

Design the execution frontier and checked edges with the future language
frontends in mind. The shared control-flow discussion is in
[Supporting more languages](../design/supporting-more-languages.md#control-flow-goto-and-implicit-cleanup).
The delivered [basic C++ slice](../examples/basic-cpp/README.md) implements
implicit cleanup on ordinary scope exits and returns without general C goto.
The [one-guard exception regression](../mdtests/cpp_one_guard_unwind.md) now
checks cleanup on one exceptional call edge as well; the completed bounded
two-guard unwinding case is recorded in the
[control-flow architecture note](../docs/internals/architecture.md#selected-control-flow-and-c-cleanup-model).

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
or exception handling. The control-flow demo owns the selected cross-call C++
exception probe. Reuse the basic C++ cleanup-edge work without introducing a
dependency cycle between the remaining issues.

## Violated invariant

Every accepted C control-flow edge must be represented in the kernel semantics
and in the checked proof certificate. A jump must carry the complete C state
at the jump, apply any required checked scope-exit effects, and resume exactly
at its target. Ordinary statements skipped by the jump execute on neither
the jump path nor its proof trace.

## Delivered forward boundary

The durable regressions are
[`forward_goto_direct.md`](../mdtests/forward_goto_direct.md),
[`forward_goto_conditional.md`](../mdtests/forward_goto_conditional.md), and
[`forward_goto_cleanup_chain.md`](../mdtests/forward_goto_cleanup_chain.md).
They cover checked edges, skipped statements and conditionals, conditional
path joins, label chains, allocation cleanup, expansion, and hostile missing
cleanup. Parser tests retain the unsupported-shape diagnostics.

The first natural-cycle regressions are
[`natural_goto_cycle.md`](../mdtests/natural_goto_cycle.md) and
[`natural_goto_conditional_backedge.md`](../mdtests/natural_goto_conditional_backedge.md).

## Intended regression

The delivered natural-cycle slice covers a small backward edge whose cycle has
an explicit invariant and deterministic termination measure. The proof resumes
at the exact label with the current path state, rejects an omitted or
non-decreasing measure, and expands to a checkable certificate. The remaining
work is one independently motivated multi-entry or irreducible shape only if
its edge invariants and source attribution have a bounded rule; do not infer
general support from the simple cycle.

## Acceptance criteria

- Backward edges use explicit checked invariants and termination evidence;
  an execution or tactic budget is never accepted as a termination proof.
- The parser assigns each accepted edge a source-attributed target and rejects
  entry into scopes whose declarations or language-specific lifetime rules
  make the edge illegal.
- The kernel edge carries its exact state, obligations, and target through a
  checked certificate without hidden flags or source rewrites.
- Multiple entries or irreducible regions, if added, state and check their
  join interface per incoming edge without scanning or cloning unrelated
  function state.
- The edge/scope representation has an explicit account of the C++ cleanup
  and Rust drop design checks above, with language-specific legality and
  reserved normal/unwind distinctions. It does not require a second proof
  engine or treat every scope exit as automatic loan recovery.
- The general-jump regressions and `scripts/check.sh` pass.
