# P2: Extend bounded control flow

The selected P1 control-flow milestone is complete: structured C loops and
loop exits, constant-expression-label `switch`, checked forward `goto` cleanup, and the
bounded C++ cleanup/unwind profile all have checked execution and regression
coverage. This issue records the smaller, independently motivated extensions
that can improve ordinary control-flow coverage without taking on general
backward or irreducible `goto`.

This is deliberately not the home for verifier-wide control-flow soundness
audits. Put those findings in [`bughunt.md`](bughunt.md). General backward,
multi-entry, and irreducible jump graphs remain deferred in
[`goto.md`](goto.md).

## Relative difficulty

These are qualitative implementation sizes, not time estimates.

| Slice | Relative size | Tricky part |
| --- | --- | --- |
| Calls in short-circuit operands | Medium | Preserve lazy evaluation while carrying call effects, resources, and outcome-specific state only through the selected operand. |
| Broader `switch` support | Medium, then high for cleanup-heavy cases | Keep case selection, fallthrough, `break`, loop nesting, and cleanup edges aligned as switch nesting grows. |
| Broader cleanup and unwind edges | High | Extend the checked edge and constructed-object model without guessing language-specific lifetime effects or merging normal and exceptional states. |

The first two can build on the existing C execution frontier. The cleanup
slice can reuse the selected C++ architecture, but each new source shape needs
an explicit importer profile and a separate trust-boundary decision.

## Slice A: calls in short-circuit operands

Existing C expressions such as `first() && second()` and `first() || second()`
must retain C's conditional evaluation. The unselected call must not execute,
contribute a memory effect, consume a resource, or impose a proof obligation.
This is a focused lowering problem, but it is not merely expression syntax:
the selected call can mutate state or have distinct returned and exceptional
outcomes.

The former standalone issue is folded into this slice. Keep the original C
regression in `mdtests/qualified_static_wide_values.md`; do not rewrite it
into an explicit `if` or introduce proof-only locals.

Acceptance requires nested `&&`/`||`, selected and unselected writes, calls
that would be undefined if evaluated on the unselected path, expansion and
reverification, and `scripts/check.sh`.

## Slice B: broaden the supported `switch` shape

The implementation now supports integer constant-expression labels in one
compound body while retaining direct children and the existing checked
fallthrough model. This was the intended medium-sized parser/lowering slice.

The nested-switch ownership and basic automatic-scope cleanup slice is now
covered: an inner `break` exits the innermost switch, fallthrough keeps an
inner local alive, a `continue` reaches the innermost enclosing loop and
retires that local, and a scalar `return` reads it before cleanup. A case-local
constructed on only one dispatch path is also retired correctly when sibling
paths join after the switch; escaped pointers are rejected after each tested
exit and join. The remaining harder follow-up is broader cleanup and unwind
behavior across more complex scope and path joins. Jumping into or across a
switch remains part of `goto.md`, not this slice.

Acceptance should include positive and negative tests for constant labels,
fallthrough, duplicate labels, nested switch ownership, loop nesting, and
cleanup on every reachable exit. Expansion and `scripts/check.sh` must agree
with ordinary verification.

## Slice C: broader cleanup and unwind edges

The selected C++ profile already checks a bounded scalar exception, matching
handler, and up to two non-throwing destructible guards. Broader support is a
larger architectural slice, not a routine follow-up test. Candidate shapes
include more constructed objects, richer handler selection, and additional
normal or exceptional scope exits.

The hard requirements are to preserve the constructed-object stack, emit
destruction in the language-defined order, keep returned and thrown states
separate, and reject unsupported constructor/destructor or handler behavior.
The importer must record the selected compiler/profile assumptions; ABI
landing pads and runtime behavior are not proof evidence. General backward or
irreducible edges, rethrow, `setjmp`/`longjmp`, and throwing destructors remain
out of scope here.

Do not start this slice without a small source example that identifies the
newly supported edge shape and its hostile negative. A regression must cover
both the normal and exceptional outcomes, expansion/reverification, and the
relevant deterministic scaling boundary.

## Shared invariant

Every accepted transfer or conditionally evaluated operation carries the
complete state and obligations at that point. Skipped statements and
unselected operands contribute no effects; cleanup runs exactly for objects
whose construction completed; and every accepted path remains visible in the
checked certificate.

## Suggested order

1. Calls in short-circuit operands.
2. A narrowly motivated cleanup/unwind extension around nested switches.

Revisit general `goto` only after its edge, scope, and termination model is
designed independently in [`goto.md`](goto.md).
