# Verify provenance-preserving pointer/integer tagging

Found by the 2026-09-04 MVR audit. Linux `struct rb_node` packs a parent pointer
and color bits into `unsigned long __rb_parent_color`. The implementation casts
a pointer to `unsigned long`, adds or masks the tag, and casts the masked value
back to `struct rb_node *`. Click currently recognizes only the integer
constant zero as a pointer conversion and otherwise keeps pointers separate
from integers.

This issue is narrower than general implementation-defined pointer/integer
conversion. MVR uses one pinned LP64 compiler/target and needs a checked tagged
pointer round trip under that profile.

## Violated invariant

A pointer recovered from an integer representation may regain provenance only
when checked evidence shows that the representation came from that pointer
and that only permitted tag bits changed. Integer coincidence must never
manufacture an allocation identity or authorize memory access.

## Intended regression

Use an unchanged C fixture shaped like `rb_node`: cast an aligned `struct
node *` to `unsigned long`, set either of two low tag bits, read the tag with a
mask, clear all tag bits, and cast back. Prove that the recovered pointer is the
original pointer and that dereferencing it addresses the original allocation.

Negative regressions must reject a misaligned source, a mask that leaves a tag
bit set, modification of an address bit, an integer with no originating
pointer evidence, overflow, and a cast under a mismatched ABI profile.

## Acceptance criteria

- The selected target profile defines pointer width, integer representation,
  required alignment, and the exact supported conversion semantics.
- Pointer-to-integer conversion records opaque origin/provenance evidence
  without equating arbitrary integers and pointers.
- Checked tag operations may inspect and change only bits proven zero by the
  source pointer's alignment.
- Clearing the complete permitted tag mask permits an integer-to-pointer cast
  that restores the original pointer identity, offset, and provenance.
- Other integer-to-pointer casts remain rejected, and arithmetic overflow or
  unsupported representation behavior cannot produce a proof.
- `rb_parent`, `rb_set_parent`, `rb_set_parent_color`, and the focused positive
  and negative regressions verify; `scripts/check.sh` passes.

Related: [gnu-c-extensions.md](gnu-c-extensions.md) and
[multiple-compilers.md](multiple-compilers.md).
