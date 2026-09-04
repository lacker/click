# Verify provenance-preserving pointer/integer tagging

Found by the 2026-09-04 MVR audit. Linux `struct rb_node` packs a parent pointer
and color bits into `unsigned long __rb_parent_color`. The implementation casts
a pointer to `unsigned long`, adds or masks the tag, and casts the masked value
back to `struct rb_node *`. Click currently recognizes only the integer
constant zero as a pointer conversion and otherwise keeps pointers separate
from integers: the parser accepts casts only to scalar integer targets, and the
evaluator reports a type mismatch when the cast source is a pointer.

This issue is narrower than general implementation-defined pointer/integer
conversion. MVR uses one pinned LP64 compiler/target and needs a checked tagged
pointer round trip under that profile. It does not wait on
[multiple-compilers.md](multiple-compilers.md): the existing `CAbi::SUPPORTED`
LP64 profile already fixes an 8-byte pointer and an 8-byte `unsigned long`,
and that single constant is the only profile fact this issue consumes.

## Pinned source shapes

The rbtree forms the design must cover, all on an `unsigned long` word `pc`
that may live in a local, a struct field, or a `WRITE_ONCE` target:

- `(unsigned long)p` for a possibly-null `struct rb_node *p`;
- `(unsigned long)p + color`, `pc + RB_BLACK`, and `pc | RB_BLACK` with the
  tag known to stay below the node alignment;
- `pc & 1` reads the tag; `pc & ~3` clears it;
- `(struct rb_node *)(pc & ~3)` and, in `rb_red_parent`, the unmasked
  `(struct rb_node *)pc` where redness proves the tag bits are zero;
- `rb_set_parent_color(node, NULL, RB_BLACK)` forms the integer `1` from a
  null pointer, and `__rb_parent(1)` must recover the canonical null pointer;
- `RB_EMPTY_NODE`: `node->__rb_parent_color == (unsigned long)node`, an
  integer equality between two pointer representations.

## Violated invariant

A pointer recovered from an integer representation may regain provenance only
when checked evidence shows that the representation came from that pointer
and that only permitted tag bits changed. Integer coincidence must never
manufacture an allocation identity or authorize memory access.

Two pointer representations compare equal as integers exactly when they name
the same block and offset with the same tag. Representations of in-bounds
pointers into distinct live blocks compare unequal. A representation compared
against an integer with no pointer origin stays undecided; it is neither
proven equal nor proven unequal.

## Design constraints

- Provenance rides on the integer term, not on a new value kind. A
  pointer-to-integer cast produces a term whose origin is the exact source
  pointer; the term flows unchanged through locals, `unsigned long` fields,
  stores, loads, and equality, so the tagged word never has to be tracked as
  a separate category of value.
- Alignment is evidence, never an assumption from the pointer's static type.
  A tag operation may change a bit only when the source pointer's address is
  proven to have that bit clear. Alignment evidence comes from the allocation
  or address-of that formed the pointer combined with its constant offset, or
  from an explicit contract proposition for pointers whose formation is not
  visible, such as function parameters in argument memory.
- Casting back requires the tag proven zero, by any means: after masking,
  or from a proposition such as the node being red. Requiring that a mask was
  syntactically applied would reject `rb_red_parent`.
- The null pointer's representation is the integer zero, so tagging null
  yields a plain small integer and clearing the tag recovers null through the
  existing constant-zero conversion.
- Tag arithmetic may not carry into address bits. Each add, or, and mask
  carries an obligation that the resulting tag stays below the proven
  alignment; an unprovable obligation is a prompt proof failure, not a
  silently truncated address.

## Intended regression

Use an unchanged C fixture shaped like `rb_node`: cast an aligned `struct
node *` to `unsigned long`, set either of two low tag bits, read the tag with a
mask, clear all tag bits, and cast back. Prove that the recovered pointer is the
original pointer and that dereferencing it addresses the original allocation.
Add the unmasked cast-back under a precondition that proves the tag is zero,
the null round trip through the integer `1`, and an `RB_EMPTY_NODE`-shaped
equality that is decided true for a self-parented node and false for a node
whose parent is a distinct live node.

Negative regressions must reject a misaligned source, a mask that leaves a tag
bit set, modification of an address bit, an integer with no originating
pointer evidence, a tag add that would carry into the address, a cast back
with a tag not proven zero, an equality against an arbitrary integer decided
either way, and a cast to an integer type narrower than the pointer.

## Acceptance criteria

- The LP64 profile defines pointer width, the integer representation of a
  pointer, required alignment, and the exact supported conversion semantics.
  Only casts between object pointers and 64-bit integer types are accepted;
  narrower integer targets are rejected.
- Pointer-to-integer conversion records opaque origin/provenance evidence
  without equating arbitrary integers and pointers.
- Pointer alignment is a checked fact derived from allocation and address-of
  evidence or stated in a contract; it is never inferred from the pointee
  type alone.
- Checked tag operations may inspect and change only bits proven zero by the
  source pointer's alignment, with a carry-free obligation on each operation.
- An integer-to-pointer cast whose tag is proven zero restores the original
  pointer identity, offset, and provenance.
- Integer equality between two pointer representations is decided by block,
  offset, and tag as stated in the invariant; equality against an integer
  without pointer origin is not decided.
- Other integer-to-pointer casts remain rejected, and arithmetic overflow or
  unsupported representation behavior cannot produce a proof.
- `rb_parent`, `rb_set_parent`, `rb_set_parent_color`, `rb_red_parent`,
  `RB_EMPTY_NODE`, and the focused positive and negative regressions verify;
  `scripts/check.sh` passes.

## Suggested slices

Each slice should land green on its own.

1. The provenance-carrying integer term, the pointer-to-`unsigned long`
   cast, cast-back when the term is syntactically an untagged address, and
   the equality rule. Covers `rb_link_node` and `RB_EMPTY_NODE`.
2. Alignment evidence: derivation from allocation and address-of, the
   contract proposition, and the misaligned negative regression.
3. Tag algebra: add, or, and-with-mask, and not, each with the tag-range
   obligation, plus cast-back under a tag-is-zero obligation. Covers
   `rb_parent`, `rb_set_parent`, `rb_set_parent_color`, `rb_color`, and
   `rb_red_parent`.
4. The remaining negative regressions.

Related: [gnu-c-extensions.md](gnu-c-extensions.md) for the `aligned`
attribute that fixes `rb_node` alignment, [struct-model.md](struct-model.md)
for field offsets feeding alignment derivation, and
[multiple-compilers.md](multiple-compilers.md) for anything beyond the single
LP64 profile.
