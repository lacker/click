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

## Language additions

Two Click spec additions are required; a third may already exist.

- `address(p)`: a spec term of type `uint64`, the integer representation of a
  pointer. It is the only way a contract or resource can describe a tagged
  word. Existing spec add, bitwise and, or, and not express tags on it, so
  `list_next` can state `ensures address(result) == node->word & ~1` and the
  kernel decides `result == next` from the equality rule.
- `aligned(p, n)`: a proposition stating that `address(p)` is a multiple of
  `n`. It may appear in `requires` clauses and as a fact inside a resource.
- A bound witness inside a resource body. A resource whose tail is recovered
  from a tagged word must name the pointer the word was built from, using the
  existing `let name: type where proposition` binder with a pointer type. The
  documentation describes that binder for proposition clauses only; if
  resource bodies reject it, extending them is part of slice 1. Do not add a
  spec-side inverse such as `origin(w)`; the existential is the honest
  statement and avoids a partial spec function.

C0 acceptance changes are separate from the spec language: casting an object
pointer to `unsigned long`, and casting `unsigned long` back to a struct
pointer. The parser currently rejects struct-pointer cast targets outright.
The provenance-carrying term, the tag algebra, the cast-back obligation, and
the equality rule are kernel work with no contract-visible syntax.

## Example: marked linked list

Before rbtree, land an `examples/` project that is real code on its own: a
singly linked list whose `next` word carries a low-bit mark for logically
deleted nodes, the sequential half of the Harris list and the same shape as
allocator and collector mark bits. It builds on `allocated-linked-list`,
reusing its recursive ownership shape.

```click
resource marked_list(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
        fact aligned(node, 8);
        let next: struct node* where node->word == address(next) + (node->word & 1);
        contains marked_list(next);
    }
}
```

Functions, each verified against unchanged C:

- `list_mark(node)` sets the low bit of the stored word;
- `list_is_marked(node)` reads it with a mask;
- `list_next(node)` clears the mask and casts back, ensuring
  `address(result) == node->word & ~1`;
- `list_count_live(head)` traverses through recovered pointers, skipping
  marked nodes, with a loop invariant over the remaining suffix;
- `list_prepend` and `list_destroy` establish and consume the resource, so
  alignment of fresh nodes comes from the allocation.

This exercises cast out, tag set and read, tag clear, cast back, dereference
through the recovered pointer, the tagged word living in a struct field, and
the null end of the list flowing through the integer zero. Only the unmasked
cast-back under a color precondition is left to the focused regression.

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
- `address(p)` and `aligned(p, n)` are documented in the language reference
  with their kernel meaning, and a resource body can bind a pointer witness.
- The marked linked list example verifies with a README, and its C sources
  are ordinary list code with no proof-only shape.
- `rb_parent`, `rb_set_parent`, `rb_set_parent_color`, `rb_red_parent`,
  `RB_EMPTY_NODE`, and the focused positive and negative regressions verify;
  `scripts/check.sh` passes.

## Suggested slices

Each slice should land green on its own.

Status: slice 1 landed on 2026-09-05 (the `PointerAddress` term, both cast
directions, the equality rule, `address(p)`, and the
`mdtests/pointer_address_*.md` regressions). Cast-back is currently
syntactic: the 64-bit value must be exactly an address term or zero. Slice 3
extends it to values proven equal to an address under the alignment and tag
obligations. The resource-body pointer witness has not yet been exercised.

Slice 2 landed the same day: `aligned(p, n)` as sugar for
`address(p) & (n - 1) == 0`, decided from a heap base (16 bytes), from the
address-of fact recorded for declared scalar locals, globals, and statics,
or from an explicit contract or resource fact, and propagated through
constant byte displacements. The smart closure records a typed
`PointerAlignment` evidence whose certificate is one `arithmetic() using`
step (or `normalize` for a heap base). Regressions are
`mdtests/aligned_*.md`. Not yet covered: globals and statics (a fact on
every implicit address-of read reshaped unrelated call summaries, so their
alignment should be recorded once at block creation), stack aggregates
(struct locals), symbolic displacements, and derivation from struct-object
resources.

Slice 3 landed the same day: tagged words `address(p) + t` are recognized
through exact identities and, under decided alignment and tag-bound
conditions, through `| b`, `& ~m`, and `& m`; the cast back records
undecided conditions as obligations and fails promptly on refuted ones; a
word's form may come from one recorded 64-bit equality such as a contract
or resource fact. Equalities between tagged words, against zero, and of
masked tags are decided with a typed `PointerWord` evidence whose
certificate is one `arithmetic() using` step naming the facts used.
Regressions are `mdtests/tagged_pointer_*.md`. The C0 front end no longer
carries a struct identity through a cast to an integer, so
`(unsigned long)p + 1` is integer arithmetic.

Slice 4 landed the same day: a resource body binds a pointer witness with
`let next: struct node* where ...;` (`docs/reference/language/index.md`);
its identity is inferred from the `where` fact's word when the word is a
recorded tagged address, otherwise from the unique held child fact a fold
would consume, and otherwise a fresh symbolic pointer named by the
instantiating body; `object(p)` cells take the struct layout's field types
so a `uint64` word reads back as itself (pointer fields keep their int32
words); and `decreases resource` accepts a recursive call whose argument
the pure kernel decides equal to a witness child from the instantiated
definition. `examples/marked-linked-list/` verifies with a README.
Regressions are `mdtests/resource_witness_*.md`,
`mdtests/object_resource_uint64_field.md`, and
`mdtests/c_decreases_resource_witness_child.md`. Not yet covered from the
intended negative regressions: modification of an address bit under a mask
and a tag mask that leaves a tag bit set as separate fixtures (the unmasked
cast-back and carry fixtures reject the resulting casts), and the
`rb_parent`-family functions verified against `rb_node` itself; those remain
open under this issue.

1. The provenance-carrying integer term, the pointer-to-`unsigned long`
   cast, cast-back when the term is syntactically an untagged address, and
   the equality rule. Covers `rb_link_node` and `RB_EMPTY_NODE`.
2. Alignment evidence: derivation from allocation and address-of, the
   contract proposition, and the misaligned negative regression.
3. Tag algebra: add, or, and-with-mask, and not, each with the tag-range
   obligation, plus cast-back under a tag-is-zero obligation. Covers
   `rb_parent`, `rb_set_parent`, `rb_set_parent_color`, `rb_color`, and
   `rb_red_parent`.
4. The marked linked list example and the remaining negative regressions.

Related: [gnu-c-extensions.md](gnu-c-extensions.md) for the `aligned`
attribute that fixes `rb_node` alignment, [struct-model.md](struct-model.md)
for field offsets feeding alignment derivation, and
[multiple-compilers.md](multiple-compilers.md) for anything beyond the single
LP64 profile.
