# Byte representation

This page is the design record for how Click relates an object's bytes to
its typed cells: what a representation copy establishes, what a one-byte
access reads and writes, and which reinterpretations stay refused. The public
summary is in [Memory model](../concepts/memory-model.md#byte-view-of-integer-cells);
the verified demonstration is
[`examples/byte-representation/`](https://github.com/lacker/click/blob/master/examples/byte-representation/README.md).

## Selected profile

Every rule below is stated for one profile. The C is C11 under the default
kernel target: x86-64 Linux, LP64, eight-bit bytes, little-endian. The target
is selected by the sidecar (`target "..."`), and with no declaration the
default applies; there is no separate compiler import record for this
profile. Layout comes from the struct declaration under that target, so
`struct record { unsigned int tag; int *target; }` has `tag` at offset 0,
four padding bytes, `target` at offset 8, and size 16. Nothing in a proof
names an offset.

The only copy primitive is `memcpy` as declared in the embedded standard
library (`stdlib/prelude.click`):

```text
extern uint8* memcpy(uint8 destination[], uint8 source[], int32 bytes) {
    requires 0 <= bytes;
    requires viewable(source[0..bytes]);
    owns destination[0..bytes];
    requires separate(memory(destination[0..bytes]), memory(source[0..bytes]));
    ensures result == destination;
    ensures bytes_equal(destination, 0, old(source), 0, bytes);
}
```

The contract is a trusted specification of the client's view of `memcpy`,
not a proof of libc. Every sidecar that calls it reports
`external assumptions: <caller> -> memcpy`. The standard library is part of
the verifier executable, so it is part of the executable identity that
incremental baselines compare (see [Testing](testing.md)).

## Cells, not bytes

Memory holds typed cells keyed by block and offset. A store of an
`unsigned int` records one four-byte integer cell, not four bytes. Four
things stay separate:

- **Storage lifetime.** A block is live from its allocation until `free` or
  scope exit. A pointer's value does not extend it.
- **Initialized representation.** Only a stored, copied, or `calloc`-zeroed
  cell is initialized. Fresh `malloc` bytes and padding have no cell.
- **Typed load validity.** A load of type `T` reads a cell only when the cell
  holds a `T` value of the load's width, or, for a one-byte load, through the
  byte view below. Anything else is refused as a load that does not fit the
  cell's value.
- **Access permission.** `owns` or `views` authority over the range, the
  object resource a successful `malloc` produces, or a function's implicit
  access to its own locals, checked independently of the three facts above.

## The representation-copy effect

After the external `memcpy` contract havocs the destination range, the kernel
plants each source cell whose complete representation lies in the copied
range at the mapped destination offset. The effect is attached to the exact
standard-library declaration, never to the name: a user function spelled
`memcpy` with a different declaration keeps only its plain external contract
(`is_recognized_representation_copy_block` in `src/surface/verification.rs`).
The transfer is `transfer_representation_copy_cells` in
`src/kernel/functions.rs`. It is part of the kernel's call transition, so
verification, expansion and its reverification, profile, and audit all run
the same rule; there is no representation-only verifier.

Integer cells keep their values, including symbolic ones. Pointer cells keep
their allocation identity: the restored pointer names the same block and
offset as the original.

This is the C11 rule for the destination object. Heap storage from `malloc`
has no declared type, and a `memcpy` into it gives the copied bytes the
effective type of the source object (C11 6.5p6), which is what the planted
cells record. The later typed loads of `dst->tag` and `dst->target` read
exactly those cells. A load of any other type at a planted cell meets a cell
of another kind and is refused (see
[Reinterpretation stays refused](#reinterpretation-stays-refused)).

The transfer only adds observations the `bytes_equal` guarantee already
justifies, and it refuses to plant a cell in four cases. The destination then
keeps its post-havoc state, which has no cell there:

1. **Split cell.** A cell the copied range does not completely cover.
   `mdtests/byte_representation_partial_copy_frontier.md` splits a scalar;
   `mdtests/byte_representation_incomplete_copy_rejected.md` omits a
   trailing field, whose read is then refused as uninitialized.
2. **Symbolic range.** A source offset, destination offset, or length that
   is not a constant, because the offset mapping would not be exact.
3. **Unaligned destination.** A mapped offset that is not a multiple of the
   cell's width, because a typed observation there would not be a defined
   load.
4. **Untyped source.** A source with no cells has nothing to plant, so a raw
   byte copy establishes nothing typed
   (`mdtests/byte_representation_untyped_source_frontier.md`).

The contract's own checks come first. An out-of-bounds copy
(`mdtests/byte_representation_out_of_bounds_copy_rejected.md`) and an
overlapping one (`mdtests/byte_representation_overlapping_copy_rejected.md`)
fail its preconditions. A destination held only by a `views` clause
(`mdtests/byte_representation_readonly_copy_rejected.md`) or lent to a live
reader (`mdtests/byte_representation_borrowed_destination_rejected.md`, a
modeled-pthread worker viewing heap bytes, with the after-join control
`mdtests/byte_representation_borrowed_destination_after_join.md`) fails
`owns destination[0..bytes]`. A loan escrows the owner's write authority, as
described in [Stable views](stable-views.md). A `static const` destination
never reaches the call: the C frontend refuses discarding its `const`
qualification (`mdtests/byte_representation_const_destination_rejected.md`).

## The byte view of integer cells

A one-byte C access at a constant offset inside a wider integer cell of the
same block reads or writes the cell's little-endian representation. Byte
`k` of integer value `v` is `(v >> 8k) & 0xFF` (`src/kernel/eval/byte_view.rs`).
The byte order is a kernel value (`ByteOrder`) installed from the selected
target. With any other order, or none, there is no view.

- A one-byte load reads that byte: an `unsigned char` load reads it as is
  (`mdtests/byte_representation_buffer_byte_read.md`), and a `signed char`
  load sign-extends a constant byte and refuses a symbolic one
  (`signed_byte_loads_sign_extend_a_constant_byte_and_refuse_a_symbolic_one`
  in `src/kernel/tests/byte_view_tests.rs`).
- A one-byte store updates the containing cell in place,
  `(v & ~(0xFF << 8k)) | (b << 8k)`. It keeps the cell's type and address and
  adds no separate byte cell. A signed 16- or 64-bit cell is updated only when
  both values are constants; otherwise the store forgets the cell
  (`mdtests/byte_representation_byte_mutation.md` proves the changed
  observation).

What stays opaque:

- **Pointer cells.** A pointer's bytes have no view. A one-byte read is
  refused (`mdtests/byte_representation_pointer_bytes_refused.md`), and a
  one-byte write forgets the pointer rather than editing it
  (`mdtests/byte_representation_pointer_byte_write_refused.md`).
- **Float and `_Bool` cells** have no view either.
- **Assembling bytes.** Several one-byte cells are never combined into a
  wider integer load.
- **Specification loads** read a snapshot's cells without the byte view; the
  view applies to C execution only.

## Typed and byte views never contradict

Memory keeps one description of any byte. A one-byte store either rewrites
the containing integer cell or forgets it. Every C store first removes the
cells that may overlap the written range (`without_possible_aliasing_cells`)
and then records one cell. A representation copy plants cells only inside a
destination range the external contract has just havocked. No path leaves a
typed cell and a byte cell describing the same storage with different
values, and no byte write can leave an old scalar value provable.

## Reinterpretation stays refused

A copy moves cells without converting them. A typed load accepts only a cell
of its own value kind, so:

- integer bytes copied onto a pointer field are not a pointer, and the pointer
  load is refused (`mdtests/byte_representation_integer_bytes_as_pointer_refused.md`);
- pointer bytes copied onto an integer field are not an integer, and the
  integer load is refused (`mdtests/byte_representation_pointer_bytes_as_integer_refused.md`).

No pointer origin is guessed from an integer, and no address is invented for a
pointer. Both refusals are bounded local checks at the load.

## Allocation identity versus authority and lifetime

A copied pointer keeps its allocation identity, and nothing else:

- **Authority.** Loading through the restored pointer needs a resource for the
  pointee, exactly as loading through the original would.
  `mdtests/byte_representation_symbolic_roundtrip.md` proves the load with
  the caller's `views p[0..1]`, and
  `mdtests/byte_representation_restored_pointer_needs_authority.md` refuses
  the same load without it, naming `p` because identity was preserved.
- **Lifetime.** Restoring a representation does not restore a freed
  allocation. `mdtests/byte_representation_use_after_free_rejected.md` frees
  the pointee and refuses `*dst->target` as an invalid access.
- **Heap authority.** Resource normalization never merges `allocation` tokens
  for blocks it proves distinct, so the several live heap authorities of a
  round trip stay unique through copies and frees
  (`mdtests/ext_memcpy_allocation_authority.md`).

## Padding

Padding bytes have no cell, so a representation copy never plants anything
there and a byte read of a copied padding byte is refused as uninitialized
(`mdtests/byte_representation_padding_byte_unobservable.md`). C11 leaves
their values unspecified; Click assigns none. Equality of a record's fields
never implies equality of its bytes, and no proof in the demo claims
whole-struct byte equality.

## Bounded lookup and scaling

The copied source cells are found with one range query over the copied
block and extent (`representation_copy_cell_moves`), and the byte view's
containing cell with a query over the at most seven constant offsets below
the access (`containing_integer_cell`). Neither scans memory, other blocks,
or old snapshots. Each planted cell pays the ordinary `CMemory::store` cost.
The regressions measure deterministic work at four or more sizes, under the
[efficiency contract](verification-efficiency.md):

- `src/kernel/tests/representation_copy_tests.rs`:
  `representation_copy_lookup_work_is_linear_in_the_copied_extent` (4 to 64
  cells) and
  `fixed_representation_copy_lookup_work_is_independent_of_unrelated_memory`
  (8 to 512 unrelated cells, constant work);
- `src/kernel/tests/byte_view_tests.rs`:
  `containing_cell_lookup_work_is_independent_of_unrelated_cells`;
- `src/surface/tests/scaling_tests.rs`: the frozen round trip beside 2 to 16
  unrelated live allocations, with the marginal work of one extra copy
  (`roundtrip_extra_copy_stays_nearly_flat_beside_unrelated_allocations`,
  `expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations`,
  `expanded_roundtrip_work_per_source_byte_is_logarithmic`).

## Outside the milestone

- Union type punning beyond the existing typed union overlay, and general
  effective-type changes.
- Reconstructing pointers from integers or integers from pointers, and
  assembling several bytes into a wider load.
- Big-endian and other targets: the byte view exists only under an
  installed little-endian order, and there is no target matrix.
- Byte-layout reallocation: `realloc` copies initialized cells between
  blocks, but no rule changes a block's layout through its bytes.
- Copies with symbolic offsets or lengths planting typed cells, and copy
  primitives other than the standard-library `memcpy` declaration.
