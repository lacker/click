# Byte representation

This page is the design record for how Click relates an object's bytes to
its typed cells: what a representation copy establishes, what a one-byte
access reads and writes, and which reinterpretations stay refused. The public
summary is in [Memory model](../concepts/memory-model.md#byte-view-of-integer-cells);
the verified demonstration is
[`examples/byte-representation/`](https://github.com/clicklang/click/blob/master/examples/byte-representation/README.md).

The [consolidated object-model design](https://github.com/clicklang/click/blob/master/design/cpp-object-model.md)
specifies the target relationship between these rules, object lifetime and
modular contracts. The bounded declared-uint32 profile now uses common guarded
typed/byte observations for execution and specifications. Other integer-cell
byte views retain the separate execution behavior described below.

## Selected profile

Every rule below is stated for one profile. The C is GNU C11 under the default
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
extern uint8* memcpy(uint8 destination[], uint8 source[], uint64 bytes) {
    requires viewable(source[0..bytes]);
    owns destination[0..bytes];
    requires separate(memory(destination[0..bytes]), memory(source[0..bytes]));
    ensures result == destination;
    ensures bytes_equal(destination, 0u64, old(source), 0u64, bytes);
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
  byte view below, or when `T` is a character type and the cell is a
  one-byte cell of the other character type (see
  [Character reads](#character-reads-of-one-byte-cells)). Anything else is refused as a load that does not fit the
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
The legacy cell view uses the selected target's installed `ByteOrder`. The
shared declared-uint32 view instead retains that target profile in its immutable
declaration snapshot. An absent profile or unsupported byte order supplies no
shared representation relation.

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
- **Assembling bytes outside declared uint32 storage.** Untyped allocations,
  arrays, wider integers and other scalar kinds do not acquire a wider typed
  value from separate byte cells.
- **Other specification loads** retain their ordinary cell meanings. Only the
  guarded declared-uint32 profile below shares byte projections with execution.

## Initializing a declared uint32 through bytes

A complete automatic scalar declaration retains its type independently of
the initialized cells. Under the selected little-endian target, a character
store that completes all four bytes of a declared `unsigned int` object
reconstructs its uint32 value as the masked bytes shifted by 0, 8, 16 and 24
bits. The bytes may be written in any order, including through a helper's
character pointer. Signed character values contribute their low eight bits.

The resulting uint32 cell replaces the byte cells through the ordinary
checked store transition. Existing typed and byte observations then read
the same representation through the shared observation law. Specification byte
reads of that declared object use the same projections; separate legacy views
of other integer kinds remain outside this rule.
This normalization grants no permission, lifetime or allocation identity.
Its declaration lookup and four exact cell queries touch no unrelated memory.

A partial representation stays uninitialized. Allocation size or a requested
load type cannot select a uint32 object: untyped blocks, byte arrays, heap
storage, record fields and other scalar declarations remain outside this
initial profile. Pointers, floating-point values and padding remain opaque.
Unknown byte values remain unknown; no missing byte is guessed or zero-filled.
The declaration metadata survives value forgetting, but reconstruction still
requires the current byte values, so stale typed observations cannot return.

`mdtests/byte_representation_initializes_declared_uint32.md` covers a previously
uninitialized scalar filled through a concrete helper; its partial-write
counterpart refuses the typed read. `byte_view_tests` also checks out-of-order
and signed byte stores, symbolic masking, later byte updates, profile refusals
and deterministic work beside unrelated memory.

## Modular output initialization

An ordinary helper can return `initialized(p[0..4])` separately from its
`owns p[0..4]` resource and byte-value postconditions. The shared specification
atom selects a memory snapshot, an address and a fixed byte extent. Checking
it requires live storage and recorded writes covering every byte. Adjacent
symbolic writes merge into interval runs within their indexed offset family.
Coverage uses one predecessor lookup, rather than iterating the requested byte
count or visiting unrelated memory. Resetting an initialization footprint splits
only overlapping runs; branch intersection retains the commonly initialized bytes.

The initial contract profile accepts top-level normal postconditions naming
mutable native byte-pointer parameters, with zero start and a constant count.
The address is frozen at function entry. Proof-entry setup marks that footprint
unwritten before materializing resource cells, so a no-op helper or a partial
write cannot certify the guarantee. The verified modular summary records
initialization at the bound input address after its ordinary value havoc.
It does not supply storage, ownership or byte values. External assumptions,
callback contracts, conditional guarantees and exceptional outputs are refused.

This effect makes an initially unwritten caller object readable. Initialization
alone supplies no word value. For a declared four-byte uint32 scalar with its
pinned little-endian profile, four exact byte equalities at the selected snapshot
can now establish the same word as concrete byte stores. The checked
`declared_uint32_from_bytes` application retains all four premises and the
observation's declaration, target, width, snapshot, and complete initialization.
Smart simplification emits that explicit application; ordinary, expanded and
retained checking use the same rule. Missing or mutated bytes, a different root
or snapshot, incomplete initialization, and absent or unsupported profiles refuse
it. Selection makes four exact premise queries without an ambient scan.

See
[`modular_byte_output_initialization.md`](https://github.com/clicklang/click/blob/master/mdtests/modular_byte_output_initialization.md),
the unchanged exact-value program in
[`modular_byte_output_word_value_requires_representation.md`](https://github.com/clicklang/click/blob/master/mdtests/modular_byte_output_word_value_requires_representation.md),
and the [checked application](../reference/tactics/index.md#declared-uint32-byte-reconstruction).
The focused shared-rule and Surface tests check the scope, profile, certificate
mutations, and deterministic work beside unrelated facts and cells.

## Typed and byte views never contradict

Memory keeps one description of any byte. A one-byte store either rewrites
the containing integer cell or forgets it. Every C store first removes the
cells that may overlap the written range (`without_possible_aliasing_cells`)
and then records one cell. A representation copy plants cells only inside a
destination range the external contract has just havocked. No path leaves a
typed cell and a byte cell describing the same storage with different
values, and no byte write can leave an old scalar value provable.

## Character reads of one-byte cells

C11 6.5p7 lets any character type read an object's bytes. A byte has one
name, its unsigned read (`Bitvector32Term::memory_read`): an `unsigned char`
load of a `signed char` cell holding `t` reads `t mod 256`, a `signed char`
load of an `unsigned char` cell holding `u` reads the two's-complement value
of `u`'s eight bits, and a symbolic `signed char` read is the conversion of
the byte's unsigned read rather than an unknown of its own. This is
`CType::read_cell` and `LoadKind::read_cell`, used by every execution and
specification route that answers a load from a cell. It is what lets a
user-space C string, whose plain `char` is signed, be read as `uint8` bytes by
`strlen` and the C-string predicates
(`mdtests/c_builtin_string_header_declares_strlen.md`,
`mdtests/a_signed_read_of_a_byte_follows_from_its_unsigned_read.md`).
Nothing wider than one byte, and no pointer, float, or `_Bool` cell, gains a
view this way.

Constant facts cross the conversion in both directions. Forward, a known
byte `u == c` folds `int8(u)` to its two's-complement value wherever a term's
constant is computed from its operands, including the constant classes a
call's guarantee is normalized with. Backward, the conversion is a bijection
from `0..255` onto `-128..127` and a `UInt8` load holds one zero-extended
byte, so `int8(u) == k` with `k` in `-128..127` means `u == k mod 256`. Three
places use that one rule: the constant classes (`constant_classes.rs`) settle
the byte when its signed read's class is settled, a byte-read equality with a
constant is decided from that class, and a checked `rewrite` by
`int8(u) == k` substitutes `u` by `k mod 256`, which also rewrites every
signed read of the byte because each contains `u`. Smart closure and its
expansion therefore cite the same written premise
(`mdtests/userspace_signed_char_fact_decides_the_unsigned_byte.md`,
`mdtests/userspace_unsigned_byte_fact_crosses_a_signed_char_call.md`). A `k`
outside `-128..127` is the conversion of no byte and is never turned into a
byte equality. The inverse applies only to a byte load operand, and only to
constants: an order fact on the signed read (`s[0] < 0`) does not yet bound
the unsigned read.

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
  `examples/byte-representation`'s `g` (`rep_copy_symbolic.c`) proves the
  load with the caller's `views p[0..1]`, and
  `mdtests/byte_representation_restored_pointer_needs_authority.md` refuses
  the same load without it, naming `p` because identity was preserved.
- **Lifetime.** Restoring a representation does not restore a freed
  allocation. `mdtests/byte_representation_use_after_free_rejected.md` frees
  the pointee and refuses `*dst->target` as an invalid access.
  `mdtests/byte_representation_freed_pointer_compare_rejected.md` refuses
  even `dst->target == pointee` after the free, because both values are
  indeterminate (C11 6.2.4p2); the same comparison before the free verifies
  (`mdtests/byte_representation_compare_before_free.md`).
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
- Reconstructing pointers from integers or integers from pointers, and byte
  assembly beyond the declared automatic uint32 initialization profile.
- Big-endian and other targets: the byte view exists only under an
  installed little-endian order, and there is no target matrix.
- Byte-layout reallocation: `realloc` copies initialized cells between
  blocks, but no rule changes a block's layout through its bytes.
- Copies with symbolic offsets or lengths planting typed cells, and copy
  primitives other than the standard-library `memcpy` declaration.
