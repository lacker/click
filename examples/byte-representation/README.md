# Byte representation

This project verifies that copying an object's representation into a byte
buffer and back preserves its scalar values and its pointer's identity, and
that the copy grants no authority it did not already have.

`rep_copy.c` is synthetic C11, fixed before any of its byte rules were
written and pinned byte for byte by `tests/examples.rs`. Its `f` allocates a
live `int` pointee, a source `struct record { unsigned int tag; int *target; }`,
a 16-byte `unsigned char` buffer, and a distinct destination record, with
cascading null checks that free what was acquired. It stores `7` through the
pointee and `11u` and the pointee address into the source record, copies all
`sizeof(struct record)` bytes source-to-buffer and buffer-to-destination with
`memcpy`, reads `dst->tag + *dst->target`, and frees all four allocations. The
sidecar proves `result == 18 or result == -1`: the tag reads back `11`, the
restored pointer is the pointee's address, so `*dst->target` reads `7`, and
every allocation is freed exactly once.

`rep_copy_symbolic.c` is the parameterized companion. `g` receives an
arbitrary `tag` and a caller-supplied `int *p`, performs the same heap round
trip, reports the restored pointer through `restored` before freeing the
destination, and returns `dst->tag + *dst->target`. Its contract proves
exact scalar equality (`result == tag + p[0]`), pointer identity
(`restored[0] == p`), and the pointee observation. The pointee load is
authorized only by the caller's `views p[0..1]`: `g` owns none of `p`'s
storage, and copying the pointer does not create any. The bounds on `tag` and
`p[0]` keep the sum and its conversion to `int` in range, so a successful
result is never `-1`.

`use_copy.c` calls `f` through its contract, not its body, and proves its own
claim `result == 18 or result == 0` from `f`'s guarantee.

## Profile and layout assumptions

| Boundary | Assumption |
| --- | --- |
| Target | The default kernel target, x86-64 Linux, LP64, eight-bit bytes, little-endian. There is no `target` override and no separate compiler import record; big-endian targets are out of scope. |
| Layout | `struct record` is `sizeof == 16`, `tag` at offset 0, `target` at offset 8, with four padding bytes at offsets 4 to 7. Click computes this layout from the struct declaration; nothing in the proof names an offset. |
| Copy primitive | `memcpy` as the standard-library declaration `void *memcpy(void *dest, const void *src, unsigned long n)`. Click binds its checked standard-library contract to that exact declaration, not to the spelling, and the call carries the kernel's representation-copy effect. It is a trusted specification of the client's view of `memcpy`, not a proof of libc, and each sidecar that relies on it reports `external assumptions: ... -> memcpy`. |
| Buffer bound | The buffer is `malloc(16)`, a literal fixed with the source; both copy lengths are `sizeof(struct record)`, so the round trip also relies on `16 == sizeof(struct record)` under this layout. |

The `(unsigned char *)(void *)` casts carry an object pointer through a
type-erased interface, the documented C0 spelling; a direct object-pointer to
byte-pointer cast is refused by the frontend.

## What the copy does and does not establish

The representation-copy effect plants each source cell whose complete
representation lies inside the copied range at the mapped destination offset.
Integer cells keep their values, and pointer cells keep their allocation
identity. Padding bytes carry no typed cell, so nothing is claimed about them,
and whole-struct byte equality is never proved. A partial cell, a symbolic
length, an unaligned destination, or an untyped source establishes nothing
typed.

The negatives live in `mdtests/byte_representation_*.md`: out-of-bounds,
overlapping, incomplete, read-only, and borrowed-destination copies; a byte
read or write of a copied pointer; integer bytes copied onto a pointer and the
reverse; a restored pointer without its pointee's resource; and a restored
pointer used after its pointee is freed. Each is refused at its own check.
