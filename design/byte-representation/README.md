# Byte-representation source probe

This is the source-selection checkpoint for the P1
[byte-representation demo](../../issues/byte-representation-demo.md), not a
Click verification example yet. The synthetic
[`rep_copy.c`](rep_copy.c) is ordinary C11 source fixed before its
representation-copy rules are written. It stays here until Click can verify
it; adding an unproved directory under `examples/` would make the normal
example gate fail. The source-integrity test in `tests/examples.rs` pins its
exact bytes. Later proof work must use those bytes, not reshape the C to
expose a friendlier proof state.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux kernel target (the default), LP64, eight-bit bytes with unsigned plain `char`. No sidecar `target` override; the kernel target remains the default. |
| Compiler and C library | No verified-compiler claim yet. Host smoke is macOS Clang (LP64) with `clang -std=c11 -Wall -Wextra -Werror -fsyntax-only`; it checks C syntax only and is not evidence for the selected Linux ABI. The eventual locked import must record the exact driver, headers, flags, and ABI observations. |
| Copy primitive | `memcpy` as declared in the frozen source (`void *memcpy(void *, const void *, unsigned long)`). The filed explicit prototypes for `malloc`, `free`, and `memcpy` keep the source warning-free without pulling in unmodeled system headers; Click applies its stdlib `memcpy` catalog contract at the call sites. Whether that prototype stays or the locked import binds the real headers is decided with the import slice. |
| Layout assumption | `struct record` is `{ unsigned int tag; int *target; }`: `sizeof == 16`, `tag` at offset 0, `target` at offset 8 on LP64. Host-observed via `offsetof`/`sizeof` (macOS Clang prints `sizeof=16 tag_off=0 target_off=8 ptr=8 uint=4`); the Linux ABI lock lands with the import slice. The `memcpy` lengths use `sizeof(struct record)`, never a literal. |
| Buffer bound | The byte buffer is `malloc(16)`, not `malloc(sizeof(struct record))`, because the frozen source must stay host-compilable while C0 local `unsigned char` arrays reject `sizeof` bounds and struct-sized `malloc` into `unsigned char *` is untested at this checkpoint. The literal is a freeze artifact, not a layout claim: both copy lengths are `sizeof(struct record)`, and the `16 == sizeof` equality is part of the layout assumption above. A later slice may re-spell the bound once the frontend supports it; the proof must then use these same bytes. |

## Frozen program

`f` allocates a live `int` pointee, a source record, a 16-byte buffer, and a
distinct destination record, with cascading null checks that free what was
acquired. It stores `7` through the pointee, `11u` and the pointee address
through the source record, copies all `sizeof(struct record)` bytes
source-to-buffer and buffer-to-destination through `(unsigned char *)(void *)`
casts, then reads `dst->tag + *dst->target` (expected `18`) and frees all
four allocations. Every allocation-failure path returns `-1` after freeing
only what it acquired.

The casts are spelled through `void *` because a direct
object-pointer-to-byte-pointer cast is rejected at the C frontend
(`retyping object-pointer casts are unsupported`); the `void *` roundtrip is
the documented C0 way to carry an object pointer through a type-erased
interface. No proof-only locals, branches, helper calls, or identifier
changes were added to make any current proof pass: there is no passing proof
at this checkpoint.

## Direct representation copy landed

The kernel now attaches a checked representation-copy effect to the exact
standard-library `memcpy` declaration (not to the spelling): after the external
contract's havoc, each source cell whose complete byte representation lies in
the copied range is planted at the mapped destination offset. A partial cell, a
symbolic range, or an unaligned destination is left alone, and an untyped source
has no cells, so a raw byte copy still establishes nothing typed.

`mdtests/byte_representation_scalar_copy.md` verifies a complete direct copy of
an initialized `unsigned int`; `byte_representation_partial_copy_frontier.md`
and `byte_representation_untyped_source_frontier.md` pin that a split cell and
an untyped source still do not establish the value.

## Current frontier (2026-09-17)

`mdtests/byte_representation_frozen_frontier.md` embeds the frozen source byte
for byte with the intended `result == 18 or result == -1` contract. The
representation rule now carries the typed reload through both `memcpy` calls,
so `dst->tag` and `dst->target` read the copied values. `execute()` then
advances to the `free` sequence and stops on a pre-existing allocation-resource
gap unrelated to the byte model: an `extern` contract's `owns
destination[0..bytes]` over an allocation-backed buffer duplicates the
allocation authority, so a later `free` reports a missing `owns allocation(...)`
fact. The reduction is two byte buffers and no typed values. That gap is the
next blocker for this probe. The representation carrier through the untyped
buffer and the pointer-provenance negatives remain in the issue.

## Deferred scope

Typed-value preservation for the scalar field, pointer-identity preservation
without manufacturing pointee authority, use-after-free and read-only
negatives, byte-mutation invalidation companions, scaling regressions, and
the durable kernel design record all remain in
[byte-representation-demo.md](../../issues/byte-representation-demo.md).
This checkpoint adds no byte rule, no contract, and no claim that any
representation property is already modeled.
