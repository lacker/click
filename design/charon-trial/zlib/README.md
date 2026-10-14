# Unchanged zlib Adler-32 adapter trial

The unchanged zlib 1.3.1 computation imports and proves its empty-input result
and its checksums for every length 1 through 5551 against the shared mathematical
specification for the canonical seed 1 and a nonnull buffer. The nonempty proofs
also preserve every input byte. **The arbitrary-length checksum postcondition
and C/Rust result equality remain unproved.** This is the C
adapter baseline for the shared [checksum specification](../../adler32-spec.click).

`adler32.c`, `zutil.h`, `zlib.h`, and `zconf.h` are byte-for-byte upstream files
from revision `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` of
[madler/zlib](https://github.com/madler/zlib/tree/51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf).
The original zlib license is included. No implementation, loop, macro, or header
was changed. The prepared input also contains GNU C Library declarations and
inline header functions; their LGPL 2.1 license is included separately.

The locked selection uses `x86_64-linux-userspace`, LP64 little-endian layout,
unsigned plain char, C11, and GCC 14. `NO_DIVIDE` and `Z_SOLO` are undefined.
The compiler import supplies its normal POSIX profile flags. Its lock records
the driver, compiler resources, ABI probe, exact options, source closure, and
prepared bytes. Ordinary verification loads the prepared input offline and
checks original local inputs; it does not run or attest the compiler. The
producer's absolute paths in the lock and line directives are provenance,
not a requirement to check out this fixture at that path.

From the repository root:

```sh
cargo build --bins
target/debug/click verify design/charon-trial/zlib/empty.click
target/debug/click verify design/charon-trial/zlib/one-byte.click
target/debug/click verify design/charon-trial/zlib/reset.click
target/debug/click verify design/charon-trial/zlib/short-memory.click
target/debug/click verify design/charon-trial/zlib/sixteen.click
```

To reproduce preparation on a machine with the compiler and include paths in
`empty.click.import.json`, regenerate the lock and prepared input:

```sh
target/debug/click import lock design/charon-trial/zlib/empty.click
target/debug/click verify design/charon-trial/zlib/empty.click
```

The normal compiler-import regression copies the fixture to an unrelated
working directory, verifies the original contract and its checked expansion,
rejects a false result, and rejects a changed original header. The adapter
imports the complete selected bodies, including `len--`, `--n`, `*buf++`, and the
nested compound statements from `DO16`, even though the empty-input proof
executes no byte-processing iteration. The one-byte proof follows the original early-return path, checks byte promotion,
prunes both reduction branches with unsigned bounds, and observes the original
shift/OR result through a bounded packing theorem. Its imported specification
lemmas have checked bodies. The empty and one-byte sidecars do not cover longer inputs; the short-loop
proof below covers lengths 2–15. Arbitrary-length termination remains unproved.

`reset.click` checks the original null-buffer reset path for any seed and every
length except one, returning 1 without byte-read authority. The original
one-byte fast path precedes its null check, so null with length one is excluded;
the negative regression rejects a claim covering that read. Connecting this
reset behavior to the Rust constructor and general incremental processing is
still pending.

The [moving-cursor byte-sum reduction](../../../mdtests/loop_entry_memory_capture_byte_sum.md)
checks actual `*p++` reads, termination, signed addition bounds, and preservation
of every byte for counts up to fifteen. The
[postdecrement reduction](../../../mdtests/loop_entry_memory_capture_postdecrement.md)
checks `while (n--)` through its wrapping zero exit. These are reduced control
and memory proofs, not proofs of the original checksum loop.

[Native 64-bit same-base prefix narrowing](../../../mdtests/native_view_prefix_narrowing.md)
now checks the full unsigned byte-count bound and preserves the source view's
lifetime and snapshot evidence. Symbolic byte and word prefixes use explicit
selected premises; low-word bounds, missing bounds, larger prefixes, and
unrelated bases are rejected. This removes the short-loop refusal when
narrowing a positive remaining count to its first byte.

`short-memory.click` checks the original `while (len--)` and `*buf++` loop
for canonical seed 1, a nonnull buffer, and every length from 2 through 15.
It proves the shared mathematical checksum, a packed result within 32 bits,
termination, and preservation of every input byte. The final
zero guard decrements the counter to UINT64_MAX before breaking; that exit
owes no back-edge decrease. The proof uses the actual remaining count and
saved pointer, with no generated processed counter. It records the whole
remaining view at the pre-decrement checkpoint, then derives the next head's
view from the checked byte offset and remaining capacity. Its import manifest
and lock reuse the same unchanged prepared C source and source closure.

The accumulator invariants identify A with one plus the consumed byte sum and
B with the consumed length plus its weighted byte sum. `short-prefix.click`
observes the exact original remaining count through a pure signed expression;
its checked count and address bridges reuse those of the Rust trial. Byte
promotion and equality bridges connect the original C reads to those sums.
The bounds A <= 3826 and B <= 57390 establish that the native additions do not
wrap. The final reduction and shift/OR packing satisfy the shared specification.
`byte.click` supplies the same checked promotion theorem to both C proofs.

**The original 5552-byte batches remain unproved.** The offline short-loop
regression checks all helper bodies together,
rechecks an expansion, and rejects missing byte authority, false component
invariants, and false checksum results. These larger checks run in nightly.

`block.click` checks a mathematical scalar recurrence, its native uint64
addition pair for prefixes below 5552 bytes, and recombination after both
original reductions. The addition-pair theorem requires the promoted byte to
match the specification byte and exact accumulator equations and bounds; it
provides no C memory authority or assumed callee result.

[sixteen.click](sixteen.click) proves the unchanged remaining-length DO16 path
for canonical seed 1, a nonnull buffer, and exactly 16 bytes. It establishes
the shared checksum, termination, and preservation of every input byte.
Its sixteen original addition pairs use checked native recurrence lemmas;
the loop invariant follows the actual remaining count and input snapshot,
without a generated processed counter. Explicit ranking facts establish
nonnegativity and the decrease from 16 to 0.

At loop exit, the proof converts the native prefix count to an integer
separately from rewriting the weighted sum's native arguments. This preserves
the exact B invariant while deriving the final component equation. The
subsequent zero-length scalar loop preserves both component equations, and
the original reductions and packing establish the shared result.

The manifest and lock reuse the unchanged prepared C input and source closure.
The nightly offline regression relocates the fixture, checks all imported
helper bodies and an expansion, and rejects missing or insufficient read
authority, false A/B invariants, and a false checksum. This establishes one
DO16 iteration; the repeated-block sidecar below extends it through nonempty tails.
The count-presentation rendering regression is retained in
[the native-count rewrite fixture](../../../mdtests/integer_rewrite_preserves_folded_count_presentation.md).

`window.click` checks symbolic prefix advance after decrementing the actual
remaining count, DO16 lane bounds and byte identities, and complete native
read bounds for one batch below 5552 bytes. The prefix observation and pointer
bridges in `short-prefix.click` now accept the existing checked count ceiling
of 22208 instead of restricting those reusable observations to fifteen.
The nightly window regression checks every dependency body as well.

The locked [repeated-block sidecar](repeated.click) proves the shared checksum,
termination, and preservation of every input byte for canonical seed 1,
nonnull input, and lengths 16–5551. All sixteen original addition pairs check
at a symbolic prefix. The DO16 loop closes its component, cursor, view, and
ranking invariants; the scalar tail extends both component equations through
the final native reductions and packing.

The tail inherits the caller's complete input view rather than acquiring a
new moving suffix at its loop entry. Its prefix equations and native bounds
place each original `adler += *buf++` read inside that held range. Read
matching retains the native index when an equivalent int32 spelling is also
known; pointer equalities and pure viewability facts grant no new resources.
Native-index retention also follows a symbolic loop cursor through checked
same-block offset equalities, including constant byte lanes. The
[focused do-while regression](../../../mdtests/symbolic_loop_cursor_wide_offset.md)
checks the caller-view read; kernel regressions check rejected accesses and
bounded lookup across increasing alias counts.
The scalar component bound is 1415761, including the coefficient in the
weighted-sum invariant. Selected-premise reduction still uses the unchanged
64-premise source-spelling limit and kernel checks.

The offline repeated-block regression checks all dependency bodies, the
complete expanded certificate, false checksum and A/B invariants, missing
read authority, and a view one byte too short. It runs in nightly to preserve
the gate budget. `repeated.click.import.json` and its lock reuse the unchanged
prepared source and headers; compiler extraction is unnecessary. The
arbitrary-length C claim and C/Rust result equality remain unproved.

| Original file | SHA-256 |
| --- | --- |
| `adler32.c` | `9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211` |
| `zutil.h` | `dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea` |
| `zlib.h` | `8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c` |
| `zconf.h` | `f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae` |
