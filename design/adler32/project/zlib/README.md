# Unchanged zlib Adler-32 adapter trial

The unchanged zlib 1.3.1 computation now proves its shared Adler-32 checksum,
termination, and preservation of every input byte for every length its
`uint64` argument can hold for a C object, arbitrary canonical decoded A/B
seeds, and a nonnull buffer.
The real two-call C client proves incremental processing across every split
under its nonnull call-pointer contracts. Checked result and reset
correspondence connect these proofs to the Rust trial for every length. See the [scoped demonstration](../checksum-correspondence.md).
The C contracts state their results with the full-width
[checksum specification](../adler32-spec-u64.click), over the original `uint64`
length without narrowing it. The running prefix of the full-stream and
canonical proofs is stated over `uint64`; each NMAX batch and short path still
computes through the [int32 specification](../adler32-spec.click), whose
counts there are at most 5552, and joins the prefix through
[the bridge](../adler32-spec-bridge.click). The only length bound left is the
view's object-size limit, `len <= 9223372036854775807u64`, which the contract's
`views buf[0u64..len]` already implies.

`adler32.c`, `zutil.h`, `zlib.h`, and `zconf.h` are byte-for-byte upstream files
from revision `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` of
[madler/zlib](https://github.com/madler/zlib/tree/51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf),
kept at their upstream paths with the original license in
[`../../vendor/zlib-1.3.1`](../../vendor/zlib-1.3.1), outside the Click
project. The project's `zlib` unit reads them there; Click's `incremental.c`
client includes `adler32.c` from it through the `zlib_incremental` unit, whose
root is the directory holding the project and the vendored trees. No implementation, loop, macro, or header
was changed. The system headers zlib includes are Click's modeled headers, not
a C library's.

The locked selection uses target `x86_64-unknown-linux-gnu` in `userspace` mode, LP64 little-endian layout,
unsigned plain char, C11, and GCC 13. `NO_DIVIDE` and `Z_SOLO` are undefined.
The [project file](../click.project.json) declares one C unit, `zlib`, for
`adler32.c` and the `incremental.c` client, built with `-std=c11` as zlib's
own build is. `zconf.h` takes `va_list` and `off_t` from Click's `<stdarg.h>`
and `<sys/types.h>`. The lock records
the driver, compiler resources, ABI probe, exact options, source closure, and
prepared bytes. Ordinary verification loads the prepared input offline and
checks original local inputs; it does not run or attest the compiler. The
producer's absolute paths in the lock and line directives are provenance,
not a requirement to check out this fixture at that path.

From the repository root:

```sh
cargo build --bins
target/debug/click verify design/adler32/project/zlib/empty.click
target/debug/click verify design/adler32/project/zlib/one-byte.click
target/debug/click verify design/adler32/project/zlib/reset.click
target/debug/click verify design/adler32/project/zlib/short-memory.click
target/debug/click verify design/adler32/project/zlib/sixteen.click
target/debug/click verify design/adler32/project/zlib/full-stream.click
```

To reproduce preparation on a machine with the unit's compiler, regenerate
the lock and prepared sources:

```sh
target/debug/click import lock design/adler32/project/zlib
target/debug/click verify design/adler32/project/zlib/empty.click
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
proof below covers lengths 2–15. The full-stream and canonical proofs below
establish termination for every length the view admits.

`reset.click` checks the original null-buffer reset path for any seed and every
length except one, returning 1 without byte-read authority. The original
one-byte fast path precedes its null check, so null with length one is excluded;
the negative regression rejects a claim covering that read. The checked [correspondence demonstration](../checksum-correspondence.md)
connects this reset behavior to the Rust constructors and checks general
incremental processing. Its installed commands also select the producer and
helper bodies.

The [moving-cursor byte-sum reduction](../../../../mdtests/loop_entry_memory_capture_byte_sum.md)
checks actual `*p++` reads, termination, signed addition bounds, and preservation
of every byte for counts up to fifteen. The
[postdecrement reduction](../../../../mdtests/loop_entry_memory_capture_postdecrement.md)
checks `while (n--)` through its wrapping zero exit. These are reduced control
and memory proofs, not proofs of the original checksum loop.

[Native 64-bit same-base prefix narrowing](../../../../mdtests/native_view_prefix_narrowing.md)
now checks the full unsigned byte-count bound and preserves the source view's
lifetime and state evidence. Symbolic byte and word prefixes use explicit
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
view from the checked byte offset and remaining capacity. The project lock
reuses the same unchanged prepared C source and source closure.

The accumulator invariants identify A with one plus the consumed byte sum and
B with the consumed length plus its weighted byte sum. `short-prefix.click`
observes the exact original remaining count through a pure signed expression;
its checked count and address bridges reuse those of the Rust trial. Byte
promotion and equality bridges connect the original C reads to those sums.
The bounds A <= 3826 and B <= 57390 establish that the native additions do not
wrap. The final reduction and shift/OR packing satisfy the shared specification.
`byte.click` supplies the same checked promotion theorem to both C proofs.

The offline short-loop regression checks all helper bodies together,
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
the loop invariant follows the actual remaining count and input state,
without a generated processed counter. Explicit ranking facts establish
nonnegativity and the decrease from 16 to 0.

At loop exit, the proof converts the native prefix count to an integer
separately from rewriting the weighted sum's native arguments. This preserves
the exact B invariant while deriving the final component equation. The
subsequent zero-length scalar loop preserves both component equations, and
the original reductions and packing establish the shared result.

The project lock reuses the unchanged prepared C input and source closure.
The nightly offline regression relocates the fixture, checks all imported
helper bodies and an expansion, and rejects missing or insufficient read
authority, false A/B invariants, and a false checksum. This establishes one
DO16 iteration; the repeated-block sidecar below extends it through nonempty tails.
The count-presentation rendering regression is retained in
[the native-count rewrite fixture](../../../../mdtests/integer_rewrite_preserves_folded_count_presentation.md).

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
[focused do-while regression](../../../../mdtests/symbolic_loop_cursor_wide_offset.md)
checks the caller-view read; kernel regressions check rejected accesses and
bounded lookup across increasing alias counts.
The scalar component bound is 1415761, including the coefficient in the
weighted-sum invariant. Selected-premise reduction still uses the unchanged
64-premise source-spelling limit and kernel checks.

The offline repeated-block regression checks all dependency bodies, the
complete expanded certificate, false checksum and A/B invariants, missing
read authority, and a view one byte too short. It runs in nightly to preserve
the gate budget. The project lock reuses the unchanged
prepared source and headers; compiler extraction is unnecessary. The
full-stream and canonical sidecars below extend the length and seed ranges;
the shared correspondence demonstration connects their results to Rust.

The locked [NMAX sidecar](batch.click) now proves the shared checksum,
termination, and preservation of every input byte for exactly 5552 bytes,
canonical seed 1, and nonnull input. It follows the original outer batch loop
and all 347 iterations of its do-while DO16 loop through a ranked invariant,
with exact component sums and weighted sums at the actual cursor. The proof
transports the loop-entry view after each sixteen-byte advance, closes both
counter outcomes, and retains the component equations through the original
modulo reductions and packing. [Batch helpers](batch-helpers.click) check the
native capacity, prefix, lane, and reduction bridges. Historical native cast
bounds use the selected state's counter.

The offline NMAX regression checks all helper bodies, complete certificate
expansion, false results and component invariants, and missing or shortened
read authority. It runs in nightly; the project lock reuses
the unchanged prepared source and headers. The stream sidecar below extends
this proof across multiple batches and their remaining tails.

[Seeded batch helpers](seeded-batch.click) now check the native addition pair
for any canonical batch-entry components, retain the seed terms in both raw
component equations, and establish addition bounds through 5552 bytes. They
check both original reductions and connect the local batch result to the
shared specification for an arbitrary previously processed prefix. The offline
seeded-helper regression verifies every dependency, expands every seeded and
stream-helper claim, and rejects false component and concatenation results.
Raw-seed helpers also compose the unreduced DO16 tail sums with the scalar tail.

The locked [stream sidecar](stream.click) applies these lemmas to the original
C for lengths 5552–22208, canonical seed 1, and nonnull input. It proves the
shared checksum, termination, and preservation of every input byte across
one to four NMAX batches, the remaining DO16 blocks, and a zero to fifteen-byte
scalar tail. The batch loop carries canonical component observations at the
processed global prefix. Its inner loop preserves a view covering both the
remaining batch bytes and the future suffix. Tail loops retain the caller's
complete read authority and use local seeded component equations plus a global
cursor bound. The scalar loop starts with unreduced components; residue
composition connects its result to the full input before the zero guard's
unsigned decrement wraps.

The offline stream regression checks every helper body, complete certificate
expansion, false checksum, cursor and raw-seed invariants, and missing or
shortened read authority. It runs in nightly. The project lock reuses the
unchanged prepared input; the C and headers remain byte-for-byte pinned.
The full-stream sidecar below extends this proof to every length and covers
every original return path.

The locked [full-stream sidecar](full-stream.click) proves the complete
canonical-seed, nonnull-input contract for every length. Its case proof
follows the original one-byte fast return, the short loop (including empty
input), and the full stream. No C body or header changed. Zero guards retain
their original unsigned wrapping effects; no processed counter was added.

[Full-stream helpers](full-stream-helpers.click) reuse Rust's checked full-range
count and byte-pointer observations. Global prefixes and future suffixes are
`uint64` counts under the view's object-size limit, while each NMAX batch keeps
its original arithmetic bounds. A prefix plus a chunk must fit its actual
total, not merely have individually bounded operands. The `_u64` helpers
establish this before associating pointers or applying the full-width checksum
concatenation.

The offline full-stream regression checks all dependency bodies, all eight
postconditions across the four original return paths, complete certificate
expansion, and negative checksum, cursor, raw-seed and authority cases. A separate nightly regression expands and checks every new helper claim
and rejects invalid cast, pointer-sum, read-bound, and endpoint claims. The
project lock reuses the unchanged prepared source and headers.

`canonical.click` now covers arbitrary canonical decoded seed components
(0–65520 each), nonnull input, and every length. It checks the
original mask/shift decoding, all four one-byte subtraction combinations,
both short-path A reductions, NMAX batches and both tail outcomes. The checksum
uses the decoded initial A/B; bits above the packed 32-bit seed are ignored by
the unchanged C. Its original source, headers and prepared artifact remain
byte-for-byte unchanged. The offline fixture verifies all 16 postconditions,
every dependency body, complete expansion, and false checksum/cursor/seed/view
claims. A separate fixture expands all 11 canonical helper claims.

`incremental.c` is a real two-call client, compiled as a single translation unit
including the pinned C implementation. `incremental.click` proves the whole
checksum and byte preservation for every split from zero through the total,
with the same length and canonical-seed limits. Both call pointers must be
nonnull: `buf != 0` and `buf + split != 0`, including empty pieces, because zlib
uses null as a reset request. Views establish read authority; they do not
establish allocation provenance or make the suffix nonnull. Checked uint64
field recovery and Integer round trips recover the first result's canonical
state before the second call. The client source is locked with GCC 13, LP64 layout,
headers, included original source and the prepared single translation unit.
Its offline fixture also verifies the callee's complete proof against that
unit, expands the client claim, and rejects invalid splits, null suffixes,
missing/shortened authority and false results.

The [checked correspondence and scoped demonstration](../checksum-correspondence.md)
now derive native C/Rust return-word equality under matched entry bytes,
length and canonical state, including the independently checked incremental
clients. The reset lemma connects the existing null/nonunit-length C result
with Rust's checked new/default fields and getter. Complete correspondence
expansion and specification-body checks run nightly; bounded normal mutations
reject missing input matching, mismatched state and false result/reset claims.
The demonstration specifies all caller authority and nonnull obligations;
composition of these separate programs does not establish an FFI boundary.

| Original file | SHA-256 |
| --- | --- |
| `adler32.c` | `9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211` |
| `zutil.h` | `dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea` |
| `zlib.h` | `8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c` |
| `zconf.h` | `f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae` |
