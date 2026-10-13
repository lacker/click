# Unchanged zlib Adler-32 adapter trial

The unchanged zlib 1.3.1 computation imports and proves its empty-input result
and its one-byte checksum against the shared mathematical specification for
the canonical seed 1 and a nonnull buffer. The one-byte proof also preserves
the input byte. **The arbitrary-length checksum
postcondition and C/Rust result equality remain unproved.** This is the C
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
lemmas have checked bodies. This baseline does not claim correctness for lengths
above one or termination for arbitrary nonnull input lengths.

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

The remaining short-loop memory work is checked transport through the saved
pointer used by `*buf++`, followed by moving-base subrange coverage for the
next head. Both require actual address and nonwrapping coverage evidence;
same-base prefixes alone do not finish the original checksum loop.

| Original file | SHA-256 |
| --- | --- |
| `adler32.c` | `9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211` |
| `zutil.h` | `dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea` |
| `zlib.h` | `8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c` |
| `zconf.h` | `f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae` |
