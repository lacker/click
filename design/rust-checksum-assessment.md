# Rust checksum source assessment

This assessment pins the unchanged Adler-32 implementations, build configuration,
and common mathematical specification selected by
[the Rust roadmap](../issues/rust-support.md). Native Charon imports the Rust
selection, and the [Adler trial](charon-trial/adler2/README.md) records its current
checked computation correctness over the explicit signed observation range.
The unchanged public entry point composes the checked constructor, general
computation and checksum getter over that range. A real client connects two
actual updates at every valid split to the full-input specification. A second
client saves the prefix checksum, restores the same canonical state through
`from_checksum`, then proves the full-input result after updating the suffix.
C correctness and C/Rust result equality remain unproved.

The checked [common specification](adler32-spec.click) defines the unweighted
byte sum, the byte-order-sensitive weighted sum, both canonical residues, and
the packed checksum over a logical byte snapshot. Its lemmas prove the appended
byte recurrence, weight shifts, nonnegative sums, residue uniqueness and
addition, canonical output ranges, packing bounds, and empty-input seed
preservation. The unchanged Rust computation is connected to these sums; the lemmas assume
no checksum body summary. The C connection remains pending.

## Immutable inputs and configuration

The companion [source manifest](rust-checksum-sources.json) records revisions
and SHA-256 hashes of the inspected files.

| Library | Immutable revision | Selected entry points |
| --- | --- | --- |
| zlib 1.3.1 | `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` | `adler32_z`, plus its `adler32` wrapper |
| adler2 2.0.1 | `89a031a0f42eeff31c70dc598b398cbf31f1680f` | `adler32_slice`; `Adler32::from_checksum`, `write_slice`, `checksum` |

The zlib release tag resolves to that commit. The Rust commit comes from
the published crate's `.cargo_vcs_info.json`; its two checksum source files
match the repository files byte for byte. Source links:
[zlib adler32.c](https://github.com/madler/zlib/blob/51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf/adler32.c),
[adler2 lib.rs](https://github.com/oyvindln/adler2/blob/89a031a0f42eeff31c70dc598b398cbf31f1680f/src/lib.rs),
[adler2 algo.rs](https://github.com/oyvindln/adler2/blob/89a031a0f42eeff31c70dc598b398cbf31f1680f/src/algo.rs).

The intended common verification target is `x86_64-unknown-linux-gnu`, with
eight-bit bytes, 32-bit C `unsigned int`, and 64-bit pointers, `unsigned long`,
and `size_t`. Keep zlib's normal remainder path: `NO_DIVIDE` and `Z_SOLO` are
unset. Do not rewrite its macro-unrolled loops or normalize its C source.
Compiler and header identities must enter the eventual Click input lock.

Keep adler2's declared Rust 2021 edition and default `std` feature. There
are no ordinary third-party dependencies for this configuration. The optional
`rustc-dep-of-std` feature is off; tests and benchmarks are not verification
roots. Use the compiler and extractor pinned by
[the Charon profile](../src/languages/rust/charon-profile.json), overflow checks
enabled, panic abort, and MIR optimization level zero. The schema-4 input lock
records Rust 2021, features, crate roots, both module files, and the complete
compiler-observed source closure.

These are selected paths and a selected build configuration. The `BufRead`
adapter, zlib compression, alternate `NO_DIVIDE` code, and checksum-combine
APIs are outside this demonstration.

## Reachable computation

C calls `adler32` -> `adler32_z`, or enters `adler32_z` directly. Its arithmetic
splits the seed into two 16-bit components, handles lengths 1 and below 16,
then processes 5,552-byte blocks through `DO16` macro expansions. It uses
`while`, `do ... while`, decrement conditions, post-incremented byte pointers,
unsigned arithmetic, remainder, shifts, and bitwise packing. These are
existing C vocabulary; source import and proof coverage still need to be
demonstrated for the unchanged translation unit and selected configuration.
Unsupported declarations elsewhere in the same file may require selected-root
extraction, not deletion from the original file.

Rust's one-shot path is:

```text
adler32_slice
  Adler32::new -> Default::default
  Adler32::write_slice -> Adler32::compute
    U32X4::from
    U32X4::add_assign / rem_assign / mul_assign
    slice length, split_at, chunks_exact, remainder, iter
  Adler32::checksum
```

The incremental path starts with `Adler32::from_checksum`, then uses
`write_slice` and `checksum`. `compute` splits off the final zero to three
bytes and processes four independent lanes in chunks of 22,208 bytes
(`5552 * 4`). It combines the lane sums with weighted corrections, then
processes the short tail. This is a scalar fixed-array implementation of a
parallel checksum identity; the proof must establish that identity rather
than pretend the implementation is the textbook serial loop.

## Required Rust interpretations

| Source construct | Required checked interpretation |
| --- | --- |
| `u8`, `u16`, `u32`, `usize` | Target-sized types, loads/stores, unsigned comparisons and arithmetic |
| `u32::from`, `as`, `%`, `<<`, `|` | Resolved conversion calls, widening/truncation, remainder and bitwise rules |
| `&[u8]`, `.len()`, indexing, `split_at` | Address plus length, initialized byte views, bounds and partition checks |
| `[u32; 4]`, tuple struct `U32X4` | Fixed arrays, construction, copies and indexed field updates |
| `+=`, `%=`, `*=` on `U32X4` | Compiler-resolved concrete operator implementations and checked contracts |
| `for`, nested loops, `.chunks_exact()`, `.remainder()`, `.iter()` | Iterator state, yielded subranges, progress and existing loop invariants |
| `mod`, `use`, inherent methods, `Default`, `Copy` derives | Crate-aware extraction and selected concrete reachable definitions |

Native Charon imports this unchanged crate with its modules, derives, resolved
methods, and concrete operators. The helper bodies and arithmetic libraries have checked sidecars. The general
computation sidecar proves bounds, termination and both final fields against
the common specification for canonical initial states and every input length
through 2,147,483,647 bytes, including full batches and both remainders.

Support the reachable concrete instantiations rather than promising arbitrary
traits or generics. Slice and iterator operations need either checked lowering
or individually named library contracts in the trust boundary. The checksum
and `U32X4` arithmetic bodies themselves must be verified, not assumed.

## Shared specification and proof boundary

For prime `P = 65521`, a canonical initial state `0 <= a0,b0 < P`, and a byte
sequence `x`:

```text
a(i+1) = (a(i) + x[i]) mod P
b(i+1) = (b(i) + a(i+1)) mod P
checksum(x, a0, b0) = a(len(x)) | (b(len(x)) << 16)
```

One-shot comparison uses `(a0,b0) = (1,0)`. Incremental comparison uses the
same canonical state on both sides and proves processing concatenated input
agrees with successive updates. Do not equate arbitrary packed seeds or
zlib's null-buffer reset behavior with a Rust slice. C requires a non-null,
initialized, readable byte range for the selected comparison, including a
valid non-null empty-range representation when length is zero. Rust permits
an empty slice with its normal validity conditions.

Both proofs preserve input bytes, establish access bounds and termination,
and exclude Rust panics. In particular, the deferred-reduction proof must
bound each intermediate Rust `u32` lane and the combined accumulators. The C
accumulators are LP64 `unsigned long`; matching outputs does not justify
silently giving the Rust operations that wider type.

Read-only slice authority should use existing Click `views` of the input
byte range; mutable accumulator fields use `owns`. Slice length and validity
remain separate from allocation/deallocation authority. Existing unsigned
types, memory ranges and loop invariants are the first choice. A 64-bit `usize`
length must not be silently truncated to fit a narrower memory-range model;
that representation needs either full target-width support or explicit checked
bounds in an intermediate subset. This assessment
does not establish a need for new public Click syntax.

## Current proof boundary and delivery

The selected scalar types, byte slices, arrays, crate configuration, qualified
methods, concrete operators, and stored shared iterators are supported by the
native adapter. Variable-length memory contracts retain an explicit
`INT32_MAX` range limit; slice metadata and native index checks keep their
full target width.

The small-batch computation proof covers every length zero through 22,207
bytes from canonical initial states, including the zero-to-three-byte tail.
It checks the lane-loop ceilings, termination, original reductions and
recombination, scalar sums, and final 16-bit stores. Both final fields equal
the common mathematical specification on the entry input snapshot. The
arbitrary-length computation has checked bounds and termination. Each full-batch
and aligned-remainder vector step connects all four constructor lanes to exact
absolute input-byte observations using actual iterator state. The remainder
uses the constructor's call-entry Integer observations and preserves the input
bytes with the entry snapshot. The full-batch loops preserve both
residues against the common specification through their native additions and
reductions. The B representative includes the deferred batch-local position
times A contribution and remains nonnegative. Its entry seed stays fixed while
Rust updates the working scalar B between batches. Actual outer exhaustion
establishes both common checksum residues for the completed full-batch prefix.
The aligned-remainder lane loop also preserves both residues through actual
iterator exhaustion, including the deferred local-position times A contribution
and the fixed entry B seed. The original remainder seed product and scalar
addition, reductions, weighted B corrections and scalar recombination preserve
both residues for the complete aligned prefix. The original scalar tail advances
both residues at each actual byte position. Checked iterator exhaustion, byte
extensionality, native reductions and 16-bit stores prove both final fields
equal the specification on the entry input snapshot for all supported lengths.

Follow the [current roadmap](../issues/rust-support.md) for implementation
saved-checksum restoration, the unchanged C proof, and architecture
requirements. Deliver coherent green proof and engine increments through pull
requests. Repair checker and expansion defects before extending the examples;
retain explicit bounds on intermediate evidence and meaningful negative tests.

## Assessment evidence

- The native locked adler2 artifact retains Rust 2021, `std`, overflow checks,
  panic abort, and the selected Linux target. The checked source hashes match
  the immutable repository files.
- Original zlib checksum source passed a host Clang syntax check with its
  pinned headers. The host macro dump confirmed LP64 widths and that
  `NO_DIVIDE` and `Z_SOLO` were absent. This is not yet a Linux Click import.
- 126 host differential checks compared the unchanged implementations with canonical
  seeds and non-null byte buffers around lengths 1, 4, 16, 5,552 and 22,208.
  They are supplementary runtime evidence, not functional verification.
- Native Charon imports the selected unchanged Rust crate. No implementation
  source was changed for the proof trial.
