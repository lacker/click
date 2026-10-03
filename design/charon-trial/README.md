# End-to-end Charon adapter trial

This opt-in trial imports unchanged `trial.rs` through Charon and checks its
three contracts with Click's existing execution, memory, and certificate rules.
The scalar increment and the increment inside an owned guard both use ULLBC
control flow. The latter restores the caller's value on early return and after
a whole-value move followed by explicit drop. It has no whole-function HIR/MIR
coverage switch and no generated processed count.

The trial is narrower than the existing frontend. It accepts `i32`, `u8`, `u16`,
`u32`, bools, scalar/reference locals and fields, flat structs, direct local
calls, scalar casts, comparisons, checked addition/subtraction/multiplication,
unsigned division/remainder, shifts and bitwise operations,
acyclic branches, nested natural while loops, whole-value moves, precise drops,
resolved unsigned `From` conversions, the scalar arrays, byte slices, borrowed scalar array fields, and shared exact-chunk protocol described below.
General traits/generics, nested owned fields, and returned references are not
enabled by this adapter yet. Extraction coverage in the
[assessment](../rust-charon-assessment.md) is broader than checked coverage here.

## Build and reproduce

Click uses its normal stable compiler. The optional external Charon driver
needs `nightly-2026-09-17`, compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, with `rustc-dev` and `rust-src`.
The build script downloads the pinned, unmodified Charon revision
`5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` into `target/charon-source` and builds
the wrapper and driver in `target/charon`. It does not change Click's default
toolchain or the legacy exporter's pin.

```sh
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component rust-src
scripts/build-charon.sh
cargo run --bin click -- import lock design/charon-trial/trial.click
cargo run --bin click -- verify design/charon-trial/trial.click
cargo run --bin click -- profile design/charon-trial/trial.click
cargo run --bin click -- audit design/charon-trial/trial.click
```

To inspect a generated certificate, expand `guarded_increment.contract` with
`--in-place` and verify the resulting sidecar through the ordinary entry point.
Keep experiments in a task worktree and restore the checked fixture afterwards.
The ordinary `rust_import` regressions perform this operation in a temporary
project and check false results, possible overflow, missing memory authority,
and incorrect restoration. Unit regressions deliberately corrupt the normalized
ownership events and check that the shared engine rejects duplicate moves,
duplicate drops, missing cleanup, and reads after move.

The normal repository gate uses the checked-in artifact and lock; it requires
neither Charon nor this extra nightly to load and verify them. The separately
invoked live compiler regression refreshes through the real extractor and checks
E0506/E0382 rejection without publishing an artifact:

```sh
export CLICK_RUST_EXPORTER="$(scripts/build-rust-exporter.sh)"
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_trial_live_refresh_and_compiler_rejections)'
```

Each external compiler invocation uses the existing owned process containment
boundary, with a 30-second deadline and bounded diagnostic output. These are
compiler crash-containment limits, not proof-search budgets.

## Borrowed loop with a live guard

[`borrowed-loop/loop.rs`](borrowed-loop/loop.rs) borrows the guard's mutable
reference on each iteration, writes the counter, and restores the original
caller value when the guard drops. Its sidecar proves `result == n`, restoration,
and termination for every `0 <= n <= INT32_MAX`, including zero iterations.
The separate `final_header` probe checks header assignments on the final false
test, including zero iterations. The proofs use `execute_until(loop(0))`, source
locals, and ordinary loop
invariants; no generated counter or manual CFG statement numbers are needed.

```sh
cargo run --bin click -- import lock design/charon-trial/borrowed-loop/loop.click
cargo run --bin click -- verify design/charon-trial/borrowed-loop/loop.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_borrowed_loop_live_refresh_and_rejected_control_flow)'
```

The adapter recognizes single-entry natural while regions with one conditional
header and one normal exit. Body diamonds, sequential loops, and nested loops are supported;
irreducible entries and extra exits are rejected. Inner regions are validated
and collapsed before their parents, with indexed predecessors and union-find
membership. Deterministic regressions at nesting depths 8, 32, and 128 check
linear analysis work and emitted size.
Headers accept total scalar copies, literals, comparisons, and boolean negation.
Memory reads, calls, arithmetic, borrows, and ownership changes in a header are
rejected. Header assignments execute on every taken iteration and once after
the final false test. Substitution has a fixed expression-size bound, and the
emitted program has two copies of each header and one of each body block.

Unknown pointer fields in local storage now have opaque provenance. Their
storage object's address space does not constrain their pointee. Pointer facts
cross iterations only with checked unchanged-byte evidence; an exact alias used
to match a store to a separated range is retained and rechecked in certificates.
Read and write authority still comes from the shared resource rules.
The zero-iteration proof retains its exact constant equality and both signed
bounds, then emits a checked arithmetic certificate. Removing any of those
premises invalidates the proof.

## Resolved conversions and compact scalar arrays

[`conversions-arrays/arrays.rs`](conversions-arrays/arrays.rs) combines
`u32::from(x)` with a repeated array, a whole-array copy, and a restoring owned
guard. Other contracts cover a million-element repeated array and its copy,
explicit element initialization and mutation, a truncating `as` cast, and a
zero-length initializer whose function call still executes exactly once.

```sh
cargo run --bin click -- import lock design/charon-trial/conversions-arrays/arrays.click
cargo run --bin click -- verify design/charon-trial/conversions-arrays/arrays.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_arrays_live_refresh_and_rejected_source_shapes)'
```

`unsigned-from-v1` requires a compiler-resolved external standard-library `From`
trait implementation, the matching method and signature, and compatible unsigned
source/destination widths among `u8`, `u16`, `u32`, and target-width `usize`.
Narrowing conversions and lookalikes fail closed. `as` continues to use Rust's
truncating scalar-cast semantics. Compiler-generated two-phase mutable call
borrows use the same exclusive reference interpretation as ordinary mutable
borrows; source borrow checking still runs.

`compact-uniform-scalar-array-v1` supports local `i32`/`u8`/`u32` arrays with
concrete lengths and byte extents at most `INT32_MAX`. Repeated initialization
stores one evaluated value in one typed run. A complete uniform initialized
array can be copied into fresh complete local storage in one checked operation;
subsequent source writes cannot change that copy. Explicit element lists use
ordinary typed stores, with work proportional to their written source. Index
reads and writes retain full-width bounds obligations.

Bulk operations check complete destination write authority, source read
authority, initialization, type, extent, and fresh storage. Empty arrays access
no bytes. Lengths 8, 1024, and 1,000,000 have the same emitted statement count,
zero generated aggregate fields, and bounded deterministic verification work.
The source fixture and negative claims also run through verification, profiling,
auditing, expansion, and expanded-certificate rechecking.

General snapshot copies, copies after an element override, whole-array
reassignment, by-value array parameters/returns, array fields and nested arrays
remain outside the compact-array increment. Unsupported
bulk source/storage shapes produce a bounded checked execution failure; they are
never assumed uniform. Fixed indices in this fixture are constant-folded by the
compiler, while Click independently checks their normalized bounds. Iterator
models remain adoption gates.

## Byte-slice checkpoint

[`slices/slices.rs`](slices/slices.rs) and its [sidecar](slices/slices.click)
exercise shared/mutable byte-slice parameters, `.len()`, dynamic reads/writes,
local reborrows and local calls, plus a restoring guard and unsigned conversion.
The named interpretation `byte-slice-metadata-v1` represents each slice as its
qualified data pointer and full-width `usize` length. Reborrows require both
components to originate from the same typed slice; shared access cannot be
strengthened to mutable access. Compiler-resolved `SliceLen` declarations are
checked for identity, signature, generic arguments, safety, and argument types.
No byte resource is required just to read metadata, including length zero and
`u64::MAX`; deterministic metadata proof work stays bounded across those sizes.

Charon's selected fallible-operation reconstruction also removes index panic
branches. Each ULLBC typed index therefore becomes an independently checked
full-width bounds obligation. Click checks the signed memory-model extent before
narrowing an offset and requires views/ownership for reads/writes. Missing bounds,
missing authority, out-of-bounds and high-bit indices, false results and false
restoration claims are rejected. Cross-width guard framing uses explicit proved
signed-index bounds derived from the `usize` preconditions. Verification,
profiling, auditing, expansion, and expanded-certificate rechecking share the
same engine.

Subslices/split operations, general iterators,
slice fields/returns, and non-byte slices are not yet accepted by this adapter.
Other remaining ULLBC assertions are rejected rather than discarded. The default
frontend's broader slice and iterator coverage remains a migration parity gate.

## Stored exact-chunk checkpoint

[`chunks/chunks.rs`](chunks/chunks.rs) and its [sidecar](chunks/chunks.click)
import stored shared `ChunksExact<u8>` iterators, a saved remainder, whole-value
moves, owned `IntoIterator`, typed `next`/`Option` matching, and a natural loop.
The loop reads both ends of each four-byte chunk. Its contract proves termination,
that the cursor reaches the fixed remainder without gaps, and preservation of
every input byte for lengths zero through 1000. A generic constructor contract
proves the remainder length for every nonzero target-width size and supported
input length. Separate probes check an explicit `next` match and a tail byte.

```sh
cargo run --bin click -- import lock design/charon-trial/chunks/chunks.click
cargo run --bin click -- verify design/charon-trial/chunks/chunks.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_chunks_live_refresh_and_rejected_protocols)'
```

`shared-byte-chunks-exact-v1` checks external standard-library declarations,
trait/implementation identities, generic receiver and result types, safe method
signatures, and exact `Option` tags/projections. The iterator has a cursor,
remaining complete-byte length, full-width size, fixed tail pointer/length, and
checked move liveness. The option has a tag and qualified slice metadata; its
payload requires `Some`. No processed count is generated. Normalization separates
the assessed `next` dispatch into a pure state guard and two edge-local state
transitions, preserving the final `None` call. Extra dispatch effects or incoming
edges fail closed. Predecessors and reference roots are indexed once; output and
charged normalization work grow linearly with the number of protocol instances.

The model uses existing checked assignments, assertions, branches, and loops.
It creates no read/write authority. Zero chunk sizes fail the panic obligation;
input lengths must fit the signed memory model before offsets are narrowed.
Oversized full-width sizes produce no chunks and preserve the entire remainder.
Regressions cover empty input, exact multiples, short tails, explicit `Some` and
`None`, missing bounds/authority, false byte/result claims, missing construction,
and duplicate moves. Metadata proof work stays bounded across lengths zero, 8,
1024, and one million. Verification, profiling, auditing, expansion, and expanded
certificate rechecking use the same engine. The live compiler regression rejects
writes through shared chunks, reuse after an owned move, and unmodeled protocols.

This increment accepts the assessed owned-loop and explicit-match shapes.
Borrowed `for` loops, mutable chunks, general iterator adapters,
iterator parameters/returns, and non-byte elements remain migration gates.
The current fixture uses internal local/state names and statement selectors for
its preservation proof; stable source/proof observations still need a separate
interface. The nested iterator checkpoint below now exercises that composition.

## Nested chunks and byte-array coercions

[`nested/nested.rs`](nested/nested.rs) and its [sidecar](nested/nested.click)
compose a stored outer four-byte chunk iterator with inner two-byte iterators.
For an eight-byte input, the contract proves termination, checks both reads in
all four inner chunks, and preserves every original byte. Each iterator has its
own cursor, remaining length, size, tail, and move liveness; there is no generated
processed count. The proof uses a checked reusable offset lemma and expanded
certificates. Compiler locals with duplicate names (including nested `iter`
temporaries) receive collision-free names derived from their local IDs. Unique
source names and parameter names remain available.

`byte-array-unsize-v1` accepts typed shared/mutable byte-array reference casts to
byte-slice references. It checks concrete length metadata against the source
array extent, argument/destination types and mutability, and the signed memory
extent. Lifetime IDs may change during coercion; normalized reference types
ignore these IDs, while rustc still checks source borrow legality. The coercion
uses existing array storage and slice metadata and creates no memory authority.
Contracts check length, mutable writes, dynamic reads, empty arrays and lengths
8, 1024, and one million. Nonempty metadata verification work stays constant
across these lengths; the empty-storage case has a separate deterministic bound.
Mismatched metadata/types, out-of-bounds reads, false byte/result claims and
shared writes are rejected. General unsizing, non-byte slices and symbolic
extents remain outside this model.

```sh
cargo run --bin click -- import lock design/charon-trial/nested/nested.click
cargo run --bin click -- verify design/charon-trial/nested/nested.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_nested_live_refresh_and_rejected_array_borrows)'
```

Ordinary verification, profiling, auditing, expansion and expanded-certificate
rechecking exercise this checkpoint. The nested proof is a fixed-length
composition regression; importing the unchanged checksum loop and proving its
arithmetic are still separate adoption gates. Source/proof observations still
need a stable interface before making Charon the default.

## Borrowed array-field checkpoint

[`array-fields/fields.rs`](array-fields/fields.rs) and its
[sidecar](array-fields/fields.click) exercise fixed `u8` and `u32` array
fields through compiler-selected record offsets and the shared memory model.
Named and tuple fields may be indexed and borrowed from shared or mutable record
references. Borrowed byte fields may coerce to slices and call local functions;
borrowed word arrays retain their extent when passed to local functions. The
trial proves reads, a mutation's neighboring-cell/marker frame, and an empty
field's length. Charon calls the tuple field `_0` in the locked artifact; its
Rust source still uses `.0`. Stable proof observations remain an adoption gate.

`borrowed-scalar-array-fields-v1` binds this interpretation into the import lock.
Each field retains one layout entry and a concrete extent, including a zero
extent. ABI validation checks byte widths, offsets, alignment and overlap across
the complete array, without flattening its elements. Extents must fit the
signed-word memory model. Full-width index bounds are checked before fixed-array
indices become signed-word offsets. Pointer qualifiers follow the record
reference; mutable array borrows from shared records are rejected. The shared
contract path also treats `u32` array fields as typed addresses, with a C
regression for the same rule.

Use explicit array-field segments for memory authority. Deterministic checks at
lengths 4, 1024 and 1,000,000 keep layout cardinality and verification work bounded
independently of the field extent. Negative cases cover out-of-bounds/high-bit
indices, missing write authority, false results, invalid layouts and forged
mutable borrows. Verification, profiling, auditing and expanded-certificate
rechecking agree on the trial.

Owned records containing arrays, whole-field copies and whole-field assignments
remain rejected. They need compact region initialization and copying that preserve
neighboring fields; the existing fresh whole-local array operation does not
provide those semantics. Add that checkpoint and shared array iteration before
claiming support for adler2's owned `U32X4` computation.

## Checksum arithmetic checkpoint

[`arithmetic/arithmetic.rs`](arithmetic/arithmetic.rs) retains the existing
unsigned arithmetic regression source unchanged and adds width and panic probes.
Its [sidecar](arithmetic/arithmetic.click) proves the exact remainder modulo
65521, shift/OR checksum packing, lossless byte accumulation, narrow truncation,
unsigned division/remainder, complements, masks, full-width shifts and guarded
division. These are operator regressions, not a verification of Adler-32.

`unsigned-checksum-operators-v1` accepts compiler-typed `Div`, `Rem`, `Shl` and
`Shr` with `Panic` mode for unsigned `u8`, `u16`, `u32` and `usize`, plus bitwise
AND/OR/XOR and complement at those widths. Division/remainder and binary bitwise
operations require matching operand types. Shift counts retain their original
integer type and width; the shared checked evaluator validates the full-width
bounds before constructing the shift term. Negative, width-sized, high-bit and
maximum-width counts fail the Rust panic obligation. Left shifts may discard
value bits, as Rust requires. Division/remainder by zero are rejected, including
when the operands occupy only eight or sixteen bits.

The selected reconstruction converts the assessed compiler checks into typed
panic-mode operations. Click reintroduces and checks those obligations using the
existing Rust lowering and kernel. Wrap/UB modes, wrapping-method calls and signed
division/shifts remain rejected by this adapter. A conditional division probe
checks that an untaken division needs no nonzero premise. False reductions,
incorrect packing and overflow claims are rejected. Verification, profiling,
auditing, expansion and expanded-certificate rechecking exercise the same model;
a matching default-frontend regression checks shared shift-count lowering.

```sh
cargo run --bin click -- import lock design/charon-trial/arithmetic/arithmetic.click
cargo run --bin click -- verify design/charon-trial/arithmetic/arithmetic.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_checksum_arithmetic_live_refresh_and_rejected_modes)'
```

The unchanged adler2 path still needs owned array-field construction/moves,
array/shared-element iteration, resolved custom operators and crate-level import coverage. Continue
those checkpoints before claiming checksum verification or changing the default.

## Profile, locks, and trust

Configuration schema 3 with `backend: "charon-trial"` selects this path. The
artifact is an envelope around Charon's typed `CrateData`, deserialized through
the pinned `charon_lib` without its rustc feature. The wrapper revision and
compiler commit are checked during refresh. The lock binds source, configuration,
artifact, wrapper and driver hashes, compiler/extractor revisions, and the
adapter/model profile. Ordinary verification reads locked inputs without running
either binary. Partial artifacts and incompatible options/profiles are rejected.
Only one source file with the locked contents is accepted.

The profile is Rust 2024 on `x86_64-unknown-linux-gnu`, panic abort, overflow checks
on, and MIR optimization level zero. It deliberately requests **optimized MIR**:
Charon's earlier-phase fallback cannot silently change the selected phase.
Constant/global initializer paths and dependencies with unmodeled bodies are
outside the accepted slice. Precise drops and ULLBC are required. No preset,
index-to-call, operation-to-call, or borrow-check bypass is enabled.

The one newly selected transform, `reconstruct_fallible_operations`, replaces
the overflow tuple/assert pattern with a panic-on-overflow operation and
removes index panic checks in favor of typed index projections. This loses
unwind detail, which the abort profile excludes. The adapter accepts only the
assessed operators and overflow modes; Click reintroduces their checked
arithmetic range and index bounds obligations. Neither wrapping nor unchecked arithmetic receives checked Rust
semantics accidentally. Charon clears consumed rustc arguments in its serialized
options, so the refresh-owned envelope separately records the exact compiler
flags and checked compiler identity.

The named interpretation `flat-record-drop-v1` covers compiler-generated
`Destruct` glue and compiler-resolved `mem::drop` for local flat records whose
fields are scalars/references. It invokes the imported, independently checked
`Drop::drop` method once and consumes the owned value. Resolution uses declaration
and trait IDs, lang/diagnostic items, and the glue receiver type; lookalike names
are insufficient. Generated glue is not separately verified as arbitrary raw
pointer code. Wider owned fields, cleanup effects, and library models need new
assessed interpretations or verified imported bodies.

The trusted compiler/extractor/adapter establishes correspondence with Rust;
the shared checker establishes the claims and rejects forged resource transfers.
rustc still establishes source borrow legality. Live loan graphs are not added
by this increment. The normalized CFG temporarily uses the existing internal
Rust vocabulary and local names. The compact scalar-array operation is shared kernel vocabulary. This trial
does not complete the stable proof-observation interface or general array-copy
coverage.

## Migration decision

Successful checked arithmetic, owned cleanup, negative authority cases, and
proof-tool agreement justify proceeding toward Charon as the Rust extraction
boundary. Keep this explicit opt-in until existing supported fixtures have
equivalent coverage, named library models, stable source/proof observations, and
scaling evidence. Extend the single ULLBC adapter rather than adding a fallback
to the legacy exporter per function. The borrowed-loop checkpoint now composes
a live restoring guard with checked
iteration and termination. The conversions/arrays checkpoint composes resolved
unsigned conversion, repeated initialization, uniform copy, indexing, and owned
cleanup. The byte-slice checkpoint carries full-width metadata, dynamic bounds,
reborrows and local calls through that same boundary. Stored exact-chunk state,
owned moves, typed Option dispatch and remainder now pass through it as well.
Nested iterator composition and byte-array coercions now pass through it too.
Next import the unchanged checksum loop and establish supported-fixture parity before switching the default and retiring legacy extraction.
