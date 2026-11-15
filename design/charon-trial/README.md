# Native Charon Rust adapter

The native adapter imports unchanged `trial.rs` through Charon and checks its
three contracts with Click's existing execution, memory, and certificate rules.
The scalar increment and the increment inside an owned guard both use ULLBC
control flow. The latter restores the caller's value on early return and after
a whole-value move followed by explicit drop. It has no whole-function HIR/MIR
coverage switch and no generated processed count.

The supported subset accepts `i32`, `u8`, `u16`,
`u32`, bools, scalar/reference locals and fields, flat structs, direct local
calls, scalar casts, comparisons, checked addition/subtraction/multiplication,
unsigned division/remainder, shifts and bitwise operations,
acyclic branches, nested natural while loops, whole-value moves, precise drops,
resolved unsigned `From` conversions, the scalar arrays, byte slices, borrowed scalar array fields, and shared exact-chunk protocol described below.
General traits/generics, nested owned fields, and returned references are not
enabled by this adapter yet. Extraction coverage in the
[assessment](../rust-charon-assessment.md) is broader than checked coverage here.

## Migration completion

Charon is the default and sole Rust extraction backend. Schema-3 configs may
omit `backend`; `charon` and the historical `charon-trial` alias select the same
path. Schema 2 is rejected before extraction or output mutation. The old
repository-owned exporter, compiler pin, build script, and CI runtime have been
removed. No function or artifact can fall back to legacy extraction.

All 16 canonical examples use the implicit native backend with their original
Rust bodies and contracts. The 72 original regression responsibilities are
retained: compiler-backed checks run against actual native artifacts, and serialized move/drop
corruption coverage now calls the lowering/kernel directly instead of forging
legacy JSON into a ULLBC file. Newly supported source patterns have positive
proofs and false-claim or authority negatives. Native iterator-state assertions
replace old JSON shapes and generated processed counts; loop proofs use semantic
frontiers. Standard unsigned identity `From<T>` calls are checked against their
resolved generic signature (`unsigned-from-v2`), with forged-signature negatives.
Borrowed iterator forwarding validates the resolved standard trait, implementation,
and associated-item signature, then keeps the concrete iterator's single state.
This preserves `for chunk in &mut chunks` and subsequent remainder access.
Extraction normalizes temporary output metadata so repeated refreshes, including
configs sharing an artifact, produce stable bytes and valid locks.
All 52 native configurations were refreshed through the pinned extractor.
Validation includes the original compiler-backed regression responsibilities,
native adapter/lowering and proof-tool checks, 20 live extraction tests, the
quality/setup gate, and 31 documentation checks.

CI builds and archives Charon and its driver once, restores the profile-derived
compiler runtime for archive consumers, and runs the live extraction gate. The
sections below retain checkpoint history; percentages and remaining gates in
those historical checkpoints describe their state when recorded. Completion
of the backend migration does not imply support for all Rust or whole crates.

## Build and reproduce

Click uses its normal stable compiler. The external Charon driver
needs `nightly-2026-09-17`, compiler commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, with `rustc-dev` and `rust-src`.
The build script downloads the pinned, unmodified Charon revision
`5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` into `target/charon-source` and builds
the wrapper and driver in `target/charon`. It does not change Click's default
toolchain.

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
export CLICK_CHARON="$(scripts/build-charon.sh)"
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
test, including zero iterations. The proofs use `step_until(loop(0))`, source
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

The state checkpoint below adds general represented lane copies and copies
after concrete element overrides. Whole-array
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
The fixture now imports its iterator as a library value: its sidecar names
the loop's iterator as `iter` and cites the `click::rust::chunks_exact`
contract, with no cursor or remaining-count local (`../rust-iterators.md`).
The state described above is the removed hidden-state model. Under the library model an iterator is a value, so a repeated
move in a tampered artifact copies it and is no longer refused; a missing
construction still is. The nested iterator checkpoint below now exercises that composition.

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

The following checkpoint adds owned local records and uniform region copies.
Shared array iteration was subsequently assessed for
adler2's owned `U32X4` computation.

## Owned uniform array-field checkpoint

[`owned-array-fields/owned.rs`](owned-array-fields/owned.rs) and its
[sidecar](owned-array-fields/owned.click) prove nine contracts for repeated-array
construction, whole-record moves, whole-field replacement, field extraction,
state independence, tuple fields, byte fields and empty fields. Replacement
preserves both neighboring scalar fields. Copies retain the value read before
any destination overwrite or later source mutation.

`compact-uniform-array-regions-v1` binds these operations into the import lock.
The existing fresh-array operation keeps its complete empty-local requirement.
The region operation separately checks local storage, constant aligned offsets,
full extents, element types, source initialization, mutable destination storage,
read/write authority and active loans. It writes one typed run, forgetting only
possibly overlapping cached values through the existing checked memory model.
It grants no new memory authority. Array fields have no scalar placeholder;
the actual constructor establishes their initialization before the record's
checked live flag permits access. Moves consume that flag exactly once.

Layout, lowered statement count and ordinary verification work remain bounded
at lengths 4, 1024 and 1,000,000. Kernel regressions check adjacent bytes,
overlapping copies, type/extent/alignment failures, incomplete authority,
readonly storage, active view loans and addressed scalar-local bindings.
Verification, profiling, auditing, expansion and expanded-certificate rechecking
agree on the unchanged trial source.

The following state checkpoint extends these copies to independently computed
scalar lanes. Borrowed symbolic or heap regions, union views and local-array
reassignment remain outside the region operation.

## Nonuniform array state checkpoint

[`array-states/states.rs`](array-states/states.rs) and its
[sidecar](array-states/states.click) prove eight contracts for computed
lanes, owned record moves, field replacement, neighboring fields, signed and
byte arrays, and source/destination mutation after copying. A sparse repeated
array contains a separately computed lane and retains it after source mutation.
The import lock names the compact scalar-array profile milestone.

Copies capture the selected source region before any destination write. They
retain constant spans as typed runs and explicit lanes as immutable scalar
values. Coverage includes run holes filled by explicit stores; incomplete or
incompatible typed coverage is rejected. Destination updates use the existing
checked overlap invalidation and establish initialization without granting
read/write authority. No copy points back to mutable source storage.

Work follows represented spans and cells, rather than array extent. Kernel
and ordinary imported verification regressions cover lengths 4/8, 1024 and
1,000,000, with fixed sparse edits. Overlapping copies preserve their original
source values; adjacent fields, permissions, initialization, qualifiers and
move flags remain checked. Ordinary verification, profile, audit, expansion and
expanded-certificate verification agree. The pinned compiler refreshes the
actual ULLBC artifact and all other checkpoint locks.

This supports concrete aligned local regions containing represented `i32`,
`u8` and `u32` values. Opaque load runs and symbolic-address cached writes are
rejected. Symbolic/heap region writes, local-array reassignment and resolved
custom operators remain migration work before
claiming parity for the unchanged checksum implementation.

## Shared scalar array iteration checkpoint

[`array-iteration/iteration.rs`](array-iteration/iteration.rs) and its
[sidecar](array-iteration/iteration.click) cover `for word in &words`, borrowed
array parameters, `.iter()`, explicit `next()`, a partially consumed iterator
moved into another local, repeated exhaustion, empty arrays, typed `u8`/`u32`
reads and a signed `i32` read. The lock names
`shared-scalar-array-iteration-v1`.

The model validates the compiler-selected core `Iter<T>`, `Option<&T>`,
inherent slice method and trait implementations, including concrete element
types and fixed-array extents. It shares reference-origin validation, Option
dispatch and CFG splitting with the exact-chunk model. A loop retains one
pure remaining-length guard and both successful and exhausted `next` events.
No processed-count variable is generated.

For a source iterator named `iter`, `iter_cursor` is a typed shared pointer,
`iter_remaining` counts elements, and `iter_live` tracks initialization and
moves. Construction checks the memory-model byte extent before converting
its length to `int32`. A successful call saves the old cursor in the typed
Option payload, advances by one element and decrements remaining length.
An exhausted call clears the Option tag while leaving cursor, remaining length
and live state unchanged. A payload projection requires `Some`; stale payload
storage cannot supply a reference after `None`. Moves transfer state and consume
the source. Reads require the original storage's view authority, and yielded
references retain their shared qualifier.

Regressions reject forged identities/signatures, mismatched Option payloads,
missing initialization, duplicate moves, missing read authority and false
element-order claims. Deterministic lowering and first-read verification work
remain bounded at 4/1024/1,000,000 elements; CFG splitting scales with protocol
count. The loop contracts currently use bounded execution on small concrete
extents; this scaling test covers a first read rather than a general reduction
invariant. Ordinary verification, profile, audit, expansion and rechecking agree.
Mutable, by-value and adapted iteration, iterator parameters/returns and general
non-byte slice APIs remain outside this checkpoint.

```sh
cargo run --bin click -- import lock design/charon-trial/array-iteration/iteration.click
cargo run --bin click -- verify design/charon-trial/array-iteration/iteration.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_shared_iteration_live_refresh_and_rejected_protocols)'
```

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

## Resolved source assignment operators

[assignment-operators/operators.rs](assignment-operators/operators.rs) imports local
`MulAssign<u32>`, `RemAssign<u32>` and `AddAssign<&U32X4>` implementations.
The multiplication and remainder method bodies are copied unchanged from adler2.
Resolved trait declarations, implementation identities, receiver and operand
signatures, call arguments and safe Rust ABI are checked before ordinary
function registration and dispatch. Stable contract names include the operand
type: `U32X4_mul_assign_u32`, `U32X4_rem_assign_u32` and
`U32X4_add_assign_ref_U32X4`. Colliding names fail import.

`resolved-source-assignment-operators-v1` authorizes dispatch to imported source
bodies. It adds no arithmetic axiom or special execution statement. A live
compiler regression uses two `AddAssign` overloads whose bodies replace the
receiver value, demonstrating that the implementation determines the behavior.
False lane results, overflow, zero divisors, missing authority and writes through
shared operands are rejected. Verification, profiling, auditing, expansion and
expanded-certificate rechecking exercise the ordinary call path.

The sidecar proves general unsigned multiplication under each lane's explicit
zero-or-safe precondition, arbitrary nonzero remainder, bounded borrowed addition
with preserved input lanes, and symbolic composition of two calls on a locally
constructed array-field record. Source bodies remain fixed. The
[symbolic scalar checkpoint](symbolic-multiply/probe.click) separately verifies
primitive multiplication, zero factors, full-width boundaries, and rejection of
missing safety premises, overflow and unguarded division by zero.

The proof machinery retains a checked refuted-disjunction witness for unreachable
panic-check paths. Equality congruence propagates through unsigned division,
remainder and XOR while preserving operation tags and load states; it grants
no arithmetic definedness. Reconstructed expressions keep unsigned casts and
explicit states, including lane zero. Both checkpoints exercise expansion and
rechecking, and indexed equality work is tested at 16/64/256/1024 inputs.
By-value aggregate operands, generic implementations, other operator traits,
external implementation bodies and dynamic dispatch remain rejected.

```sh
cargo run --bin click -- import lock design/charon-trial/assignment-operators/operators.click
cargo run --bin click -- verify design/charon-trial/assignment-operators/operators.click
cargo nextest run --test rust_import --run-ignored only -E 'test(charon_assignment_operators_live_refresh_and_source_semantics)'
```

The unchanged adler2 path still needs by-value aggregate operator operands,
crate-level import coverage and a checksum-loop proof. Charon remains opt-in.

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
unsigned conversion, repeated initialization, nonuniform state copy, indexing, and owned
cleanup. The byte-slice checkpoint carries full-width metadata, dynamic bounds,
reborrows and local calls through that same boundary. Stored exact-chunk state,
owned moves, typed Option dispatch and remainder now pass through it as well.
Nested iterator composition and byte-array coercions now pass through it too.
Next import the unchanged checksum loop and establish supported-fixture parity before switching the default and retiring legacy extraction.


## Parity and continuous extraction

The [parity inventory](parity.json) records every legacy Rust example config.
Entries remain when fixtures switch backends. A normal regression rejects
missing or duplicate entries; the required live CI
gate copies each unchanged Rust source and Click sidecar into an isolated
project, replaces only its import configuration, extracts ULLBC, and runs the
shared checker. `verified` means the whole existing sidecar passes. `rejected`
means extraction/normalization is missing; `proof-gap` means extraction succeeds
but the existing proof observations or contracts do not yet work. Expected gaps
must retain their diagnostic; any changed outcome fails the gate so the
inventory is revised with the implementation. This is fixture-level parity,
not a percentage of the Rust language.

Current result: **11 of 16 legacy fixtures verify unchanged** (68.75%). All
**16/16 fixtures import (100%)**; five have proof gaps. The shared byte
`split_at` model now verifies the original `rust-split-at` source and all four
frozen contracts/proofs. Remaining proof gaps are legacy iterator ghost names
in `rust-iterators`, `rust-chunks-exact`, and `rust-iter-references`, and numeric
statement frontiers in `rust-loops` and `rust-byte-sum`. Resolve these
observations in the adapter/proof interface without restoring a generated
processed count or rewriting Rust bodies. The default switch and legacy
retirement remain later migration gates; fixture parity is not a Rust-language
completeness metric.

The optional `migrated_sidecar` field records a separate proof port for an
unchanged source and contract. `rust-loops`, `rust-byte-sum`, `rust-chunks-exact`,
`rust-iterators`, and `rust-iter-references` now pass with these sidecars, so
source-and-contract coverage with migrated proofs is **16/16 (100%)**. A regression checks that each frozen original is digest-pinned and
parses, and the live sweep verifies each port
against freshly extracted original source. It still checks the original
sidecar and its recorded outcome separately; frozen-sidecar parity remains
11/16. Five digest-pinned archived sidecars retain their proof-interface gaps;
canonical adoption uses their verified ports with unchanged source/contracts.

The gate also runs all existing live compiler/borrow-checker rejection tests.
Locally use `scripts/check.sh --charon-live`, which builds pinned Charon.
CI builds pinned Charon, reuses the prepared Click test archive, and requires
this separate gate in its final `test` check. Locked-artifact tests remain in
the ordinary partitions.

[charon-profile.json](../../src/languages/rust/charon-profile.json) centralizes
compiler/extractor pins, extraction flags, and named semantic versions. It is
compiled into the adapter and read by the compiler build script. The historical identity byte ordering, including its combined array entry, is
preserved. `shared-scalar-slice-length-v1` extends interpretation and deliberately
changes the semantic identity; checked-in locks have been updated. External
Charon locks require `click import lock` again. Future interpretation changes
must version their named entry and deliberately refresh affected locks.

## Shared scalar array lengths

The [array-length checkpoint](array-lengths/README.md) imports `rust-arrays`
with its Rust source and Click sidecar unchanged. Rust coerces the shared array
reference to a slice before its compiler-resolved `SliceLen` call. The adapter
now accepts matching `i32` and `u32` scalar receivers alongside existing byte
slices, using paired slice metadata without reading or materializing elements.
This closes `rust-arrays` parity. Further inspection found that the array-value
fixture has no by-value array signatures: its rejection came from treating a
whole-array reference assignment as a scalar operation. It now verifies
unchanged, including compact copies from borrowed storage. Compiler pins and
extraction flags are unchanged.

## Whole-array assignments and borrowed states

The [array-value checkpoint](array-values/README.md) adds the missing ULLBC
assignment path for `*reference = array_value`. It uses existing checked compact
region writes, constructor operand capture, and state copies. Local scalar
arrays support literal/repeat replacement, self-copy, and independent copies
through mutable references. Deterministic 8-, 1024-, and million-element checks
retain bounded storage, lowered statement count, and proof work.

`local-scalar-array-reference-assignment-v1` deliberately versions this model
expansion; checkpoint lock identities are updated with unchanged compiler pins
and existing artifact bytes. The unchanged `rust-array-values` source and sidecar
now verify all sixteen contracts, including reads from shared external arrays
and writes to mutable external arrays. The external scalar-array profile milestone
versions this extension. Immutable source states preserve bytes after source
or destination mutation. Sparse represented lanes and compact runs are captured
without materializing the unknown remainder. Full read/write authority,
read-only qualifiers, active destination loans, alignment, local initialization,
and known object bounds remain checked. Empty arrays touch no bytes.

The accepted external pointers are argument/object storage with aligned
constant or single scaled 32-bit bases, alongside automatic storage. Live heap
allocations, typed union overlays, and general symbolic pointer expressions
remain outside this compact path. Genuine by-value array parameters and
aggregate returns are separate adapter gaps. Deterministic regressions cover
8, 1024, and million elements, source/destination states, sparse lanes,
source-load substitution, pointer spelling shapes, and unrelated source cells.
The frozen source is unchanged; no generated per-element operation or iterator
processed count is introduced.

Compact external writes require a whole-footprint decision for existing possibly
aliasing runs. If separation cannot be checked compactly, they refuse promptly
rather than traversing the logical array extent.

## Split loop headers

The [loop-header checkpoint](loop-headers/README.md) imports unchanged
`rust-loops` and `rust-byte-sum` through single-entry linear ULLBC header chains.
Guard reconstruction follows pure scalar copies, comparisons, and paired
shared-slice metadata in order across blocks. Header statements execute on
every test, including the final false test. Calls, memory reads, arithmetic,
shared entries, and extra exits remain outside this guard model.

The unchanged three Rust loop bodies verify with loop selectors in a separate
sidecar. The original numeric-selector sidecars remain frozen and counted as
proof gaps. `split-shared-slice-while-header-v1` versions the interpretation;
checkpoint locks are refreshed without changing prior ULLBC bytes or compiler
pins. Deterministic scaling checks cover header work and emitted code size.

The shared proof interface now also accepts
`step_until(assignment(local, N))`, selecting a named ordinary store, local compound update, or
call-result assignment by zero-based static occurrence. The loop checkpoint
proves source-local initialization through this selector, including live
re-extraction with an unrelated compiler local. Indexed selection avoids
counting unrelated helper statements; it preserves checked forward execution.
Selecting a final store does not move before right-hand-side helpers. This
adds a stable observation mechanism without changing frozen numeric-selector
sidecars, Rust interpretation pins, locks, or parity percentages.

`step_until(read(N))` additionally selects the Nth statement containing an
explicit scalar load, before the statement executes. The complete unchanged
byte-sum source and original prefix-sum contract now verify using loop, read,
and named assignment frontiers. The load, overflow checks, index update,
invariant preservation, and termination are checked through ordinary steps;
the proof uses neither compiler temporary names nor generated iterator state.
Both executable layout paths index read frontiers once with deterministic
linear scaling checks and constant-work lookups.

## Shared slice IntoIterator

[into-slices](into-slices/README.md) imports the unchanged `rust-iterators`
source through the compiler-resolved `IntoIterator for &[T]` implementation.
The named model checks the core trait, implementation path, method linkage,
signatures, concrete scalar element and shared mutability before constructing
ordinary typed iterator state. Shared i32/u32 slice parameters and source calls
carry paired pointer/usize length values; reborrows require metadata from the
same pointer origin. Actual loads still need checked views and the iterator
retains its signed-word memory-model extent bound.

`shared-scalar-slice-into-iteration-v1` versions this added interpretation.
Existing ULLBC bytes and extraction/compiler pins are unchanged; checkpoint
locks are deliberately updated. The frozen parity sweep records the newly
importing sum as a proof gap, not a verified fixture. Import coverage increases
to 15/16 (93.75%); frozen proof parity stays 10/16 (62.5%), and coverage with the
two previously migrated sidecars stays 12/16 (75%).


### Shared byte split_at and tuple component storage

[split-slices](split-slices/) locks genuine ULLBC for the unchanged
`rust-split-at` source and sidecar. The adapter resolves `core::slice::split_at`
by declaration path, shared receiver, byte instantiation, safe Rust signature,
and builtin two-element tuple result. Two explicit shared slice component
slots preserve the compiler value; projections, complete copies/moves,
replacement results, and storage ends use these slots. Component names reserve
both pointer and length identities against source locals. General tuple
construction, tuple parameters/returns, borrowed tuples, mutable split results,
and non-byte splits remain unsupported.

The CFG path reuses the existing checked split operation. It captures receiver
pointer/length before evaluating the midpoint, checks `mid <= len` and the
signed memory-model offset bound, then writes `(pointer, mid)` and
`(pointer + mid, len - mid)`. Both lengths retain full usize width; reads retain
ordinary range and view authority checks. No byte buffers are copied and no
proof-only processed count is introduced.

The checkpoint verifies all four frozen contracts/proofs, empty input, both
endpoint splits, and stored tuple copying/replacement. Tests reject missing
bounds, missing read authority, false byte/length claims, forged method/type/
projection metadata, and live mutable/non-byte/function-boundary shapes;
failed refresh preserves the previous artifact and lock. Verify, profile,
audit, and expansion agree. Deterministic work tests at extents 8/128/1024
ensure byte reads do not enumerate a slice. The semantic profile versions
`shared-byte-split-at-pair-v1` and updates checkpoint lock identities without
changing earlier ULLBC artifacts.

This increment changes imports from 15/16 to 16/16 (93.75% to 100%), strict
frozen proof parity from 10/16 to 11/16 (62.5% to 68.75%), and original
source/contract coverage including the two existing proof ports from 12/16 to
13/16 (75% to 81.25%). These are fixed fixture-baseline metrics, not a claim
that the migration or Rust-language support is complete.

## Original chunks proof port

[chunk-proof](chunk-proof/README.md) verifies the byte-identical original
`rust-chunks-exact` source and unchanged contract with a migrated proof. It uses
the imported iterator's cursor, remaining length, and remainder directly.
`step_until(loop(0).back_edge())` checks the rest of a loop preservation region
without counting compiler cleanup statements. `close_invariants()` still
checked every invariant and the decreasing measure separately; that tactic has
since been retired, and the back edge now closes each member with `solve()`.

This advances original-source/contract coverage with proof ports from 13/16
(81.25%) to **14/16 (87.5%)**. Frozen sidecars remain 11/16 (68.75%), imports
remain 16/16 (100%), and the default switch and legacy retirement remain open.

## Original implicit byte iteration proof port

[iterator-proof](iterator-proof/README.md) verifies the byte-identical original
`rust-iterators` source and unchanged mathematical sum contract. The proof uses
the real iterator cursor/remaining length and the source `byte` and `total`
locals. Named states and loop/read/assignment/back-edge selectors replace
legacy ghost names and compiler statement counts. Every overflow, memory read,
invariant, and decreasing measure remains checked.

This advances original-source/contract coverage with proof ports from 14/16
(87.5%) to **15/16 (93.75%)**. `rust-iter-references` is the remaining proof-port
gap. Frozen sidecars remain 11/16 (68.75%), imports remain 16/16 (100%), and
default switching and legacy retirement remain separate gates.

## Original reference byte iteration proof

The [iterator-proof](iterator-proof/README.md) checkpoint now verifies the
unchanged `rust-iter-references` source and its full mathematical sum contract.
`let { result: loaded_byte } = step();` binds the value of the checked scalar read,
following the existing checked call-result binding model. The proof uses actual
iterator cursor/remaining state, readable source frontiers, and named states;
it contains no MIR IDs, compiler statement indices, or synthetic processed
count. Ordinary read permissions, signed overflow, and decreases are checked.

Original source-and-contract coverage reaches **16/16 (100%)**, up from
15/16 (93.75%). Imports stay **16/16 (100%)**, and frozen sidecars stay
**11/16 (68.75%)**. This completes the fixed baseline's proof ports; it does
not complete default switching, frozen-proof compatibility work, or legacy
importer retirement.

## Canonical native example adoption

Eleven canonical examples now use schema-3 `charon-trial` configurations,
native ULLBC artifacts, and fresh import locks. Their Rust source and Click
sidecars are unchanged, and legacy JSON outputs are no longer needed.
Ordinary example verification checks those locked native inputs offline;
the required live gate still re-extracts all 16 original Rust fixtures and
checks their frozen outcomes and proof ports. Archive consumers need no
Charon compiler installation.

Canonical-example adoption is **11/16 (68.75%)**, up from 0/16. This is a
rollout measure using the same fixed fixture inventory, separate from imports
and original source/contract proof coverage (both **16/16, 100%**) and frozen
sidecar compatibility (**11/16, 68.75%**). The remaining five canonical examples
still use the legacy exporter until their completed proof ports are adopted.
The implicit backend default and legacy exporter retirement remain open.

## Complete canonical proof-port adoption

All **16/16 canonical Rust examples (100%)** now use native Charon imports,
up from 11/16 (68.75%). The five remaining examples adopt their verified proof
ports with unchanged Rust source, signatures, specification functions,
preconditions, and postconditions. Their fresh native artifacts and locks are
checked in for offline example verification.

`parity.json` records each replaced original sidecar's archived path and SHA-256
digest. On 2026-10-26 the archives received their initial syntax respelling
(tactic names, Rust signatures, `as` casts, qualified library citations):
each respelled file is byte-identical to what the retired reading adapter
produced from the original bytes, so its contracts, specification functions
and proofs, gaps included, are the original's. `frozen_sha256` pins the
respelled bytes and `original_sha256` the originals, which git history
holds. The 2026-11-15 `rewrite` argument migration respells equality
arguments as two expression arguments and refreshes the affected frozen
digests; original digests and recorded outcomes stay fixed. The live gate
checks every current canonical proof after fresh extraction, then
independently checks archived frozen outcomes.
Legacy-backend regressions also explicitly use archived legacy proofs.
No historical frozen failure is relabeled as a success.

Imports, original source/contract proof coverage, and canonical adoption are
all **16/16 (100%)**. Literal frozen-sidecar compatibility remains **11/16
(68.75%)**, a historical compatibility measure rather than a promise to retain
legacy generated names. The implicit backend default and legacy extractor
retirement remain open migration gates.
