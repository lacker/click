# P1: Support safe Rust and verify a shared C/Rust checksum specification

## Goal and priority

Deliver a useful, explicitly bounded safe-Rust verification path through
Click's existing proof language and checked engine. Then verify unchanged C
and Rust implementations of the same checksum against one mathematical
specification. This issue is P1 by user direction on 2026-09-30. General Rust
coverage remains later work; the Linux rbtree remains the key launch demo.
Rust frontend work can proceed alongside C/C++ work, with coordinated changes
to shared resource and execution rules.

There are two independently reviewable milestones:

1. **Experimental Rust support:** verify meaningful functional contracts over
   unchanged `.rs` source using Click sidecars, including scoped borrowing.
2. **Shared C/Rust library demonstration:** prove selected existing checksum
   implementations satisfy the same specification, establishing equality of
   their results under matched input and state conditions.

Ship and document the first milestone as soon as it is complete. Do not wait
for the library demonstration to announce the supported subset.
Both milestones must satisfy the architecture consolidation requirements below;
successful isolated feature fixtures are not sufficient evidence that the
features compose or that their representations scale.

## Unmet capability and required invariant

Click now has an experimental Rust source import and verification path. The
borrow fixture and move/drop guard verify unchanged Rust through shared Click
proof tooling. General library support and the shared checksum demonstration
remain unmet. The nested owned-field regression now verifies the unchanged
Rust source with final caller value 42 and rejects a claim of 1. Shared call
rules reserve the returned field and retained storage fragments exactly once.
Parent mutation after explicit child drop and disjoint mutable field borrows
also verify; conflicting borrows and use after move are rejected by rustc. See
[the supported subset](../docs/reference/rust.md) for exact bounds and
reproduction commands.

For supported source, compiler-established type and borrow guarantees must
survive translation into the checked execution model. Mutations, calls,
resource transfers, and recovery must preserve their meaning, and false
functional claims must be rejected. The C and Rust programs must satisfy one
shared specification without rewriting their implementation to suit the
verifier. Unsupported constructs must produce bounded, actionable diagnostics
rather than silently receiving C semantics.

## Existing evidence and architecture

Start with the [worked resource correspondence](../design/rust-resource-correspondence.md),
[language design](../design/supporting-more-languages.md), and
[stable views](../docs/internals/stable-views.md). The correspondence pairs
four Rust compiler/runtime witnesses with four independent resource traces
and three compiler rejection cases. Production shared-loan correspondence
also has checked tests. Exclusive child borrowing and value transport are
model-only; the small field model suspends the whole parent, more strictly
than Rust's field-sensitive rules. Disjoint range partitioning has separate
evidence and must be connected to any exclusive dependency representation.

Use a pinned rustc integration and reuse its type and borrow checking for the
supported safe subset. Select extraction boundaries by semantic coverage and
composition evidence. HIR versus MIR is not a contest with one universally
correct answer; the requirement is a consistent verification representation.
A complete lifetime/loan export or an independent borrow checker is not a
prerequisite unless the selected proof interpretation needs it. Retain Click
sidecars and checked proof operations when borrowing designs from other tools.

Map ordinary exclusive access to borrowed `owns` authority and ordinary shared
access to stable `views`. Keep allocation lifetime, access authority, and type
validity distinct: an `&mut T` does not grant deallocation authority, and a
Rust move transfers value resources rather than merely lending them. Sidecar
or ghost access must not introduce conflicting authority rustc never checked.

Keep one proof language and one bounded verification engine. Rust-specific
frontends belong beside the existing language modules; share kernel operations
where their semantics agree. Lock source identity, compiler/exporter version,
selected target/layout, semantic flags, and dependencies into prepared inputs.
Document the compiler and translator trust boundary. Do not introduce a
parallel Rust verifier or rename every C-prefixed type as a prerequisite.

## Current checkpoint

The first experimental frontend imports a pinned rustc typed HIR artifact for
single-file safe scalar/reference functions. The basic Rust example exercises
branching, a local reborrow followed by parent reuse, and a direct field helper
call with preservation of the other field, plus a shared-field borrow across
a disjoint write. Verification, profiling, auditing,
and expansion share the existing engine. See `docs/reference/rust.md` for the
exact subset and trust boundary.

This is an increment toward milestone 1, not its completion. The production
subset now includes whole-value moves, checked drops, nested field borrows,
and disjoint mutable field regressions. Explicit extracted loan authority
suspension/recovery and wider source coverage remain outstanding; source borrow
legality currently comes from the pinned compiler.

## Architecture consolidation before further library coverage

The 2026-10-02 review identified four design changes required for the long-term
frontend. Preserve the useful foundations: pinned compiler semantics and layout,
locked prepared inputs, explicit panic obligations, shared memory authority,
and checked proof certificates. Consolidate the representations in coherent
increments rather than replacing the proof engine or rewriting source programs.

### 1. Make supported operations compose with ownership

The exporter currently uses structured typed HIR for scalar/reference functions,
but switches a whole function to the narrower drop-elaborated MIR exporter when
any MIR local has a local record type. This is a semantic coverage cliff.
For example, a function returning `u32::from(x)` for `x: u16` imports, but adding
`let _guard = Guard { field: 1 };` makes the same conversion fail with
`MIR call outside direct local scalar/reference calls`. MIR arithmetic and
byte slices have separate restrictions, and owned-value MIR loops are rejected.

Introduce a common typed semantic body representation for evaluation, places,
checked operations, resolved calls, control flow, and ownership/drop events.
HIR may supply source structure and proof locations; MIR may supply resolved
evaluation and cleanup. Specify which compiler phase establishes each fact and
how source structure corresponds to semantic operations. Do not combine the
two by heuristic matching or maintain separate definitions of Rust arithmetic
and call semantics according to whether a function contains an owned record.

Acceptance:

- Existing supported conversions, arithmetic, references, arrays, slices, and
  iteration compose with modeled owned records, moves, and drops. Add tests that
  combine these features, including a guard surviving across a supported loop.
- Preserve evaluation order, single evaluation, checked overflow/bounds,
  short-circuiting, and cleanup on every supported exit. Negative functional,
  panic, permission, and duplicate-cleanup cases reach the appropriate boundary.
- Shared control-flow joins remain shared; body size and checking work do not
  grow with the number of paths. Preserve source attribution through lowering.

### 2. Keep array shape and bulk operations compact

Current local-array lowering enumerates every element in the aggregate layout;
`[value; N]` also builds an element-sized vector and emits N stores. Tiny source
such as `[0u8; 1_000_000]` can therefore generate a huge verifier program.
Four checksum lanes do not establish a scalable representation for buffers.

Represent array element type, length, repeated initialization, and whole-array
copies compactly, with range-based value and authority reasoning. An explicit
N-element source initializer may require N work; a repeated initializer must
not require N verifier operations merely because its runtime storage is large.
Preserve one evaluation of the repeated operand, including when N is zero.

Acceptance:

- Empty arrays, repeated initialization, explicit initialization, copies,
  aliasing/reborrows, element updates, and neighboring-byte preservation verify
  with the same source semantics and permission rules.
- Deterministic regressions vary repeat/copy length, explicit source initializer
  size, and unrelated context independently. Compact operations do not allocate
  one layout field, proof term, or generated store per represented element.
- Ordinary verification, expansion, and audit agree; no higher work budgets or
  specialized source rewrites compensate for representation growth.

### 3. Separate source identities and proof observations from lowering names

Functions, records, and locals currently cross the artifact boundary largely as
strings. Generated slice parameters and iterator state use names such as
`bytes_len` and `chunks_remaining`; valid Rust names can collide with them.
Sidecars also depend on these names and repeated `(int32)(uint32)` conversions.
Expression and statement variants lack systematic source spans.

Use compiler-resolved identities, typed place projections, and source locations
independently of display spelling. Add stable source-facing observations for
slice contents/lengths and iterator remaining ranges so representation changes
do not require rewriting every contract and invariant. Retain an explicit
mapping for readable diagnostics and checked expanded proofs. Migrate existing
sidecars deliberately rather than silently changing their meaning.

Acceptance:

- Shadowing and source names matching generated suffixes remain importable;
  qualified item identities support later modules and resolved method calls
  without depending on globally unique short names.
- Contracts and loop invariants use stable observations; generated temporary
  spelling and storage representation can change without changing the claim.
- Panic/permission diagnostics identify the original Rust operation. Expansion
  preserves identity and snapshot meaning and parses and verifies normally.
- Full-width Rust metadata remains intact. The current signed-word memory-range
  bound stays explicit until shared kernel support removes it; a nicer proof
  surface must not conceal that semantic restriction or truncate `usize`.

### 4. Centralize resolved library models and their trust assumptions

`From`, slice iteration, splitting, and exact chunks currently use separate
recognition and lowering paths. Keep compiler resolution, but replace the
growing collection of special cases with a common registry of supported
operations or instances. A model records the resolved item/type arguments,
compiler/profile requirements, preconditions, effects, panic behavior, and
whether its semantics come from verified imported code or a named trusted
interpretation. The same model must apply inside and outside owned functions.

Acceptance:

- Supported standard-library calls and instances share resolution and semantic
  dispatch. Lookalike user methods, unsupported implementations, and unmodeled
  instances fail promptly rather than receiving a model by spelling alone.
- Model identity participates in prepared-input compatibility; source/profile
  or model changes require the appropriate refresh and invalidation.
- Iterator models preserve actual state, exhaustion, shared bytes, and remainder
  coverage without generated processed-count shortcuts. Conversion models
  preserve values and evaluation order. Mutable/adapted forms require their own
  assessed resource and state transitions before being enabled.
- Documentation names trusted models individually. Checksum computation remains
  verified code; a library summary must not assume the checksum postcondition.

### Implementation references and delivery order

The inspected projects offer complementary designs:

- [Verus](https://github.com/verus-lang/verus/blob/main/source/CODE.md) translates
  Rust HIR/THIR to its own VIR, then to a statement-oriented representation and
  assertion IR. Borrow its separation of compiler integration, semantic IR,
  and proof backend, and study its
  [mutable-reference interpretation](https://verus-lang.github.io/verus/guide/mutable-references.html).
- [Creusot's body translator](https://github.com/creusot-rs/creusot/blob/master/creusot/src/translation/function.rs)
  translates MIR to FMIR; its
  [program backend](https://github.com/creusot-rs/creusot/blob/master/creusot/src/backend/program.rs)
  lowers that to Coma for Why3. It provides a complementary MIR-based example
  of keeping Rust semantic normalization separate from backend reasoning.
- [Charon](https://github.com/AeneasVerif/charon) extracts simplified MIR,
  resolved declaration/trait information, and source information into an
  independent representation. [Aeneas](https://github.com/AeneasVerif/aeneas)
  consumes its LLBC representation and translates a safe-Rust subset into pure
  functional models for proof assistants. Study the extraction and borrowing
  abstractions without replacing Click's existing memory and proof model.

The [2026-10-02 Charon assessment](../design/rust-charon-assessment.md) completes
the initial extraction comparison. The pinned candidate extracts an owned guard
combined with conversions, arrays, and borrowed iteration, rejects invalid
borrowing/moves, keeps repeated arrays compact and CFG joins shared, and extracts
the unchanged pinned adler2 path. This is extraction evidence, not checksum
verification. Its newer compiler, per-body MIR phase provenance, library models,
source/proof correspondence, and checked resource mapping remain adoption gates.

The [end-to-end adapter trial](../design/charon-trial/README.md) now routes checked
arithmetic and a restoring owned guard through ULLBC and the existing engine.
The borrowed-loop checkpoint now proves iteration, termination, and restoration
with a live guard, including zero iterations and the maximum signed bound.
It rejects unsupported CFG exits/entries and effectful guards; scaling checks
cover sequential loops and diamonds. Shared pointer framing retains exact alias
and separation premises, rather than inferring provenance from local storage.
Keep migration opt-in until the supported fixtures have equivalent coverage.
The conversions/arrays checkpoint now composes a resolved `u32::from` call,
repeated initialization, uniform whole-array copy, and restoring `Drop` guard.
Its shared compact initialization operation checks authority and initialization;
8-, 1024-, and million-element arrays retain bounded node count, storage, and
deterministic proof work. Empty initializer calls execute once. General snapshot
copies, copies after element overrides, and whole-array reassignment remain
migration work. The byte-slice checkpoint now carries shared/mutable parameters,
full-width length metadata, dynamic read/write bounds, reborrows and local calls
through ULLBC, including restoring guard cleanup. `byte-slice-metadata-v1` checks
compiler-resolved length calls and paired pointer/length origins; typed indices
restore panic obligations removed by Charon's selected transform. Missing bounds
and authority, high-bit indices, and false cleanup claims are rejected. Metadata
work remains bounded for empty, small, million-byte and maximum-width lengths;
proof tools recheck the same certificates. Array coercions, subslices, returned
slices, slice fields and iterators remain parity work. Next bring stored
`chunks_exact`/remainder state and checksum loop composition through the adapter.
Establish stable source/proof observations and equivalent coverage before
switching production imports. Preserve source metadata and a
Click-owned semantic boundary; do not rebuild rustc's HIR-to-MIR semantics just
to retain syntax. Use the assessment's configuration rather than adopting an
unaudited preset. Then consolidate semantic
operations and identities, compact arrays, stable proof observations, and the
model registry in reviewable increments. Extend checksum syntax on top of these
boundaries rather than adding more incompatible paths. These are requirements
for closing this issue, not evidence that the changes have already landed.

## Initial assessment

Produce a small, reviewable extraction experiment over scalar branching,
struct-field mutation, and a local reborrow followed by parent reuse. Identify
how the chosen representation connects writes through the child to the value
subsequently observed through its parent. Record which facts rustc establishes
and which transitions Click checks. This assessment selects the boundary;
it is not itself completion of Rust support.

In parallel, inspect and pin the proposed library sources. Record their
reachable functions, Rust constructs, C compiler configuration, and proof
obligations. Use that concrete inventory to plan coverage; do not assume an
algorithm's simplicity means its optimized implementations are already supported.

The [pinned checksum assessment](../design/rust-checksum-assessment.md) records
zlib 1.3.1 and adler2 2.0.1, selected build configurations, reachable constructs,
and the shared specification. Unsigned `u8`/`u32` scalar arithmetic now has a synthetic regression with
checked panic obligations, casts, bitwise operations, and proof expansion.
Byte slices now have variable-length read/write contracts, 64-bit `usize`
metadata and bounds checks, existing `views`/`owns` authority, direct calls,
and checked expansion. Memory-access contracts currently bound length by
`INT32_MAX`. Fixed-array references now support `u8`, `u32`, and `i32` elements,
compiler-evaluated lengths, checked indexing and element borrows, `.len()`,
local aliases/reborrows, and direct calls. Bounds are checked at the full
target `usize` width before address formation; zero-length and oversized
indices, false values, missing authority, and conflicting borrows have
regressions. Local scalar arrays now support literal and repeat construction,
independent whole-array copies and assignment through references, and local
array borrows. Constructor evaluation order, one evaluation for repeats
(including empty arrays), self-copy, and full source/destination authority
have regressions. Fixed byte arrays now coerce to shared/mutable byte slices
in local initialization, slice reassignment, and direct calls, preserving
length and storage authority. Empty arrays and parent reuse have regressions.
General `usize` scalar arithmetic now includes checked addition/subtraction/
multiplication, division/remainder, shifts, bitwise operations, compound
assignments, and integer casts at the full 64-bit target width. Computed slice
indices and length increments, full-width boundary values, panic rejection,
and proof expansion have regressions. Unlabeled HIR `while` loops now use
shared invariants, resource clauses, and decreasing measures, with scalar
accumulation, full-width byte-slice iteration, nested loops, panic rejection,
and checked expansion regressions. Guards currently exclude calls, indexing,
and arithmetic; general iterator/control-flow coverage and owned-value MIR loops
remain outstanding. The [byte-sum fixture](../examples/rust-byte-sum/README.md)
now proves an unchanged loop summing arbitrary bytes in slices of length
`0..=1000`, using an exact mathematical prefix fold, a full-width `usize`
counter, intermediate overflow bounds, and a decreasing measure. False sums,
incorrect invariants, missing bounds, and expanded proofs have regressions.
This is synthetic functional accumulation; the pinned checksum libraries
remain unverified.
The [slice iterator fixture](../examples/rust-iterators/README.md) proves the
same sum with unchanged `for &byte in bytes` source, using compiler-resolved
iterator calls, copied byte bindings, explicit cursor/remaining-slice state, and
shared loop rules. No processed count is generated; its prefix invariant is
authored in the sidecar.
The [reference iterator fixture](../examples/rust-iter-references/README.md)
proves the same sum with `for byte in bytes.iter()` and shared-reference
dereferences. Direct slices and `.iter()` support both copied and reference
bindings, with read authority and shared-reference write rejection regressions.
Only immutable shared byte-slice bindings are supported; mutable iteration,
stored byte iterators, and iterator control flow remain outstanding.
Shared byte-slice `chunks_exact` now supports stored and direct iterators,
consuming loops and loops borrowing the iterator mutably, shared subslice
bindings, and a fixed `remainder` before or after consumption. Explicit cursor,
remaining complete-byte length, chunk size, and tail state model the iterator;
no processed count is generated. The
[exact-chunk fixture](../examples/rust-chunks-exact/README.md) proves that the
chunks reach the tail without gaps and preserve every input byte for arbitrary
inputs of length `0..=1000`. Empty inputs, exact multiples, short tails,
full-width oversized chunks, one evaluation of the size, nested loops, shared
write rejection, zero-size panic rejection, and checked expansion have
regressions. Mutable chunks, iterator copies/adapters, and explicit `next`
remain outstanding; this fixture does not verify adler2.
Checked `u16` scalars, references, and compiler-layout record fields now support
primitive lossless unsigned `From` calls, including `u32::from(u8/u16)`. The
[conversion fixture](../examples/rust-integer-conversions/README.md) verifies a
fixed accumulator wrap-boundary case and generic reference/field updates with
read/write authority and preserved neighbors. Conversion operands evaluate
once in order; casts truncate to sixteen bits and arithmetic checks that width.
This is not an arbitrary checksum proof. Tuple structs, array iteration,
indexed compound assignments, and checksum-specific operator implementations
still block the unchanged adler2 loop.
Shared byte-slice `split_at` now supports two plain local tuple bindings,
full-width panic bounds, and an explicit signed-word pointer-offset limit.
Both slice lengths and reads through variable split points have regressions,
along with empty/endpoint splits, preserved full-width metadata, false claims,
missing read authority, and expanded-proof verification. Mutable splitting,
general tuple values, and range subscripts remain outstanding.
By-value array parameters/returns, non-byte slices, and crate extraction also
remain outstanding. Neither library is verified
by this assessment.

## Milestone 1: experimental safe Rust

Support monomorphic functions over modeled integers and booleans, plain
structs, local initialization, branches, direct calls, `&`/`&mut` parameters,
and local reborrowing. Returning scalar or plain supported values is sufficient
initially. Use one pinned toolchain and target with an explicit overflow and
panic policy. Compiler acceptance alone does not prove absence of panics or a
functional postcondition.

The defining small regression is an unchanged Rust function over a two-field
struct. A helper reborrows one field, writes 7 through the child, then reuses
its parent to increment the field to 8. A caller proves that final value and
preservation of the other field. A shared-field case allows a disjoint write
while preserving the borrowed field. A non-`Copy` value move and disjoint
mutable field borrows supply companion resource regressions.

Pair positive verification with a false final-value claim, conflicting access,
use after move, stale child access, forged recovery, and duplicate recovery.
Distinguish source rejected by rustc from a functional claim rejected by Click.
Compiler rejection alone is not evidence that checked resource transitions
reject forged authority. Production-level negative tests must exercise the
actual selected transition rules rather than only the independent design model.

Acceptance:

- Ordinary Click verification imports unchanged `.rs` source and verifies the
  defining contracts through sidecars and the shared engine.
- All applicable negative cases fail at the documented compiler or checker
  boundary; the false functional claim reaches and fails Click's checker.
- Source attribution and actionable unsupported-feature diagnostics work;
  verify, profile, audit, and expansion agree wherever those tools apply.
  Expanded proof text verifies through the ordinary entry point.
- The supported subset, semantic flags, panic policy, trust assumptions, and
  a reproducible working example are documented. It is accurate to advertise
  experimental safe-Rust support without implying general Rust coverage.

## Milestone 2: unchanged Adler-32 implementations, one specification

The leading candidate pair is [zlib's C Adler-32 implementation](https://github.com/madler/zlib/blob/develop/adler32.c)
and Rust's [adler2](https://github.com/oyvindln/adler2). Pin exact revisions and
one supported configuration before implementation. This is selected Adler-32
coverage, not verification of zlib's compression algorithms or every adler2 API.
If source assessment finds a materially better pair, document the evidence and
replacement scope before changing this acceptance target; do not substitute a
fresh synthetic implementation and call it existing-library verification.

The inspected adler2 2.0.1 implementation uses chunk iterators, fixed arrays,
and custom arithmetic operators. Add slices, indexing, loops/invariants,
compiler-resolved method/operator calls, and the reachable library contracts
needed by the selected path. Generic library machinery may be instantiated
for this path without claiming general trait or generic support. Any assumed
library contract must be named in the trust boundary; the checksum computation
itself must be verified rather than assumed.

Define Adler-32 once over a logical byte sequence. Relate each implementation's
buffer/slice contents and accumulator representation to that shared definition.
Use explicit compatible initial-state and API preconditions so equality is not
asserted between different reset, seed, or null-buffer behaviors.

Acceptance:

- Both pinned implementations verify unchanged against the shared mathematical
  checksum specification for arbitrary finite inputs satisfying the contracts;
  selected configuration and API boundaries are explicit.
- Prove that input bytes remain unchanged, accesses are in bounds, arithmetic
  follows the specified semantics, Rust panic checks are unreachable, and the
  selected computations terminate.
- Prove incremental processing agrees with processing concatenated input,
  including empty inputs and chunk/remainder boundaries. Verify the optimized
  loops in the selected paths, not just a fixed-length or scalar replacement.
- Derive C/Rust result equality from their independently verified shared
  specification. Runtime differential tests are supplementary evidence.
- A false checksum postcondition is rejected. The fixture records original
  source identity and runs reproducibly in the normal verification gate.
- Publish a scoped demonstration: Click proves these selected C and Rust
  checksum implementations compute the same result under the stated contracts.

## Boundaries and delivery

Unsafe Rust, interior-mutability protocols, returned references, general
traits/generics, closures, async, threading, and broad standard-library
verification are outside this issue except for explicitly assessed compiler-
resolved library instances needed by the checksum path. A borrowing-focused
example remains alongside the checksum so resource compatibility has its own
acceptance evidence.

Submit coherent green increments through the fork PR workflow. Frontend import
and source fixtures can develop independently; coordinate changes to shared
kernel resources and execution. Follow the tooling-first policy in `AGENTS.md`:
reduce verifier/expansion/diagnostic failures before building more examples,
and do not route around them by changing the original programs. Representation
changes on hot paths require deterministic scaling regressions across multiple
sizes, including growing unrelated context. Run useful focused checks per
increment and the required gates; report their actual results.

Delete this issue and its list entry when both milestones, regressions, and
public documentation land. Retain architectural findings in the durable design
records so issue closure does not erase the supported boundaries.
