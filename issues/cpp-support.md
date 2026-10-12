# P2: Extend C++ support toward Bitcoin Core

The long-term goal is to verify substantial parts of unchanged Bitcoin Core.
Grow support through independently useful, bounded proofs that exercise the
common execution and resource model. Each delivered slice must state exactly
which source, properties, compiler profile, and dependencies it covers.
Importing C++ syntax or proving one helper does not establish verification of
Bitcoin Core as a whole.

## Current remaining work

**Current priority: stabilize the bounded object model before widening C++
coverage.** The [consolidated object-model design](../design/cpp-object-model.md)
owns the shared storage, object lifetime, initialization, representation and
authority invariants. Its finite next steps are to audit evidence for currently
admitted operations, unify typed/byte observations for the declared uint32
profile, close demonstrated lifecycle/call-path inconsistencies, and validate
the acceptance matrix before resuming the unchanged decoder proof. This is
remaining work, not a claim that the consolidated model is implemented.

Two compatibility boundaries have been approved. C allocated storage needs
an explicit allocation/effective-access policy, distinct from C++ construction
and object lifetime; allocation, initialized bytes and ownership must not
silently create a C++ object witness. Also, address-only equality in a contract
does not guarantee that a loaded or returned pointer can be dereferenced. The
affected branch and abstract-callback proofs need an explicit typed-place
guarantee (or a separately designed full-pointer-value contract), preserving
their original C and retaining the insufficient contracts as rejection cases.
Implement explicit C allocation/access rules and typed-place guarantees for
the affected contracts. Do not restore the old numeric-alias fallback to make
the compatibility tests pass. Approval of these boundaries does not establish
that their implementation or the acceptance matrix is complete.

The current integration checkpoint is not green. The latest full library
checkpoint ran 5,694 tests: 5,665 passed and 29 failed, with no timeouts (139
nightly tests skipped). That run does not include all integration fixture suites
and is not a full gate verdict. It repaired the million-element Rust array
regression within the unchanged work/time limits: free- and bound-variable
collection now retain compact run dependencies separately. Focused checks also
pass the original retained constructor proof, final-release helper, hidden-record
expansion, mixed-snapshot call proof and adjacent-range C allocation proof.

Remaining reproduced integration failures include complete-width pointer naming,
resource close/contract certification, native Rust slice extent transport,
branch pointer transport, and loaded-pointer contracts that still rely only on
address equality. The confirmed C multidimensional-row defect also needs declared
row identity preserved before scalar decay. Temporary test-only diagnostics are
not part of the release implementation and must be removed. Validate original
source proofs after repairs, not just reduced unit tests, and complete the full
acceptance matrix before publishing or merging this checkpoint.

Before activation of checked pointer designation, the returned composed-observer regression was repaired: proof-entry input names
now use already checked explicit separation facts, without initializing raw
outputs. Ordinary, expanded and retained verification preserve the original
value and frame claims. The PR 646 constructor-input repair now restores the
unchanged constructor and scalar-unwind integration tests. Matching native
object-input requirements authenticate the destination and scalar referent;
indexed ownership composition supplies complete field separation even when
the receiver and input use different pointer blocks. These facts justify the
bounded padding exclusion while retaining the full unwritten output footprint.
All four original cleanup Markdown fixtures and `basic-cpp` passed that checkpoint.
They must pass again with designation enabled before this stabilization work is
complete; scalar-range input and pointer-valued output transport are currently
under integration. Preserve their source, contracts and value/frame claims.

The [constructor-padding implementation sequence](../design/cpp-object-model.md#constructor-padding-implementation-sequence)
requires declared storage layouts, preserved subobject boundaries and checked
input designation at calls. Field ownership alone cannot repair this failure;
adding a full-storage separation precondition would change the original contract.
Complete automatic aggregate declarations now retain their layouts independently
of values and initialization, including by-value copies and allocated return
objects. Explicit embedded-record boundaries now retain parent relationships,
full extents including padding, and alignment alongside flattened scalar fields.
Constructor binding now checks a declared complete layout or explicit child
boundary against the selected layout. Symbolic entry carries the same structural
requirement separately from raw storage, without fixing the containing allocation
size. C++ declarations and child boundaries now retain their nominal import identity.
Native scalar and record references, receivers, and the bounded constructor scalar
input profile retain separate validity requirements, checked both at symbolic entry
and actual calls. Native member selection preserves the enclosing root and explicit
path. Object-validity witnesses and complete-width ownership separation jointly
justify the constructor input read; neither fact alone supplies the repair.
Keep object-validity facts separate from permissions and initialization. Audit
which native interfaces supply those facts and check them at calls; explicit
raw-storage requirements are needed only where native guarantees are insufficient.
The [native-interface audit](../design/cpp-object-model.md#native-interface-audit-and-surface-syntax)
identifies where reference and typed-object evidence is lost during lowering.
No new keyword or written precondition has been added to the constructor contracts;
the call checker now enforces the native structural destination requirement.

The subsequent audit also reproduced a shared C/C++ soundness defect:
[one-past member pointers can read sibling fields](../bugs/pointer-arithmetic-crosses-scalar-subobject.md).
Checked pointer designation is now mandatory stabilization work, not merely an
optional metadata cleanup. The [implementation design](../design/cpp-object-model.md#checked-pointer-designation-representation-and-implementation)
now specifies separate address and semantic-value identities, domain-preserving
transport, checked lvalue access and matching modular-call obligations. The first
carrier-preservation prerequisite retains existing qualifiers through pointer
transformations. The shared carrier now also represents unresolved or explicit
object/array designations, with domain-aware value identity, full-value
substitution, binder traversal and resource matching. Raw address equality
cannot substitute a different designation. Native scalar declaration and record/member producers now authenticate these
terms, and exact complete pointer stores and reloads preserve them. Loaded-value
origins retain their defining snapshot and cell through paired substitution and
checked memory transport. Activation remains bounded: unknown legacy loads do not
acquire object evidence. Retained domains now reach executable arithmetic and access checks,
array/global declarations, scalar-array member decay and reference binding.
Verified bodies can certify input-preserving or declared-child pointer results
and exact final full-width pointer-member equations. Scalar/record prefix
requirements and their actual-call checks are implemented; integrated source
validation remains in progress. General pointer outputs and broader result
origins remain outside those bounded effects. Independent entry reconstruction
now admits exact declared opaque composite heads without importing caller cells
or unfolding child evidence; its new head/profile regressions still require
integrated validation. Numeric pointer equality does not certify full-value
transport, native validity, ownership or initialization. Uncertified checked
crossings remain unresolved.
The sibling-pointer defect remains open until the full ordinary/expanded/retained
cross-boundary matrix is checked. The design also
records the concrete
[byte-access source-profile choice](../design/cpp-object-model.md#byte-access-requires-an-explicit-source-profile-choice)
that must be settled before expanding the cast-and-index byte writer.

The bounded relation between modular byte-value postconditions and the caller's
automatic declared uint32 is delivered by the shared representation law, with
ordinary, expanded and retained verification of the unchanged exact-value
fixture. It preserves the typed-cell machinery and is not a decoder-specific
rule. Other representation profiles, the admission audit for object/subobject
access, and the selected C++ byte-traversal integration remain separate
acceptance obligations. Raise any actual profile choice before widening admission.

The original design cleanup and selected fee arithmetic proofs are delivered.
`GetFeePerK` is also verified on the unchanged pinned header: it delegates to
`EvaluateFeeDown(1000)`, requires positive size and the Down result-fit profile,
and does not use `GetFee`'s empty-rate or minimum-correction behavior.
Wide call-result conversions use the existing callee-typed capture and checked
cast certificates. Named captures make modular observer bounds available to
those certificates; no new kernel rule or automatic range inference is needed.
These were the selected implementation steps that required no new design.

The independent bounded span observers, reference writes, sibling frames and
backing-lifetime prerequisites are also delivered under the accepted profile
below. The selected unchanged `SpanPopBack<int>` target and read/write callers
are now verified through shared destination construction, trivial assignment
and full-expression retirement.

After that stabilization milestone, the following broader work needs a concrete
source/contract selection or a semantic profile decision before implementation:

- **Further fee methods and construction.** The remaining `CFeeRate` methods
  involve embedded construction/assignment, aggregate returns, comparison-category
  values, serialization, or strings. `FeeFrac` addition and subtraction, including
  self-aliasing, are already verified. Select an exact claim before extending
  constructors, free operator selection, or aggregate results.
- **Expression and lifetime profiles.** Converted call arguments, call-based
  brace initialization, arithmetic/composed expressions around calls, broader
  memory-reading siblings and nontrivial embedded destruction,
  and header destructor bodies need explicit sequencing, aliasing,
  lifetime, or admission choices. Broader cleanup/unwind remains owned by
  [control-flow.md](control-flow.md).
- **Remaining scalar and import coverage.** Original wide call conversions are
  admitted, but automatic observer normalization/range inference remains separate
  from explicit proofs. Select source requiring additional native wide arithmetic,
  wide mutable references/memory/aggregates/callbacks, byte reinterpretation,
  broader header constant forms, mixed-source executable macros, namespaced method selection,
  overload signature selectors, or same-named record layouts before widening a
  profile. The portable `DivFallback` path is a separate target, not a substitute
  for the pinned `__int128` implementation.
- **Bounded bytes and serialization.** Select an unchanged span/cursor or
  serialization helper and specify bounds, consumed/produced length, byte meaning,
  and malformed-input behavior. The proposed first target below isolates span
  bounds and returned-reference lifetime before byte encoding.
- **Owning containers.** Select one `prevector` operation with explicit content,
  ownership, allocation, copy/move, destruction, small-buffer transition, and
  invalidation claims.
- **Larger Bitcoin components.** Choose a bounded script, transaction, or
  validation component and specify safety and functional behavior separately.
  General inheritance, virtual dispatch, RTTI, arbitrary standard-library
  verification, full exception semantics, concurrency, and cross-target coverage
  remain deferred until a selected proof needs them.

## Verified target: SpanPopBack

Select the unchanged `SpanPopBack<int>` in Bitcoin v31.1
`src/span.h:75`, commit `9be056a8a72b624dae9623b2f7bded92c2a21c91`.
The header is already in the pinned input closure, with SHA-256
`485dc37ba8ed9b0e8d8212061122a5c1cd4e71e6ecc5380ac1a2277de395b0e3`.
This release uses `std::span`, not a Bitcoin-owned span class. The selected
instance is a mutable, dynamic-extent `std::span<int>` on the existing LP64
C++20 target. A fixture translation unit may instantiate the original header
template; it must identify that harness separately from Bitcoin source and
retain the pinned compiler profile. Offline ordinary, expanded and retained
proofs now cover the helper and modular read/write callers.

### Implemented prerequisites

Integral template values now retain the canonical builtin type and exact
signed decimal value in their contract-facing names, alongside Clang's
canonical declaration identity. For example, dynamic extent is
`__value_unsigned_long_18446744073709551615`; negative values use `neg_`.
Equal-width `unsigned long` and `unsigned long long` remain distinct, while
aliases canonicalize. Existing Boolean names are unchanged. Narrow integral,
enum and pack arguments remain outside this slice.

Unsigned 32/64-bit descriptor fields use the existing shared typed cells and
explicit C layout validation. Explicitly defaulted trivial destructors need
no executable cleanup; nontrivial destructor checks still apply. The pinned
`std::span<int>::size()` and nested extent-storage method now have offline
ordinary, expanded and retained proof coverage through a separately identified
harness with unchanged archived headers and compile flags. Their contracts
require only the extent field's authority and retain its native uint64 type.
Ordinary mutable `int*` returns now use shared typed C call results, including
modular direct return calls. Pinned unchanged `std::span<int>::data()` has offline
ordinary, expanded and retained proof coverage. Reading the descriptor pointer
requires its field authority but no backing element authority, and returning it
preserves identity without granting new storage authority. Other pointer types,
C++ reference returns and aggregate results remain outside this increment.

The full-width scalar regression does not claim that a backing allocation of
that size can be constructed. The complete helper uses the bounded profile below.

The user accepted an int32-bounded first backing-range proof, preserving native
`size_t` storage and arithmetic. Implementation exposed a further bound:
shared segment resources use a 32-bit byte extent, so a single four-byte
`int` range requires `N <= UINT32_MAX / 4`, or **1,073,741,823 elements**.
The proposed `INT32_MAX` bound alone is not the full usable range profile.
The user accepted that explicit narrower limit for the first proof; wider
shared byte extents are deferred. Do not silently narrow the
source length or assume the unsigned index equals a truncated range endpoint.

Native pointer addition now admits signed/unsigned 32/64-bit offsets through
existing common execution rules, retaining the original index type and pointer
identity. Pointer subtraction currently admits only signed int32 offsets;
wide subtraction and pointer differences remain bounded import refusals.
Offline ordinary, expanded and retained checks cover concrete forward/backward
positions, singleton and three-element last loads, frame preservation and
missing authority. Empty, one-past dereferences and full-width invalid offsets
fail under trivial postconditions. These are explicitly synthetic arithmetic
prerequisites, not a source proof of `SpanPopBack` or its symbolic length.
The complete helper now supplies checked native-index/range-endpoint evidence.

Read-only wide-index refusals now distinguish compact recorded cell ranges from
individual source stores in the shared resource tracker. C0 and offline C++
regressions reject invented source-store attribution and speculative unequal-index
repairs. They request the unresolved address relation or preservation instead;
relevant explicit equality rewrites still give ordinary, expanded and retained
proofs. Actual individual-store alias/frame diagnostics remain covered.

### Verified contract

This is a semantic summary; executable native sidecars are in
[bitcoin_core_money_range.rs](../tests/bitcoin_core_money_range.rs). Let the incoming
descriptor denote pointer `p` and mathematical length `N`:

```text
requires:
  authority to update the span descriptor
  1 <= N <= 1073741823                        // accepted single-range byte-extent limit
  p[0..N] is live, initialized and readable
  descriptor storage is separate from that backing range

ensures:
  span.data == old(p)
  span.size == N - 1
  result refers to old(p)[N - 1] in the same live allocation
  every original backing element is unchanged
  caller authority over the original backing range is preserved
  no backing storage is allocated, freed, or transferred
```

The stored size remains native `size_t`; the bound does not retag it as int32.
The returned reference denotes an element outside the shortened span but
inside the original backing allocation. Destroying or copying the descriptor
does not end that reference's storage lifetime; freeing or invalidating the
backing allocation does. The helper grants no new pointee ownership or write
permission. A caller that already owns the last element can write through the
returned reference using that existing authority. Empty spans are excluded by
the contract; do not promise a recoverable error or rely on debug assertions.

### Decisions exposed by the actual source

1. **Library boundary and concrete profile.** Recommend verifying the selected
   pinned `std::span` operations (`size`, `back`, runtime `first`, construction
   and trivial assignment) rather than introducing assumed span intrinsics.
   The pinned libstdc++ header is
   `sysroot/usr/include/c++/12/span`, SHA-256
   `f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd`.
   Its descriptor contains `_M_ptr` and nested `_M_extent._M_extent_value`.
   Source layout and provenance must come from Clang, not these spellings or
   hard-coded offsets. Integral template identity and unsigned descriptor
   storage prerequisites are implemented above; the remaining operations
   still need frontend admission and source proofs.
2. **Descriptor values and reference returns (accepted).**
   The user accepted this profile: preserve native reference result signatures in sidecars
   (`int32&`), matching native reference parameters. The result is a non-owning
   alias represented by the shared pointer/allocation-lifetime model. Reading or
   writing through it still needs caller-held backing authority; no exclusive
   borrow or ownership transfer is introduced. Its lifetime follows the backing
   allocation, not the span descriptor.

   Treat this trivial span's by-value result and defaulted copy/assignment as
   ordinary shared C aggregate field copies with checked Clang layouts and
   temporary lifetimes. Copy the descriptor pointer and native uint64 extent,
   never pointee contents or authority. Verify the selected constructors and
   methods from their pinned source. General nontrivial class value semantics
   remain outside this profile.

   Native mutable and const int32 reference results now preserve alias identity
   for existing reference parameters and direct call forwarding. Sidecars use
   `int32&` / `const int32&`: `result` reads the referent and `&result` is its
   address. Alias-only proofs need no backing ownership; value claims need
   existing authority. Ordinary, expanded and retained proofs run offline, with
   negative checks for false alias/value claims, missing authority, signature
   and const mismatches, and rehashed artifact mutations.

   New integer reference results can bind through pointer dereferences using
   shared checked object addresses. Formation requires live storage for the
   complete referent and excludes null, expired and one-past addresses without
   reading or initializing it. This reuses the shared bounds/lifetime predicate;
   reading still requires separate authority and defined contents. Automatic
   mutable/const int32 reference locals now preserve direct aliases and matching
   modular reference call results. Writes target the referent under existing
   authority; ending the local alias does not destroy its backing allocation.
   Trivial copy assignment between already-live records now reuses shared C
   aggregate field copies and the same checked layout used by proof metadata.
   The pinned `std::span<int>` assignment copies its pointer and nested native
   uint64 extent offline, without backing authority. Const sources, projected
   record assignment and self-assignment are covered; missing read/write
   authority, user-defined copy bodies, move assignment, const destination and
   hostile artifact paths are refused. Ordinary, expanded and retained proofs
   agree. Bounded returned construction and initialization are implemented as
   described below. The unchanged pinned `back()` now
   verifies for both a one-element backing range and the accepted symbolic
   domain `1 <= N <= 1,073,741,823`, through its actual constexpr assertion and
   nested observer calls. Explicit shared Integer/conversion certificates prove
   native nonempty subtraction and the backing-count/index bridge. The kernel
   projects unsigned native indices through full-width bounds and checked scalar
   result equalities; bounds on low words alone remain insufficient. Ordinary,
   expanded and retained offline proofs establish native alias identity and old
   referent value. Missing bounds, descriptor/backing views, empty size, false
   aliases/values and invalid byte extents are refused. Deterministic scaling
   checks cover unrelated facts. The full `SpanPopBack` proof combines these
   reference contracts with returned construction and temporary retirement.
   **Expression observers (accepted).** Admit nested calls in unsequenced
   operands only when verified read-only observer contracts establish operand
   independence. General interfering calls remain deferred. For example,
   `back()` reads `_M_ptr` and
   calls `size()` in the same addition. Do not choose an order silently or
   introduce a span-specific intrinsic. Read-only contracts use shared `views`
   authority: a final unchanged-value claim alone is insufficient because a
   callee could write and restore the value. The pinned `size()`/extent and
   `data()` chains now verify using views alone. Literal-false `do` wrappers
   lower to one execution of their checked body, with runtime/repeated loops,
   break/continue and unsupported local lifetimes refused. Nonthrowing scalar
   expression calls now use the shared normalizer in return values and ordinary
   conditions. Their contracts must contain views only, including nested
   argument calls. Arithmetic, comparisons, pointer offsets, reference-address
   formation and lazy `&&` preserve evaluation semantics. Offline ordinary,
   expanded and retained regressions cover symbolic reads, widening and skipped
   read permissions, with mutation/ownership and forged metadata negatives.
   Shared storage checks now transport live-range evidence across verified
   pointer equalities, without granting read or initialization authority;
   missing, expired and one-past storage still fails.
   Integral logical negation, runtime `__builtin_is_constant_evaluated()` and
   checked-unreachable statements now admit the constexpr assertion condition.
   Clang's manifestly constant branch selection remains distinct from runtime
   execution. Declared macros keep locked definitions and executable expansion
   locations; undeclared macro dependencies are refused. Reference typedefs
   retain resolved widths/qualification, and generated reference-result proofs
   use the native address/referent spellings. Trivial record returns from live
   lvalues now use shared aggregate values and checked nominal layouts, including
   nested descriptor fields. The source must use Clang's resolved trivial copy
   constructor; whole automatic objects eligible for named copy elision, moves,
   user-defined copies and nontrivial destruction remain refused in that copy
   slice; bounded prvalue construction is supported by the separate profile below.
   Every copied leaf needs initialized read authority;
   copying a pointer field grants no pointee authority. Offline ordinary, expanded,
   retained and forged-metadata checks cover this slice (artifact schema 46).
   Bounded construction and initialization are implemented below;
   interfering expressions remain
   refused until their execution orders can be represented and checked.
3. **Initial bounds profile (accepted).**
   The user chose the explicit single-range limit above for the first proof. Keep
   native unsigned arithmetic and prove the cross-width range/index bridge,
   nonempty subtraction and pointer formation from the actual backing range.
4. **Shared construction destinations (implemented).**
   The accepted interface, source admission and cross-language compatibility
   contract lives in [aggregate construction](../design/aggregate-construction.md).
   Artifact schema 52 distinguishes construction returns, forwarding, new-object
   initialization and assignment through a distinct RHS temporary. The importer
   validates argument-value-only constructor/helper bodies and permitted trivial
   copies by field-value equivalence. Address-sensitive returned constructors,
   NRVO, moves, user-defined copies and nontrivial cleanup remain refused.
   Native signatures and `result` field contracts need no user-managed return
   slots or new Surface construction clause. Runtime `first` and the complete
   unchanged `SpanPopBack` path now verify with expression retirement.

### Work independent of returned construction

The accepted bounded span/reference profile now verifies unchanged pinned
`std::span<int>::front()` with `1 <= N <= 1,073,741,823`: its native reference
aliases the first backing element and preserves its old value using descriptor
and backing views. Ordinary, expanded and retained verification pass; empty
callers, missing bounds/views and false alias/value claims are refused.

Pinned `size_bytes()` is also verified with descriptor views alone, without
backing storage authority: its result is the native modulo-2^64 product of the
extent and four-byte element size. Empty, bounded and wrapping extents retain
that meaning. Expanded/retained verification and missing-authority/false-product
refusals are covered.

Unchanged pinned `operator[]` now has a bounded native-index reference proof:
`index < N` and the same nonempty extent bound identify the corresponding backing
element and its old value. Direct `Class::operator[]` selection maps to
`Class_operator_index`. A shared strict uint64-to-Integer comparison bridge and
checked normalization from explicit full-width index bounds supply the address
projection; a low-word bound alone remains insufficient. Ordinary, expanded and
retained verification cover the method and modular caller, with missing bounds,
authority and false reference claims refused.

Write-through callers of `front()`, `back()` and `operator[]` now verify with
ownership of the backing segment and views of the descriptor. They preserve
descriptor fields, set the selected element to the input value, and prove a
quantified frame for every other backing element. The back caller states the
native/signed last-index address bridge explicitly. Shared address alignment
supports a captured interior pointer without treating unrelated pointer-read
tokens as offsets or granting new authority. Ordinary, expanded and retained
checks reject views-only writes and false unchanged-element claims. The indexed
caller also rejects a false frame that includes the element it writes.

The independent lifetime prerequisite is covered by synthetic descriptors with
an explicit constructor and a nontrivial destructor that clears the pointer
field. A native reference into external backing remains readable and writable
after descriptor destruction under caller-held backing authority. A reference
into a destroyed local object's own field cannot be read; returning its address
alone grants no live storage or read authority. These fixtures do not claim
that pinned `std::span` automatic construction is supported.

Native reference binding now reuses the existing checked int32 field-address
path, retaining const qualification and requiring caller-held authority for
loads and writes. Literal `nullptr` and zero conversions to mutable `int*` reuse
the shared C null pointer value, without grants of storage authority. Nonliteral
`nullptr_t` conversions, other pointee types and nonzero integer casts remain
outside this profile. Artifact schema 52 requires refreshing earlier locks.

The unchanged pinned runtime `first(K)` now verifies through checked returned
construction for `0 <= K <= N <= 1073741823`, preserving the data pointer and
receiver fields. Ordinary, expanded and retained proofs pass; a zero-count caller
needs no backing authority. The complete `SpanPopBack` helper preserves the
original backing frame for symbolic bounded lengths. Modular read/write callers,
singleton-to-empty and three-element cases pass; missing permissions, bounds and
separation, empty input, out-of-range `first` and views-only writes are refused.
The owned write caller preserves every other original backing element.
Ordinary, expanded and retained checks agree.

The unchanged pinned runtime `last(K)` now constructs a suffix descriptor for
`0 <= K <= N <= 1073741823`, with native pointer `p + (N - K)` and extent `K`.
The caller retains descriptor views and its complete backing view, with a
quantified unchanged-element frame. Empty, full and empty-input suffixes,
ordinary verification, method/caller expansion and retained checking are covered;
missing bounds/views and false pointer/extent claims are refused. Returned
constructor arguments reuse read-only observer normalization for value-only
arguments. Shared wide-range coverage checks the non-wrapping suffix displacement
and full-width observer equality, without granting new backing authority.
The unchanged runtime `subspan(offset, count)` now verifies finite windows under
`offset <= N`, `count <= N - offset` and the same extent bound. The explicit
`dynamic_extent` count also verifies the original assignment branch and returns
length `N - offset`. Empty, end, full and empty-input windows, method/caller
expansion, retained checking, missing permissions/bounds and false result claims
are covered. Header uint64 literal conversions and scalar assignment observers
use the existing checked declaration and read-only normalization paths. Shared
range coverage recognizes both `(N - K)[0..K]` and `offset[0..N - offset]` with
full-width identities and underflow/byte-extent bounds. An explicit checked
`size()` result capture supplies the sentinel branch's arithmetic bounds.
Omitted default arguments, compile-time `subspan` and other scalar/import work still need
an exact source and contract selection under the profile boundaries above.

Existing typed pointers, array/range authority, stable views, allocation
identity, and field layouts provide the foundation. Pointer fields to int32
and embedded record layouts already have C++ support, as do unsigned size
fields and the pointer-offset forms above. Selected-file and locked-header embedded member
construction now uses checked child-constructor calls in declaration order,
with unwritten destination footprints, native contracts and sibling/backing
frames. Scalar member initializers can invoke checked nonthrowing read-only
observers. Trivial destruction permits these local objects in the normal-only
exception-enabled profile. The bounded value-only returned-construction profile now supports factory
returns, forwarding, initialization of new objects and materialized trivial-copy
assignment with full-expression retirement. Broader prvalue and copy forms
remain refused; they do not justify a separate C++ memory model. The unchanged pinned libstdc++ pointer/count constructor is now
verified offline through ordinary contracts for both `to_address` helpers,
`__extent_storage`, and `span`. Successful concrete compile-time assertions
produce no runtime operation. The caller retains its backing-range view under
the accepted native uint64 count bound; ordinary, expanded and retained checks
pass, and omitting the backing view is rejected. Returned construction and the
complete `SpanPopBack` target have separate end-to-end coverage above.

The delivered helper and caller coverage retains the original headers, archive
hashes, LP64 C++20 / Clang 19.1.7 profile and uint64 extent. Backing authority
survives the assignment temporary's retirement. Separate descriptor-destruction
fixtures cover references into independently live backing and refusal of expired
local referents. Direct conversion of a whole reference-return call to a scalar
return remains outside the importer profile; read/write harnesses bind the
returned native reference before using it.

No endian or typed-from-bytes rule is needed here. `ser_readdata32` is a later
candidate: it reads into a local integer through `std::as_writable_bytes` and
needs a concrete stream plus byte-type and pointer-reinterpretation admission.
The shared [byte design](../docs/internals/byte-representation.md) now retains
declared automatic scalar types and completes a uint32 representation when
four checked character writes initialize its bytes on the selected little-endian
target. Partial local and helper writes remain uninitialized, and helper byte
writes refresh the caller's scalar binding rather than retaining its old value.
The rule is shared execution semantics, not a trusted decoder intrinsic; untyped
storage, other scalar kinds and specification byte views remain outside the
profile. Automatic mutable signed/unsigned 32/64/128-bit C++ integers may now
omit their initializer. Their declarations lower to ordinary uninitialized
storage, and reads require initialization; record construction and reference
binding remain mandatory. Normal, expanded and retained checks cover later
assignment, and offline validation rejects forged uninitialized record or
reference declarations. This changes the artifact schema to 53; refresh older
locks. Native `unsigned char` scalar values and fields now use `uint8`
contracts, retaining promotions, modulo casts and one-byte field layout. Other
character types remain outside the importer profile. The C++ importer now admits mutable native `int32*`, `uint32*` and
`unsigned char*` pointers, retaining their element types and strides in loads,
stores, calls and field layouts. Taking the address of an automatic native
scalar does not initialize or read it; a checked typed store initializes it.
Pointer loads and call boundaries reject substituted pointee types. Writable
byte-span construction and pointer reinterpretation remain prerequisites for
the unchanged decoder. Scoped fixed unsigned-char-backed enum values
now use native `uint8` contracts while retaining checked nominal identities and locked declaration
spans in the importer. Explicit numeric conversions preserve the underlying
bits, including all 256 values of empty enums. The actual pinned `std::byte`
declaration has offline normal, expanded and retained forwarding coverage.
Artifact schema 54 requires refreshing older locks. Mutable pointers to the actual pinned `std::byte` declaration now lower to
native `uint8*` contracts with retained enum identities, one-byte strides and
ordinary ownership. Offline normal, expanded and retained regressions cover
stores, automatic enum addresses and modular helper calls. The importer checks
the declaration span and locked libstdc++ header hash; rehashed artifacts cannot
substitute another enum or declaration source. Other enum pointers remain
refused. Artifact schema 55 requires refreshing older locks. Explicit one-way `reinterpret_cast` from mutable supported native object
pointers to the authenticated `std::byte*` now preserves allocation identity
and uses the shared byte-access rules. Initialized native pointer locals and
same-type assignment use ordinary scalar allocation. Four concrete byte writes
complete an unwritten declared uint32 representation; partial writes and writes
without ownership remain refused. Call-result casts retain their explicit typed
conversion chain. Artifact schema 56 requires refreshing older locks.

Checked native contract byte-view casts now express cross-pointee identity as
`result == (uint8*)p`, preserving allocation identity, byte offset, and source
qualification. Access authority and initialization remain separate. The pinned
`std::byte*` call-result regression verifies this relation normally and with
expanded and retained certificates. Incompatible pointer comparisons receive
a direct type diagnostic instead of an empty-path kernel error.
Trivial by-value record parameters now use the same independent aggregate
copies as C. A checked `record_copy` call argument preserves nominal identity
and source projection; copying a descriptor preserves its backing pointer
without creating backing authority. Moves, prvalue arguments, and nontrivial
copying or destruction remain outside this bounded slice. Artifact schema 57
requires refreshing older locks. Current-memory typed loads through an entry
pointer can state backing effects independently of the callee's private copy.

Shared scalar initialization now allocates the object, checks its initial
value, and freezes read-only storage while preserving address and lifetime.
C read-only automatic scalars and C++ `const`/`constexpr` native integer locals
use that transition. Helper results initialize a distinct read-only source
object after the checked call; ordinary assignment cannot repeat initialization.
Artifact schema 58 requires refreshing older locks. Native qualification,
address observations, stale-address rejection, and expanded/retained proof
checks remain explicit. Const aggregate/array locals and general constant
evaluation remain outside this bounded slice.

Authenticated standard-byte class-template arguments are now retained with
their positions and enum declaration metadata, including in records whose
fields do not mention the argument. Offline validation checks the encoded
identity and the actual locked standard header. Other enum arguments remain
refused. Artifact schema 59 requires refreshing earlier locks.

Current standard-library policy exports system-header interfaces as axioms,
without their bodies. The selected dynamic-extent
`std::as_writable_bytes(std::span<int>)` therefore uses an explicit catalog
contract, rather than a proof of libstdc++'s implementation or its `constexpr
extent` initializer. The unchanged const-reference and by-value harness callers
return a standard-byte descriptor with the same backing address and native
uint64 length `4 * N`.
Descriptor copies transfer no backing authority, initialize no backing bytes,
and preserve the original allocation lifetime. Offline ordinary, expanded and
retained checks cover that boundary. Shared read-only scalar construction
remains available for actual non-system-header source. The by-value proof retains
checked separation between the complete private parameter object and the result's
pointer field across parameter cleanup. Actual aggregate argument copies check
source read permission and
initialization before private callee storage is allocated.

Ordinary modular byte-output initialization is now supported below. Span
construction alone still establishes neither backing initialization nor byte values.
Byte alias access must be restricted to the actual pinned `std::byte` declaration;
an arbitrary enum with the same underlying type does not gain that privilege.
Automatic scalar declarations now create explicit ownership of their exact
byte extent in the shared kernel, independent of initialization. Direct reads
and writes require that permission; modular helper calls can borrow and return
it without caller-side ownership annotations. Scope exit and re-declaration
retire the allocation owner. Caller scalar bindings are refreshed from memory
after modular effects, rather than retaining stale pre-call values. The same
allocation transition serves C, C++ and Rust.

An ordinary helper can now state `ensures initialized(p[0..N]);` separately
from `owns p[0..N]` and byte-value postconditions. The bounded profile freezes a
mutable native byte-pointer parameter's input address and uses a constant byte
count with zero start. Its proof-entry footprint stays unwritten while resources
are named; incomplete writes, holes, no-op bodies and reads before writes are
refused. Checked calls record initialization of exactly the guaranteed range,
without allocating storage or assigning its byte values. Exceptional, conditional,
callback and external initialization guarantees remain refused. Indexed runs
combine adjacent symbolic writes and retain only common initialized bytes at a
join; reset touches only overlapping runs. C and pinned `std::byte` caller checks
cover ordinary, expanded and retained verification. Resource semantics version
65 invalidates older retained proof artifacts.

The bounded shared value prerequisite is now implemented for automatic declared
four-byte uint32 scalars with a pinned little-endian target profile. Execution
and logical byte reads use the same selected-snapshot projections. Four exact
initialized byte-value premises reconstruct the word through one checked packing
rule; casts, allocation size and arbitrary observations cannot issue its type or
target evidence. The unchanged exact word-value claim in
`mdtests/modular_byte_output_word_value_requires_representation.md` is positive.
Ordinary, expanded and retained verification and missing/mutated premise and
result checks pass, alongside width/profile/initialization/snapshot boundaries
and unrelated-fact/cell scaling. The explicit application uses existing proof
syntax and retains all four snapshot-relative byte premises. See the
[object-model design](../design/cpp-object-model.md#one-representation-consistent-observations).
This completes the shared C bridge prerequisite; remaining C++ traversal,
object-model integration and the selected decoder's full value contract still
require their own checked evidence.

`ReadCompactSize` additionally brings stream failure and canonical
encoding rules; do not bundle those decisions into this span slice.

## Delivery history

The notes below record successive supported profiles. Earlier refusal and
"next" statements describe their point in that history and can be superseded
by later deliveries; the remaining-work list above is the current roadmap.

## Delivered baseline and current gap

The [basic C++ example](../examples/basic-cpp/README.md) verifies reference
aliasing, selected local objects, constructors/destructors, normal cleanup,
and a direct modular caller. The [control-flow issue](control-flow.md) records
the delivered bounded scalar-exception and conditional-lifetime cases, and
owns broader cleanup/unwind work.

The [Bitcoin Core integration](../integrations/bitcoin-core-money-range/README.md)
already verifies the unchanged `MoneyRange` from v31.1, commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`, through its real Clang compilation
command. Its hermetic input closure includes `src/util/feefrac.h`,
`src/policy/feerate.cpp`, and `src/span.h`; these provide concrete next targets
without guessing what this Bitcoin release contains.

The first value-method milestone is delivered in this change: ordinary
methods, const record references, mixed signed 64/32-bit fields, same-width
field addition, and signed integer equality. The upstream
[`FeeFracIsEmpty.click`](../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click)
proves exactly `size == 0` while preserving both fields.
[`FeeFracAdd.click`](../integrations/bitcoin-core-money-range/FeeFracAdd.click)
and [`FeeFracAddSelf.click`](../integrations/bitcoin-core-money-range/FeeFracAddSelf.click)
prove exact sums for distinct and self-aliasing objects under sufficient
half-range overflow bounds. The synthetic `value-methods` compiler-import
fixture also proves modular source callers and frames unrelated caller memory.
It checks expansion and retained audit sessions, false claims, missing field
authority, and missing overflow bounds. Artifact tests reject receiver
qualification mismatches, const writes, const-to-mutable calls, and mixed-width
addition. The existing Bitcoin archive and project flags remain unchanged.

The arithmetic prerequisite also delivers signed scalar parameters/returns,
64-bit locals and modular captures, checked signed `+`, `-`, `*`, `/`, `%`,
negation and comparisons, explicit promotions, C++20 signed narrowing, and
integer-to-Boolean conversion. Unchanged upstream `operator-=` is verified
for distinct objects under half-range bounds and for self-aliasing across the
entire signed range. A modular source caller frames unrelated memory.

The `signed-arithmetic` fixture preserves Bitcoin's quotient/remainder
correction expression with a signed 64-bit dividend and checks fourteen
concrete rounding/boundary cases, both directions and signs, exact division,
and signed extrema. It proves general quotient/remainder contracts and checks
expansion, retained audit, hostile claims, zero divisors, and signed overflow.
The shared kernel now discharges positive-divisor guards and bounded signed
64-bit multiplication, folds signed wide arithmetic through indexed equalities,
and handles self-subtraction. Regressions cover lazy evaluation of undefined
constant division and fixed query work across unrelated fact populations.
These arithmetic prerequisites do not prove the general rounding theorem or
the upstream `__int128` path. The next milestone below remains open.

Unsigned scalar support now delivers by-value 32/64-bit parameters, returns,
locals and modular captures, wrapping arithmetic, comparisons, division/remainder
and the supported mixed conversions. C++20 uint64-to-int64 conversion now
preserves all source bits through a distinct kernel cast mode, with sign-bit
and extrema regressions, arbitrary-input round trips, modular caller framing,
and following signed overflow checks. Ordinary C conversion behavior is retained.
Unsigned references and record fields are outside this slice. The unsigned
fast-path fixture preserves both fee expressions but returns the intermediate,
so it is not a proof of upstream `EvaluateFee`.

The unchanged `GetSizeOfCompactSize` in the pinned `serialize.h` is proved for
all uint64 inputs in four disjoint ranges (encoded lengths 1, 3, 5, 9). Its
`sizeof` and static constexpr `numeric_limits::max()` calls are pinned-Clang
compiler constants with retained source spans and locked input closure.
Ordinary verification, expansion/reverification, retained audit and hostile
length claims agree. Full-width unsigned constant bounds use the queried
endpoint's index, with fixed-work regressions over unrelated fact populations.
This establishes encoded length, not byte serialization or parsing.

Concrete function templates are now imported through ordinary selected callers.
Boolean value arguments and the supported unqualified builtin scalar type
arguments have distinct Clang identities and sidecar names, including equal-width
`long`/`long long` distinctions. Pinned Clang selects `if constexpr` in constant
evaluation context; the artifact retains the selected arm, constant condition,
and source spans. Selected unsupported behavior fails explicitly. Regressions
cover modular callers, receiver ownership, framing, false contracts, type
identity, Boolean substitution, absent else arms, and rejection of unsupported
arguments and dependent selection. Both instantiated unsigned fee fast-path
expressions verify concrete rounding cases, expansion and retained audit. These
are synthetic prerequisites; no additional upstream fee proof is claimed.

Direct return calls now support matching signed/unsigned 32/64-bit and Boolean
results, including implicit `this` calls to concrete method template instances.
The synthetic `FeeFrac` fast-path wrappers preserve Bitcoin's direct
`return EvaluateFee<...>(at_size)` form. Regressions prove modular scalar
forwarding, branches, caller framing, typed capture before normal destruction,
and object-free exception propagation, with selected-caller expansion and audit.
Call graph and cleanup validation remain explicit. Uncaught return-call cleanup
edges have structural coverage; guarded `try` returns and resource-bearing
exceptional contracts remain outside this slice.

Nested scalar calls now support one call argument in a direct free-function
return call, including deeper chains and multiple stable scalar siblings.
By-value scalar parameters/locals, literals, locked constants, and supported
integer/Boolean casts are stable and total, so all argument orders agree even
when the inner call writes memory or throws. Aliasing memory-reading siblings, arithmetic,
multiple nested calls, and sibling side effects remain explicit errors. Typed
captures preserve normal cleanup and inner exceptions skip outer calls.
Regressions cover widths/signedness, Boolean results, each argument position,
casts, source-name collisions, mixed-width branches, hostile claims, and
selected-caller expansion and audit. Name allocation and argument lowering have
deterministic scaling regressions. The synthetic 64-bit fee fixture preserves
`Div(Mul(...), divisor, round_down)` and proves concrete positive/negative rounding
and exact division, including concrete Boolean template wrappers; zero divisors
and unproved product bounds are rejected.
The scalar-isolated field-reading sibling extension is described below; Bitcoin's
wide helper path remains unsupported.

Static scalar helpers now retain class and declaration identity without an
implicit receiver or importing unrelated object layouts. Ordinary
`Class::helper` selection, class-qualified/unqualified calls, and reachable
concrete template instances support the existing scalar call positions,
including stable nested arguments. The synthetic static `Mul`/`Div` rounding
fixture verifies both signs through Boolean template wrappers, expansion and
audit. Scalar-type, distinct-class, initializer, exception, false-claim, and
artifact regressions are covered. Object-qualified calls and pointer/reference
signatures remain rejected. Bitcoin's wide path, `Assume`, and field-reading
siblings still require further support.

Scalar call evaluation now uses one normalization path: explicit evaluation
statements followed by a typed value. Return and integer-local initializer
wrappers retain their source role, but nested calls and their ordering checks
are shared with discarded calls. Supported nested initializers no longer need
source rewriting into return calls. Returns still capture before destruction;
exceptional evaluations use the existing active cleanup edges. Ambiguous sibling
reads/effects remain rejected in every context.

C++ now prepares execution, contract-facing signatures, explicit layouts, and
local-object metadata within its frontend. C++ and Rust supply the same
prepared execution package to the shared verifier. The verifier no longer
traverses C++ bodies or translates C++ types. Original typed artifacts,
load source identities, and locked compiler/source identities remain attached
to the prepared input. The plain C parser already supplies the same signature
and layout vocabulary; its lazy translation-unit path remains intact.

Lifetime cleanup is now derived from typed declaration/record identities and
one scoped construction stack, independently of the artifact's exit lists.
Validation and lowering use the same lifetime events: successful construction,
lexical exit, return, and unwinding to a catch boundary. Returns before any
construction and between two constructions have unchanged-source regressions;
normal return capture, reverse destruction, conditional/sibling scopes, and
scalar exception fixtures retain their behavior. No per-branch live-environment
clone or scan of a final return's cleanup list is needed. Deterministic tests
cover growing event and cleanup-edge counts. Existing semantic-profile limits
remain for the validity/profile/budget cleanup below. Partial construction,
temporaries, copy/move, broader scope arrangements, and wider exceptions are
future lifetime events/admissions, rather than additional lowering paths.

Checked compiler-assumption obligations are delivered. A direct
`__builtin_assume` statement is identified by Clang's builtin declaration and
lowered to a labeled assertion in the common kernel. Its condition must be
proved at the site, never silently trusted. Because the builtin does not
evaluate its operand, supported conditions are total scalar predicates over
by-value parameters/locals and locked constants, with supported casts,
comparisons, and conjunction. Memory reads, runtime calls, arithmetic, and
side effects remain rejected. Offline regressions cover missing/false
conditions, conditional execution, constant reachability, normal destruction,
expansion/reverification, retained audit, forged artifacts, and growing statement
inventories. Ordinary user-named `Assume` calls remain ordinary calls. This is
the obligation mechanism prerequisite; Bitcoin's library `Assume` macro still
needs separate support. Artifact schema is now 42 and earlier locks require
an explicit refresh. The unchanged Bitcoin division helper remains unsupported.

## Required invariant

Every accepted selected C++ operation must have faithful, checked execution
semantics: receiver identity, field ownership, aliasing, integer definedness,
lifetime, and all accepted outcomes must survive import and lowering.
Unsupported reachable behavior must fail explicitly. Like
[rust-support.md](rust-support.md), use one proof language and one bounded
verification engine. Keep the compiler/translator trust boundary explicit and
share existing kernel operations where their semantics agree; a separate
C++ verifier or a wholesale renaming of C-prefixed kernel types is not a
prerequisite. Unselected declarations
in a project header must not force verification of an entire class or standard
library, but their layouts and other semantically relevant information must
still be validated. Preserve unchanged upstream source as the integration
regression for every new slice.

## Delivered design consolidation

This section records the earlier importer/scalar cleanup. The subsequent
[object-model consolidation](../design/cpp-object-model.md) and its stabilization
criteria are the current foundation work; delivery of this earlier cleanup does
not establish completion of that work.

The planned cleanup steps are delivered. Continue with the fee arithmetic
milestone above, preserving unchanged-source proofs, hostile-artifact and false
claim rejection, verification/expansion/audit agreement, and deterministic work
bounds. Wider arithmetic must extend the shared scalar model and common kernel,
including execution types, contract types, and definedness obligations.

Scalar interpretation now uses one descriptor for the pinned target's Boolean
and signed/unsigned 32/64-bit value kinds, with qualification kept separate.
The validator, execution lowering, and contract interfaces share classification,
scalar type comparisons, and checked literal interpretation. One conversion
policy selects shared kernel casts and the explicit C++20 signed-bit cases;
Clang retains promotions and usual arithmetic conversions as typed nodes.
Arithmetic still uses the common kernel: signed overflow is undefined,
unsigned arithmetic wraps, division truncates toward zero, and division/remainder
require nonzero divisors and exclude the signed minimum/-1 pair. Reference and
field restrictions stay position-specific. New boundary tests check scalar
qualification, unsupported widths, and literal ranges. Offline source proofs
cover Boolean widening and uint64-to-int64 bit preservation, including expansion,
retained audit, and false claims. Existing arithmetic/proof fixtures are unchanged;
artifact schema is now 42. The full `__int128` path remains a prerequisite for the
full fee arithmetic milestone, rather than another isolated family of type matches.

The inventory validity/profile/budget slice is delivered. The single-record and
leaf-plus-dependent constant shape caps are replaced by named declaration
budgets (256 records, 1,024 constants, and 1,024 functions). Constant forests
retain the existing initializer semantics and checked evaluation agreement.
Record layouts retain the existing field/ABI semantics and require distinct
proof-facing names. Unused layouts now fail structural graph validation.
Lowering builds record and constant indexes once and shares them across all
functions. Serialized nesting/containers are bounded before deserialization,
and call depth uses cached full subgraph depths so traversal order cannot hide
an exhausted limit. Multi-size constant/record/function regressions cover the
new inventories; malformed dependencies, duplicates, bad evaluated values,
orphan layouts, and budget boundaries remain rejected.

Scope validation now uses a lexical environment whose children borrow their
parent and own only newly declared places and names. Entering a normal scope or
catch handler neither clones outer types nor scans all outer names. Catch names
belong to the handler environment. Multi-size deterministic regressions check
shared outer storage, local-only entry counts, sibling isolation, duplicate
identities, shadowing, and forged references. The existing lifetime combinations
remain constrained by their semantic profile; lifetime inventory counts use
the named budgets described below.

Graph place indexing is delivered. Each visited function builds one index of
borrowed declaration IDs and places, including parameters, locals, and catch
bindings across blocks and branches. Reference arguments and destructor edges
use indexed type lookup. Duplicate IDs anywhere in a function are structural
errors, including reuse across disjoint sibling scopes; equal readable names
with distinct IDs remain valid. Lexical environments still establish visibility
and lifetime checks still establish cleanup order. Deterministic regressions
cover growing parameters, locals, and reference edges without repeated body
searches, plus malformed IDs. Source regressions verify, expand, and audit
reference-call proofs with growing unrelated places and reject false claims.
Lifetime inventory budgets are delivered: each function allows up to 1,024
local declarations, including catch bindings, and 256 cleanup scopes. Exporter
and checker count independently, including both branch arms. Larger inventories
of top-level destructible objects, sibling scopes, and objects within a supported
scope share the existing construction stack and reverse cleanup checks.
Multi-size regressions cover prefix returns, cleanup order, validation/lowering
work, proofs, expansion, audit, malformed exit lists, and atomic budget failures.
The three-scope restore proof records restoration at each boundary with explicit
steps; its C++ source is unchanged. Multiple trivial aggregates, deeper scopes,
overlapping outer/sibling combinations, and the existing conditional/exception
arrangement restrictions remain semantic-profile limitations. Current schema 45
requires an explicit refresh of earlier locks.

Recursive function metadata validity is delivered in its own module. Before a
function's semantic profile is checked, a borrowed traversal validates every
statement, expression, initializer, argument, cleanup, and type-alias chain,
including both branch arms and nested scopes/handlers that the current profile
will reject. Declaration metadata, source spans, and alias provenance/cycles
are structural checks; supported widths, operand relationships, lexical
visibility, and lifetime arrangements remain semantic checks. The existing
serialized nesting budget bounds recursive input. Local semantic validators
reuse the metadata helpers when checked in isolation. Regressions mutate every
span and identity in a corpus covering all recursive variants, distinguish
malformed metadata from unsupported nested lifetimes, and measure growing
syntax/alias work without cloning lexical environments. Artifact schema is now
38 and existing supported-source proofs remain unchanged.

Next extend the shared scalar and kernel design for the fee arithmetic milestone.

Field-reading siblings beside a scalar-isolated nested call are delivered.
The producer and offline checker require that nested call's inputs to be scalar
values, with no pointer/reference inputs or further input calls. Mutable globals
and external calls remain rejected, so the call cannot access caller storage.
The shared normalizer snapshots field siblings before the call, checking read
authority even when the call throws. Aliasing and hidden input calls remain
rejected; general alias analysis and other memory-reading siblings are deferred.
Offline proofs cover every argument position, supported field casts, initializer
and discarded contexts, concrete positive/negative and exact/remainder fee
rounding in a synthetic method/template/static-helper wrapper, expansion,
reverification, and retained audit. Hostile checks cover missing authority, false
results, direct/hidden aliases, and unchecked reads before exceptions. Argument
inventories have deterministic validation/lowering scaling regressions. This
does not yet admit the unchanged Bitcoin wide arithmetic/Assume source.

Resolved function identities and contract names are delivered. One immutable
ID-to-name index drives kernel definitions, every call (including construction
and cleanup), load owners, and proof interfaces. Unique readable names remain
unchanged; free namespace names flatten `::` to `_`. Colliding spellings use
`__click_cpp_decl_` followed by the full hexadecimal UTF-8 declaration ID.
That prefix is reserved, including for user declarations, so encoded names are
injective without digest assumptions or order-dependent numbering. Anonymous
namespace spellings also use encoded names. Nested namespace selectors work. The original
artifact IDs remain independently available, and `contract_name(id)` exposes
the binding on the lowered import. Regressions cover reachable overloads with
`long`/`long long` parameters of equal width, namespace/global spelling collisions,
and same-named static helpers in different namespaces. Selected overloads still
require a future signature selector; namespaced method selection and same-named
record layouts remain outside this slice. Existing template instance names remain
readable when unique. Hostile reference-name/ID mismatches still fail validation.

The expression normalizer and prepared execution boundary are delivered in
this consolidation. Future expression positions and richer ordering support
must extend the same normalizer. In particular, calls inside arithmetic,
conditions, assignments, and constructor arguments remain outside this slice;
integer local initialization, return calls, and discarded calls share the
current stable-sibling policy.

## Fee arithmetic milestone

Select unchanged `FeeFrac::EvaluateFeeDown/Up` and their instantiated helpers
from this pinned release. State input bounds that make the result representable
and prove the documented rounding direction, including negative fees, exact
division, and a nonzero remainder. Concrete Boolean template instances and `if constexpr` now have prerequisite
coverage. The unsigned-to-signed-64 conversion prerequisite is also delivered:
the synthetic fast paths now preserve the signed return and concrete rounding
cases. The selected upstream source still requires `__int128`
and support for its library `Assume` annotation on this target. Stable scalar
and isolated field-reading sibling arguments in `Div(Mul(...), size, RoundDown)`
are now supported. The selected upstream `EvaluateFee` callers are verified
under the explicit input and result-fit profiles recorded below.

The shared exact multiplication-range prerequisite is delivered. An explicit
`integer_product_bounds` certificate checks the four corner products of two
constant-bounded mathematical Integer operands. A checked lemma proves that
a signed 64-by-32-bit product fits the signed 128-bit range; machine values
compose through their separate `to_integer` observers. Hostile certificates,
large constants, deterministic scaling, expansion/reverification, profiling,
and retained audit have coverage. This is shared proof arithmetic available to
C, Rust, and C++; it does not yet execute native `__int128`.

The shared fixed-width constant and conversion layer is delivered. Formats
record signedness and 8–128-bit width; private checked payloads preserve the
full signed and unsigned 128-bit ranges. Checked numeric conversion and explicit
modulo conversion have distinct APIs, with exhaustive small-value and exact
wide-endpoint oracle tests. Existing machine bounds, Integer observations and
reverse conversions, rewrite normalization, and C++ literals/constant casts
use this layer. Runtime bridges require an exact format match. General
source-level `__int128` execution is limited to the bounded intermediate
profile below; the shared kernel also provides the listed internal operations.

The shared runtime now has an explicit modulo cast boundary for existing
8–64-bit integer values. C++20 and Rust select the same symbolic conversion
policy; constant conversions use the shared checked payloads. Width,
signedness, and operand definedness remain explicit. Narrow signed carriers
are sign-extended, and cast construction stays local to the operand root.
Ordinary C narrowing and checked Integer conversions retain their separate
rules. This removes frontend mask/cast sequences before extending widths.

The bounded shared wide scalar runtime is delivered: typed 128-bit literals
and variables, scalar locals and function parameters/results, substitution,
16-byte scalar size/alignment under the pinned profile, and exact Integer
observations. Reverse Integer conversions retain both wide range obligations;
truthiness observes all bits. Legacy arithmetic carriers are refused;
native arithmetic and typed memory access are admitted only in the slices below.
C0 identities carry the kernel types without adding source parser admission.

Symbolic wide widening, narrowing, and signedness changes are delivered at
the shared explicit modulo boundary. Cast terms retain both machine types;
constant substitution preserves every bit and sign extension. Ordinary C
wide signed conversions retain representability obligations. Exact Integer
observation preserves numeric widening, while value-changing casts remain
typed machine observations. Root construction and validation stay bounded,
including large operands; source admission remains open.

Checked signed 128-bit multiplication is delivered. Exact operand observations
feed a shared Integer product; both native range guards must hold before the
shared checked machine conversion produces the typed result. Unknown bounds
retain both signed-overflow paths. Existing 64-by-32 product-bounds certificates
discharge the guards without admitting unproved native definedness. Boundary
oracles, earlier operand undefined behavior, narrow operand promotion, function
results, specification capture, and indexed work scaling are covered.
Unsigned wrapping multiplication and other native wide operations remain open.

Exact typed 16-byte memory cells are delivered through the shared typed-load
and typed-store operations. Signed and unsigned load kinds preserve their
checked formats; symbolic reads retain snapshot identity and certified defining
facts. Full-width extents, initialization, and resource authority remain
required. Framing and store invalidation include the high eight bytes, and the
conservative unknown-width bound is sixteen. Generated store sequences include
wide cells and compare indexed gap skipping with the complete reference path;
load/validation work is tested over multiple unrelated-memory sizes.
Byte reinterpretation and source admission remain open.

Shared wide object pointers, pointer slots, fixed scalar arrays, and arrays of
wide pointers are delivered, with exact internal C0 type identities. Element
strides and scalar alignment are sixteen bytes; pointer objects and slots
remain eight bytes under LP64. Address-of, indexing, and local declarations use
the shared paths. Regression coverage includes full-width payloads, one-past
and uninitialized reads, separate slot/pointee authority, startup versus
ordinary-entry initializer authority, and symbolic storage scaling through one
million elements. Compact narrow-array copies reject overlapping wide cells.
Source pointers/arrays, wide byte reinterpretation, and wide callbacks remain open.

C++ frontend admission now covers signed/unsigned `__int128` intermediates:
mutable locals, full-width compiler constants, C++20 integral casts, Boolean
conversion of all bits, and checked signed multiplication. The existing scalar
interpretation maps directly to shared formats and kernel types; no C++ numeric
carrier was introduced. Function boundaries also admit by-value wide scalars, as described below.
Exporter and schema both reject unsupported wide operations. Current schema 45
requires refreshing older artifacts. High-bit products and modulo casts verify
through execute/simp, expansion, and retained audit; narrow and wide overflow
remain obligations even under a trivial postcondition. Shared wide-to-Boolean
conversion and safe nested modulo cast normalization are now covered directly;
known narrow 64-bit operands use indexed equalities with signedness retained.
Oracle checks cover all signedness combinations and both narrowing and widening,
and deterministic multi-size tests keep unrelated fact populations out of the
wide product lookup.

Wide scalar parameters/results and proof contracts are delivered. The exporter
and schema accept matching-width calls and captures; source entry uses the
shared typed symbolic values. Contracts spell `int128` / `uint128`, observe
all bits with `to_integer`, and use checked `to_int128` / `to_uint128` with
both destination bounds. Negative full-range literals retain their Integer
context through reverse conversions. Regressions cover extrema, hostile
high-bit claims, cast round trips, modular calls with framed narrow memory,
expansion/reverification, audit, and deterministic signature scaling at
2/8/32/128 parameters. Current schema 45 requires refreshing earlier locks.

The nested-call regression records a bounded search limitation: `simp` closes
a direct observer equality but does not chain two Integer equalities. Keep
that proof-composition follow-up explicit; do not accept pending goals or
retag wide values as narrow integers. Remaining native wide arithmetic and
wide source memory/aggregate admission remain separate work.

Shared truncating constant division is delivered as the next foundation.
The checked machine-format operation returns both quotient and remainder with
signedness and width preserved, rejects mismatched formats and zero divisors,
and refuses signed MIN/-1 for either operation. Existing 32/64-bit folding
and recursive constant observations use it. Exact-oracle coverage includes
all 8–128-bit formats, full signed/unsigned extrema, every byte pair, and
linear work over 2/8/32/128 explicit operations. This is representation
semantics; frontend promotions and language UB/panic policies remain separate.
This constant foundation did not admit wide source division; its artifact schema was 38.

The shared symbolic truncating quotient/remainder representation is delivered.
It uses distinct interned Integer DAG nodes, exact nonzero constant folding,
conservative affine refusal, and shared-node-aware traversal, substitution,
alpha keys, framing, and diagnostics. Zero divisors remain opaque, and no
unguarded cancellation or native definedness claim is introduced. Multi-size
regressions cover shared DAGs and numeric bit-length work. Arithmetic-spine
proposition substitution now memoizes shared children instead of revisiting
them along every path.

Native wide division/remainder execution is delivered for already-resolved,
matching signed or unsigned 128-bit operands. Zero and signed MIN/-1 guards
precede result construction for both operations. Unknown guards retain UB
paths; the normal path retains exact certified Integer observations of its
quotient/remainder. Signed overflow uses the existing logical proposition
model (`left != MIN || right != -1`). Rechecking and deterministic scaling
regressions cover native execution and exact guard lookup. Promotions remain
explicit; this native foundation used schema 38 before the source admission below.

Full-width quotient/remainder proof spellings and expansion are delivered.
`truncating_quotient` and `truncating_remainder` operate on mathematical
Integers and require a nonzero divisor even when surrounding arithmetic
erases the result. Native operand obligations survive; mathematical MIN/-1
remains unbounded, distinct from native overflow. Regressions cover constant
signs/extrema, hostile claims, missing guards, expansion/reverification, shared
pure aliases, and indexed guard lookup. Deferred expressions remain excluded
from obligation-free arguments and total fold summaries.

Wide C++ signed/unsigned division and remainder are delivered in schema 39.
The exporter retains Clang's explicit arithmetic conversions and the offline
validator rejects mismatched operand widths or signedness. Native guards accept
both equality-as-false and inequality-as-true contract spellings using indexed
lookup. Synthetic source regressions cover exact full-width constants and
symbolic results, signed MIN/-1 and zero rejection despite trivial posts,
modular calls with framed narrow memory, promotions, offline loading,
expansion/reverification, and retained audit. This is prerequisite support,
not a proof of unchanged upstream fee arithmetic.

Full-width signed/unsigned comparisons are delivered in schema 40. All six
relations share one Integer condition constructor between native execution and
pure-spec branch transport, retaining signedness and Clang's explicit
promotions. Exact and complementary premises use indexed queries; no ambient
proof-context scan is needed. Symbolic Boolean results, high-bit constants,
mixed-width conversions, source branches, modular calls with framed memory,
undefined operand refusals, offline verification, expansion, and retained
audit have coverage. The existing narrow scalar profile now admits `!=` too.
Kernel regressions compare signed/unsigned endpoints against a full-width
ordering oracle and check ambient-fact and explicit-operation scaling.

Range-checked narrowing proofs are delivered through the shared explicit
`integer_cast_identity` certificate. Two named bounds establish that a typed
modulo cast preserves its full mathematical observation; the kernel checks
both endpoints against the destination range, operand identities and formats,
polarity, references, and the conclusion. This neither assumes conversion
bounds nor changes out-of-range C++ wrapping. Signed/unsigned 128-to-32/64-bit
casts, implicit returns, native quotient/remainder narrowing, modular caller
framing, offline verification, expansion, retained audit, hostile certificates,
and deterministic scaling have coverage. That narrowing slice used artifact schema 40.

The unchanged upstream `FeeFrac::Mul` is now proved on the pinned wide profile.
Scalar brace initialization retains Clang's resolved semantic conversion for
`__int128{a}`; explicit full-width observer bounds feed two product certificates
that discharge native 128-bit overflow guards. The shared kernel exposes the
normal result's exact mathematical product, with native guards retained in
pure observation and capture. Fresh upstream export, false products, missing
bounds, modular caller framing, expansion/reverification, retained audit, and
ambient-fact scaling have coverage. That product slice used artifact schema 40.

The first explicit library-contract slice now admits pinned, assumed
Boolean-only statement contracts. The config names a qualified function and
header SHA-256; the artifact retains that descriptor and offline loading checks
its authority, dependency bytes, and preprocessor closure. The call requires a
proof that its evaluated condition is true before using the assumed normal,
no-memory-effects behavior. Ordinary same-named functions retain call semantics.
Missing or false conditions, unsafe signatures/arguments, altered pins,
expansion/reverification, cleanup, modular framing, offline authority, and
deterministic statement scaling have coverage. That slice used artifact schema 41.

The next library-contract slice now handles Boolean forwarding temporaries,
discarded Boolean rvalue-reference returns, resolved Boolean/scalar templates,
and up to eight forced `consteval` metadata arguments. Exact-type records bind
only to const references and require trivial destruction; integer metadata is
also supported. Metadata factory names and canonical declaration files, plus
the resolved specialization, remain visible in schema 42. Offline checking
binds their provenance to the pinned preprocessor closure. Pure runtime
`constexpr` calls are deliberately not inferred from constant-expression
eligibility. Cleanup, modular framing, hostile arguments and provenance, and
4/16/64/256-statement scaling have coverage.

The literal-metadata slice now admits runtime construction from a direct narrow
string literal under a separate, SHA-256-pinned constructor-family contract.
Both by-value and const-reference bindings require exact record types and
trivial destruction; by-value parameters also require trivial copying.
Runtime pointers, argument effects, conversions, additional/default arguments,
nontrivial initialization/cleanup, and selected-source definitions are refused.
Tagged metadata retains the literal, resolved record type, binding, constructor
pin, and canonical declaration file. Offline checks bind that file to the exact
pinned dependency and closure; diagnostics expose both assumptions. Proofs,
expansion/reverification, retained audit, cleanup, caller framing, hostile pins
and artifacts, and 4/16/64/256-statement scaling have coverage. This slice uses
artifact schema 45; previous locks require an explicit refresh.

The unchanged `FeeFrac::Div` now imports and lowers its complete body under the
explicit assertion and standard-library constructor assumptions. The real
annotation retains its Boolean temporary, forced source location, and literal
string-view value initialization. The missing-contract and consteval-only
refusals remain. Admitted native execution still rejects a missing condition,
missing wide division guards, and the unbounded narrow correction, even with a
trivial postcondition. Neither library implementation is verified, and the
general division/rounding theorem remains open.

The arithmetic foundation now supplies shared explicit `integer_division_bounds`
and `integer_relation_transport` certificates. Four operand endpoints bound a
truncating quotient or remainder, with zero excluded from the divisor interval.
A separate equality transport moves one whole bound/equality operand along a
named equality, including nonlinear terms. Kernel oracle, malformed-certificate,
large-value and budget tests, unused-fact and node-count scaling, pure fixtures,
and C++ native quotient/remainder narrowing composition have coverage. Those
narrowing proofs derive result bounds from operand intervals rather than taking
result ranges as preconditions, and retain expansion/reverification and audit.
No frontend schema or conversion semantics change.

The shared `integer_bound_exclusion` certificate now excludes a constant
strictly outside one named Integer bound. The unchanged `FeeFrac::Div` proof
can derive `1 <= d` from its real `d > 0` precondition, bridge that bound to
Integer, and exclude `0` and `-1` to discharge its wide division guards.
The pinned source regression advances to the still-unproved narrow correction
without assuming either guard. Complete native quotient/remainder guard proofs
retain expansion/reverification and audit; signed endpoint oracles, hostile
certificates, magnitude budgets, and fact/node scaling cover the shared rule.
No automatic range inference or frontend schema change is introduced.

The standard-library signed observation bridges now preserve and reflect
non-strict order for int32/int64, and int64 has the same observation-injectivity
bridge as int32. Checked wide-to-narrow cast identities and explicit Integer
bound transport can therefore establish native correction bounds without
assuming them. Complete proofs on the unchanged narrowing fixture cover both
widths and a modular caller that frames unrelated memory, with expansion,
reverification, retained audit, and hostile claims. Independent boundary models
and forged standard-theorem declarations cover the shared kernel laws.
The general Bitcoin correction and complete rounding theorem remain open.

A complete bounded safety proof now executes the unchanged pinned
`FeeFrac::Div`, including both narrowing conversions and every short-circuit
correction path. Its initial input profile was `-100 <= to_integer(n) <= 100`
and `0 < d <= 100`; quotient/remainder bounds are derived, transported through
exact observations, checked against both cast destinations, and reflected into
native correction bounds. The existing explicit assertion and literal
constructor contracts remain assumptions about the library implementations.
Full claim expansion/reverification, retained audit, hostile bounds/claims and
certificate references, and the same synthetic pattern with a modular caller
that frames unrelated memory have coverage. Shared contract scalar casts now
name signed/unsigned 64- and 128-bit conversions and parse correctly on the left
of comparisons. No exporter or kernel arithmetic change was needed.

Shared `int64_add_to_integer` and `int64_subtract_to_integer` laws now extend
int32's exact native-operation observations, retaining the essential native
definedness premise. The unchanged Bitcoin proof derives Integer and native
bounds on the corrected return value, rather than closing a trivial
postcondition. It admits every positive int32 divisor and numerators with
absolute value at most `INT64_MAX - 1`, then proves the result lies between
`-INT64_MAX` and `INT64_MAX`. Remainder bounds use the divisor magnitude, so both
narrowing identities remain checked even for this much wider numerator range.
The same synthetic correction pattern propagates native result bounds through
a modular caller and frames unrelated memory. Guard/width/operation forgery,
overflow boundary oracles, full expansion/reverification, retained audit and
multi-size application scaling cover the shared bridge laws.

Shared symbolic truncation laws now relate the dividend, quotient and remainder
under an explicit nonzero divisor. Positive-divisor remainder bounds and
nonnegative/nonpositive dividend sign laws also have exact checked declarations,
signed arbitrary-width oracles, hostile guard/type/operand cases,
expansion/reverification and deterministic multi-size application coverage.
These shared Integer laws apply independently of C++, C or Rust; they do not
infer native safety or expose nonlinear terms to affine arithmetic.

Shared Integer theorem arguments now capture native observations at their
fixed application state. Native evaluation and mathematical domain obligations
remain checked even for reflexive callee claims. Capture uses indexed lookups of
only referenced locals, arrays and snapshot names. Smart `apply` retains written
argument guards in its explicit evidence and checks that evidence before
returning a simple candidate; expansion cannot erase a required overflow guard.
Current, entry, marked and result observations, multiple native widths, hostile
types/domains, full expansion and multi-size capture/application scaling have
coverage. The unchanged Bitcoin and synthetic proofs apply the shared
reconstruction law to observed inputs and explicitly connect both narrowed
locals to their mathematical quotient/remainder terms.

Checked shared Integer equality rewriting now substitutes exact occurrences
inside compound expressions through the existing simple `rewrite` rule. Exact
available evidence, orientation, types, relation polarity, binder refusal,
shared DAG work and ambient-fact independence have coverage. Diagnostic names
are constructed only on refusal, keeping successful rewrites independent of
unused locals; deterministic multi-size surface checks pin that boundary. Pure and fixed-state
proofs expand and reverify, with erased evidence and false claims refused. The
unchanged Bitcoin and synthetic proofs now establish
`to_integer(n) == to_integer(quot) * to_integer(d) + to_integer(mod)` after both
checked narrowing identities. Internal fold/match binders remain an explicit
shared rewrite boundary; exact whole-fold replacement is supported.

Shared Integer rewriting now preserves the syntax of unrelated native
observations: exact Integer congruence does not fold native casts or known
conditionals merely while visiting them. Kernel regressions cover those opaque
identities and actual Integer payload substitution. The unchanged synthetic and
Bitcoin sidecars also prove the exact mathematical values of `quot + 1i64` and
`quot + -1i64` by rewriting the checked addition identity before substituting the
observed quotient. False correction offsets are refused; ordinary verification,
expansion/reverification, and retained audit exercise the proof sequence.

The bounded exact rounding value is now proved for the complete unchanged
`FeeFrac::Div` and the synthetic regression. In floor mode, a negative
truncating remainder yields `quotient + -1`; a nonnegative remainder yields
`quotient`. In ceiling mode, a positive remainder yields `quotient + 1`; a
nonpositive remainder yields `quotient`. The zero-remainder case is explicit
in both modes, and the synthetic modular caller exports all four guarantees
while framing untouched memory. A proof-backed shared
`int32_less_than_to_integer` lemma derives strict observation order from the
existing non-strict reflection bridge; no C++-specific axiom is introduced.

The defining floor/ceiling product inequalities are now proved on this same
bounded profile. Floor mode guarantees `result * d <= n < (result + 1) * d`;
ceiling mode guarantees `(result - 1) * d < n <= result * d`. All operations in
these specifications are mathematical Integer operations, and the modular
caller exports the four mode-guarded inequalities while framing memory.
Shared proof-backed `integer_floor_from_remainder` and
`integer_ceiling_from_remainder` lemmas combine reconstruction, remainder bounds
and exact correction values. Shared affine certificates treat complete symbolic
products and truncating terms as opaque Integer atoms; they do not derive
nonlinear laws. Exact `integer_multiply_add` distributivity uses the existing
checked polynomial certificate behind a proof-backed library lemma. False
inequalities, omitted reconstruction/remainder or correction premises, missing
evaluation guards, expansion/reverification,
retained audit and deterministic scaling have coverage.

The joint numerator/divisor profile admits wider int128 numerators and every
positive int32 divisor. Shared explicit `integer_quotient_bound` certificates
and proof-backed lower/upper lemmas derive quotient bounds from these scaled
premises, including negative and symbolic bounds. The unchanged upstream
sidecar and synthetic modular caller retain exact correction values, both
rounding product inequalities, native safety and memory framing. Rejection,
expansion/reverification and deterministic local-work tests cover the rule.

The correction endpoint cases are now proved on the inclusive joint profile
`INT64_MIN * d <= n <= INT64_MAX * d`. Both exact endpoint quotients are
admitted. Shared proof-backed lower/upper correction lemmas use reconstruction
and the remainder sign to exclude the endpoint only in the branch that needs
a correction; native `+1`/`-1` safety is proved there. The unchanged upstream
helper and synthetic modular caller retain exact correction values, floor and
ceiling product intervals, full int64 output bounds, and memory framing.
A reproduced Integer arithmetic rendering failure for equality from normalized
opposite bounds is fixed, with ordinary verification and expanded certificate
regressions. No C++ arithmetic axiom or source edit is introduced.

Shared explicit `integer_multiply_order` certificates now preserve or reverse
Integer product order using an exact ordered pair and multiplier-sign premise.
Proof-backed nonnegative/nonpositive multiplication lemmas and
`integer_scaled_product_bounds` derive the joint Div input envelope from the
full int64 fee bounds and `0 <= at_size <= size`. A checked caller-bound fixture
also derives the int64 truncating-quotient bounds, with hostile missing-premise,
expansion/reverification, signed endpoint oracle and local-work scaling checks.
This is a shared arithmetic prerequisite; it does not yet prove the upstream
`EvaluateFeeDown/Up` implementations or their unsigned fast paths.

Both unchanged `EvaluateFeeDown/Up` entry points now export their complete
reachable graph: the resolved Boolean template instance, Mul and Div. Evaluated,
explicitly pinned library assertions admit supported nonvolatile field reads
with normal authority/initialization checks, while the unevaluated builtin
continues to reject memory reads. Optimization-only `likely`/`unlikely`
statement attributes preserve their underlying branches; other attributes are
refused. Concrete fast-path caller proofs establish `7 * 2 / 3` as 4 downward
and 5 upward and preserve the receiver fields, with ordinary verification,
expansion/reverification, hostile field/size/amount/result claims and bounded
work-scaling regressions. This is source admission and concrete fast-path
coverage, not a symbolic caller proof.

Symbolic traversal exposed and fixed a shared execution-tooling defect:
64-bit field selectors retain their native width, automatic selectors must
lower back to the exact kernel condition, and short-circuit operand selectors
remain explicit even when each truth value has only one remaining path.
A reduced unchanged field/conjunction fixture checks ordinary verification,
expansion/reverification, retained audit, missing authority and false results;
signed/unsigned wide loads also round-trip at nonzero offsets. Shared plain C
regressions check negated conjunctions and disjunctions through expansion.
This removes a
stack-overflow retry loop and an unverifiable short-circuit expansion, without
changing the Bitcoin source or increasing execution budgets.

The unchanged `EvaluateFeeDown/Up` callers now have symbolic wide-path
contracts for negative fees and positive fees at least `2^33`. Under the explicit
full int64 fee observer bounds,
positive int32 size and `0 <= at_size <= size`, both preserve the fields and
return within int64 observer bounds. Down proves the floor product inequalities;
Up proves the ceiling inequalities. The proof names the captured denominator,
Mul result and Div result using existing `let ... = step(...)` bindings, then
transports exact Integer equalities with explicit rewrites. Both helper bodies
are verified from the existing sidecars in the same prepared project. Caller
and template-instance expansion/reverification, retained verification, missing
field/domain premises, forged product equalities and false rounding bounds are
covered. No new arithmetic axiom, search heuristic or Bitcoin source edit is
needed.

The two fee domains share one caller template, with separate native branch
guards and ordinary, expansion, retained-verification and hostile regressions
for each mode.

The shared machine model now has exact uint64 addition, multiplication,
subtraction, division/remainder and non-strict order bridges. Addition and
multiplication require explicit UINT64_MAX bounds; subtraction requires no
underflow; division/remainder explicitly exclude zero in both the native and
Integer evaluation domains. Checked declarations and typed
parameters keep these laws separate from signed definedness and uint32
arithmetic. Boundary models, hostile guards/types, ordinary C modular callers,
expansion/reverification and deterministic order-application scaling cover this
prerequisite for Bitcoin's unchanged unsigned fast paths.

Fast-path composition exposed two shared conversion gaps, now repaired.
`integer_cast_identity` recognizes the existing ordinary 32/64-bit conversion
terms through the shared typed modulo policy, retaining both explicit
source-range bounds. Ordinary symbolic uint64-to-int64 casts and returns require
the native unsigned INT64_MAX bound, rather than working only when constants
fold. The signed/unsigned 32/64-bit conversion matrix, ordinary C modular
callers, hostile bounds/certificates, endpoint checks and expansion cover these
prerequisites; no Bitcoin source edit or new arithmetic axiom is needed.

The unchanged unsigned `EvaluateFeeDown` caller now has a symbolic contract
for `0 <= fee < 2^33`, positive int32 size and `0 <= at_size <= size`,
with explicit native branch guards, fee observer bounds and field views.
`FeeFracEvaluateFastDown.click.in` composes the existing verified helper sidecars
in the same project and proves both caller levels. Exact cast certificates,
no-wrap uint64 multiplication and nonzero division transport the source product
to Integer arithmetic; quotient bounds justify the checked signed return.
The result is nonnegative and at most `2^33 - 1`, equals the truncating quotient,
and satisfies `R * D <= F * A < (R + 1) * D`. The fields are preserved.
Wrapper and instance expansion/reverification, retained verification and hostile
missing authority/domain/fee bounds and false quotient/rounding claims are covered.
No assumed result range, new arithmetic axiom or Bitcoin source edit is needed.

The unsigned `EvaluateFeeUp` fast path is also delivered on the same symbolic
input profile. `FeeFracEvaluateFastUp.click.in` preserves the source's mixed
casts and exact `fee * amount + size - 1` numerator. Separate checked uint64
addition and subtraction bridges establish no wrap and no underflow for the
intermediate operations. The shifted quotient is nonnegative, its loose upper
bound justifies the signed return, and reconstruction plus multiplication order
sharpen it to `2^33 - 1`. The result equals that quotient and satisfies
`(R - 1) * D < F * A <= R * D`, preserving both fields. Wrapper/instance
expansion and retained verification agree; missing domain/fee bounds, missing
numerator bridges, forged shifted identities and false rounding are refused.
Zero fee/amount, exact division and maximal fast-path operands remain in scope.
The unchanged implementations now have separate proofs for both rounding modes
in all three native fee domains, under `0 <= at_size <= size` and positive size.

Unified caller contracts are now delivered for both modes on the joint input
profile. `FeeFracEvaluateBounded.click.in` has no native fee-branch prerequisite:
it requires the full signed fee observer bounds, positive int32 size,
`0 <= at_size <= size`, and field views. The proof splits on the unchanged
source comparisons, derives fast-path observer bounds through checked signed
64-bit `<` and `>=` bridges, and reuses the existing fast/wide proof fragments.
Both caller levels preserve fields, derive int64 result bounds, and prove exact
floor/ceiling product inequalities across all signed fee values. Ordinary,
expanded and retained verification and hostile missing bounds, false rounding
and missing comparison transport are covered. The new shared bridges check their
exact typed declarations and native premises; endpoint models, forged declarations
and checked expansion cover them independently of Bitcoin.

Strict positive-divisor quotient bounds are now proof-backed shared lemmas,
with explicit sign guards, checked expansion and hostile endpoint/guard tests.
A mathematical fixture proves the initial int64 quotient fit for both wider
mode-specific domains. Separate `FeeFracDivResultFitDown/Up.click` sidecars now
verify native quotient and remainder narrowing, the selected correction and
exact floor/ceiling results on the unchanged upstream Div implementation.
Down accepts `MIN * d <= n < (MAX + 1) * d`; Up accepts
`(MIN - 1) * d < n <= MAX * d`, with positive int32 `d` and the corresponding
explicit native mode guard. The other correction direction is not a proof
obligation on the selected profile. Ordinary, expanded and retained verification
and hostile mode/divisor/numerator, strict endpoint, rounding, cast and
correction evidence are covered by eight hermetic phases. Both profiles are
alternatives to the existing joint helper contract; existing callers retain it.

The alternative `FeeFracEvaluateWideResultFit.click.in` caller profiles now
compose these mode-specific Div contracts with the unchanged Mul sidecar for
both Down/Up and negative/positive-wide fees. They replace `at_size <= size`
with explicit `0 <= at_size <= INT32_MAX` and the selected mode's product-fit
premises, retaining field views, signed fee bounds, native source guards,
checked multiplication, exact rounding and field frames. Four modular contract
applications fix size to 1 and amount to 2. Sixteen hermetic phases cover the
profiles' ordinary, expanded and retained verification, missing authority and
fit guards, weakened strict endpoints, false rounding and forged product
transport. The original unsigned fast and unified profiles retain the joint
amount/size bounds as regressions; the wider alternatives follow.

The unsigned fast Down/Up result-fit profiles now replace `at_size <= size`
with native amount bounds and a mode-specific upper product-fit premise. The
fast branch's explicit nonnegative fee/amount observers make its lower signed
bound automatic. Rectangular certificates bound the actual uint64 product;
Up separately checks its addition/subtraction before division. A strict scaled
quotient bound derives the full int64 return-cast limit from Down's product or
Up's adjusted numerator. Both caller levels export exact rounding, quotient
identity, result bounds and field frames. Four modular examples include
`at_size > size` and a uint64 product above `INT64_MAX` whose quotient fits.
Twelve hermetic phases cover ordinary, expanded and retained verification,
missing/weakened fit and operand guards, false rounding and missing/forged
numerator transport. Original fast profiles remain separate regressions.

The alternative `FeeFracEvaluateResultFit.click.in` profiles now combine the
wider fast and fallback fragments into one full-signed-fee caller contract per
mode. Both caller levels require field views, positive int32 size, native
amount bounds and the selected mode's two product-fit premises, with no fee
branch or amount/size prerequisite. Actual signed source comparisons derive
the fast observer bounds. The two wide branches keep separate captures and
exact product transport. All branches preserve fields and export signed
result bounds and exact floor/ceiling intervals. Four modular examples per
mode cover all source branches, amounts above size, and a fast product above
`INT64_MAX` with a fitting quotient. Seventeen bounded phases cover ordinary,
wrapper/instance expansion and retained verification, missing authority,
operand/fit bounds, weakened strict endpoints, source-comparison transport,
false rounding and missing/forged arithmetic evidence. The original joint
profile remains a regression; alternative helper interfaces remain explicit.

Preparation for the unchanged `CFeeRate::GetFee` wrapper now admits named
standard-layout class records with the existing signed scalar/pointer field
profile, including private, protected and default-private fields. Clang still
checks access legality at source uses; resolved declarations and exact field
layouts lower to the same C memory model as structs. Sidecar views/ownership
remain necessary, with no runtime access-control assumption or kernel change.
Synthetic const readers and mutable methods cover ordinary, expanded and
retained verification, false frames/values, missing authority and read-only
writes. Illegal source access, unions, mixed-access non-standard layouts,
general inheritance and bit-fields remain refused. Exporter refusal diagnostics
now use the actual source/header path instead of attributing a header line to the
selected translation unit.

Reachable record declarations now retain spans in explicitly locked project
headers. The exporter shares declaration-source handling with scalar aliases;
the artifact checker accepts record/field spans only in the selected source
or its configured dependencies, and requires a field declaration to share its
record's source. Function bodies and member-use spans still belong to the
selected source. Exact layout and declaration identities use the existing
memory model. Offline const readers and mutable methods verify, expand and
reverify with retained checks. Missing dependency authority, stale header
bytes, forged record/field sources and executable spans remain refused;
unrelated header records do not enter the proof graph. Existing deterministic
inventory checks now cover both selected-source and header record origins.

Embedded record declarations now preserve child declaration IDs, exact extents,
alignment and offsets, including repeated uses of one child type and nested
private fields in locked headers. The artifact checker indexes the declaration
graph before resolving fields, rejects unknown/misnamed/const child types and
by-value cycles, and follows embedded fields when checking reachability. A
bounded topological walk validates layouts without recursively expanding shared
declarations. Contract preparation reuses C's nominal embedded-struct metadata
and physical leaf layout; a separate 65,536-leaf budget bounds materialized
layouts across the import. Synthetic const readers and scalar outer-field
updates verify offline, expand/reverify and retain proofs while preserving
nested field frames. Forged layouts, missing authority, false sibling frames,
read-only writes, cycles and excessive shared-layout expansion are rejected.

Nested source member reads, writes and signed compound updates now retain a
root place plus an ordered path of resolved field declarations. The compiler
exports each field-use span and owner identity. Artifact validation and direct
lowering share an indexed path resolver that checks each owner/field/name and
accumulates exact byte offsets, without scanning unrelated sibling fields.
Root constness controls mutation through the entire path; field views and
ownership remain necessary at the accessed leaf. Ordinary, expanded and
retained offline proofs cover private nested fields, const methods, reference
parameters, parenthesized accesses, explicit `this`, signed 32/64-bit leaves,
compound-update bounds and sibling frames. Nested pointer-field checks keep
const-object access separate from ownership of the mutable pointee. Automatic
object restrictions are checked at declarations, preserving isolated constructor
argument diagnostics. Hostile paths, header-labeled use
spans, read-only roots, missing/wrong sibling authority and unsupported projected
place consumers are refused. Deterministic regressions cover increasing path
depth and sibling populations.

The pinned unchanged `CFeeRate::GetFee` regression now passes the `FeePerVSize`
record-layout, direct Boolean condition-call, locked-header executable and
converted `EvaluateFeeUp()` initializer boundaries. Its complete graph imports
and lowers with explicit header dependencies; the composition proof below
verifies the wrapper.

Projected method receivers and record/scalar reference arguments now use the
same ordered field paths. Call validation resolves the projected nominal type
through the shared index and propagates root constness to mutable reference
binding. Lowering passes the exact subobject byte address into the existing
contract-call machinery. Offline ordinary, expanded and retained proofs cover
const methods, mutable child methods, record helpers, signed-32 field references
and sibling frames. Shared permission indexing and joint consumption rejoin scalar bytes returned
by a call with bytewise field padding over symbolic object pointers; C and
kernel regressions cover the same boundary without changing ownership extents.
Byte-endpoint regrouping is limited to selected memory suppliers; ambient
normalization preserves borrowed clause boundaries. Authority wrapper folds
consume and compose only their checked exchange, retaining unrelated memory
and population units. Positive mixed-width frame and negative hidden-unit
regressions cover this boundary alongside the full Markdown proof corpus.
Post-return authority wrapper folds and unfolds now retain their checked
resource exchange through contract certification. Certification prefers the
entry paired with a jointly checked return context, preserving borrowed field
identities across separate clause proofs. The unchanged mixed-width frame
reproduction verifies, expands and rechecks in a retained session; hostile
proofs and deterministic checks reject missing/duplicate child authority and
removal of unrelated memory. The wrapper-unfold tooling blocker is resolved.
Recomputed-digest artifacts reject forged targets and use
spans, missing/reordered paths and const roots passed to mutable callees. Source
checks retain C++ access, constness, temporary and pointer-root restrictions;
wide mutable references remain outside the profile. Deterministic checks cover
reference resolution at increasing path depth and sibling populations.

Concrete class-template record instances now preserve Clang's canonical USRs
and use ordered scalar/Boolean argument tokens and named empty tag tokens in
contract-facing names. Record, field and method identities stay distinct across
equal layouts; aliases canonicalize. Existing record layout, access, ownership,
destruction and body restrictions still apply. Offline ordinary, expanded and
retained proofs cover scalar and tag instances, simultaneous equal-layout
instances and sibling frames; recomputed artifacts reject cross-instance
receiver binding. Instantiated storage, constructor/method/destructor calls and
automatic-object reference representation are covered alongside ordinary records.
Clang completes reachable unused parameter specializations before exporting
layout. Unsupported arguments, incomplete declarations, colliding record names
and unsupported inheritance fail without an artifact.

Single public non-virtual base layouts now retain a distinct nominal base edge,
Clang's offset/size/alignment and the base-specifier source span. Data-free,
standard-layout, trivially copied/destructed wrappers preserve the complete
base layout at offset zero. Sidecars use `base` as a separate nested layout;
ordinary/expanded/retained offline proofs preserve base-field sibling frames
through containing records and distinct tagged instances. Recomputed artifacts
reject forged base identities/names/layouts, cycles and copied field lists.
Deterministic multi-size checks cover the shared declaration graph walk.

Ordered base-subobject projections now support inherited field reads/writes,
implicit inherited method receivers and const/mutable base-reference arguments.
Mixed field/base paths retain each nominal owner/target and use span, propagate
complete-root constness and use the shared indexed byte-offset walk. Field
projection encoding remains compatible. Ordinary/expanded/retained offline
proofs cover two-level bases, forward declarations, containing records,
mixed-width leaves, mutable updates/calls and sibling frames. Recomputed
artifacts reject equal-layout nominal substitutions, bad spans, reordered or
incomplete paths and forged const roots; hostile proofs reject missing authority
and false results/frames. Multi-size checks retain one unit of path work per edge.

Direct Boolean method/free-function calls now normalize once before an `if`
branch, sharing typed captures, bounded nested argument evaluation and modular
contracts with initializer/return calls. Pure condition encoding and compiler
constexpr selection remain unchanged. Offline ordinary/expanded/retained proofs
cover state changes before both outcomes, inherited receivers, sibling frames,
fresh captures and scalar exceptional outcomes. Artifact checks reject forged
callee/result/argument identities and metadata; composed call expressions and
non-Boolean call conditions remain bounded refusals. Active-object unwind
cleanup is checked structurally within the existing lifetime profile. Ordinary
try/catch retains predicate exceptions; the guarded-try condition-hoisting shape
remains pure-only, including for recomputed artifacts.

Reachable ordinary methods/free functions now execute from explicitly locked
headers. Each function retains one definition/body origin; executable spans and
callee-use spans stay within their caller's source, while alias declarations
use the locked declaration inventory. The selected root stays in its configured
logical source. Every reachable implementation still needs ordinary verified
contracts. Offline ordinary/expanded/retained proofs cover cross-header
observers, inherited receivers and mutators, sibling frames, aliases, scalar
exceptions and calls back into the selected file. Missing dependencies, stale
header bytes, forged mixed-source metadata, unsupported bodies and recursion
fail without partial artifacts. Deterministic multi-size graph tests preserve
linear work and check caller/callee span ownership.

Converted scalar-call initializers now retain an inner-to-outer chain of
Clang's exact cast kinds, explicit/implicit origins, source/result widths and
qualifiers, alias provenance and executable spans. The shared scalar normalizer
captures the callee's original result once before applying the existing C++20
modulo/Boolean conversion policy. Offline ordinary/expanded/retained proofs
cover header alias casts, implicit widening, Boolean chains, narrowing and
mutating helpers with sibling frames. Hostile type/kind/origin, false-fit,
authority and source-overflow claims fail. Scalar exception contracts still
verify offline; active-guard rethrow cleanup has structural coverage. No new
kernel conversion policy or inferred fit bounds were added. Schema 45 requires
refreshing earlier locks.

Unchanged `CFeeRate::GetFee` now imports its complete reachable executable graph
with explicit dependencies on `consensus/amount.h`, `policy/feerate.h` and
`util/feefrac.h`. The composition proof is delivered below.
Converted scalar returns now reuse the initializer conversion-chain exporter,
metadata validation and scalar normalizer. Callee contracts retain their
original result type; the selected return retains its converted type, which
is captured before destruction. Offline ordinary/expanded/retained proofs cover
implicit widening, explicit modulo/Boolean chains, header alias provenance,
once-only mutators with sibling frames, normal destruction and scalar
exceptions. Forged chains/types/origins, false result/fit/authority claims and
callee source overflow fail;
active-object exceptional cleanup has structural coverage. Exporter and artifact
validation bound both initializer and return chains to 256 Clang conversion
steps; multi-size checks preserve linear validation work.
Converted call arguments, call-based brace initialization and broader composed
expressions remain separate.
Converted original 128-bit call results now use the same typed capture and
conversion chain. Explicit named captures transport modular observer bounds
to the existing checked cast certificate; preservation requires both destination
endpoints. Mathematical bounds never silently retag the native result. Automatic
observer normalization remains separate from these explicit proofs.
The unchanged `GetFee` now composes read-only `IsEmpty` and the unified Up
result-fit contract. Empty size returns zero without fee observer or product
fit premises. Nonempty size uses the caller-stated Up fit endpoints and full
fee observer bounds, exports the ceiling interval with the explicit negative
minimum correction, excludes zero for nonzero negative-fee calls, and preserves
both field views. Explicit helper-result captures and zero-observer rewrites
use existing shared proof rules. Execution-theorem proof blocks retain the
executed arguments' record metadata, including nested field paths, within
their clause scope; a small independent regression covers expansion, retained
checking, omitted premises and invalid fields. Ordinary verification, expansion/reverification,
retained certificates and modular empty/negative/zero/oversize callers have
offline coverage. Missing authority/domain/fee/fit bounds, weakened strict fit,
false empty/correction claims and stale reachable headers fail promptly.
The unchanged `GetFeePerK` wrapper now composes the unified Down contract at
1000 bytes with explicit positive-size and result-fit assumptions. Unlike
`GetFee`, its source does not check emptiness or apply a minimum correction.
Offline ordinary/expanded/retained checks and positive, negative, zero-fee and
wide modular callers are delivered. Missing size/authority/fit premises and
false rounding claims fail promptly.
Broader automatic object arrangements, nontrivial embedded destruction,
header destructor bodies, header constant definitions and mixed-source
executable macro spans remain separate work.
Keep object construction and the other `CFeeRate` methods separate until their
own contracts are selected. Continue bounded ordinary/expanded/retained and
hostile provenance, authority, fit and correction checks without editing Bitcoin.
The selected source narrows `n / d` to int64 and
`n % d` to int32 before correcting.
A zero numerator observer alone still does not establish the narrowed
correction's bounds. Use explicit checked certificates and useful
shared lemmas; do not edit Bitcoin or infer unproved ranges. `Assume` remains
an evaluated `inline_assertion_check<false>` call, separate from the unevaluated
compiler builtin. Add wide addition/subtraction
or negation only if selected source requires them. Keep mathematical Integer
semantics separate, especially its planned Euclidean division. Automatic
machine observer ranges, general range inference, further `CFeeRate` methods and
the portable `DivFallback` implementation remain open.

Before implementing the upstream proof, freeze a small regression that
preserves the chosen rounding/conversion pattern. Include hostile false
rounding claims, zero divisors, unproved overflow or narrowing bounds, and
unsupported reachable behavior. Acceptance requires the unchanged source
proof and modular callers, explicit compiler/library assumptions, ordinary
verification agreeing with expansion/reverification and audit, documentation
of the precise supported profile, and `scripts/check.sh`. Add deterministic
multi-size scaling regressions if the work changes a verifier hot path.

## Follow-up direction

These are candidate slices, not claims that their dependencies are supported
or a requirement to implement the entire list in one change. Choose the
next unchanged source and exact contract before implementation; update this issue to retain only remaining open work.

| Slice | Candidate and useful claim | Concepts it forces |
| --- | --- | --- |
| Bounded bytes and serialization | Select one unchanged span/cursor or serialization helper; prove bounds, consumed/produced length, and byte meaning or round trip. | C++ loops, array/range authority, representation and endianness, returned references, and explicit malformed-input behavior. |
| Owning containers | Select one bounded operation of Bitcoin's `prevector`; prove content preservation and ownership on each accepted outcome. | Allocation, object initialization, copy/move, destruction, small-buffer transitions, and iterator/reference invalidation. |
| Larger Bitcoin subsystem | Choose a bounded script, transaction, or validation component and state its safety and functional claims separately. | Composition of verified helpers, explicit external/library contracts, and domain specifications beyond language support. |

The selected fee rounding and `CFeeRate` evaluation proofs are delivered for
the pinned `__int128` profile, with explicit fit/domain assumptions. Further
fee methods must preserve the same unchanged-source boundary. Bitcoin's `Assume`
annotations remain exposed as contract obligations or explicit assumptions,
not silently counted as proved checks.

For spans, object-copying a view must not duplicate pointee ownership; returned
references must stay tied to the backing object's live storage. For containers,
prove exactly which operations invalidate old views, and reject their later
use. A modular library contract must declare whether its implementation is
verified or assumed, and pin the relevant implementation/profile. Resolving
a template instance is not itself a proof of the library it calls.

## Shared work and deferred coverage

Reuse the existing common resource and arithmetic machinery where its semantics
agree with C++. Coordinate mathematical division support with
[mathematical integers](../docs/internals/mathematical-integers.md), byte
reasoning with the [byte-representation design](../docs/internals/byte-representation.md),
and lifetime/aliasing investigations with
[supporting-more-languages.md](../design/supporting-more-languages.md).
C++ references can alias; do not impose Rust's exclusive-borrow rules on them.

Broader unwinding belongs to [control-flow.md](control-flow.md); concurrency
and atomics belong to [concurrency-and-atomics.md](concurrency-and-atomics.md).
Virtual dispatch, general inheritance/subobject identity, RTTI, arbitrary
standard-library verification, full exception semantics, and cross-target
coverage are deferred until a selected proof requires a precise slice.

Preserve upstream C++ just as existing C is preserved: adaptation belongs in
the importer, execution model, sidecar contracts, and proof tools. Tooling
instability blocks milestone work under `AGENTS.md`; do not work around it
with altered source, irrelevant proof bookkeeping, or larger search budgets.
