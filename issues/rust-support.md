# P1: Support safe Rust and verify a shared C/Rust checksum specification

Priority: P1.

Soundness: incomplete. Language coverage. Unsupported Rust is refused. The
pinned Charon front end is a documented trusted dependency.

## Goal and scope

Deliver a useful, explicitly bounded safe-Rust verification path through Click
sidecars and the shared checked engine. Verify selected unchanged Rust and C
Adler-32 implementations against one mathematical specification, then derive
result equality under matched input and state conditions. This is P1; the Linux
rbtree remains the key launch demo.

The implemented shared construction/return-destination contract is recorded in
[aggregate construction](../design/aggregate-construction.md). It preserves
existing Rust aggregate return, initialization and move/drop protocols. The
checksum milestones below can continue with their current semantics; they are not blocked on that design.

Experimental Rust support and the checksum demonstration are independently
reviewable milestones. Document and ship the supported subset without waiting
for the full library proof. Neither milestone implies general Rust coverage.

## Current capabilities and evidence

The Charon migration is complete. Native Charon is the sole extraction path;
canonical examples and compiler-backed regressions use it, and the legacy
exporter and toolchain have been retired. No HIR/MIR frontend migration remains.
Ordinary verification loads locked artifacts offline through the shared engine.

Supported operations include checked scalar arithmetic, branches, direct calls,
shared/mutable references and local reborrows, supported records and move/drop
protocols, compact scalar arrays and snapshot copies, byte slices, splitting,
and stored shared iterators with actual cursor/remaining state. Crate imports
lock roots, edition, features, target, qualified declarations, and the complete
compiler-observed source closure. Concrete constructors, record returns and
parameters, and selected resolved operators execute verified imported bodies.

The unchanged pinned adler2 2.0.1 selection imports successfully. Its original
`Adler32::compute` body now proves both final fields equal the common checksum
specification on the entry input snapshot, for every length zero through
2,147,483,647 bytes from any canonical initial state. It terminates, preserves
input bytes, checks every native access and arithmetic guard, and stores both
fields below 65,521. The proof follows actual full-width cursor and remaining
state through full batches, the aligned remainder, scalar accumulation and the
final tail. Checked signed observations impose the explicit proof range limit;
no generated processed counter or assumed checksum summary supplies the result.

Checked helper bodies and lane-state lemmas connect the actual constructor
bytes, four-byte recurrences, deferred B seed contributions, reductions and
ordered recombination to the shared mathematical specification. Full-range
native-count and byte-position bridges preserve exact values and addresses.
The specification independently proves concatenation and incremental equality
for A, B and the packed checksum under explicit signed-range split bounds and
canonical A seeds. A locked real Rust client now performs two unchanged
`write_slice` calls at every split of every supported input, including empty
prefixes and suffixes, proves the full-input packed specification, and preserves
all bytes. Its proof connects actual updated fields and suffix byte addresses
to the checked concatenation theorem. A second locked client saves the prefix
checksum, restores a fresh receiver through unchanged `from_checksum`, and
proves the same full-input result and byte preservation after the suffix update.
Bounded unpacking rules recover exactly the canonical fields produced by the
first update; arbitrary saved words are not assumed canonical.

Constructors, one- through four-byte computations, and the shared checksum
getter verify. The getter proves exact packing for any two u16 fields and has a
checked bridge from field specifications to the packed specification. The
unchanged `adler32_slice` entry point composes the checked constructor, general
computation and getter for every length zero through 2,147,483,647, returns the
common packed checksum, and preserves every input byte. `write_slice` accepts
any canonical initial state and returns canonical fields satisfying the common
A/B specification. Logical byte-index guards are bridged explicitly to native
64-bit range membership. The specialized empty call needs no byte authority.

The independently locked, unchanged zlib one-byte and short-loop paths prove
their packed results equal the same specification and preserve every input byte
for canonical seed 1 and lengths 1–15; its empty path also verifies.
General-length C correctness and C/Rust result equality remain pending.

Full original-computation smart audits exhaust the standard ten-minute run
bound before completing a site, while ordinary verification succeeds. Continue
with ordinary verification and retain audits where they complete; the audit
timeout supplies no proof verdict. Standalone native-count and chunk-position
claims pass complete audits. Whole-body correctness, false final A/B claims,
and larger proof-tool checks run nightly.

Composition regressions cover record and scalar-array storage starts, shared
chunk-view transport, and all four returned/copied vector lanes across local
stores. Automatic scope exits retire construction ownership. Negative tests
reject missing input authority, noncanonical seeds, and false induction or
final bounds. Whole-proof verification and tool agreement run nightly.

Detailed support boundaries and reproducible commands belong in
[the Rust reference](../docs/reference/rust.md). Current checksum evidence lives
in [the Adler trial](../design/charon-trial/adler2/README.md). Keep this issue a
current roadmap: replace status when work lands rather than append checkpoints.

## Remaining work, in delivery order

### 1. Verify C and publish the shared demonstration

Pin the selected configuration and revision of
[zlib's Adler-32](https://github.com/madler/zlib/blob/develop/adler32.c), verify
its unchanged optimized path against the same specification, and derive C/Rust
result equality. Match seed/reset and null-buffer behavior explicitly.

The [unchanged pinned zlib trial](../design/charon-trial/zlib/README.md) imports
all selected bodies and proves the canonical empty-input and one-byte cases
offline; the one-byte result satisfies the shared specification and preserves
the byte. Its null reset path verifies for any seed and nonunit length.
Expression updates preserve consumed values, loop exit-side effects, native
unsigned wrap, and checked pointer strides; nested `DO16` blocks also import.
Ordinary loop memory footprints are captured before modified counters and
cursors are havocked. Ranked reductions now cover a moving-cursor byte sum
and `while (n--)`, including its wrapping zero exit, without a processed
counter. Checked native 64-bit same-base prefixes now retain full-width
coverage bounds and lifetime evidence; symbolic prefixes have explicit
selected-premise proofs. Native byte subranges also retain a checked offset,
nonwrapping remaining capacity, and lifetime evidence. The unchanged C short
loop now proves the shared packed checksum, termination, and preservation of
every input byte for canonical seed 1, nonnull input, and lengths 2–15. Exact
component-sum invariants follow the actual remaining count, with checked byte
promotion and native addition bounds. Checked native addition-pair and
double-reduction packing lemmas are available for the larger computation.
The locked DO16 sidecar now proves the shared checksum, termination, and
preservation of all input bytes for canonical seed 1, nonnull input, and
exactly 16 bytes. It follows actual remaining-count state, checks all sixteen
native addition pairs, and preserves the component equations through the
zero-length scalar tail. The offline nightly regression checks helper bodies,
expansion, and rejection of false results/invariants and missing authority.

Checked symbolic count-advance, lane-identity, and native read-bound lemmas
support repeated DO16 blocks below 5552 bytes. The saved 16–5551-byte draft
checks all sixteen original addition pairs and closes the repeated-block
invariants. Its full contract remains unproved: the scalar tail stops at
the original scalar-tail byte read after `*buf++`. Bounded selected-premise
reduction now gets past the first-byte view construction that previously
selected 71 premises and exceeded the unchanged 64-premise spelling limit.
The actual C read still reports missing held read authority; a pure
`viewable` fact does not grant that authority. See the
[tracked read regression](../bugs/zlib-repeated-tail-loses-native-read-authority.md)
before extending the scalar-tail proof.

Complete that scalar tail, then the original 5552-byte batches. Maintain exact
component equations and native bounds across reductions; the arbitrary-length
C result remains unproved.

Connect the original nonempty computation to the common specification, then
prove compatible seed/reset/null-buffer behavior and incremental processing.

Acceptance:

- Both implementations independently satisfy the shared specification for
  arbitrary inputs covered by their contracts; accesses, arithmetic, byte
  preservation, termination, and incremental processing are proved.
- Result equality follows from those proofs. Differential runtime tests are
  supplementary evidence.
- Publish reproducible locked fixtures and a scoped demonstration. Keep slow
  whole-proof checks nightly and bounded regressions in the normal gate.

### 2. Close experimental-support architecture requirements

Resolve these requirements alongside the library proof; do not postpone them
behind new language coverage:

- **Borrow authority:** connect explicit exclusive-child suspension/recovery
  to production resource transitions. Compiler borrow rejection alone does not
  establish rejection of forged sidecar authority. Test stale child access,
  forged/duplicate recovery, disjoint field borrowing, and parent reuse.
- **Stable proof observations:** provide source-facing slice, array, and
  iterator observations so contracts need not depend on compiler temporary
  names or storage details. Preserve qualified identities, shadowing, source
  spans, snapshot meaning, and expanded-proof correspondence.
- **Consistent library models:** consolidate supported resolved instances and
  document their preconditions, effects, panic behavior, and named trust
  assumptions. Validate declarations/signatures and bind model versions into
  prepared identities; lookalike methods must not acquire models by spelling.
- **Composition and scale:** keep one semantic execution path, shared CFG joins,
  compact repeated initialization/copies, and checked cleanup on supported
  exits. Combine references, arrays, arithmetic, iterators, owned records and
  drops in regressions. Verify/profile/expansion/audit must agree where applicable.

Assess each item against current production evidence before adding mechanisms;
retain existing working representations where they already meet acceptance.
The experimental milestone closes when its defining borrowing/move regressions,
production negative tests, proof-tool agreement, and accurate public support
and trust documentation satisfy these requirements.

## Semantic boundaries and delivery rules

rustc establishes source typing and borrow legality. Click checks functional
claims and supplied memory authority; references grant no allocation or
deallocation authority. Keep allocation lifetime, access authority, and value
validity distinct. Lock source, compiler/exporter, target/layout, semantic flags,
models, and relevant dependencies. Preserve full-width Rust metadata and range
endpoints. Proofs using signed index observations, including the current checksum
trial, must state and check their narrower range explicitly.

Unsafe Rust, interior mutability, returned references, general traits/generics,
closures, async, threading, heap support, mutable/adapted iterators, and broad
standard-library verification are outside this issue unless a concrete instance
needed for the selected checksum path is explicitly assessed.

Keep original Rust and C sources unchanged when developing proofs. Repair
lowering, resource rules, contracts or proof tooling instead of making source
more verifier-friendly. Reproduce and fix tooling defects before extending
examples; retain meaningful negative tests and deterministic scaling checks.
Deliver coherent green increments through the fork PR and merge queue workflow.
Delete this issue and its list entry when both milestones and documentation land.

Durable design references: [resource correspondence](../design/rust-resource-correspondence.md),
[Charon assessment](../design/rust-charon-assessment.md),
[adapter trial](../design/charon-trial/README.md),
[language design](../design/supporting-more-languages.md), and
[stable views](../docs/internals/stable-views.md).
