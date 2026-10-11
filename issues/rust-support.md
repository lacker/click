# P1: Support safe Rust and verify a shared C/Rust checksum specification

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

The unchanged pinned adler2 2.0.1 selection imports successfully. Constructors,
constants, lane helper bodies, numeric ceilings, and lane preservation verify.
The general, small-batch, and four-byte sidecars check full-width native iterator
state with explicitly bounded signed observations. The original computation has
a terminating whole-body bounds proof for every
length from zero through 2,147,483,647 bytes from any canonical initial state.
It carries all eight lane ceilings, scalar-tail ceilings, the shared input view,
and actual vector and scalar iterator state through reductions, recombination,
scalar sums, short tails, and final 16-bit stores.
Both output fields remain below 65,521. Checked partition lemmas relate full-width
lengths, signed indices, four-byte prefixes, and zero-to-three-byte tails.
General signed-range partition lemmas establish aligned full-batch remainders
and decreasing actual outer-iterator remaining counts, without truncating usize
metadata. Full outer-batch induction, lane reduction/reset, and the final vector and scalar
remainders are checked in the whole-body proof. Checksum correctness remains
incomplete.
The shared mathematical specification proves byte-sum and weighted-sum
concatenation and incremental equality for A, B, and the packed checksum under
explicit signed-range split bounds and canonical A seeds. These are independent
mathematical proofs; implementation-level incremental correctness still depends
on the general computation proofs.
The shared mathematical specification has checked one- and four-byte append
recurrences, including the ordered weights 4, 3, 2, 1 for a vector step,
weight shifts, nonnegative sums, residue addition, output and packing bounds,
residue congruence with signed quotient witnesses, and preservation of canonical
seeds on empty input. The original remainder helper also supplies exact Integer
remainders for all four lanes under its native nonzero-divisor precondition.
Checked Integer lane-state lemmas establish the optimized four-byte recurrence,
including the original recombination offset and weights, and preservation of
both residues through lane reductions. The constructor exports each lane’s
exact mathematical entry-byte value. The small-count cursor bridge also proves
equal byte addresses for the full native count and its checked signed index,
using equality of exact values rather than low-bit truncation. Source-proved
read bridges connect the native count and all four positions in its chunk to
the signed byte observations used by the common spec, with checked signed-index
guards. The original small-batch vector loop checks each constructor lane’s
native and Integer value against its shared subslice and its position in the
original input. That position is derived from the actual remaining count after
`Next`, with checked native and signed subtraction bounds. One- and four-byte prefix
lemmas preserve both A and B residues against the common specification,
including the ordered weighted update under explicit index and nonnegative
representative bounds. A scalar read bridge derives the last returned byte
from the actual post-`Next` remaining count and checks its exact signed-index
observation. A joint native vector-prefix bridge now connects the
checked word additions and exact constructor byte observations to both common
prefix residues. Its iterator adapter derives the prefix from stored remaining
state and checks the four-byte advance and remaining-length bounds. The original
small-batch vector loop carries both residues against the common
specification at every actual remaining count and establishes their relations
for the completed four-byte prefix, from any canonical A and B seeds. The B
representative includes the deferred prefix-length times A-seed contribution,
the original four lane weights and the `6*MOD` offset, and stays nonnegative.
Initialization, native lane additions, exact input-byte observations, signed
prefix subtraction safety and exact Integer prefix advances are checked.
A now passes through the original lane reductions and four scalar additions
into its prefix residue before the tail. The native B seed product and
addition prove the exact deferred prefix-length times seed contribution,
including the exact length-cast observation. B also passes through the scalar
and lane reductions, ordered weighted corrections and four scalar additions,
with checked native subtraction, multiplication, addition and store bridges.
Both prefix residues pass through the original scalar tail: each actual
post-`Next` remaining count identifies the returned byte and the next common
prefix, and both checked native additions preserve their residues. The B step
uses the newly updated A value. Signed subtraction definedness and the exact
native-to-Integer byte and assignment observations are checked explicitly.
The loop-exit bridge and final checksum postconditions remain pending, as do
the arbitrary-length computation’s nested loops. Full original-computation smart audits
currently exhaust the standard ten-minute run bound before completing a site,
while ordinary verification succeeds. This is an audit-tool limitation, not a
reported proof failure; continue checksum proof work with ordinary verification
and retain audit coverage where it completes. The standalone native-count and
chunk-position observation claims pass complete audits. The loop bridge uses
scoped native byte equalities and explicit Integer premises.
The unchanged Rust one- through four-byte computations prove both fields equal
the shared specification on the entry byte snapshot, starting from A = 1 and
B = 0. The four-byte bridge checks the native unsigned recombination and its
ordered B weights. The unchanged shared checksum getter proves the exact packed
value for any two u16 fields, preserves both fields under shared views, and has
a checked conditional bridge from the field specification to the packed
specification. The unchanged `adler32_slice` entry point composes the constructor,
mutable computation, and shared getter for every input length zero through
four, proves the common packed specification from A = 1 and B = 0, and preserves
every input byte. The empty call needs no input-byte authority. The serial-tail
bridges check unsigned prefix sums, the ordered B weights, and removal of the
native modulus offset before connecting both fields to the common specification.
General-length correctness, broader public-entry-point composition, and
implementation incremental correctness remain pending.
The independently locked, unchanged zlib one-byte path proves its packed result
equal the same specification and preserves its input byte; its empty path also
verifies. General-length C correctness and C/Rust result equality remain pending. The specification is not yet connected
to either implementation’s general computation.

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

### 1. Verify Rust against the common checksum specification

Use the [shared Adler-32 specification](../design/adler32-spec.click), following
[the checksum assessment](../design/rust-checksum-assessment.md). Relate the
original optimized lane state and reductions to that definition, then compose
the checked constructor, computation, and checksum getter at the public
entry point.
Prove arbitrary finite input correctness under the explicit supported memory
range and API preconditions, including compatible initial states.

Acceptance:

- The unchanged selected Rust computation terminates, preserves input bytes,
  cannot panic, and returns the specified checksum.
- Incremental processing equals processing concatenated input, including
  empty and chunk/remainder boundaries.
- A false checksum postcondition fails. No assumed library summary supplies
  the checksum computation's postcondition.

### 2. Verify C and publish the shared demonstration

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

### 3. Close experimental-support architecture requirements

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
