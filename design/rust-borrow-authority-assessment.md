# Rust borrow authority: production evidence and next protocol

This assessment records the production borrow-authority boundary beyond the
[completed Linux frontend milestone](rust-charon-assessment.md#completed-linux-frontend-delivery). The independently checked checksum
proofs are complete within their published contracts. Borrow authority remains
an architecture requirement, with the following production boundary.

## Current evidence after call-scoped integration

| Required case | Current evidence | What remains |
| --- | --- | --- |
| Updated child contents return to the parent | Native Rust reborrow, field-guard cleanup and modular owned calls verify through the production engine. | Synchronous borrowed-memory calls now carry an explicit child receipt; local reference lifetimes remain separate. |
| Parent reuse after the child's last use | `rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop` checks the unchanged `set_seven` witness body, then a real caller. Both contracts expand and reverify. | Extend retirement to escaping/conditionally live references and early exits. |
| Disjoint fields remain usable | `rust_owned_disjoint_mutable_fields_verify` checks actual simultaneous field references and updated values; the production call planner partitions exclusive requirements. | Production call receipts now combine nested dependencies with the existing footprint partition; local borrow dependencies remain open. |
| Stale child access and duplicate recovery fail | Production exclusive-call tests reject stale receipts, duplicate returns and missing discharge; native sidecar negatives reject absent write authority. | The first scalar source subset now rejects expired local handles; wider source coverage remains open. |
| Wrong child identity or holder cannot recover | Production exclusive-call receipt tests reject wrong holders, other call identities, altered supports and a fabricated terminal rollback. | Source endings check live invocation handles and child dependencies; wider source coverage remains open. |

The new native regression deliberately leaves the child reference's storage
alive when the parent is reused. It proves `4 -> 7 -> 8` behavior for the
resource-correspondence helper without requiring an initial value: the child
writes 7 before the parent increments. It rejects final value 7, shared-only
authority for the helper's write, and shared-only authority at the caller.
It checks actual imported helper and caller bodies, not an assumed helper
summary. It does not assert that a stale-child sidecar has been rejected.

In `src/languages/rust/lowering.rs`, scalar `E::Borrow` becomes the address of
the borrowed place cast to the reference's pointer type. Reference declaration
records mutability/type and assigns the pointer; it does not mint an exclusive
child loan. A checked trace of `set_seven` shows `child = value`, `*child = 7`,
and the later load/store through `value`, with no exclusive loan transition.
This is evidence about the current representation, not a reproduced verifier
defect: pinned rustc establishes source borrow legality, while Click checks
functional behavior and memory authority.

Synchronous `owns` calls already reserve exclusive footprints from the caller
and give them to the callee. `plan_stable_view_transfer` reserves these before
planning shared views, records supporting occurrences and retains disjoint
caller resources. This prevents duplicated or overlapping call ownership.
`LoanLedger::reborrow`, however, creates a shared view and pins its parent;
the separate exclusive-call receipt now tracks synchronous borrowed memory.
A successful native Rust example alone cannot close local exclusive borrowing: its
reference declarations still create aliases without local child identities.

## Implemented first increment: synchronous borrowed-memory calls

`src/kernel/loans/exclusive_calls.rs` is integrated into the existing call
planner and checked loan-call evidence. It covers `Borrow` requirements over
owned memory. Consumed/moved resources, abstract/composite ownership, and
suspended worker transfers retain their existing protocols.

The planner reserves ownership before issuing a receipt. That receipt binds
one fresh call identity, caller and callee participants, every selected
ownership support (including joined fragments), and the containing exclusive
call when present. The identity is fresh even if a completed call resumes at
the exact original ledger root. A persistent holder index finds the containing
call directly; nested calls increment its dependency count. The outer call
cannot return while a nested child remains active.

Memory authority stays in the existing resource partition. The receipt never
mints an owned fact. The caller residual lacks read/write authority for the
borrowed footprint while retaining disjoint resources; the callee receives
exactly the reserved ownership. Entry and recovery checks validate the live
receipt and its selected supports against that plan. Callee memory updates and
returned contents still come from the ordinary checked call result.

Return requires the exact receipt and original caller, ends the child once,
and releases the parent dependency. Checked evidence rechecks both entry and
return against exact predecessor roots and also requires the receipt to be
closed in the terminal successor. Merely claiming a rollback to an equal
caller root cannot replace child return. Expired receipts, changed supports,
wrong holders, other call identities, missing discharge and duplicate return
are refused. Canonical caller-root restoration remains the existing mechanism;
checked terminal history retains the actual discharge.

Normal kernel regressions cover nested return order, disjoint parent read/write
authority, joined support fragments, move-role separation and forged recovery.
Deterministic persistent-map measurements at 16, 64, 256 and 1024 unrelated
scopes bound a selected entry/return operation by indexed lookup work. Updates
share the selected receipt payload and do not scan unrelated scopes. The
whole-ledger invariant walk is test-only.

The native witness regression now also verifies `nested -> update -> set_seven`,
with a separately owned neighbor set to 9. All three contracts expand and
reverify; false value and missing helper, caller or neighbor write authority
are rejected. This checks actual imported Rust bodies through the same engine.

## Checked local-reference endings

`PreparedRustImport::certify_scalar_reference_end` now checks an explicit MIR
borrow/frontier pair against the immutable locked import. Its private
certificate constructor binds the result to the import identity, selected
function and exact MIR points. Function names are indexed once per import;
each query examines only the selected function and continuation.

The supported subset is a mutable scalar reborrow from a local reference,
with the borrow and frontier in one block followed by an acyclic straight-line
continuation. The checker follows copies, reborrows and replacement definitions
from the selected child. It refuses future uses, branches, cycles, aggregate
transport, reference returns and opaque capture, including capture nested in
scalar expressions. Conversions involving a selected alias are conservatively
refused. Storage events never discharge aliases. Reassigning the parent name
does not hide an outstanding child, while replacing a child binding does not
retire copies of the original reference.

The native `set_seven` fixture checks this certificate against actual exported
MIR, checks its import identity and rejects an ending before the child store.
Fourteen bounded unit regressions cover alias copies, storage markers, replacement,
parent reassignment, capture, unsupported paths, call continuations and invalid
points. A deterministic 16/64/256/1024 alias-chain regression bounds work to the
selected input, up to indexing factors. The native fixture also binds its child
store to the exact immutable MIR expression and borrow instance.

The ending certificate now indexes checked scalar memory accesses by MIR point.
Each access retains its read/write kind, per-statement occurrence, reference
local, exact expression, selected borrow point, function and locked import
identity. Copies and direct reborrows retain the original borrow identity;
replacement definitions distinguish a later reference in the same local.
Reborrowing computes an address and is not itself recorded as a scalar read.
Shared aliases may supply read evidence but cannot supply write evidence or
produce a mutable reborrow. A scalar read used to choose another address is
refused as alias transport rather than binding that new address to the original
footprint. A second 16/64/256/1024 regression checks access indexing and lookup.

Locked Rust preparation now carries MIR point, expression-node and reference
identities into typed loads and stores. Lowering indexes only the current
statement's immutable expression nodes, in the same order as the source checker;
it does not use structural expression keys or search other functions.
`CheckedScalarReferenceEnd::bind_executed_accesses` joins its indexed accesses
with completed kernel producer observations from the selected execution. It
checks import identity, function, point, node, reference local and access kind,
then retains the actual pointer and execution alongside the original borrow.

Stores retain source provenance in their existing checked store certificate,
after memory checks succeed. Completed reads retain a private receipt even when
a cached scalar returns without minting a new load variable. Read receipts match
their exact memory state, pointer and type; rewritten facts discard that
provenance. These private consequences are not path selectors. Source-bearing
producer records survive composition as a selected delta, without deduplicating
two operations that happen to have the same semantic memory proposition.
Source metadata remains outside statement/fact comparison and grants no resource
right. Regressions check actual read/write producers, rejection of a different
lock identity, absence of a store observation on a failed write, and distinct
cached reads in one statement.

This read-only certificate proves absence of future selected-reference uses in
that subset. It does not grant memory authority, end a production loan or
change ordinary import/verification acceptance. An unsupported ending query
does not itself reject the Rust program.

## Checked local-reference lifecycle

`src/kernel/loans/local_references.rs` adds the local-reference lifecycle to
the existing immutable `LoanLedger` and its sealed, predecessor-bound checked
transitions. This is a kernel protocol increment; ordinary Rust lowering does
not yet issue these transitions or use their access checks.

Registration checks an exact live owned occurrence for one scalar (`i32`,
`u8`, `u16` or `u32`) and retains its holder, footprint and type. It reserves
one root identity for that occurrence. A reborrow has a fresh reference identity
and the exact parent's shared backing; names and pointer equality cannot
substitute for it. While the child is active, the protocol refuses parent
access, another child from that parent, and parent retirement. Nested borrowing
suspends the intermediate reference too. Independent scalar roots remain usable.

Recovery requires the exact live child, original holder, live ownership support
and absence of a dependent child. It retires that child once and restores its
parent's lifecycle custody. A copied child binding remains expired even after
a new borrow of the same address. Root retirement also waits for its child;
registering the same support afterward creates a fresh identity. Reused checked
transitions require the exact predecessor; altered evidence is refused.

The protocol neither partitions nor mints ownership, stores memory contents,
or rolls memory back. Its access check additionally requires the exact scalar
pointer and type; normal checked memory producers must still establish their
ordinary authority. Whole scalars are the initial subset: aggregate subranges,
fragment joining, shared aliases and call transport need their own integration.
Regression tests cover nested order, copied stale bindings, disjoint roots,
wrong holders/arenas/types/pointers, missing or replaced supports, duplicate
recovery and stale or altered transitions. A test-only invariant walk checks
the dependency/root indexes. Deterministic measurements at 16, 64, 256 and 1024
unrelated roots bound selected lifecycle operations by persistent indexed
lookups; production transitions do not walk the ledger or resource context.

## Executed scalar-reference boundaries

Rust lowering now attaches private source provenance to the assignment for a
direct mutable scalar reborrow. The ordinary assignment producer emits a
private receipt only after successful assignment, checking the actual parent's
pointer before the assignment against the child's pointer and pointer type
afterward. Failed assignments and ordinary untagged pointer copies emit no
borrow receipt. Source provenance stays outside statement/fact comparison;
rewritten facts discard the receipt.

`CheckedScalarReferenceEnd::bind_executed_endings` joins a completed borrow
receipt with a checked child store immediately preceding the selected ending.
It checks the locked import, function, exact MIR points, parent/child source
bindings, indexed store operation and actual pointer. Both receipts must occur
in order on the same execution path. Exactly one matching birth and ending
must exist on that path; repeated observations are refused instead of being
combined across possible dynamic invocations. Endings after other statement
kinds currently have no execution binding. Neither source labels nor a store
without the selected borrow receipt suffice.

These receipts are execution evidence, not recovery rights. They do not yet
carry a local-reference lease or establish a dynamic invocation identity, and
these receipts cannot activate the private scalar-memory lease adapter below.
Private provenance tags remain comparison-neutral; recovery must additionally establish
the selected operation's membership in the locked source plan. Private
receipt deltas retain each producer occurrence without scanning ambient facts;
the existing 16/64/256/1024 regression now also checks borrow receipts.

## Private scalar-memory lease adapter

The kernel now connects local-reference custody to ordinary scalar memory
execution through a private `CState` adapter. Birth selects a direct owned
occurrence for one external or declared automatic scalar, checks existing
mutex/shared-loan write
restrictions, and removes that owner and its derived memory views from the
ordinary resource context. A private reservation in the ledger retains the exact original occurrence.
A fresh child lease identity travels in the pointer value and through
lvalue evaluation; copying the pointer does not copy its authority into the
public resource frame.

Each child load/store validates the ledger, holder, live child identity, exact
pointer/type and reserved occurrence. It temporarily supplies the selected
owner to the existing memory producer, which still performs its ordinary
checks. A successful store withholds that temporary owner again before
publishing its successor. Recovery retires the child exactly once; nested
recovery restores parent custody, and outer recovery returns the original scalar
owned occurrence, preserving the support identity needed by call receipts.
Only authority changes: the memory after the child's writes remains current.
Expired copies keep their lease and fail even after ordinary ownership returns.

Lease identity participates in pointer value equality/hash/ordering using a
fresh id; language pointer comparison still compares addresses. Local copies,
identity-preserving pointer casts, pointer displacement and `&*child` retain
custody. Displaced or differently typed dereferences fail the exact access
check. Pointer-to-integer escape and storing a leased pointer outside a private
local are refused. Pointer qualifiers, bounds and lease identities share optional metadata so
ordinary unqualified pointers allocate nothing and the pure-fact representation
size limit stays unchanged.

While a lease is active, untagged memory loads require an ordinary owner;
view-only and symbolic-contract-load bypasses cannot read the reserved scalar.
Disjoint owned neighbors remain usable. Calls, aggregate operations, allocation
changes, loop summarization and explicit lifetime retirement are refused until
they have a custody protocol; returning with an outstanding lease is refused.
A maintained holder/root index avoids ledger scans. Kernel execution regressions
cover parent denial, child writes, nested recovery, copied stale aliases, wrong
holders/branches/types/addresses, cast/address preservation and bypass refusal.
Selected adapter operations have a deterministic 16/64/256/1024-owner scaling
regression.

## Source-bound scalar lease execution

Locked lowering now supports exclusive scalar borrow forests on a shared path
through straight-line code and structured acyclic branches. Roots reborrow
reference parameters; nested children
reborrow an existing local lease. Scalar assignments, direct reference copies
and storage events are followed. Unsupported reference escapes, opaque effects,
aggregates, calls, loops and early returns retain their previous lowering and
do not acquire local lease coverage.

A source alias names one borrow node. A reborrow adds a dependency edge; copies
keep the same node, and replacement definitions change only the assigned alias.
The checker records direct uses while traversing the selected function once.
A reverse birth-order pass propagates each subtree's last use to its ancestors.
A single region projection follows the existing checked CFG postdominator
structure. Lexical arm paths and ancestor jumps locate each use's continuation
relative to its borrow definition. Definitions in one arm cannot be used in a
sibling or its enclosing continuation, and an arm cannot overwrite an existing
outer reference binding. Scalar writes, condition reads and local copies are
followed without enumerating paths or cloning alias maps per branch.

For arm-local definitions, lowering emits a sealed scope checkpoint before the
conditional and a checked close on each arm. Nested conditionals use nested
checkpoints. The kernel permits only local-reference registration, borrowing,
recovery and retirement while a checkpoint is open. It records only newly
issued IDs and their checked active count; an entry reference cannot be ended.
At close, every new reference must be inactive and every newly borrowed root's
original owned occurrence must be present. The current holder and exact sealed
scope identity must match. Nonlocal ledger transitions, transport and return
with an open scope are refused.

The scope then marks its statically certified, private arm-local reference slots
uninitialized, including their memory footprints, and restores the exact entry
ledger. This prevents a later abstraction from turning a dead reference into
a fresh ordinary pointer. Local reference IDs use a global fresh counter,
which reconciliation never rewinds; captured stale values still fail lookup.
Memory is not rolled back. Existing live entry references and unrelated loan
state survive exactly. The ordinary join retains its exact-ledger check.
No ambient ledger history is scanned: validation follows the scope's selected
transition delta, new roots and cleanup slots.

Every computed ending follows all uses of the node and its descendants, including
copies and scalar expressions. Frontier identity includes both the block and
statement position; a join-frontier end runs before that block's first statement. Independent regressions compare the resulting
frontiers with the existing single-borrow checker. StorageDead alone grants
no recovery; an unused borrow can end immediately after its checked birth.

Each actual successful borrow assignment reserves the selected owned scalar or
borrows an existing lease. Its semantic birth plan binds exact lowered operands
and checked source membership. Observation labels cannot issue a birth. Nested
leases share one original reservation, rather than multiplying memory authority.
The source key belongs to the individual lease node, not the shared backing.

Lowering emits an explicit `CStatement::EndScalarReference` after the complete
source statement at each checked frontier. Several endings at one frontier are
emitted innermost first. Normal statement sequencing prevents an ending from
running after a failed load, assignment or store. Reads and stores now carry
only read-only observations; recovery is an explicit semantic operation.

An ending's opaque source identity selects a fresh live reference through the
indexed `(holder, source plan)` map in the current invocation. The kernel still
checks the exact holder, active identity, backing occurrence, type and child
dependencies. A parent cannot recover while its child is live. A successful
ending consumes its index entry exactly once. Parent custody returns first;
closing the outermost root restores the original owned occurrence. Current
memory is preserved throughout, and stale copies remain expired. Endings do
not depend on an original child variable or guessed observation history.

Source labels are shared in one immutable family; its precomputed fixed-width
identity and frontier positions form the hot semantic key. Preparation and
execution inspect selected statements and indexed state deltas. Deterministic
16/64/256/1024 regressions cover ordinary source length, alias chains, read
endings, nested depth and repeated shared diamonds, including arm-local scopes. A selected-end regression also bounds execution work
across growing live-handle indexes. Selected scope work is also bounded at
16/64/256/1024 ambient-history sizes (954/1044/1134/1224 map-work units).
No per-borrow whole-function scan is used.

The unchanged native `set_seven`, alias-move and read-ending witnesses activate
explicit end operations. A new native fixture covers shared and separate
nested frontiers, parent reuse, and a modular caller. Kernel tests cover ordered
recovery, missing/foreign/duplicate handles, alias replacement, unsupported
parent access and failed operations. Native proofs include expansion/recheck
and false-value/authority negatives. A native branch fixture covers conditional
writes, nested leases across both arms, parent reuse and a modular caller,
with expansion/rechecking and value/authority negatives. Kernel tests check
an actual join with live custody and refusal of premature parent access,
expired aliases and duplicate ends. Condition reads, later join reads and nested
regions pin common frontier placement.

A pinned arm-scope fixture verifies independent and nested arm-local reborrows,
a local alias and a modular caller, including expansion and value/authority
negatives. Kernel tests check live-close refusal, wrong holders/source scope,
entry-reference preservation, original support, missing ownership, duplicate
close, stale IDs after reconciliation, cleared slots and escaped/cross-arm
reference refusal.

The Rust semantic profile versions this source coverage and the resource
semantics version covers the new kernel operation. Matching existing locks are
rebound without changing source, compiler or artifact hashes.

## Remaining local-reference work

Shared borrow graphs, aggregate fields and reference storage, call transfer,
memory havoc, escaping or conditionally live arm references, writes to outer
reference bindings, early returns and loops still need checked source/runtime
protocols. Functions outside the activated subset retain their existing
lowering. Pinned rustc establishes source borrow legality and does not replace
submitted-sidecar authority checks. Neither observations nor a submitted alias
list grants a recovery right.

## Reproduce the assessment

With the pinned tools activated and `CLICK_CHARON` set to the pinned exporter:

```sh
cargo test --lib rust_correspondence_
cargo test --lib correspondence_calls_production_
cargo test --lib exclusive_call_
cargo test --lib local_reference_
cargo test --lib scalar_reference_
cargo test --lib source_scalar_
cargo test --test rust_import rust_arm_local_borrows_close_without_escaping_before_the_join -- --ignored
cargo test --test rust_import rust_scalar_borrow_stays_live_through_both_branch_arms_and_ends_at_join -- --ignored
cargo test --test rust_import rust_nested_scalar_borrows_end_explicitly_at_shared_and_separate_frontiers -- --ignored
cargo test --test rust_import rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop -- --ignored
cargo test --test rust_import rust_owned_field_parent_can_write_after_explicit_child_drop -- --ignored
cargo test --test rust_import rust_owned_disjoint_mutable_fields_verify -- --ignored
```

The four independent model traces and two production correspondence tests pass;
they establish different claims. The three individually selected native
fixtures cover actual Rust execution and proof checks; the exclusive-call
regressions exercise the integrated production planner and evidence path. No full nightly run is
needed for this assessment. The original
[worked correspondence](rust-resource-correspondence.md) retains its model and
compiler boundaries; this record adds production evidence without treating
compiler rejection as submitted-sidecar rejection.
