# P2: Close object-model gaps in supported C++

Priority: P2.

Soundness: soundness-adjacent. Supported access must preserve object type,
initialization, pointer designation and lifetime independently of permission.
The current-master audit below is bounded, not a proof of every admitted path;
no new false acceptance was reproduced. Confirmed false acceptances remain P1
under the repository's soundness policy.

## Goal and current evidence

Make the operations Click already admits compose across calls and resources,
without regressing existing C or Rust. Work from current master, not from the
retired implementation of [PR #646](https://github.com/clicklang/click/pull/646).
The [current-master audit](../design/object-model-current-audit.md) records
source paths, executable witnesses, limits and remaining checks.

Already implemented: pointer subobject bounds and designation, complete pointer
read names, exact construction destinations, initialized/unwritten storage,
initialized output-resource transfer, and the bounded typed/byte representation
rules. These are mechanisms to preserve, not unfinished implementation groups.
Constructed-view getters preserve external backing references through cleanup,
with the original read/write and hostile-contract witnesses checked. The audit
distinguishes checked witnesses from broader claims still needing coverage.

## Remaining work

### 1. Preserve pointer/resource compatibility

[`rb_produces_through_the_root_cell.md`](../mdtests/rb_produces_through_the_root_cell.md)
now verifies with its original C and contract. Its proof states the three
ownership-derived separation facts needed to frame the node's fields across
the root store. Generated prerequisites retain lexical names, typed reads,
and the selected states of pointer arguments. Ordinary verification,
expansion, cold checking and retained replay pass, and storing null is refused.
See the [repair evidence](../design/object-model-current-audit.md#pointer-field-resource-fold-baseline-failure-and-repair).

- [x] Restore the small pointer-field resource-fold fixture across proof modes,
  keeping its C and contract.

- [ ] Check the affected existing descriptor/resource, pointer-field,
  constructor and cleanup witnesses when delivering a remaining slice.
  Pointer identity, extent and the relevant frame must survive calls, resource
  unfold/refold, branches and loops; unrelated writes must not destroy them.
- [ ] Keep ordinary verification, expansion, cold and retained checking in
  agreement. Use existing deterministic multi-size controls for changed hot
  paths, and the required CI/merge-queue checks for delivery. Do not raise
  budgets or weaken contracts to obtain a pass.

Current rbtree refusals have their own
[launch work](rbtree-example.md) and existing bug reports. Reproduce their
current frontier there before attributing one to the object model. In
particular, the pointer-cell representation repair is implemented but its
[original sidecars still need end-to-end closure](../bugs/pointer-field-cells-are-cached-as-words-a-pointer-read-cannot-use.md).
Historical failure counts are not a current defect list for this item.

### 2. Finish the native-interface evidence matrix

For the supported profiles, record what justifies each access at symbolic body
entry and what the actual caller must establish. Cover scalar and record
references/receivers, raw pointers, by-value records, embedded construction,
and pointer/reference results. Use current importer, lowering and shared-kernel
rules; historical archive metadata is not evidence of upstream support.

- [ ] Pair each entry promise with an actual-call positive and rejection
  witness, including subobject bounds, initialized versus unwritten input,
  constness, layout/type and backing lifetime. Credit the existing witnesses
  in the audit before adding tests.
- [ ] Resolve uncovered paths with a checked rule or a specific refusal.
  Establish a concrete admitted source case before changing semantics. A
  signature, byte owner or equal address cannot by itself supply all the
  evidence for access.
- [ ] Publish the resulting supported boundary and assumptions. A separate
  `valid_place` API or the archive's representation is not an acceptance
  requirement; the semantic guarantees are.

### 3. Check modular byte-output composition

The shared `consumes uninitialized(...)` / `produces ...` contract already
expresses body-checked output initialization. Do not rebuild this mechanism.
The selected C++ byte tests separately cover ordinary modular byte writes and
four stores initializing a declared uint32. What remains is their composition:

- [ ] Check a pinned C++ `std::byte*` helper that consumes four unwritten bytes
  and produces them initialized, called with a declared uint32's byte view.
  Prove the exact little-endian word after the modular call.
- [ ] Reject an unwritten byte, missing write permission, a stale observation,
  and a forged byte declaration. Check expansion, cold rewritten verification
  and retained checking for the positive witness.

This small composition is the foundation acceptance case. Bitcoin
`ser_readdata32`, cursor exceptions, broader writable spans and owning containers
belong to [C++ coverage](cpp-support.md); they are not prerequisites for closing
this item.

## Small intended regression

The modular byte-output witness above must read the exact uint32 after the
helper returns, with no initialization assumed merely from ownership or the
value postcondition. Preserve the original source and contract when reducing
a failure. The existing
[C++ scalar initializer](../mdtests/cpp_initializer_produces_written_memory.md)
and [unwritten-output rejection](../mdtests/produces_refuses_memory_the_function_did_not_write.md)
exercise the shared output-transfer prerequisite.

## Acceptance and scope

Close this item when the interface matrix has named evidence or explicit
refusals, the modular byte-output composition passes its positive and hostile
checks, and affected existing C/C++/Rust behavior and proof modes remain checked.
Keep the repaired getter and pointer-field fold witnesses green.
Record any confirmed residual defect at its current reproduction; a missing
coverage check is not itself a demonstrated semantic bug.

Retain typed cells, allocation identities/generations, immutable states and
indexed resource ranges. Keep storage, object/type validity, initialization,
values and access authority distinct. Address equality supports aliasing but
does not manufacture designation. Construction binds the actual destination;
copying does not rebase self-pointers; lifetime end invalidates access to the
backing object. Apply each language's own rules at its frontend boundary.

There is no blanket C++ feature freeze: each new slice must preserve these
invariants and supply its own admission, call and refusal evidence. Broader
lifetime/replacement semantics, union overlap, general inheritance, additional
targets and integer-carried pointer origins are separate coverage work.

The [design record](../design/cpp-object-model.md) preserves the accepted laws
and historical implementation rationale. Recovering the old branch, assigning
all its regressions, reproducing its helper API, or reaching a historical
example count is not a deliverable. History is linked from the current audit.
