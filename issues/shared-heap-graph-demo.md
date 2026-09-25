# P1: Shared heap graph and resource invariants

## Sequential lifecycles and exclusive opening verified; mutex authority remains

The target semantics are recorded in
[Resource invariants, counting, and synchronization](../docs/internals/resource-invariants.md).
Membership units, authoritative population state, and access authority are
separate. Counted facts hold at closed boundaries. Sequential populations
remain thread confined; mutex and atomic access protocols are later work.

The first implementation checkpoint checks counted invariants at observing
call boundaries and checks returned transition obligations before the surface
records a checked return-resource exchange. It preserves checked partition
evidence across a consuming call so a later disjoint store can transport the
population invariant. The tautological-ensure reducer now passes in the
normal gate, as do regressions rejecting broken call-entry invariants and
wrong count updates. Sequential opening now suspends access independently of membership.

The release expansion blocker is fixed. Every completed path now applies
its checked return-resource exchange, including a simple proof of a consuming
contract with no returned resource claim. All 18 smart sites in the six
unchanged helpers pass expansion, independent rechecking, and audit. The
regression `shared_population_release_expansion_retains_lifetime` preserves
the frozen source; `population_simple_exit_rejects_final_leak.md` ensures a
simple closer still rejects an omitted final `free`.

Initialization support is implemented explicitly: `child_ref` promises
`defined(obj->refs)` and `defined(obj->payload)`, and parent links promise a
defined pointer. These facts retain checked ownership/loan dependencies and
cross only typed no-write memory edges with unchanged lifetime metadata.
Failed allocation resolution now records such an edge. The complete positive
`population_initialized_cleanup.md` regression covers both allocation results;
`shared_heap_population_initialized_body_gap.md` intentionally omits the
initialization contract and remains rejected.

Unknown pointer reads from fresh heap/temporary storage no longer inherit
the storage block's provenance. They use opaque load identities, while a
known stored pointer retains its actual target. This prevents a parent's
child-pointer field from being structurally separated from the child merely
because the parent and child are different allocations. The focused positive
and negative `heap_pointer_field_*` fixtures cover modular stores; the full
caller proofs below now verify.

The payload bridge and final population accounting are fixed.
`mdtests/shared_heap_population_lifecycles.md` embeds the frozen C and both
complete callers. Proved argument aliases now use the same ledger key for
Count observations and transitions, including final removal. All eight claims
pass all 42 expansion/reverification sites. No C changes were needed.

Sequential scopes now carry checked exclusive access and restoration identities.
Nested/aliased opens and population-based callbacks during an open scope are
rejected; explicit body-piece helper calls remain supported. The next design
work is composing mutex guards with declared resources, then shared and atomic
access protocols. Membership alone still
must not authorize concurrent access. The sequential result is not a mutex or
concurrent-reclamation proof.

## Frozen program and current evidence

[`design/shared-heap-probes/shared_parent.c`](../design/shared-heap-probes/shared_parent.c)
is the fixed sequential C regression. It has two independently allocated
parents sharing one child, one branch-on-count `child_release`, both parent
removal orders, allocation-failure cleanup, a read through the surviving
parent, and exact final deallocation. Do not reshape this C to suit the proof.
[`shared_parent.click`](../design/shared-heap-probes/shared_parent.click) verifies
all six modular helper bodies and both complete caller lifecycles against
those bytes, including the payload claim and final resource certification.
The positive lifecycle fixture runs in the normal gate.

The certification reducer adds only
`ensures old(p->kid) == old(p->kid);` to `parent_detach`. It previously lost
the checked population invariant across the later `p->kid = 0` store. The
positive `shared_heap_population_certification.md` regression now verifies
all six helpers with that ensure. The helper-side repair is not evidence
that the complete caller lifecycle or concurrent use is verified.

The existing [resource documentation](../docs/concepts/resources.md) says a
population body belongs to the population as a whole and that retain/release
must preserve it. Its `open(resource) { ... }` proof scope restores the body at
scope exit. The frozen probe uses ordinary non-atomic C, and Click's selected
pthread model does not yet establish a concurrent shared-heap protocol.

## Required positive and negative regressions

- Verify the unchanged sequential helper contracts and both complete caller
  lifecycles, including allocation failures, surviving-parent payload reads,
  and exact final free.
- Add the tautological-ensure reducer to the normal gate. It must have the same
  resource verdict as the helper without that ensure.
- Reject a release that removes a logical reference without the required C
  counter update, a missing retain, duplicate units, a premature free, a
  double release, and a read after final release.
- Preserve the invariant across a disjoint parent-link write using checked
  memory/resource evidence; reject transport when that write may alias the
  child's counter or payload.
- Specify and exercise a thread-safe reference-count design under an explicit
  supported synchronization model. Reject an unsynchronized plain-`int32`
  shared counter and unsafe final reclamation. This may depend on work in the
  linked concurrency issues; record the dependency rather than treating the
  sequential fixture as a concurrency proof.
- Keep the resource rules general to counted populations and independent
  parents, not this struct layout or two-parent count. Add deterministic
  scaling checks for more parents and unrelated live graph resources, as
  required by the [efficiency contract](../docs/internals/verification-efficiency.md).

## Completion criteria

Publish the invariant/observation/transition semantics first. Then repair the
kernel and certification boundary with focused positive and negative fixtures;
verify, expand/reverify, profile, and audit the frozen source; and pass
`scripts/check.sh`. Delete this issue and its list entry only after the design,
implementation, regressions, and full lifecycle proof land. Preserve the
frozen C and use Click contracts, tactics, or kernel rules for proof work.
