# P1: Shared heap graph and resource invariants

## Next task: settle the invariant semantics

The next task is a **design decision**, not another proof-script tweak. Click
needs a precise rule for when a counted resource's declared facts hold, when a
proof may temporarily open that invariant, and which other execution contexts
may observe the resource while it is open. The rule must support both:

1. A sequential, non-thread-safe reference-counted child with ordinary C
   `int32 refs`, as in the frozen probe below.
2. A genuinely thread-safe reference-counted child, using an explicit lock or
   atomic protocol and safe final reclamation. A sequential proof must not
   silently become a concurrent proof.

Decide and document these points before changing contract certification:

- Is a population-wide `fact` required at every C statement, or at defined
  closed-state boundaries? If temporary violation is allowed, what checked
  authority excludes other observers, and what operation must restore it?
- What does holding one `child_ref(obj)` unit let a thread observe while other
  units exist? The current resource body owns the child's allocation and
  object once for the population; it does not describe synchronization.
- At which exact transition does `consumes child_ref(obj)` change the logical
  population count? Distinguish transfer of a unit into a callee, consumption
  by a verified call, and certification of the enclosing function's net
  contract effect.
- What evidence about the population invariant is recorded at that transition,
  and how is it carried across later, demonstrably disjoint C writes and
  memory snapshots? Final certification must check the actual returned
  resource state without assuming an unproved invariant.
- How would the concurrent version protect the C counter, payload access, and
  final free? State the selected memory/synchronization model and the
  relationship to the [P1 concurrency demo](concurrency-demo.md) and
  [broader atomics issue](concurrency-and-atomics.md).

A rule that accepts a resource merely because its unit is absent at return is
insufficient: the remaining population may still exist, and `obj->refs` must
agree with its logical count. Conversely, reconstructing a transition at a fresh
snapshot should not lose already checked evidence from the consuming call.

## Frozen program and current evidence

[`design/shared-heap-probes/shared_parent.c`](../design/shared-heap-probes/shared_parent.c)
is the fixed sequential C regression. It has two independently allocated
parents sharing one child, one branch-on-count `child_release`, both parent
removal orders, allocation-failure cleanup, a read through the surviving
parent, and exact final deallocation. Do not reshape this C to suit the proof.
[`shared_parent.click`](../design/shared-heap-probes/shared_parent.click) verifies
all six modular helper bodies against those bytes. A scratch caller proof
advanced through both detaches and parent frees; its remaining success-path
claim was `out == payload`. The complete lifecycle sidecar is not yet in the
normal gate.

The present certification reducer adds only
`ensures old(p->kid) == old(p->kid);` to `parent_detach`. That tautology makes
contract certification report an unproved
`fact obj->refs == count(child_ref(obj));` of `child_ref` at return. The trace
shows a matching fact at one memory snapshot and the required fact at another;
`p->kid = 0` follows the verified `child_release(kid)` call. The unmodified
helper verifies. A proposition that changes no contract meaning should not
change whether the resource transition is certified.

Code inspection found a specific authority boundary to audit:
`apply_outcome_contract_resources` calls the kernel transition and discards its
returned proof obligations. A path can record `checked_resource_transition =
true` while retaining a `resource population invariant` obligation. The
resource-claim certification shortcut reuses the checked transition, while an
additional pure claim prepares the path and encounters that obligation. Do not
remove the obligation or extend the shortcut until a negative regression shows
that incorrect C counter updates remain rejected. The exact proof failure may
also need sound transport of the post-call fact across the later parent-link
store; investigate that under the invariant semantics chosen above.

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
