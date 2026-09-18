# P1: Shared heap graph demo

## Objective and violated invariant

Requested on 2026-09-15 as a before-launch architecture milestone. Verify a
small sequential C lifecycle in which two independently managed parent objects
retain the same heap child. The pointer graph and the ownership accounting
must compose without duplicating the child's storage or freeing it while a
remaining parent can access it.

The [refcount example](../examples/refcount/README.md) already checks a single
object's reference-count lifecycle, including final release. This milestone
tests composition of references inside other owned objects. It is not another
isolated counter demo. Rbtree remains the main launch demo.

## Intended regression

Use a child with a payload and a reference count, and two separately allocated
parents containing pointers to that child. Each parent owns one logical child
reference. Attach/retain the child to both parents, release any temporary
creator reference, destroy one parent, read the payload through the surviving
parent, then destroy the remaining parent. Prove the payload read is valid and
has its specified value, and that final release frees the child exactly once.

Both destruction orders must verify. The final state discharges all parent and
child allocation obligations. Account for ordinary allocation failures and
partially constructed parents: failure must preserve the resources still held
by the caller and release only successfully acquired temporary resources.

Choose small ordinary C and freeze it before sidecar development. A synthetic
diamond-shaped graph is acceptable when identified as such. Do not clone the
shared child, replace sharing with a tree, split a normal branch-on-count
release routine into proof-selected final/nonfinal C entry points, or add
proof-only branches and locals to make verification pass.

## Required modular model

- Build on ordinary composite resources and counted reference populations.
  The child's allocation and payload are owned once for the population; each
  parent carries a conserved reference capability, not another copy of the
  underlying allocation or exclusive memory resource.
- Give retain/release and parent creation/destruction body-independent
  contracts. A parent operation may use the reference it owns without exposing
  or consuming references held by unrelated parents.
- A pointer value alone does not create a logical reference. Copying an owning
  parent descriptor does not duplicate its capability. Incrementing the C count
  must correspond to a checked logical change, with overflow excluded.
- Final release requires evidence that no references remain; an equality in a
  local memory snapshot cannot replace population conservation. Restore the
  correct remaining resources on every nonfinal path.
- Use a generic resource/protocol construction rather than a kernel rule
  specific to two parents, this struct layout, or a particular release order.
  Shared references can be packaged and transported through modular calls.

## Negative regressions

- Omit a retain when attaching the second parent: its claimed reference cannot
  be constructed and the later lifecycle must not verify.
- Drop the first parent and free the child while the other parent's reference
  remains: reject the free and any claimed final-release proof.
- Duplicate a parent/reference resource by folding, copying, branch joining,
  or a produced call postcondition: reject the extra authority.
- Double-release a reference or dereference after final release: reject using
  the exact missing capability or retired allocation identity.
- A failing parent creation must not consume another parent's reference or
  publish ownership of uninitialized parent fields.

## Acceptance criteria, scaling, and dependencies

- The original two-parent lifecycle, both destruction orders, allocation
  failure paths, and modular helper bodies verify through ordinary Click.
  The surviving parent read and exact final deallocation are proved, not
  assumed in an unverified release contract.
- All negative regressions fail for their intended local reasons. Preserve
  existing refcount, borrowing, arena, and tree regressions.
- Any resource-language extension is general, kernel-checked, and documented
  with conservation laws. Reuse existing population machinery if sufficient;
  first reduce a failure before proposing a new ownership-collection primitive.
- Verify, expand/reverify, profile, and audit agree on the original C using
  the shared bounded engine. Record source provenance and supported profile.
- Add deterministic scaling regressions at four or more sizes: increase the
  number of parents sharing a child, then increase unrelated live graph
  resources around a fixed retain/release. Local updates must not traverse all
  incoming pointers, all holders, or every graph node. Destruction of a whole
  graph may pay for the nodes and edges it actually releases, as specified by
  the [efficiency contract](../docs/internals/verification-efficiency.md).
- Positive and negative fixtures join the normal gate; `scripts/check.sh`
  passes. Delete this issue and its list entry once implementation,
  regressions, and durable documentation land.

This uses sequential ownership and does not depend on concurrency, C++, goto,
or completion of the arena example. Coordinate general resource changes with
[arena ownership](arena-resource-ownership.md) and
[resource algebra extensions](resource-algebra-extensions.md). Cyclic garbage
collection, weak references, concurrent reference counting, shared mutable
payload protocols, and arbitrary cyclic-graph proofs remain deferred. The
small diamond establishes sharing, not cycle reclamation. Follow `AGENTS.md`
when proof tooling exposes a blocker.

## Current status, 2026-09-18

The first verifier chunk is green, but the complete frozen two-parent lifecycle
is not finished. The companion encoding is the supported shape for the next
steps: each parent owns its link cell and keeps a top-level `child_ref(kid)`
unit; the parent resource does not nest the memory-bearing counted family.

Landed and covered by the normal gate:

- `mdtests/child_release_branch_on_count.md` proves the single C
  branch-on-count release, including the explicit nonempty-population goal on
  the non-final path.
- `mdtests/parent_attach_call_frame.md` covers attach, a disjoint retain call,
  the post-call parent fold, and a payload read through the companion link.
- The call/frame transport now resolves a pointer-valued load through the
  checked memory-DAG history when the call excludes that cell. The fallback is
  scoped to explicit resource-body pointer facts; unrelated general fact
  discharge does not gain a new search route.
- `scripts/check.sh` passes, including the full unit, integration, example,
  and mdtest gates.

The full frozen `shared_parent.c` diamond is still open. In particular, the
parent-detach path decrements a counted child reference and then clears
`p->kid`; the surviving counted unit must still be returned under the old
child pointer. The current companion representation cannot express that
post-state handoff, and attempts to close it fail with a live-allocation or
resource-population obligation. No parent resource nesting workaround was
accepted.

## Completed chunk, 2026-09-18: one branch-on-count release

The reduced blocker is the single `child_release` in the frozen
`design/shared-heap-probes/shared_parent.c` (`if refs == 1 free else
decrement`). It is now covered by
`mdtests/child_release_branch_on_count.md`: the counted population is kept
symbolic from its `field == count(pop)` invariant, and the non-final path
proves the post-transition obligation explicitly with
`have count(child_ref(obj)) != 0`.

The implementation deliberately defers that nonempty-population obligation
until result-aware post-execution facts are available. Allocation coverage is
still granted only when the live counted population body actually contains
the allocation; a stale ghost count or a proof-retained unit cannot suppress
the final-path free requirement.

The leak error names counted families and suggests proving
`count(...) != 0`.

## Completed chunk, 2026-09-18: disjoint-call load transport

The focused `parent_attach_call_frame` regression also verifies the formerly
blocked shape where `parent_attach` stores `p->kid`, calls `child_retain(kid)`,
and only then folds `parent(p)`. The pointer-valued `p->kid` fact is recovered
from the checked memory-DAG call frame because the retain call excludes that
cell. Calls that may write the field do not receive this transport.

The remaining next chunk is the parent-detach handoff: preserve the surviving
`child_ref` and its allocation under the pre-store child pointer while the
parent link transitions after `p->kid = 0`. Then wire both destruction orders,
allocation-failure paths, and the negative regressions from the frozen probe.
