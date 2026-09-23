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

## Current status, 2026-09-22

This issue remains open. The frozen C source is unchanged and the normal gate
passes, but there is still no passing sidecar for the full lifecycle. The
current blocker is the lookup of a child reference through a folded parent
resource at a modular call boundary.

Verified and landed:

- `mdtests/child_release_branch_on_count.md` proves the exact branch-on-count
  `child_release`, including the nonempty counted-population obligation on
  the decrement path.
- `mdtests/parent_attach_call_frame.md` proves the attach shape: storing the
  parent link, calling a disjoint retain helper, folding the parent resource,
  and reading through the surviving link.
- `mdtests/shared_heap_detach_old_resource_handoff.md` proves the minimal
  detach handoff with `produces child_ref(old(p->kid))`. Its old-pointer
  lookup is resolved from checked entry-memory evidence, and it no longer
  fails with the stale `child_ref(null@0)` diagnostic.
- `mdtests/shared_heap_detach_leak_diagnostic.md` covers the negative case and
  names both the leaked allocation and the counted resource holding it.
- The call/frame transport and surface diagnostics are covered by the normal
  `scripts/check.sh` gate.
- `mdtests/shared_heap_two_parent_caller.md` now composes two attaches, the
  first detach, a read through the surviving parent, and the final detach.
  This clears the earlier caller-side named-resource transport blocker.
- `mdtests/shared_heap_two_parent_branch_release_positive.md` composes the
  same two-parent sequence with the exact branch-on-count release. The caller
  starts with one creator reference, both attaches retain, the creator and
  first parent release, the second parent reads, and final detach releases.
  The checked counted-resource transition already carries the count change;
  `parent_detach` does not need a pure postcondition that reloads `p->kid`
  after the C body clears it.
- A proof-only unfold after a modular call no longer mutates heap-cell
  initialization metadata as if it were a C store. The new kernel regression
  ensures naming a fresh uninitialized heap cell cannot make it readable.

Still failing to compose:

- The exact frozen `design/shared-heap-probes/shared_parent.c` diamond has
  two allocation-failure paths and two destruction orders, but no passing
  sidecar yet. The latest scratch proof certifies all six helper bodies,
  handles all three null checks in `run_first_destroyed`, composes both
  `parent_attach` calls, and releases the creator reference. Its first failure
  is the subsequent `parent_detach(first)`:

  ```click
  let { link: first_link } = step(parent_attach(first, kid), {});
  let { link: second_link } = step(parent_attach(second, kid), {});
  step(child_release(kid), {});
  let first_out = step(parent_detach(first), { link: first_link });
  ```

  Click cannot evaluate the `child_ref(p->kid)` contract argument because the
  folded parent's field load reports `UninitializedRead`. Unfolding the parent
  in the caller exposes enough checked evidence to prove `first->kid == kid`,
  but refolding and calling detach still gives a different symbolic resource
  argument rather than the held `child_ref(kid)`. The existing contract syntax
  already expresses the required handoff: it consumes the named `parent(p)`
  instance and `child_ref(p->kid)`. Repair entry-state resource-argument
  evaluation so it can use that selected parent's checked, framed
  `p->kid == kid` fact to read and normalize the field to `kid`. The rule must
  depend on the exact owned parent instance and its memory frame; a bare
  pointer or an unrelated equality cannot create a child reference. Regress
  the frozen heap-parent call plus missing-retain and wrong-child cases before
  considering any new contract syntax.
- The separate minimal reducer
  `mdtests/shared_heap_two_parent_branch_release.md` fails while certifying
  `parent_detach` because it asks for a redundant pure count postcondition
  through the field the C body clears. The positive counterpart shows this
  postcondition is unnecessary for the reduced lifecycle. Do not add guarded
  postconditions or a new population-lifetime rule on the strength of that
  failing reducer alone.
- The frozen caller's second destruction order, allocation-failure proof
  fixtures, negative caller regressions, and deterministic scaling fixtures
  remain before this issue can close.

## Completed chunk, 2026-09-21: retain initialization through call havoc

The false undefined-behavior boundary is now fixed in the memory model. A
verified call may invalidate a cached scalar value because its write footprint
is mutable, but it must not turn a cell that was already initialized back into
fresh uninitialized storage. Heap memory now carries bounded typed-cell
initialization metadata separately from cached values; call and interface
havoc preserve it, joins intersect it, stores establish it, and frees remove
it. Typed scalar loads consult that metadata only after the ordinary concrete
cell and established-fact routes.

The kernel regression
`call_havoc_preserves_initialization_of_a_heap_scalar` covers the exact
transition: malloc, store, mutable call havoc, then a typed read. Existing
heap, resource, and shared-parent fixtures remain green. This removes the
first `UninitializedRead` symptom in the shared-heap reduction; the exact
frozen diamond still needs to be rerun and its next genuine proof obligation
recorded before the issue can close.

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

The remaining composition work is at the caller boundary: transport the
initialized parent-link resource into `parent_detach`, preserve the surviving
`child_ref` across `p->kid = 0`, and then wire both destruction orders,
allocation-failure paths, and the negative regressions from the frozen probe.

## Historical minimal detach reduction, 2026-09-18

The detach blocker is now reduced independently of the branch-on-count
release. The following split-release source is only a reducer; it is not a
replacement for the frozen `child_release` body.

```c
struct child {
    int32 refs;
    int32 payload;
};

struct parent {
    struct child* kid;
};

void child_release_nonfinal(struct child* obj) {
    obj->refs = obj->refs - 1;
}

void parent_detach(struct parent* p) {
    struct child* kid = p->kid;
    child_release_nonfinal(kid);
    p->kid = 0;
}
```

The complete Click reduction is:

```click
spec enum ParentLink {
    Empty,
    Linked(struct child*),
}

resource child_ref(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    fact obj->refs == count(child_ref(obj));
}

resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}

verifying "shared_heap_detach_repro.c";

void child_release_nonfinal(struct child* obj) {
    requires 1 < obj->refs;
    owns child_ref(obj);
    consumes child_ref(obj);
} by {
    open(child_ref(obj)) {
        execute();
    }
    simp();
}

void parent_detach(struct parent* p) {
    consumes link: parent(p);
    requires link.link != ParentLink::Empty;
    owns child_ref(p->kid);
    consumes child_ref(p->kid);
    produces child_ref(p->kid);
    produces out: parent(p);
} by {
    match link.link {
        ParentLink::Empty => {
            contradiction(link.link == ParentLink::Empty);
        },
        ParentLink::Linked(kid) => {
            unfold(link);
            execute();
            let out = fold(parent(p), { link: ParentLink::Empty });
            simp();
        },
    }
}
```

The original first failing proof step was the post-state/resource check for
`parent_detach`, not the `child_release_nonfinal` call. With only
`consumes child_ref(p->kid)`, the call fails immediately because the
non-final release contract needs two units: one `owns` unit for the surviving
population and one unit to consume. Adding the `owns` clause lets the call
execute, but function exit reports:

```text
live allocation obligation was neither returned nor freed: `owns allocation(p->kid, 8)`;
held by owns child_ref(p->kid)
```

The corrected handoff is `produces child_ref(old(p->kid))`. The surface
The corrected handoff is `produces child_ref(old(p->kid))`. The surface
resource check now resolves that entry-state pointer from checked viewability
evidence, so the old `missing resource fact owns child_ref(null@0)` failure is
gone. The following diagnostic records the original allocation-lifetime
failure that motivated the fix:

```text
could not prove `produces child_ref(old(p->kid))`: live allocation obligation
was neither returned nor freed: `owns allocation(p->kid, 8)`; held by owns
child_ref(p->kid)
```

The diagnostic now identifies the exact live allocation and the owning
`child_ref` population, and renders the recovered pointer in this leak path
using surface Click syntax rather than an internal pointer expression. The
minimal reducer is now a historical explanation of the original failure; the
current blocker is the caller-side resource transport described above.
