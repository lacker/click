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

## Next chunk, 2026-09-18: one branch-on-count release

The reduced blocker is the single `child_release` in the frozen
`design/shared-heap-probes/shared_parent.c` (`if refs == 1 free else
decrement`). No contract expresses "consume one of an arbitrary population":
`consumes child_ref(obj)` pins the entry population to 1 (the non-final path
then leaks), `owns` plus `consumes` pins it to 2 (the final path then fails).
An explicit `rewrite` of the guard against the body invariant reduces the
final-branch goal to `1 == 2`, confirming the contradiction is in the fixed
prior, not the proof steps.

The regression is `mdtests/child_release_branch_on_count.md` (currently
`expect fail: LiveAllocationLeak` on the non-final path). Two tempting
shortcuts are unsound and must not be implemented: trusting a stored ghost
`count(...) > 0` fact (it goes stale across the decrement and would mask a
final path that forgets `free`), and covering from actual-state counts (a
proof-retained unit masks an orphaned allocation the contract consumed).

Landed support (all in the normal gate): `click verify --allow-sorry` with
`sorry();` as a complete contract or `have` body for reductions; the leak
error names counted families and suggests proving `count(...) != 0`; `let`
-bound constant quantities lower (previously rejected by a leftover wrapper).

Recommended implementation, in order: (a) contract-level quantity binders
that reuse the proven `amount`-parameter paths (surface-scoped; e.g. let the
prior be named), or (b) kernel symbolic prior derived from the body
`field == count(pop)` invariant. Either must keep the pinned test's
final-path free requirement and all negative regressions (double free,
use-after-free, true leak with stale facts) failing. Flip the pinned fixture
to `expect pass` only when the same proof verifies with no `sorry`, and rerun
the full gate: symbolic counts touch every counted contract.
