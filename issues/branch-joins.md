# Make branch joins preserve explicit checked interfaces

## Status

Shared-continuation C branches have the right broad model: the two temporary
arm proofs rejoin behind one checked continuation frontier, and
`branch ensuring` supplies an explicit interface when their concrete states
differ. The implementation does not yet give that model one precise ownership
boundary.

The motivating failure is `proof_branch_composite_resource_transform.md`.
Both arms fold `ready_bundle(key)`, the interface exports
`owns ready_bundle(key)`, and the continuation explicitly executes
`observe(ready_bundle(key))`. During a two-arm interface join, however, Surface
eagerly applies part of the composite observation law and inserts

```text
ready_bundle(key) contains ready_permit(key)
```

before the explicit `observe`. The typed kernel join artifact recognizes the
listed pure fact and exported ownership but not this unlisted projection, so it
declines the join. Its error is ignored and ordinary verification later reruns
the whole C body as a fallback. A decided one-feasible-arm interface does not
run the same eager observation, so the meaning of one surface form currently
depends on branch feasibility.

This issue makes the join boundary explicit and gives resource observation its
own retained kernel evidence. It is a focused proof-composition cleanup, not a
new branch syntax or a general redesign of resources.

## Violated invariant

A shared-continuation branch join must publish exactly one kernel-checked
successor interface. Its meaning must not depend on whether one or two arms
were feasible, and it must not acquire facts from an unrelated implicit proof
operation.

For a branch rooted in context `R`, with continuing arm contexts `A` and `B`,
the joined context should contain only:

- the exact root facts, whose kernel propositions retain their original
  symbolic and snapshot meaning;
- exact propositions independently introduced and still available in both
  arms;
- pure `ensuring` assertions checked in both concrete arms and at the one
  deterministic abstract successor;
- exact residual resources common to both arms;
- explicitly exported resource assertions, checked in both arms and
  normalized into one successor representation;
- locals whose values agree in both arms, plus fresh abstract values for
  differing locals constrained by the explicit interface; and
- common snapshots and other metadata whose merge policy is explicitly
  presentation-only or kernel-checked.

The join must not compute general logical closure or project a composite
resource body merely because the composite is exported. Immediate algebraic
consequences intrinsic to the exact resource fact must be distinguished from
definition-driven observation. In particular, owning a composite may remain
folded across the join; its declared facts, immediate contained views, and
containment/separation propositions appear only when an explicit checked
`observe(resource)` performs that one-layer projection.

For the motivating example, the continuation immediately after the join
should have approximately:

```text
local selected = an abstract value
fact selected == key
owns ready_bundle(key)
```

Only the following explicit `observe(ready_bundle(key))` should add the
bundle's immediate declared facts, containment relations, and duplicable
contained views.

## Join taxonomy and scope

Do not force one merge law onto every operation currently described as a
join:

- A plain nonterminal C `branch` is an exact join. Its continuing arm states
  must be identical; it retains exact common arm facts and resumes the shared
  continuation.
- `branch ensuring` is an interface join. It may abstract differing locals,
  memory, and resource representations, but only through its checked explicit
  interface and deterministic common-state rule.
- A condition with one kernel-feasible arm is path selection, not a two-arm
  merge. It retains the selected concrete state, while applying the same
  interface assertions with the same observation policy as the two-arm form.
- A terminal C branch does not join two C states. It retains separate checked
  return paths under one finished proof frontier.
- When one C arm returns and the other reaches the shared continuation, the
  returned path is not merged into that continuation state. The continuing
  arm advances privately to function exit before terminal path aggregation;
  this existing distinction should remain explicit.
- Proof-language `if` and `cases` close two proofs of the same goal. Their
  kernel split identity and completeness checks are already the appropriate
  rule; they do not create a shared C successor state.
- A loop proof establishes initialization, preservation, effect, exit, and
  termination obligations. It is not a branch-state join and is out of scope.
- Nested `have` and resource scopes restore a parent proof after checking a
  scoped operation. They are out of scope unless they use the branch-join
  machinery or expose the same evidence-loss bug.

## Audit findings and decisions

### 1. Composite observation is fused into the two-arm interface join

`apply_branch_interface_with_proof_facts` applies the composite observation
law while constructing an abstract two-arm interface. That creates unlisted
pure facts and viewed child resources. The decided-interface path returns
before this abstraction phase and therefore behaves differently.

Remove definition-driven composite observation from the join. Preserve only
the explicit composite resource fact and any precisely documented intrinsic
resource-algebra core. Audit memory ownership, loadability, quantities, and
owned-to-view coercion separately so this change does not accidentally require
`observe` for facts that are part of the resource fact's basic algebra rather
than its composite definition.

### 2. `observe(resource)` lacks retained kernel execution evidence

`observe` is already an explicit deterministic simple proof step. Its Surface
implementation checks a held resource and computes a one-layer projection,
but the execution evidence trace does not retain a typed kernel observation
artifact. Quantity observations retain individual kernel theorems; ordinary
composite projections do not have the equivalent proof-object evidence.

Add a checked observation artifact tied to the exact input state, held
resource fact, registered kernel composite definition, output resource delta,
and pure-fact delta. Final execution sealing should consume that artifact and
promote only its validated public fact delta. Observation work must remain
proportional to the projections actually declared by the one observed
resource; it must not scan or recursively expand unrelated resources.

### 3. Interface artifact retention is optional and diagnostically invisible

The Surface join ignores `record_interface_branch_join` failure and continues
with an independently checked fallback. The test-only
`CHECKED_EXECUTION_INTERFACE_JOINS` counter increments after the attempt even
when no artifact was retained. Tests can therefore report a "checked join"
while finalization still executes the C body again.

Covered interface shapes must either retain the typed kernel artifact or fail
at the join with a local actionable diagnostic. During migration, a genuinely
unsupported shape may use an explicitly measured fallback, but an attempt must
not be counted as successful retention. The transformed-resource regression
must directly require zero whole-body executions.

### 4. Semantic successor construction is split across Surface and kernel

The kernel checks branch identity, exact source arms, exhaustiveness, arm
traces, deterministic abstraction, interface facts, and resource
availability. Surface still assembles the complete successor `CState`,
`ProofFacts`, resource context, and metadata, then publishes that merged value
through a generic frontier-join operation whose kernel container validates
lineage rather than the semantic merge.

Make the checked join result the authority for the semantic successor delta.
Surface may retain syntax, source locations, and printable arm certificates,
but it should not be able to add an unvalidated semantic fact or resource
between the checked artifact and the published frontier. This can be done
incrementally; it does not require converting every proof rule into a new
kernel evidence type.

### 5. Arm metadata merge policies are duplicated and partly undefined

Interface, exact, and terminal joins separately migrate effect facts, entry
prerequisites, derivations, unfolded-predicate names, loop proofs, snapshots,
and presentation cursors. The duplication has already drifted: the exact join
currently invokes `migrate_arm_loop_proofs` twice.

Unfolded-predicate names are unioned across either arm for exact and terminal
joins, reset to the parent set for an interface join, and inherited from the
sole arm for a decided path. Decide whether this set is semantic authority or
only a planning/presentation hint. If it is semantic, an arm-local unfold
cannot silently become common; if it is presentation-only, move or document it
accordingly. Then centralize each shared arm-metadata policy so the join
variants cannot drift. Remove the duplicate loop-proof migration as a
nonsemantic cleanup.

### 6. Scaling coverage does not cover every material join cost

Existing regressions cover persistent fact allocation, fork-local snapshot
merging, transformed resource contexts, and successive joined branches. The
interface abstraction still discovers stable locals by scanning locals and
compares/clones non-scalar memory across sibling states. Terminal path
aggregation deduplicates outcomes by a linear search over previously retained
paths.

Add deterministic work curves before changing these representations:

- sequential interface joins with many unrelated locals and memory cells;
- joins with a small explicit resource interface and a large unrelated
  resource context; and
- terminal joins with increasing retained outcome-path counts.

If a curve is superlinear in unrelated state or path count, introduce indexed
fork deltas or keyed outcome deduplication. Do not add speculative caches or
deep-structural cache keys.

### 7. Documentation blurs intrinsic resource consequences and observation

The resource documentation correctly says that owned composites require an
explicit one-layer `observe`. The branch documentation also says that
"deterministic consequences" of listed resources remain available, including
loadability and an ownership view. Clarify that statement so it covers only
the documented intrinsic algebra of the exported resource fact. It must not
be read as permission for a join to observe a composite body implicitly.

## Intended regressions

Add small deterministic tests that establish all of the following:

1. Immediately after a two-arm `branch ensuring`, an exported folded
   composite is owned, while its body fact, containment proposition, and
   immediate child view are absent unless they were independently explicit
   common facts.
2. `observe(composite)` adds exactly one checked projection layer and retains
   a kernel observation artifact. Nested projections require repeated
   `observe` steps.
3. The same interface has the same fact/resource projection policy when one
   arm is infeasible and when both arms are feasible.
4. A fact independently introduced in both arms survives; an arm-only fact,
   snapshot, resource, unfold marker, or derived view does not gain common
   authority.
5. Exact common residual resources survive, while differently transformed
   ownership survives only through an explicit resource interface.
6. A forged observation fact, child resource, containment relation, changed
   memory, or mismatched composite definition is rejected by the kernel at the
   producing operation.
7. `proof_branch_composite_resource_transform.md` verifies with zero checked
   whole-function body executions after its explicit arm steps.
8. The deterministic scaling curves above remain approximately linear, up to
   logarithmic persistent-index factors and work proportional to explicit
   interface and projection output.

## Acceptance criteria

- The shared-continuation join law and its distinction from terminal,
  logical, decided-path, and loop operations are documented precisely.
- A join publishes no composite-definition projection that was not already an
  exact common fact or produced by an explicit checked `observe`.
- `observe(resource)` retains typed kernel evidence for its exact one-layer
  pure and resource delta.
- One-arm and two-arm `branch ensuring` use the same interface semantics.
- The kernel-checked interface artifact, rather than a later whole-body
  execution, authorizes the published semantic successor.
- Artifact-retention diagnostics count success rather than attempts, and a
  covered artifact failure is local and actionable.
- Arm metadata uses one documented merge policy per metadata class; the
  duplicated loop-proof migration is removed.
- No new surface syntax is required, existing C remains unchanged, and any
  proof that relied on implicit composite observation is repaired with an
  explicit `observe` rather than a C change.
- Join and observation scaling regressions satisfy the repository's
  verification-efficiency contract.
- `proof_branch_composite_resource_transform.md` seals without a C-body rerun,
  documentation describes the implemented rules, and `scripts/check.sh`
  passes.

## Relationship to double execution

This issue owns the branch-interface and observation cleanup. The broader
`double-execution.md` issue continues to own removal of all independent body
execution and opaque-contract fallbacks. Once the regressions here retain
complete typed evidence, the branch-related fallback should be removed there
rather than replaced with another cache or hidden certification pass.
