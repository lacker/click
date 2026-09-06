# Give function-pointer values checked named contracts

Found by the 2026-09-04 MVR audit. Click can dispatch a function-pointer call
when its exact concrete target is known. Calls through abstract callback
parameters are rejected until they carry a checked contract; the earlier
whole-project fallback that enumerated every signature-compatible function was
removed because it was non-modular and scaled with unrelated project state.
Linux's augmented rbtree core is genuinely generic: exported functions
receive an `augment_rotate` callback, and erase helpers invoke `propagate`,
`copy`, and `rotate` through a caller-supplied
`struct rb_augment_callbacks`.

## Implemented first slice

- Exact concrete function-pointer targets continue to dispatch normally.
- An abstract function-pointer call without a behavioral contract fails
  promptly with a source-level diagnostic. It does not scan or branch over
  same-signature functions in the verified project.
- Top-level named `contract` blocks describe pure requirements and guarantees,
  resource transfers, and effect footprints independently of a C body.
- `Contract(pointer)` facts are indexed by the exact symbolic pointer and
  authorize abstract calls through parameters and pointer-backed struct
  fields without enumerating project functions.
- A verified or explicitly external concrete function forms a named contract
  fact when its exact interface matches or its supported pure contract
  behavior refines the named contract. Parameter names are treated as binders;
  named preconditions imply implementation preconditions, and implementation
  postconditions imply named postconditions. Reversed variance is rejected.
- Scalar preconditions and postconditions over current and function-entry
  memory refine the same way when both interfaces have a nonempty exact
  resource transition and compatible unguarded mutable footprints. The check
  uses one symbolic entry memory and one footprint-havoced post memory; a
  callback that promises an exact increment satisfies a progress contract,
  while a callback that also permits no change does not.
- Unguarded mutable footprints are covariant: each concrete range must be
  provably contained in a range permitted by the named contract. Constant and
  symbolic subranges are accepted, while a larger concrete footprint is
  rejected from the published contract rather than inferred from the C body.
- Distinct field contracts can be packaged in a composite callback-table
  resource, borrowed through verified helpers, and composed in a pipeline
  whose final callback mutates a separately owned resource.

The remaining semantic step is refinement for resources, guarded effects, and
broader state-dependent propositions at concrete-pointer formation. Resources
still match exactly; a concrete function should eventually be allowed to
consume no more and return no less. Stateful sequence, algebraic,
resource-predicate, explicit-memory-snapshot, and guarded-footprint
propositions are not yet part of refinement. The Linux augmented rbtree
regressions below also remain to be added on top of those general rules.

## Violated invariant

A call through an abstract function pointer must be checked against an
explicit contract carried by that pointer. Signature compatibility alone
cannot justify its result, memory effects, resource transfers, or preservation
of the rbtree invariant.

## Intended regression

An unchanged rotation helper accepts a callback over two struct pointers,
mutates a small tree fragment, and invokes the callback. Its sidecar requires
the callback to preserve the tree-shape resource while updating only a named
augmentation footprint. Two concrete callbacks satisfying the contract pass;
a callback with an extra write and one that consumes a required resource fail.

A second regression loads three callbacks from a const struct object and
retains the distinct contract associated with each field.

## Acceptance criteria

- Surface Click can declare a contract for a function-pointer parameter and
  for a function pointer loaded from a modeled struct field.
- The contract can quantify over call arguments, name pure pre/postconditions,
  and transfer or borrow ordinary resources and effect footprints.
- Each indirect call checks the callback precondition and applies only its
  declared postcondition and effects; signature matching alone proves nothing.
- Concrete function-pointer formation checks that the target implementation's
  verified contract refines the required callback contract.
- Callback contracts compose through another verified function without
  enumerating all whole-program targets.
- The augmented rbtree callback sites, positive and negative regressions, and
  `scripts/check.sh` pass.

Related: [struct-model.md](struct-model.md),
[global-variables.md](global-variables.md), and
[const-qualified-types.md](const-qualified-types.md).
