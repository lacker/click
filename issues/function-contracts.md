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
  memory refine the same way when both interfaces have a compatible nonempty
  resource transition and compatible unguarded mutable footprints. The check
  uses one symbolic entry memory and one footprint-havoced post memory; a
  callback that promises an exact increment satisfies a progress contract,
  while a callback that also permits no change does not.
- Mutable footprints are covariant: each concrete range must be provably
  contained in a range permitted by the named contract. For load-free guards
  inferred from conditional resources, the concrete guard must imply the
  named guard under the named preconditions. A concrete callback may omit a
  guarded effect or borrow its resource without writing; a weaker guard and a
  larger range are rejected.
- Memory resource transitions refine with an inferred frame. Named input
  resources must provide the concrete requirements; residual ownership and
  scoped borrows are preserved and recombined with the concrete guarantees,
  which must then provide the named guarantees. Constant and symbolic owned
  subranges are accepted, as are concrete subrange views supplied by named
  ownership. Requiring concrete ownership from a named view, extra concrete
  requirements, and missing concrete returns are rejected.
- Unit abstract-token transitions use the same inferred-frame rule. A named
  contract may carry tokens that the concrete callback does not need, and
  named ownership may supply a concrete token view. Token identity remains
  exact in the resource name and arguments; extra concrete requirements,
  ownership from a named view, and consumption of a token promised back by
  the named contract are rejected.
- Unit folded-composite transitions also use the inferred-frame rule. Folded
  composites remain opaque during refinement: names and arguments match
  exactly, and the check never searches or unfolds definitions to satisfy a
  concrete child requirement.
- Distinct field contracts can be packaged in a composite callback-table
  resource, borrowed through verified helpers, and composed in a pipeline
  whose final callback mutates a separately owned resource.
- A closed pure theorem can prove `Contract(&function)` explicitly. Its proof
  starts with `unfold(Contract)`, which introduces arbitrary call arguments,
  and uses ordinary non-execution proof blocks, including `have`, theorem
  application, rewriting, quantifiers, and proof-level `if`. The checker follows the written proof tree;
  it does not enumerate guards or scan project functions. The resulting
  theorem can be applied to introduce the reusable contract fact at a
  higher-order call site.
- A pure theorem may bind a symbolic callback with a nameless C
  function-pointer type such as `step: void (*)(int32*)`, require one named
  contract for it, and ensure another. Unfolding both contracts runs the same
  precondition, postcondition, resource-frame, and mutable-footprint
  refinement judgment used for concrete targets. Applying the theorem
  transports the contract fact for that exact symbolic pointer; certification
  considers only explicitly applied theorem authorities.
- Symbolic nonnegative quantities of owned abstract tokens and nonrecursive
  folded composites participate in the same inferred-frame judgment. A named
  quantity may supply a smaller concrete requirement when the named
  preconditions prove containment; the symbolic remainder is framed and must
  recombine with the concrete output to supply the named guarantee. The
  verifier treats each quantity as one algebraic resource fact and never
  enumerates its units.
- An explicit concrete or abstract refinement theorem may use the ordinary
  `unfold(Predicate)` tactic after opening its contract or contracts. The
  checker then compares the registered predicate body over the same symbolic
  entry and post-call memories as scalar refinement. Every differing opaque
  predicate identity must be opened by a checked proof step, which ordinary
  `simp` may select; direct pointer formation remains opaque.

- Finite sequence comparisons and membership over current and entry memory
  participate in refinement, including concatenation. Selected sequence
  equalities supply their element equalities in linear work. Concrete and
  abstract refinement proofs retain the ordinary resource and effect checks.

- Explicit `executes callback(...)` theorems reuse ordinary one-call execution
  proofs to adapt resource representations. `step(Contract)` selects one
  ownership transition and footprint while supported independent guarantees
  from other applicable interfaces constrain the same call. The first slice
  supports void and return-valued callbacks and reusable implications from
  one or more named source contracts to a named target contract, with ordinary proof cases and
  theorem application. A return-valued step forwards the actual typed call
  result without another source-level proof step. Extra theorem parameters
  remain a future extension of this proof form.

The remaining semantic step is refinement for broader state-dependent
propositions at concrete-pointer formation.
Guarded effects participate in footprint containment, but stateful
postconditions with conditional footprints require an explicit closed theorem
when ordinary logical reasoning is required; automatic concrete-pointer formation remains limited
to an unguarded named footprint. Stateful algebraic,
resource-relation, and explicit-memory-snapshot propositions are not yet part
of refinement. The Linux augmented rbtree regressions below also remain to be
added on top of those general rules.

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
