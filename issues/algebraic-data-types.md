# Complete general-purpose algebraic data type support

P2: general completeness, not a blanket MVR dependency. The core ADT feature
set already supports ownership-backed tree models and a verified left rotation.
MVR algorithm proofs and the specific integration gaps they expose belong in
[recursive-structure-models.md](recursive-structure-models.md). Promote only
the required slice when a concrete MVR proof needs it. Soundness defects
remain P1 regardless of which program exercises them.

## Implemented baseline

Click has first-class generic and strictly positive recursive ADTs, typed
symbolic variables, constructors, symbolic matches and pure calls, checked
constructor rules, structurally recursive pure functions, same-datatype
induction, and generic theorems checked at arbitrary types. The
[prelude](../stdlib/prelude.click) supplies List and Nat with checked laws.
Pure Click defines symbolic terms; only C executes.

Exclusive resource fields connect these values to concrete ownership.
Guarded and matched bodies, direct recursive children, explicit field and
child selection on folds, path-specific return folds, and entry proof matches
support the unchanged initializer and left rotation in the
[modeled-binary-tree example](../examples/modeled-binary-tree/README.md).
The rotation preserves its exact HeapTree transformation and derived
in-order node list. Unfold consumes the parent; no named open handle remains.

## Remaining generalizations and intended regressions

- **Proof-match generality.** Extend beyond one or two constructors at unchanged
  function entry: wider families, shared continuations, matches after C or
  resource transitions, additional payload sorts, proof prefixes before
  contradiction, and all-impossible matches. Use small cells and three-variant
  enums; reject missing arms, escaping witnesses, sibling-path evidence, and
  contradictions without premises. Preserve symbolic pure-match semantics.
- **Richer resource bodies.** Support mixed or mutually recursive resource
  families, nested guards/matches, general resource if/else, arbitrary
  scrutinees, and child-field equations beyond immediate constructor bindings.
  Small mutually recursive models should fold only with justified finite
  descent, complete ownership, and the selected body's facts. Do not eagerly
  traverse an unknown model. Coordinate with the resource-algebra issue.
- **Field snapshots.** Capture a newly constructed symbolic model at a named
  proof point, unfold its owner, and reuse the captured value in a later fold.
  Preserve capture-time meaning without a live handle; reject stale memory
  claims and unjustified replacement fields.
- **Contract and witness transport.** Extend ordinary inline-call transport,
  concrete-function formation/refinement for resource-parameterized contracts,
  independent child arguments, and algebraic existential witnesses. Check a
  small helper returning an updated model; reject implicit field preservation,
  duplicated ownership, and witnesses escaping their clause or call scope.
- **Pointer constructor literals.** Elaborate contextual null pointers such as
  `Ptr::At(0)` without granting memory authority. Retain the current rejection
  regression until implemented; reject invalid integer-to-pointer formation.
- **Surface ADT resource arguments.** Carry typed symbolic arguments through
  surface declarations and body instantiation, matching kernel support.
  Extend [adt_indexed_resource.md](../mdtests/adt_indexed_resource.md) with
  transfer/substitution checks; retain its rejection until supported. Ordinary
  abstract state should continue to use fields, not extra model arguments.
- **Algebraic quantifiers.** Check arbitrary types and existential witness
  scope across specifications; expression-local ADT let is not existential
  transport. Reject a proof that reuses a witness outside its scope.
- **Mutual induction.** Prove a property across a mutually recursive datatype
  group with correctly typed cross-datatype hypotheses. Reject hypotheses
  for non-descending values. Mutually recursive pure functions already work.
- **Sequence syntax unification.** Elaborate literals, `++`, and `in` to
  List, append, and membership instead of their separate representation.
  Preserve [sequence-transform](../examples/sequence-transform/README.md)
  proofs, including order and multiplicity.
- **Memory-range snapshots.** Project a readable symbolic typed range to an
  exact snapshot List without enumeration. Reject missing readability
  and claims that ignore writes; preserve provenance through old and named
  snapshots.

## Violated invariant and acceptance criteria

A logical value must retain its type and meaning wherever supported, without
accidental restrictions from its representation or proof context. Model values
carry neither runtime storage nor memory authority; a fold must justify its
relation to concrete memory and owned children.

- Each extension above has checked positive and negative regressions, while
  preserving the existing ADT, resource, and unchanged-C proofs.
- Simple checking stays output-sensitive in explicit terms and certificate
  deltas, without scanning or cloning unrelated state. Representation changes
  have deterministic multi-size scaling regressions.
- Expanded proofs recheck, failures remain bounded and actionable, and
  `scripts/check.sh` passes.
- This issue closes when these generalizations are covered, not when MVR
  launches. It does not own additional tree algorithm deliverables.

Integer specification coverage is landed and documented in
[the mathematical-integer internals](../docs/internals/mathematical-integers.md);
the remaining ADT generalizations do not depend on the retired Integer P1
issue. Related: [recursive-structure-models.md](recursive-structure-models.md)
and [resource-algebra-extensions.md](resource-algebra-extensions.md).
