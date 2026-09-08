# Add algebraic data types to specifications

MVR dependency. Complete first-class use of symbolic algebraic data types in
resources, contracts, and collection models. The pure ADT foundation is
implemented; the immediate target is connecting the pure tree model to
ownership of the unchanged C tree.

## Current capabilities

- Rust-like generic `spec enum` declarations with sum-of-products constructors,
  nested fields, and regular strictly positive recursive datatype groups.
  Recursive groups must admit finite values.
- First-class `ClickType` parameters for pure functions, predicates, and
  theorems, algebraic pure-function results, and expression-local typed or
  inferred `let` bindings.
- Arbitrary typed symbolic ADT variables, constructor terms, symbolic matches,
  and opaque pure-function applications. Constructor schemas are shared;
  unknown recursive values are not expanded into trees of possible fields.
- Checked constructor formation, disjointness, congruence, injectivity, and
  exhaustive matching with scoped typed field bindings.
- Structurally recursive pure functions, including multiple recursive fields
  and mutually recursive groups. Explicit `unfold` exposes one defining
  equation. Structural `induct` checks constructor cases and provides hypotheses
  for immediate recursive fields of the same datatype.
- Generic pure functions and predicates with call-site type inference. Generic
  theorem bodies are checked at declaration using rigid arbitrary types;
  applications also use checked, cached concrete instantiations. Generic proof
  expansion and rechecking are supported.
- The [prelude](../stdlib/prelude.click) supplies `List<T>`, append, membership,
  and their checked generic laws; `Nat`, addition and its identity, successor,
  associativity, and commutativity laws; and Nat-valued `list_length` with its
  constructor and append-length laws.
- The [modeled-binary-tree example](../examples/modeled-binary-tree/README.md)
  defines an example-local `Tree<T>`, Nat-valued `tree_size`, and `tree_mirror`.
  Checked generic theorems prove mirror involution and size preservation.
  These are pure-model proofs only: there is no `tree_at(root, model)` resource
  and no verified C function contract in that sidecar yet.
- The [sequence-transform example](../examples/sequence-transform/README.md)
  verifies fixed-size copying, concatenation, reversal, and membership using
  sequence literals. Its C remains unchanged.
- Kernel resource identities and population keys accept typed C or symbolic
  ADT arguments in shared immutable storage. Kernel tests cover arbitrary
  indices, equality-justified transfer, type and constructor distinctions,
  linear ownership, counts, pointer/scalar substitution inside models, and
  deterministic scaling. A model index itself grants no memory authority.
  This is kernel support, not surface resource declarations or C contracts.
- Resource bodies accept leading `field name: ClickType;` declarations,
  including multiple fields and nested generic ADTs. Field declarations are
  type-checked and retained as shared kernel-checked schemas. Field-bearing
  resources are non-countable: `count(...)` and quantity clauses reject them.
  [resource_fields.md](../mdtests/resource_fields.md) checks declarations only;
  instance use and field establishment remain explicitly unsupported.
- The kernel has a separate exclusive instance representation with identity,
  shared typed field state, equality-checked linear transfer, and indexed
  lookup. It rejects duplicate identity, views, and counted quantities.
  Kernel spec projections distinguish current state from an explicitly supplied
  entry snapshot; ownership alone does not prove preservation. Fields and
  arguments grant no memory authority. Kernel tests cover these rules,
  substitution, and deterministic multi-size scaling. This does not yet expose
  named instances or field projections in Click source.

Pure Click expressions define symbolic terms; only C executes. A pure `match`
does not automatically split a proof or introduce proof-scope bindings.
Explicit proof control provides case reasoning. `normalize() using { ... }`
checks conditional reductions against explicitly cited premises.

## Current gaps

- Surface resource parameters still reject ADT values. Kernel resource
  identities support them, but resource specifications still use C
  expressions/types and composite definitions use C parameters. Surface
  lowering, C-contract model inputs/outputs, and checked body instantiation
  must carry symbolic arguments without encoding them as C values. C-only
  body evaluators reject a model argument rather than treating it as a scalar.
- Resource fields cannot yet be bound, projected, established, or updated in
  ownership proofs. Field-bearing declarations must not enter the legacy
  counted/composite instance representation with their fields erased.
- Resource bodies support one load-free `if` guard with an empty false case,
  but no `else` or constructor `match`. Resource-body witnesses are restricted
  to C pointers, so they cannot bind existential child models.
- Algebraic quantifiers and the model-binding/transport path needed by C
  contracts remain unfinished. Expression-local ADT `let` support does not
  establish this resource/contract functionality.
- Mutual structural induction is not implemented, although mutually recursive
  datatypes and pure functions are supported.
- Sequence literals, `++`, and `in` still use a separate internal sequence
  representation. This limitation applies to that syntax, not to ADTs in
  general. The syntax must elaborate to the library's `List<T>`, append, and
  membership rather than remain a second logical collection universe.
- Symbolic typed-memory-range projection to a snapshot `List<T>` is missing.

## Agreed resource design and next implementation steps

Resource definitions should expose typed pure fields, such as `contents` or
`model`, accessed through named owned instances. There is no special single
model field: a resource can have several fields. Resources with fields are
non-countable and exclusively owned. Identity, abstract state, and ownership
must remain distinct; equal field values do not make two instances identical.
Field-free resources retain their existing counting rules.

Bodies should relate those fields to owned memory, including by constructor
`match`, just as they can already define conditional bodies with `if`. This
is a logical definition, not runtime execution or an instruction to traverse
a model automatically.

Implement and check the following slices in order:

1. **Resource fields and instance binding.** Declaration parsing, type checking,
   shared kernel schemas, rejection of counting, and the exclusive kernel
   identity/field-state representation are implemented. The agreed binding is
   `owns cell: marked_cell(p);`, with current `cell.model` and entry-state
   `old(cell.model)` projections. Wire these into source contracts and checked
   fold/unfold; field establishment/update syntax remains deferred. Check a
   small nonrecursive resource with an arbitrary field
   value, not only concrete constructors. The earlier kernel symbolic-index
   infrastructure remains available but does not implement instance fields.
   [adt_indexed_resource.md](../mdtests/adt_indexed_resource.md) records the
   current exact declaration-level rejection for `marked_cell(p, mark: Mark)`.
   Keep that unsupported-parameter diagnostic until the parameter path is
   supported. Add the intended arbitrary-state read/return proof using named
   resource fields, with meaningful negative transfer tests.
2. **Checked resource `match`.** Check exhaustive constructor arms and their
   scoped typed fields. Fold/unfold selects a justified arm and exposes only
   its immediate owned resources and pure facts. An unknown model remains
   opaque until explicit proof evidence establishes the relevant case; no
   operation eagerly unfolds the whole recursive value. Recursive definitions
   must retain a checked finite, well-founded interpretation.
3. **Contract model bindings and the heap relation.** Support typed symbolic
   models and necessary witnesses across function entry and exit. Define
   a tree resource with a model field in the existing modeled-binary-tree
   sidecar. Its empty
   case requires a null root; its node case owns the node fields, relates the
   payload to memory, and contains disjoint resources for the two child models.
   Record node identities as well as stored values, without granting ownership
   merely because a pointer occurs in a model. Keep the tree model example-local.
4. **First end-to-end C proof.** Verify unchanged `tree_node_init`: ownership of
   the supplied node fields and two modeled child trees becomes ownership of
   the correctly modeled parent. Require a nonnull, separately owned parent;
   neither child can be duplicated or overlap it.
5. **Structure-level proofs.** Continue with rotations and traversals under
   [recursive-structure-models.md](recursive-structure-models.md). That issue
   owns the exact node/in-order preservation and subsequent insert/erase
   regressions. Iterative structural termination is tracked separately in
   [structural-loop-termination.md](structural-loop-termination.md).

Resource `match` and the modeled C contracts remain unimplemented. The kernel
identity tests and existing pure tree proofs must not be reported as
verification of the C tree.

### Agreed binding; deferred field establishment

The agreed contract syntax is `owns cell: marked_cell(p);`. It binds the
exclusive instance entering and leaving the function. `cell.model` denotes
its current field state, while `old(cell.model)` denotes its entry state.
Returning the instance does not itself promise unchanged fields: that requires
a postcondition such as `ensures cell.model == old(cell.model);`.

The next implementation must connect these source bindings to checked
ownership and body unfolding, preserving binder scope across calls and keeping
function-entry snapshots distinct from loop-entry snapshots. The intended
first C regression is an unchanged `return *p;` function using a field-bearing
cell resource, with a proof that returns the same instance and preserves an
arbitrary `Mark` field. Missing ownership, a different instance, or an unproved
field change must fail.

Syntax for initially establishing or changing fields remains deferred. Fields
are ordinary symbolic Click values, not freely assignable ghost storage.
No field value itself grants memory authority. A model change must
re-establish the resource's relation to the concrete memory.

The existing contract `let ... where` introduces separate existential witnesses
per clause; it must not silently become a shared instance binding. Do not
replace arbitrary-state proofs with concrete-only models or add ghost C arguments.

## Violated invariant

An immutable logical value must preserve its type and meaning wherever a
specification needs it, including resource arguments, witnesses, quantifiers,
and function contracts. A heap model must be justified by the owned structure,
not an unconstrained ghost assertion. Model values carry neither runtime
storage nor memory authority.

## Intended regressions

- A model-indexed resource can be transferred with an arbitrary ADT argument;
  wrong types and a changed, unproved model argument are rejected.
- Resource matching accepts exhaustive typed arms and rejects missing or
  duplicate constructors, wrong field types, escaping binders, and unchecked
  branch selection. Fold/unfold certificates reject tampered models or facts.
- The unchanged `tree_node_init` verifies with the exact parent/child model.
  Claims with a wrong value, swapped children, or a duplicated nonempty subtree
  fail; possessing a pointer in a model alone must not authorize a C load or
  store.
- Algebraic quantifiers preserve arbitrary types and witness scope. Mutual
  induction checks the appropriate hypotheses across a recursive group.
- Sequence syntax elaborates to `List<T>` while retaining the existing
  sequence-transform proofs. Equality distinguishes order and multiplicity.
- A readable symbolic memory range projects to its exact snapshot list without
  enumeration. Missing readability evidence and claims that ignore an
  intervening write fail. `old(...)` and named snapshots retain pointer
  provenance and the correct list contents.

## Acceptance criteria

- The current pure ADT capabilities remain supported, and the resource,
  contract, quantifier, mutual-induction, sequence-syntax, and range-projection
  gaps above are implemented with checked positive and negative regressions.
- The modeled tree resource and unchanged initializer provide an end-to-end
  regression; later tree algorithm obligations stay explicitly tracked in
  the related recursive-structure issue.
- Models remain symbolic. Explicit simple checking is output-sensitive in the
  selected source, model terms, and certificate, without scans or clones of
  unrelated state. Performance-sensitive representation changes have
  deterministic scaling regressions over multiple input sizes.
- Proof expansion produces recheckable certificates, diagnostics remain
  bounded and actionable, and `scripts/check.sh` passes.

Related: [recursive-structure-models.md](recursive-structure-models.md),
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md), and
[resource-algebra-extensions.md](resource-algebra-extensions.md).
