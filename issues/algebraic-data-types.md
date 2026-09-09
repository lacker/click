# Complete algebraic data types and modeled resource ownership

MVR dependency. The pure ADT foundation is implemented. The main remaining
goal is connecting symbolic tree models to ownership of the unchanged C tree.

## Implemented: pure ADTs

- Rust-like generic `spec enum` declarations, nested constructor fields, and
  regular strictly positive recursive datatype groups that admit finite values.
- First-class `ClickType` parameters for pure functions, predicates, and
  theorems; algebraic results; and typed or inferred expression-local `let`.
- Arbitrary typed symbolic variables, constructors, symbolic `match`, and
  opaque pure-function applications. Unknown recursive values are not expanded
  into trees of possible fields. Only C executes; pure Click defines terms.
- Checked constructor formation, disjointness, congruence, injectivity, and
  exhaustive matching with scoped typed fields. Pure `match` does not itself
  split the proof. Explicit proof control supplies case evidence, and
  `normalize() using { ... }` checks reductions against cited premises.
- Structurally recursive pure functions, including multiple recursive fields
  and mutually recursive groups. Explicit `unfold` exposes one equation.
  Structural `induct` supplies hypotheses for immediate recursive fields of
  the same datatype.
- Generic functions and predicates with call-site inference. Generic theorem
  bodies are checked with rigid arbitrary types; applications use checked,
  cached instantiations. Expanded generic proofs can be rechecked.
- The [prelude](../stdlib/prelude.click) provides `List<T>`, append, membership,
  `Nat`, addition, and Nat-valued `list_length`, with checked generic list laws,
  arithmetic laws, and append-length laws.
- The [modeled-binary-tree example](../examples/modeled-binary-tree/README.md)
  defines example-local `Tree<T>`, `tree_size`, and `tree_mirror`. Generic proofs
  establish mirror involution and size preservation. These are pure-model
  proofs, not verification of the C tree's memory safety or algorithms.
- The [sequence-transform example](../examples/sequence-transform/README.md)
  verifies fixed-size copying, concatenation, reversal, and membership using
  sequence literals, without modifying its C.

## Implemented: named instances and memory bodies

- Resources declare multiple `field name: ClickType;` fields, including nested
  generic ADTs. Checked schemas retain field types and order. Field-bearing
  resources are exclusive and non-countable: quantities, counting, and views
  are rejected. Field-free resources retain their existing rules.
- `owns cell: marked_cell(p);` binds an instance with arbitrary symbolic fields.
  `cell.model` reads its current field, while `old(cell.model)` reads its entry
  field. Identity, field values, and ownership are distinct. Equal fields do
  not identify two instances; ownership alone does not promise preservation.
- `unfold(cell)` exposes a nonrecursive, witness-free memory body and its
  facts, optionally under the existing single `if` with an empty false case.
  The guard must be proved true or false; unknown guards do not eagerly split.
  The false case exposes no body ownership or facts. Bare field names in the
  body denote the instance's fields.
  An exclusive open handle retains the identity and fields, but grants no
  folded ownership for calls or returns.
- `fold(cell)` requires the matching open handle, complete body ownership, and
  established body facts at the current memory. It restores the same identity
  and unchanged fields. A declaration or field value alone grants no memory
  authority, and raw body ownership alone cannot create an instance.
- Checked folds may follow C returns on multiple retained execution paths.
  Each fold is tied to its exact path's ownership, memory, and guard case;
  sibling evidence cannot supply the fold. Completion collects the path-local
  exchanges and certifies complete path coverage. A proof snapshot cannot
  replace the checked execution outcome.
- Explicit callback applications transport named instances. For example,
  `contract Read(cell: marked_cell(p)) for int32(int32* p) { owns cell; ... }`
  declares a proof parameter, and `step(Read(first))` supplies it. Parameters
  are explicit, with no defaults or inferred argument lists. Declaring a
  parameter does not supply ownership. Returned fields are fresh and
  constrained only by the callback contract's guarantees.

Regressions cover arbitrary fields, exact entry snapshots, repeated callback
calls, preservation of unselected instances, missing or duplicate ownership,
wrong identity, changed fields, invalid folds, tampered certificates,
expansion/rechecking, and deterministic multi-size scaling:

- [resource_fields.md](../mdtests/resource_fields.md)
- [resource_instance_bindings.md](../mdtests/resource_instance_bindings.md)
- [resource_fields_memory_body.md](../mdtests/resource_fields_memory_body.md)
- [resource_fields_guarded_memory_body.md](../mdtests/resource_fields_guarded_memory_body.md)
- [contract_resource_parameters.md](../mdtests/contract_resource_parameters.md)
- [contract_resource_call_transport.md](../mdtests/contract_resource_call_transport.md)
- [contract_resource_call_no_implicit_preservation.md](../mdtests/contract_resource_call_no_implicit_preservation.md)

## Remaining work toward the C tree

1. **Resource `match` and child ownership.** Resource bodies currently lack
   `else` and constructor `match`. Check exhaustive constructor arms and
   scoped typed fields, exposing only the selected arm's immediate resources
   and facts. Support nested named child resources and a checked finite,
   well-founded interpretation of recursive definitions. No operation should
   eagerly traverse an unknown model.
2. **Field establishment and updates.** Define how body proofs initially
   establish fields and justify changed fields. Fields are symbolic values,
   not freely assignable ghost storage; every change must re-establish the
   relation to concrete memory. Support arbitrary symbolic terms in post-state
   snapshots, not just entry variables or concrete constructors. Syntax for
   establishment and updates remains undecided.
3. **Contract and witness transport.** Complete ordinary inline-call transport
   and concrete-function formation/refinement for resource-parameterized
   contracts. Resource-body witnesses currently admit only C pointers, not
   existential child models. Contract `let ... where` witnesses are separate
   per clause; they must not silently become shared instance bindings.
4. **Tree heap relation.** Add an example-local resource with a tree-model field
   to the modeled-binary-tree sidecar. The empty case requires a null root;
   the node case owns the node fields, relates the payload to memory, and owns
   disjoint modeled children. Preserve node identities as well as values.
   A pointer occurring in a model grants no ownership.
5. **First C proof.** Verify unchanged `tree_node_init`: a separately owned,
   nonnull parent and two modeled children become a correctly modeled parent
   tree. Reject wrong values, swapped children, duplicated nonempty subtrees,
   and parent/child overlap. Then continue rotations and traversals under
   [recursive-structure-models.md](recursive-structure-models.md); iterative
   termination is tracked by
   [structural-loop-termination.md](structural-loop-termination.md).

The modeled-binary-tree sidecar does not yet contain a verified C function
contract. Pure tree proofs and kernel identity tests are not verification of
the C tree.

## Other ADT gaps

- **Surface ADT resource arguments.** Kernel resource identities and population
  keys support symbolic ADT arguments, with checked transfer and substitution.
  Surface resource parameters and body instantiation still use C types and
  expressions. Carry symbolic arguments without encoding them as C values or
  erasing fields into legacy composites. Preserve the explicit rejection in
  [adt_indexed_resource.md](../mdtests/adt_indexed_resource.md) until supported.
  Ordinary abstract state should use resource fields, not extra model plumbing.
- **Algebraic quantifiers.** Preserve arbitrary types and witness scope across
  specifications; expression-local ADT `let` is not existential model transport.
- **Mutual induction.** Check hypotheses across a mutually recursive datatype
  group; ordinary same-datatype structural induction is already supported.
- **Sequence syntax.** Literals, `++`, and `in` still have a separate internal
  representation. Elaborate them to `List<T>`, append, and membership while
  retaining existing sequence-transform proofs and order/multiplicity semantics.
- **Memory-range snapshots.** Project a readable symbolic typed range to an
  exact snapshot `List<T>` without enumeration. Reject missing readability and
  claims that ignore writes; preserve provenance through `old` and named
  snapshots.

## Invariant and acceptance criteria

A logical value must retain its type and meaning wherever a specification uses
it. Heap models must be justified by ownership, not unconstrained assertions;
model values themselves carry neither runtime storage nor memory authority.

- Preserve the implemented pure ADT and resource capabilities while closing
  the gaps above, with checked positive and negative regressions.
- Establish the tree heap relation and verify the unchanged initializer.
  Track later algorithm obligations in the related recursive-structure issue.
- Keep simple checking output-sensitive in the selected source, terms, and
  certificate, without scanning or cloning unrelated state. Representation
  changes require deterministic multi-size scaling tests.
- Expanded proofs must recheck, failures must remain bounded and actionable,
  and `scripts/check.sh` must pass.

Related: [recursive-structure-models.md](recursive-structure-models.md),
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md), and
[resource-algebra-extensions.md](resource-algebra-extensions.md).
