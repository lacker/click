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
- `unfold(cell)` exposes a witness-free immediate memory body and its
  facts, optionally under the existing single `if` with an empty false case.
  The guard must be proved true or false; unknown guards do not eagerly split.
  The false case exposes no body ownership or facts. Bare field names in the
  body denote the instance's fields.
  Memory-only bodies, including guarded and matched bodies, leave no open
  handle. Recursive children can be independently named with `as { ... }`;
  only the older parent-qualified compatibility syntax retains a handle.
- A resource body may instead `match` one ADT field with exhaustive
  `Type::Variant(bindings) => { ... }` arms. Constructor evidence selects an
  arm without implicit proof-by-cases. Bindings have the constructor's
  instantiated types, including pointers and nested ADTs. Only that arm's
  immediate owned memory, folded children, and facts are exposed. Arm bindings cannot escape
  or capture incidental C locals. Return folds recheck constructor evidence
  on their retained execution path.
- Match arms can declare direct recursive children with `owns left: tree(lp);`
  and equations such as `fact left.model == lm;`. Each child uses the same
  resource definition; every child field must equal an immediate constructor
  binding of its declared type. The matched model field therefore strictly
  descends through a proper submodel, without extra recursion syntax.
- `unfold(root) as { left: l, right: r };` consumes the parent and exposes
  independently owned, folded children without retaining a parent handle.
  `let root = fold(tree(p), { model: value }, { left: l, right: r });`
  consumes the selected children plus immediate memory. Each selected-arm slot
  must occur exactly once with a distinct owned identity. Child arguments and
  fields must match the proposed model; replacement identities and reordered
  children are allowed. Named `consumes` inputs support constructing parents
  from separately owned children. The older parent-qualified syntax remains
  compatible and requires its recorded children unchanged.
- Plain memory bodies support explicit construction from raw ownership:
  `let c = fold(cell(p), { model: Mark::Set(value) });` supplies every field and
  checks the complete body ownership and facts. Initializers accept typed
  symbolic expressions, including ADT constructors, entry-model values,
  matches, and pure-function applications; they do not execute pure functions
  or split arbitrary models into cases. The legacy `fold(c)` shorthand
  selects entry-state fields without requiring an open handle. Guarded and
  matched memory-only bodies also support explicit fields: fold selects the
  proved guard or constructor case from the proposed instance and checks its
  complete body. Recursive-child bodies accept explicit child selections.
  A declaration or field value alone grants no memory authority.
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
- [resource_cell_construction.md](../mdtests/resource_cell_construction.md)
- [resource_adt_construction.md](../mdtests/resource_adt_construction.md)
- [resource_conditional_construction.md](../mdtests/resource_conditional_construction.md)
- [resource_independent_children.md](../mdtests/resource_independent_children.md)
- [resource_tree_node_init.md](../mdtests/resource_tree_node_init.md)
- [resource_fields_guarded_memory_body.md](../mdtests/resource_fields_guarded_memory_body.md)
- [resource_fields_match_memory_body.md](../mdtests/resource_fields_match_memory_body.md)
- [resource_recursive_children.md](../mdtests/resource_recursive_children.md)
- [contract_resource_parameters.md](../mdtests/contract_resource_parameters.md)
- [contract_resource_call_transport.md](../mdtests/contract_resource_call_transport.md)
- [contract_resource_call_no_implicit_preservation.md](../mdtests/contract_resource_call_no_implicit_preservation.md)

## Remaining work toward the C tree

### Constructor elimination in execution proofs (blocks left rotation)

An arbitrary resource model needs an explicit proof operation that splits on
its constructors and introduces typed field names. Knowing `model != Empty`
does not currently expose the unknown fields of `Node`. Pure `match` remains
a symbolic expression, and theorem-level `induct` is not an execution-proof
case split. Do not specialize the rotation to concrete payloads or subtree
models to bypass this gap.

The reduced regression is
[resource_nonempty_model_needs_constructor_cases.md](../mdtests/resource_nonempty_model_needs_constructor_cases.md):
reading a cell whose model is an arbitrary `Some(value)` is safe, but `unfold`
requires an explicit constructor term. It currently records the bounded
rejection. The intended positive proof names `value` in the `Some` case and
discharges the impossible `None` case from the precondition.

The selected syntax is `match model { Type::Variant(fields) => { tactics } }`
in proof blocks, distinct in context from pure match expressions.
The kernel now provides constructor exhaustion as a disjunction of constructor
equations with existentially bound, typed fields. It validates the datatype
schema and reserves the scrutinee's variable identities, including variables
inside symbolic matches and calls. Tests cover generic and recursive fields,
pointer payloads, capture avoidance, complete constructor families, and
malformed or unsupported inputs. This rule alone neither chooses witnesses
nor grants ownership; **the proof-level tactic is not yet implemented**.
Its current payload sorts are signed 32/64-bit integers, pointers, and ADTs.

The remaining integration needs scoped witness introduction, execution-frontier
case splits and joins, and source/certificate support. Acceptance requires
exhaustive checked cases, fresh
typed bindings with correct scope, retained C execution/ownership on each
branch, expansion/rechecking, and rejection of omitted reachable cases or
escaping fields. Then verify unchanged `tree_rotate_left` for arbitrary
nonempty root/right-child models, preserving both node identities/payloads and
all three arbitrary subtrees. Its sidecar still has no rotation contract.

### Other remaining work

1. **Broader child bodies.** Direct, structurally descending same-resource
   children are implemented. Child arguments accept read-only C expressions,
   including stored struct links. Loads require the immediate body's memory
   ownership; fold checks that ownership before interpreting the arguments.
   Expression safety and path premises must be proved, with no implicit case
   splitting. Child field equations accept
   immediate constructor bindings, not arbitrary expressions or existential
   fields. Mixed resource families, mutually recursive resource groups,
   witnesses, nested resource guards/matches, arbitrary scrutinees, and general
   resource `if/else` remain unsupported. Keep recursion finite and avoid
   eagerly traversing an unknown model when extending these cases.
2. **Field snapshots.** Explicit field establishment and updates work for
   memory bodies and selected recursive children. Fields are symbolic values,
   not freely assignable ghost storage; every change must re-establish the
   relation to concrete memory. Extend fixed post-state snapshots to arbitrary
   symbolic terms, not just entry-bound variables. A regression should capture
   a newly constructed model at a named proof point, unfold its owner, and
   reuse that captured model in a later explicit fold without a live handle.
3. **Contract and witness transport.** Complete ordinary inline-call transport
   and concrete-function formation/refinement for resource-parameterized
   contracts, and transport parent-qualified child handles through explicit
   contract arguments. Resource-body witnesses currently admit only C pointers, not
   existential child models. Contract `let ... where` witnesses are separate
   per clause; they must not silently become shared instance bindings.
4. **Tree algorithms.** Continue rotations and traversals under
   [recursive-structure-models.md](recursive-structure-models.md); iterative
   termination is tracked by
   [structural-loop-termination.md](structural-loop-termination.md).

The modeled-binary-tree sidecar now verifies the unchanged `tree_node_init`.
Its `tree_at` resource has a `HeapTree` model preserving node identities and
payloads, a null empty case, owned struct fields, and disjoint children reached
through the stored links. The initializer consumes separate parent memory and
two arbitrary modeled children to construct the modeled parent. The focused
fixture and kernel/surface tests cover expansion, invalid models and links,
missing/duplicated ownership, overlap, and unrelated-resource scaling.
No C traversal or rotation is verified yet.

## Other ADT gaps

- **Pointer constructor literals.** A pointer-valued constructor argument
  such as `Ptr::At(0)` is currently rejected as an integer/pointer type
  mismatch. Support contextual null-pointer formation, preserving its pointer
  type and granting no memory ownership. Keep the rejection regression until
  that elaboration is implemented; do not change existing C to supply a
  proof-only null-pointer parameter.

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
- Preserve the tree heap relation and verified unchanged initializer.
  Track later algorithm obligations in the related recursive-structure issue.
- Keep simple checking output-sensitive in the selected source, terms, and
  certificate, without scanning or cloning unrelated state. Representation
  changes require deterministic multi-size scaling tests.
- Expanded proofs must recheck, failures must remain bounded and actionable,
  and `scripts/check.sh` must pass.

Related: [recursive-structure-models.md](recursive-structure-models.md),
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md), and
[resource-algebra-extensions.md](resource-algebra-extensions.md).
