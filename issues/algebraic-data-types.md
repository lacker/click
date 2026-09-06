# Add algebraic data types to specifications

Split from [recursive-structure-models.md](recursive-structure-models.md) on
2026-09-05 and broadened from the original specification-sequence issue on
2026-09-05. Exact finite order is useful well before recursive heap models:
array copies, buffer transforms, vector append, traversal results, and tree
rotations all need to relate an ordered collection at two snapshots. The
sequence work exposed the more general missing abstraction: Click has no
user-defined immutable algebraic data types, constructor patterns, or
structural recursion and induction over logical values.

The intended foundation is a specification-only, Rust-like sum-of-products
declaration. Its recursive values are mathematical constructor trees, not C
layouts and not runtime allocations. In schematic surface syntax, the MVR
model should be definable as:

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}
```

`List<T>` is the conventional name because proofs expose its inductive
`Nil`/`Cons` structure. It can still model the finite ordered contents of an
array, vector, C linked list, or tree without claiming that the implementation
uses any particular representation.

The fixed synthetic C scaffold for the first nonrecursive uses lives in
[`examples/sequence-transform`](../examples/sequence-transform/README.md).
Its sidecar verifies the implemented fixed-literal slices while keeping the C
unchanged.

## Implemented precursor slices

- finite homogeneous literals, including `[]`;
- persistent `++` terms with constant-time root sharing and empty identity;
- `==` and `!=` lowering to typed kernel sequence terms;
- element-wise `old(...)` and named-snapshot elaboration;
- checked contracts for `sequence_copy3` and `sequence_concatenate2`;
- shape-independent element-wise equality, including `++` associativity; and
- a checked contract for in-place `sequence_reverse3`;
- proposition-level `element in sequence` membership over literals and
  concatenations; and
- a checked exact-result contract for `sequence_contains3`.
- generic nonrecursive `spec enum` declarations with nullary and product
  variants;
- fully type-applied constructors, structural `==`/`!=`, and exhaustive
  `match` expressions over constructed values whose fields may be symbolic C
  values; and
- checked rejection of wrong constructor field types, nonexhaustive matches,
  and recursive fields in this initial datatype slice;
- a first-class `ClickType` family distinct from C's `C0Type`, with algebraic
  types accepted as pure-function, predicate, and theorem parameter types and
  as pure-function result types; and
- arbitrary symbolic nonrecursive algebraic values, structural reflexivity,
  exhaustive elimination, and pure positive/negative mdtests that require no
  C translation unit; and
- typed kernel algebraic terms with one variable node per arbitrary value,
  constructor nodes with checked instantiated schemas, retained match nodes,
  and shared datatype definitions. The earlier eager encoding as an integer
  tag plus fields for every possible variant has been removed; and
- checked constructor formation, disjointness, congruence, and injectivity,
  with explicit surface certificates and indexed exact-hypothesis lookup.

These forms are currently backed by a dedicated internal sequence term. They
must remain supported while their public semantics migrate to `List<T>`:
`[]` constructs `List::Nil`, a nonempty literal constructs nested
`List::Cons`, `++` calls list append, and `in` calls list membership. They must
not remain a second, privileged logical collection universe.

Still open are algebraic `let` bindings and quantifiers, resource arguments,
theorem application with algebraic arguments, nested and strictly positive
recursive fields, structural decreases and induction, the library-defined
`List<T>`, recursive-resource use, and symbolic typed-memory-range projection.
Opaque and recursive algebraic-valued pure function calls also wait on that
recursive representation; nonrecursive calls are elaborated compositionally.
Generated structural induction principles remain to be added as checked
datatype rules. Correlation between repeated matches of one symbolic value is
tracked in [algebraic-match-path-correlation.md](algebraic-match-path-correlation.md).

## Violated invariant

A specification must be able to define and reason about immutable logical
variants compositionally instead of adding a new privileged kernel type for
every abstract model. Recursive logical values must be finite and support
explicit, exhaustive elimination. They must not carry runtime storage or
memory authority.

## Intended regression

First define a small nonrecursive generic datatype such as `Maybe<T>`. Verify
construction, structural equality, exhaustive pattern matching, type
substitution, and use through predicates, pure functions, theorems, and
resources. Negative regressions reject wrong constructor arguments,
nonexhaustive or duplicate match arms, escaping pattern binders, and invalid
recursive declarations.

Then define the recursive `List<T>` above. Define append and membership by
pattern matching, with recursive calls justified by structural descent. Prove
empty identity, append associativity, and the membership law using explicit
structural induction. Negative claims must distinguish `[a, b]` from `[b, a]`,
`[a]` from `[a, a]`, and membership from ownership of an object addressed by a
pointer element.

Then verify the unchanged `sequence-transform` C fixture with contracts that
express these results conceptually:

- copying three cells preserves their exact entry sequence;
- concatenating two two-cell inputs produces their sequence concatenation;
- reversing three cells produces the entry sequence in reverse order; and
- membership returns true exactly when the target occurs in the input
  sequence.

The fixed-size fixture may construct three-element list literals directly. A
checked projection from a typed memory range to its snapshot list is the next
regression, so the same abstraction scales to dynamic buffers without
enumerating their cells in a contract.

## Acceptance criteria

- Specifications can declare immutable, generic algebraic data types with
  typed sum variants and product fields. Constructors, variables, parameters,
  `let` bindings, quantifiers, contracts, predicates, pure functions,
  theorems, and resource arguments preserve their instantiated types.
- Pattern matching is explicit and exhaustive, binds typed constructor fields
  only within an arm, and gives each arm the checked constructor refinement.
- Recursive declarations accept only sound strictly positive occurrences.
  Recursive functions can cite structural descent, and proofs can perform
  explicit structural induction with hypotheses for recursive fields. Neither
  operation unfolds an unknown whole value automatically.
- A library-defined `List<T>` supplies `Nil`, `Cons`, append, and membership.
  Existing `[]`, `++`, and `in` syntax elaborates to that public abstraction.
  List equality is structural and is not delegated to an unchecked solver.
- Lists support the modeled C scalar values and provenance-carrying data
  pointers needed by MVR. `old(...)` and named snapshots preserve list values.
  A stored pointer retains identity, offset, nullness, and provenance but
  grants no pointee ownership or memory access.
- A typed memory range can be projected to a symbolic list at a named
  snapshot only with the corresponding readable evidence. Projection does not
  eagerly enumerate a symbolic range.
- Constructor and symbolic terms use persistent, output-sensitive
  representation and checking. Repeated append must not copy or scan unrelated
  terms or silently become quadratic.
- Pure positive and negative regressions, the `sequence-transform` contracts,
  a range-projection regression, and `scripts/check.sh` pass.

Related: [recursive-structure-models.md](recursive-structure-models.md) and
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md).
