# Add a specification sequence type

Split from [recursive-structure-models.md](recursive-structure-models.md) on
2026-09-05. Exact finite order is useful well before recursive heap models:
array copies, buffer transforms, vector append, traversal results, and tree
rotations all need to relate an ordered collection at two snapshots. Click can
currently state element-wise facts and bounded permutation predicates, but it
has no first-class immutable value that preserves order, multiplicity, and
element identity together.

This is a specification type, not a C runtime list. The public name should be
sequence (with a surface spelling such as `seq<T>`), because the value models
finite ordered contents independently of whether the implementation is an
array, vector, linked list, or tree.

The fixed synthetic C scaffold for the first nonrecursive uses lives in
[`examples/sequence-transform`](../examples/sequence-transform/README.md).
Its sidecar currently imports the implementation without claiming the missing
sequence specifications.

## Violated invariant

A specification must be able to name and relate exact finite ordered contents
without expanding every element into a separate proposition or confusing
order preservation with permutation. Logical sequence values must not carry
runtime storage or memory authority.

## Intended regression

First verify pure sequence claims for empty and singleton construction,
concatenation identity and associativity, equality, and membership. Negative
claims must distinguish `[a, b]` from `[b, a]`, `[a]` from `[a, a]`, and
membership from ownership of an object addressed by a pointer element.

Then verify the unchanged `sequence-transform` C fixture with contracts that
express these results conceptually:

- copying three cells preserves their exact entry sequence;
- concatenating two two-cell inputs produces their sequence concatenation;
- reversing three cells produces the entry sequence in reverse order; and
- membership returns true exactly when the target occurs in the input
  sequence.

The fixed-size fixture may construct three-element sequence literals directly.
A checked projection from a typed memory range to its snapshot sequence is the
next regression, so the same abstraction scales to dynamic buffers without
enumerating their cells in a contract.

## Acceptance criteria

- The specification language has an immutable finite sequence type for
  supported C scalar values and provenance-carrying data pointers.
- Sequence values support typed variables, parameters, `let` bindings,
  quantifiers, function contracts, predicates, pure functions, and resource
  arguments.
- The initial algebra includes empty and finite literals, singleton,
  concatenation, equality, and membership. Empty identity and concatenation
  associativity have small kernel-checked reasoning rules; arbitrary sequence
  equality is not delegated to an unchecked solver.
- `old(...)` and named snapshots preserve sequence values. A pointer stored as
  an element retains identity, offset, nullness, and provenance but grants no
  pointee ownership or memory access.
- A typed memory range can be projected to a symbolic sequence at a named
  snapshot only with the corresponding readable evidence. Projection does not
  eagerly enumerate a symbolic range.
- Sequence terms use persistent, output-sensitive representation and checking.
  Repeated concatenation must not copy or scan unrelated terms or silently
  become quadratic.
- Pure positive and negative regressions, the `sequence-transform` contracts,
  a range-projection regression, and `scripts/check.sh` pass.

Related: [recursive-structure-models.md](recursive-structure-models.md) and
[mathematical-integers-in-specs.md](mathematical-integers-in-specs.md).
