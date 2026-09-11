# Mathematical integers

`Integer` is Click's exact, signed mathematical number type for
specifications. It is separate from every C integer type and has no C storage,
ABI, machine width, or implicit runtime allocation. The kernel and standard
library may represent it internally in implementation-specific ways, but the
surface contract below is stable.

## Type and conversions

The public name is `Integer`; there is no `Int` alias. Existing `int` remains
the C `int32` type. Integer literals are arbitrary-size mathematical values
when their context is `Integer`. Machine values and Integer values do not mix
implicitly.

An unused `Integer` parameter does not reinterpret a separately machine-typed
literal or expression. Expected-type propagation follows the expression and
its binding context; it does not leak across unrelated clauses.

`to_integer(x)` accepts each supported signed or unsigned machine-integer type
and preserves its numeric value. Signed `-1` and unsigned `4294967295u32` are
therefore different Integer values. Converting an already evaluated machine
value is total, but evaluating the argument retains all of its C definedness
obligations. In particular, `to_integer(x + 1)` does not discharge an
overflow obligation for `x + 1`.

Reverse conversions are destination-specific: `to_int16`, `to_int32`,
`to_uint8`, `to_uint16`, `to_uint32`, `to_int64`, and `to_uint64`. A conversion
requires proof that the Integer lies in the destination's exact range. It does
not truncate, wrap, saturate, or insert an unchecked assumption. A symbolic
conversion requires both bounds, even in a reflexive proposition.

The same rule applies to conversions between `Nat` and `Integer`. `Nat` to
`Integer` is total; `Integer` to `Nat` requires a nonnegative proof. Checked
round-trip and arithmetic laws relate the types without identifying them by
implicit coercion. `Nat` remains the structural, nonnegative datatype used by
its own induction theorems.

`to_integer(a + b)` and `to_integer(a) + to_integer(b)` are distinct
expressions. A signed machine-addition equality needs evidence that the C
operation is defined; an unsigned equality must account for modular arithmetic.
No unconditional conversion distribution rule is sound.

## Exact operations and definedness

Integer literals, unary negation, addition, subtraction, multiplication,
equality, disequality, and order comparisons are supported. Exact Integer
arithmetic does not overflow. Bitwise operations remain machine operations.

Division and remainder are deliberately deferred from the current supported
surface, but their semantics are settled for a future implementation. They use
Euclidean division: for nonzero `d`,

`a == (a / d) * d + a % d` and `0 <= a % d < abs(d)`.

Thus `-7 / 3 == -3` and `-7 % 3 == 2`; this is distinct from C's truncation
toward zero. A zero divisor is a definedness obligation. See the deferred
[division and remainder issue](https://github.com/lacker/click/blob/master/issues/integer-division-and-remainder.md).

Every checked conversion and every future checked division must establish its
definedness in the current proof context before a theorem or execution
certificate is accepted. Evaluation facts are not arbitrary assumptions.

## Specification coverage

Integer is supported in:

- specification bindings, typed `let` bindings, and contextual literals;
- universal and existential quantifiers over the unbounded domain;
- pure function parameters and results, and theorem parameters and claims;
- datatype fields and generic type arguments;
- resource model fields and resource pattern bindings;
- typed range-fold accumulators, endpoints, and bodies; and
- mixed C/Integer propositions where every boundary is explicit and checked.

Existing binders, function syntax, match syntax, and fold syntax are reused.
Fold indices and accumulators have independent types: an `int32` index may read
C array elements while an `Integer` accumulator computes an exact sum. Empty
and reversed range behavior is unchanged, and fold initial values and bodies
must have one accumulator carrier.

Quantifier domains remain logically unbounded. Finite enumeration is only a
bounded proof technique. Universal introduction and existential witnesses use
capture-avoiding substitution, preserve carrier identity, and retain any
definedness obligations in the witness or proposition. Deep repeated universal
introduction has a known quadratic cost and is deferred for targeted scaling
work; correctness checks and existing budgets remain in force. See the
[deep quantifier scaling issue](https://github.com/lacker/click/blob/master/issues/deep-quantifier-scaling.md).

For an existential witness, definedness remains attached to that same witness.
It cannot be weakened into an implication whose guard is false, since that
would permit an irrelevant witness to establish the existential claim.

## Arithmetic automation and trust boundary

The supported arithmetic automation is linear: addition, subtraction, order,
and multiplication by constants, together with explicit machine-conversion
and checked C-arithmetic laws. General multiplication is a valid Integer term,
but there is no promise of general nonlinear automation.

Arithmetic planning emits explicit, inspectable evidence. The kernel validates
operators, coefficients, terms, premises, and range claims independently;
zero-premise tautologies are valid, while sparse or altered premise indices
fail locally. Expansion prints ordinary proof steps, and ordinary verification
rechecks those steps without rerunning the planner. Profiling and audit use the
same checked boundary.

Fold reasoning uses explicit empty-range and next-element laws. Fold terms are
opaque affine atoms in the bounded certificate fragment. The planner accepts
selected checked premises and explicit constant scaling; it does not enumerate
a symbolic range or invent an arithmetic assumption. The unchanged C
summation regression proves exact functional correctness with an `Integer`
prefix sum while separately proving that each machine addition is defined.

## Sharing, scope, and identity

Integer expressions use immutable shared nodes. A chain of aliases such as
`a0 = x; a1 = a0 + a0; ...` must remain linear in source size rather than
expanding into an exponential arithmetic tree. Canonical nodes have stable,
shallow identities and traversals visit each reachable node once where the
operation permits.

Interning keys contain shallow child identities. Cache maintenance must not
rehash an unrelated large numeral repeatedly or retain dead expression graphs
indefinitely. Alpha keys serialize shared graphs with local child indices.
Renaming and substitution caches include lexical binder scope, and carrier
identities distinguish C values from Integer values.

Substitution and generic rewriting preserve shared arithmetic nodes. They do
not eagerly evaluate newly constant expressions: replacing a variable with a
large repeated-squaring DAG must not allocate an enormous numeral from a tiny
proof. A shared replacement is validated once and its shallow root is charged
at each occurrence.

Memory loads and fold atoms retain exact snapshot identity. Alpha-equivalent
loads from one retained snapshot may match; a different snapshot, endpoint,
body, carrier, or definedness context does not. Snapshot identity is opaque to
arithmetic and is never inferred from a raw term identifier or fingerprint.

## Work budgets and certificate scaling

Numeric work has two independent costs: reachable expression visits and
magnitude-dependent arithmetic work, including numeric bit length. A numeric
operation consumes the active verification budget before doing the operation.
Lowering also checks the configured simple-operation allowance. A counter added
after arithmetic is insufficient, and a weighted charge must not be simulated
by a loop of unit checkpoints.

Shared DAG traversals, substitution, alpha comparison, certificate checking,
and snapshot matching must scale with the selected expression and certificate,
not unrelated proof state. Premise references are explicit and checked before
storage allocation. Large constants do not silently truncate, and enormous
mathematical ranges do not trigger uncontrolled enumeration.

The trust boundary is independent kernel checking of the resulting proof
object and certificate. C source remains the verification boundary: the
unchanged summation program is the regression, and proof authors must not add
no-op C branches, proof-only locals, helper rerouting, or renamed identifiers
to make an Integer proof succeed.

## Related references

- [Kernel implementation](kernel.md)
- [Verification efficiency](verification-efficiency.md)
- [Memory derivation DAG](memory-dag.md)
- [Language reference: mathematical integers](../reference/language/index.md#mathematical-integers)
- [Canonical unchanged-C summation regression](https://github.com/lacker/click/blob/master/mdtests/integer_sum_range_fold.md)
- [Missing element-bound regression](https://github.com/lacker/click/blob/master/mdtests/integer_sum_range_fold_missing_bounds.md)
- [Intermediate-overflow regression](https://github.com/lacker/click/blob/master/mdtests/integer_sum_range_fold_intermediate_overflow.md)
