# Add Euclidean division and remainder for `Integer`

P2: arithmetic completeness after the shipped `Integer` foundation. Exact
addition, subtraction, multiplication, comparisons, conversions, folds, and
quantified proofs are available; division and remainder remain deliberately
deferred. This is independent of C's signed truncation semantics.

## Violated invariant

An `Integer` specification expression must have one stable, checked meaning
for every mathematical input. For a nonzero divisor `d`, division and
remainder must satisfy the Euclidean laws

`a == (a / d) * d + a % d` and `0 <= a % d < abs(d)`.

The zero-divisor case must be a definedness obligation. The implementation
must not silently use C's truncation-toward-zero result, introduce an
unproved assumption, or make a failed certificate appear valid. Existing C
division and remainder keep their C semantics and must remain a separate
bridge with their existing definedness and overflow rules.

## Intended regression

Add small checked `Integer` theorems and direct semantic models covering
positive and negative dividends and both signs of nonzero divisor, including
`-7 / 3 == -3`, `-7 % 3 == 2`, `7 / -3 == -2`, `7 % -3 == 1`,
`-7 / -3 == 3`, and `-7 % -3 == 2`, together with the Euclidean
reconstruction and range laws. Reject a zero-divisor proof, and reject any attempted unconditional
rewrite that identifies an `Integer` operation with C truncating division or
remainder. Expand each accepted proof and independently reverify its
certificate; tampering with the quotient, remainder, divisor, or definedness
evidence must fail locally.

## Acceptance criteria

- `Integer` division and remainder implement the stated Euclidean semantics
  for both divisor signs, with exact arbitrary-size values and a mandatory
  nonzero definedness check.
- The operations work in bindings, pure functions, theorem parameters,
  datatype/resource fields, folds, and quantified propositions wherever the
  existing `Integer` surface is supported.
- Checked certificates retain the divisor and definedness evidence;
  `click expand`, ordinary verification, profiling, and audit agree, and an
  expanded proof independently rechecks.
- Regression coverage includes zero divisors, negative and positive operands,
  large values, malformed certificates, and explicit separation from C
  truncation semantics.
- Symbolic traversal and certificate bookkeeping are local to the selected
  expression and certificate, approximately linear up to logarithmic indexing
  factors. Numeric algorithm costs are charged by operand bit lengths without
  promising linear-time arbitrary-precision division. Multi-size tests cover
  arithmetic, expansion, and re-verification without skipping soundness checks.
- The focused regressions and `scripts/check.sh` pass.
