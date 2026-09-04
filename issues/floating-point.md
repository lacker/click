# Model floating-point values

The kernel now has typed opaque storage values for `float` and `double`, but it
does not yet model their arithmetic or other value semantics. Real C libraries
commonly use `double` for numeric fields, including the pilot json-c target.
Keep this as one issue, but land the work in the ordered slices below so that
each commit has a usable, checkable boundary.

## Violated invariant

Click should model an unchanged C floating-point operation under an explicit
ABI and IEEE-754 semantic contract, or reject the unsupported operation with a
positioned diagnostic. It must not silently replace floating-point behavior
with mathematical reals, host-language arithmetic, or integer bit patterns
whose rounding and exceptional values have not been specified.

Existing C source is the regression boundary. Do not rewrite a C function to
make a proof pass; put adaptations in the model, lowering, contracts, or
diagnostics.

## Semantic decisions

The implementation should document and test these decisions before exposing
the first executable slice:

- `float` is IEEE-754 binary32 with 4-byte size and alignment; `double` is
  IEEE-754 binary64 with 8-byte size and alignment under the supported LP64
  target. `long double`, decimal floating point, and compiler-specific extended
  precision are outside this issue.
- C0 evaluates each operation at the declared result type using
  round-to-nearest, ties-to-even. Alternate rounding modes, `fenv`, traps,
  and excess-precision controls are unsupported and must be diagnosed rather
  than silently ignored.
- The model represents values exactly enough to distinguish finite values,
  signed zero, infinities, and NaNs. Generated NaNs use one documented
  canonical representation; copying a value preserves its representation.
  C value comparisons still follow C/IEEE rules: `+0 == -0`, every ordered
  comparison with a NaN is false, and `!=` with a NaN is true.
- Ordinary IEEE overflow and floating division by zero produce the specified
  infinity or NaN result; they are not integer-style C undefined behavior.
  Conversions to an integer are a separate operation and are undefined when
  the source is NaN, infinite, or outside the destination's range.
- The first model need not expose the floating-point environment or raw
  representation casts. Operations such as `isnan`, `isfinite`, and exact
  bit-casts must either be modeled explicitly or remain rejected.

## Implementation slices

### Slice 0: freeze the semantic boundary

Write the ABI, rounding, exceptional-value, comparison, conversion, and
evaluation-format rules into the language and internals documentation. Add a
negative parser regression for `long double` and unsupported floating-point
environment constructs if the parser can encounter them.

Acceptance:

- A fresh agent can determine the result of every supported primitive operation
  without consulting an implementation detail or the host platform.
- The documentation names the supported ABI and explicitly distinguishes C
  undefined behavior from IEEE exceptional results.
- `scripts/check.sh` passes.

### Slice 1: typed storage and ABI layout

Add `float` and `double` to `CType`, `CValue`, memory-load/store typing, C0
declarations, parameters, locals, struct fields, and supported array/heap
shapes. Preserve the value across assignment, calls, struct copies, and
allocation without performing arithmetic. Parse decimal constants only when
they can be converted deterministically to the declared binary format; reject
hexadecimal floating literals and unsupported suffixes until they have an
explicit model.

Regression design:

- unchanged C functions pass a `float` and a `double` through parameters,
  locals, struct fields, arrays, `malloc`, `calloc`, and `realloc`;
- `repr(C)` layout tests check size, alignment, and field offsets;
- a negative fixture rejects unsupported floating literal or type forms with a
  concise source-positioned diagnostic.

Acceptance:

- A stored value is loaded with its declared width and type, including signed
  zero and NaN representation where the source can provide one.
- No floating expression is lowered to an integer or mathematical-real value.
- Existing integer, pointer, struct, and heap tests remain green.

### Slice 2: constants, classification, and value-preserving conversions

Add deterministic binary32/binary64 literal conversion, unary negation, and
classification predicates for finite, infinite, zero, subnormal, and NaN
values. Add `float`/`double` widening and narrowing with the selected rounding
rule, plus integer-to-floating conversions. Keep floating-to-integer casts
behind their explicit definedness checks.

Regression design:

- tie-to-even literals and conversions at both precisions;
- positive and negative zero, the largest finite value, infinities, and NaNs;
- integer-to-float rounding and float-to-integer rejection for NaN,
  infinity, and out-of-range values.

Acceptance:

- Constant results do not depend on the host machine's floating-point mode or
  whether an intermediate was evaluated as `f32` or `f64`.
- Every lossy conversion either has a specified rounded result or emits the
  documented undefined-behavior/unsupported outcome.

### Slice 3: C/IEEE comparisons and conditions

Add `==`, `!=`, `<`, `<=`, `>`, and `>=` for `float` and `double`, including
symbolic operands. Model unordered NaN outcomes, signed-zero equality, and
short-circuit conditions. Add the classification predicates needed for
contracts so a proof can state finite-value preconditions without inspecting
kernel internals.

Regression design:

- comparisons of finite values at both precisions;
- every comparison against NaN, including `!=`;
- `+0` versus `-0`, infinity ordering, and conditional branches guarded by
  finite/NaN facts;
- negative proofs where a missing finite-value premise leaves a comparison or
  conversion obligation unresolved.

Acceptance:

- Comparison truth values agree with the documented C/IEEE rules for all
  classifications, not just ordinary finite inputs.
- Symbolic comparison terms remain checkable and do not use an ordered-real
  shortcut that treats NaN as an ordinary value.

### Slice 4: rounded arithmetic

Add `+`, `-`, `*`, and `/` for both precisions, with unary operations and
constant folding driven by an exact, deterministic IEEE implementation. Model
subnormal results, overflow to infinity, signed-zero results, invalid
operations, and division by zero. Do not use an unchecked host `f32`/`f64`
calculation as the symbolic semantics; if a software IEEE evaluator or proof
primitive is needed, its rounding and special-case behavior must be tested
independently.

Regression design:

- exact finite arithmetic and tie cases at both widths;
- cancellation, underflow/subnormals, overflow, infinity arithmetic, zero
  signs, and invalid operations producing NaN;
- symbolic contracts for simple arithmetic identities that are actually valid
  under the selected rounding model;
- negative tests for identities that are invalid because of rounding or NaN.

Acceptance:

- Constant and symbolic arithmetic agree on the same operation semantics.
- The verifier never proves a false real-number identity merely because the
  corresponding mathematical expression simplifies.
- Arithmetic behavior is bounded and diagnostics remain actionable when a
  proof requires unsupported nonlinear or exceptional-value reasoning.

### Slice 5: C conversions, promotions, contracts, and library integration

Complete the supported C conversion rules: integer/float conversions,
`float` promotions where applicable, mixed `float`/`double` arithmetic, return
and argument conversions, and assignment narrowing. Connect the model to
struct/heap resources, pure theorems, contract literals, and the standard
library predicates used by a json-c-shaped example. Keep `long double`, raw
floating representation access, alternate rounding modes, and unsupported
math-library functions explicitly rejected.

Regression design:

- an unchanged C function with `float` and `double` parameters, locals,
  fields, comparisons, and arithmetic;
- mixed-width and integer conversion cases with boundary values;
- positive finite-value contracts and negative NaN/overflow/conversion cases;
- a small json-c-shaped numeric field example using `double` without changing
  the original C source.

Acceptance:

- `CType`, `CValue`, expression evaluation, memory operations, conditions,
  contract lowering, and diagnostics agree on the same IEEE/ABI model.
- Overflow, NaN, infinities, conversions, comparisons, and rounding each have
  explicit regression coverage.
- The positive and negative regressions pass and `scripts/check.sh` passes.

## Related work

The completed integer model supplies the width-aware C type and memory
boundaries. [mathematical-integers-in-specs.md](mathematical-integers-in-specs.md)
is related but separate: floating-point values are finite-width IEEE values,
not a request to replace them with unbounded specification integers.
