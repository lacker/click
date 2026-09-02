# Model floating-point values

The kernel has no floating-point value or arithmetic type, and the C0 parser
rejects `float` and `double`. Real C libraries commonly use `double` for
numeric fields, including the pilot json-c target.

## Violated invariant

Click should either model a C floating-point operation with documented
rounding and undefined-behavior rules or reject it as an explicitly unsupported
construct. The current rejection is tracked here until a sound model is
designed.

## Intended regression

An unchanged C function with `float` and `double` parameters, locals, fields,
comparisons, and arithmetic should verify under a documented floating-point
contract. A negative test should reject NaN-sensitive or unsupported operations
with a positioned diagnostic until that model exists.

## Acceptance criteria

- `CType`, `CValue`, expression evaluation, and contract lowering agree on the
  chosen IEEE/ABI and rounding semantics.
- Overflow, NaN, infinities, conversions, and comparisons have explicit rules.
- The positive and negative regressions pass; `scripts/check.sh` passes.
