# Lower calls in short-circuit right operands

## Invariant

Existing C expressions such as `first() && second()` must preserve conditional
evaluation of `second()` when lowered. A sidecar must not require the C to be
rewritten into proof-friendly control flow or locals.

## Regression

`mdtests/qualified_static_wide_values.md` retains a startup example with
`read_low() < 0 && read_high() > 4294967295UL && zero == 0`. It currently
expects the explicit unsupported diagnostic, not a successful proof.

## Acceptance criteria

- Lower right-operand calls for `&&` and `||` with the original sequencing
  and side effects; unselected calls must not execute or require resources.
- Cover nested operators, selected and unselected writes, and calls that
  would be undefined if executed in the unselected branch.
- Change the retained startup regression to a passing proof without changing
  its C, and check expansion/reverification and `scripts/check.sh`.
