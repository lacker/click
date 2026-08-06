# Certify sequential frontier-loop exit arithmetic

## Problem

A grouped proof can construct and replay two frontier-local loop rules in
sequence, derive that both exit indices equal one, and verify the final return
step. Fresh whole-contract kernel certification then rejects the same return
expression `i + j` as possible signed overflow.

This is a replay/certification disagreement. The two loop invariants bound
each index between zero and one, and each false exit guard fixes it to one.
Do not change the C return expression or concretely unroll either loop.

## Minimal regression

Use unchanged C with two sequential one-iteration counting loops followed by
`return i + j`. Prove each loop at its frontier with `0 <= index <= 1`, then
return. The proof replay and fresh certification must agree that the addition
is safe and returns two.

## Acceptance criteria

- Both verified loop rules apply in sequence during independent contract
  certification.
- Exit invariants and false guards provide the arithmetic facts needed for
  the final addition's no-overflow condition.
- Replay and certification produce the same return path.
- The migrated `later_loop_preserve` mdtest passes without changing its C or
  adding redundant implementation operations.
