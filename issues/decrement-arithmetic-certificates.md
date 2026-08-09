# Make decrement arithmetic replay consistently

Returning an object from a bounded pool exposed disagreements among arithmetic
search, simplification, overflow checking, and certificate replay for ordinary
signed decrement facts.

The required implications are small and deterministic:

- `x >= 0` rules out signed overflow in `x - 1`;
- `x > 0` implies `0 <= x - 1` and `x - 1 < x`; and
- `x == y` implies `x - 1 == y - 1` when both subtractions are defined.

Signed comparison canonicalization must also preserve the polarity and operand
order of `<`, `<=`, `>`, and `>=`. Search succeeding under one spelling while
replay rejects an equivalent spelling is a correctness bug.

## Regression

Add kernel-level tests for each implication and one Click contract that
decrements a nonzero counter while preserving a nonnegative invariant and an
equality to a logical resource count.

## Acceptance criteria

- Overflow decisions use the weakest correct bound.
- All four signed comparison spellings canonicalize consistently.
- `simp` and explicit certificate replay prove the same decrement goals.
- The regression completes within simple-tactic budgets.
