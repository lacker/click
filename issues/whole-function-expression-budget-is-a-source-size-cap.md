# Whole-function expression budget is a source-size cap

## Violated invariant

A supported straight-line C function must not fail certification merely because
its explicit source contains more expression nodes than a fixed execution
budget. Execution bounds should stop dynamic expansion such as unrolling,
recursive calls, or path explosion; they must not impose an undocumented
whole-function source-length limit.

On current master, a generated function containing repeated `x = x;`
assignments reaches `kernel certification hit execution limit ExpressionSteps`
at exactly 3,333 assignments. Each assignment consumes three units from the
fixed 10,000-unit `ExecutionBudget::default()` expression allowance. A release
build verifies 3,000 assignments (6,011 combined C and Click lines) in about
0.45 seconds, while 3,333 assignments fail promptly. The failure remains after
path width and statement-tree accounting are corrected, so it is independent
of those bugs.

Do not repair this by raising the fixed constant. The budget needs to
distinguish work proportional to selected explicit source from extra dynamic
execution work.

## Intended regression

- Generate a straight-line function and explicit proof large enough to cross
  the old 10,000-expression cutoff, and require successful certification.
- Measure deterministic work at four geometric sizes and retain the existing
  near-linear bound.
- Keep a separate adversarial regression showing that genuinely expanding
  execution still exhausts its relevant dynamic budget.

The ordinary regression should use the smallest size that crosses the old
cutoff. The 5,000- and 10,000-assignment release fixtures are corroborating
capacity and latency checks, not required additions to every debug gate.

## Acceptance criteria

- Explicit straight-line source does not consume a fixed global allowance as
  though it were dynamic expansion.
- The replacement accounting states which work is proportional to selected
  source and which work is bounded independently.
- No default limit is raised merely to move the cutoff.
- The generated regression fails on the old accounting, passes on the new
  accounting, and preserves near-linear deterministic work.
- The 5,000-assignment release fixture verifies successfully; the
  10,000-assignment fixture either verifies within the ordinary project
  deadline or exposes a separately named non-budget bottleneck.
