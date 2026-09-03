# Rank count-up loops, nested loops, recursion in loops, and compound measures

Found by the 2026-09-01 kernel audit at cb034b21.

The loop ranking checker accepts only a measure decremented in place as
`measure = measure - K` for positive constant `K` (`src/kernel/termination.rs:745-751`;
`refined_lower_bound` and `check_loops` at `:536-833` track a single
decremented variable). The canonical `while (i < n) { i = i + 1; }` decrements
nothing, so the most common loop shape cannot be ranked. Nested loops are
rejected (`:775-777` "nested loops in one ranking proof are not yet
supported"); a recursive call inside a loop is rejected (`:445-454`,
`:719-728` "recursive calls inside a loop require a lexicographic measure");
the surface accepts only one named int32 variable as a measure
(`src/surface/verification.rs:1440-1451` "compound ranking expressions are
not yet supported"); structural-resource termination supports direct,
simply-guarded recursion only (`termination.rs:477-527`, `:919-921`).

## Violated invariant

Click's optional termination judgment should cover the loop and recursion
shapes real C uses: count-up loops with a bounded guard, nested loops,
lexicographic measures, and recursion mixed with iteration.

## Progress in the first implementation slice

Loop termination plans now carry checked C expressions rather than only a
variable name. The kernel tracks scalar aliases and update-sugar assignments
on every back-edge path, checks the expression and its post-body value as
int32 arithmetic, and uses certified function preconditions and loop
invariants as ranking assumptions. A count-up regression using `n - i` is in
`mdtests/c_decreases_count_up.md`; nested-loop and lexicographic propagation
are still open.

## Intended regression

Mdtests with `decreases` clauses: `for`-style count-up over `n - i`; a
doubly nested scan with a lexicographic `(n - i, m - j)` measure; a binary
search on `hi - lo`; a loop that calls a recursive helper on a strictly
smaller argument; a mutually recursive pair with a shared measure. Each must
pass as an mdtest with its `decreases` clause (a `decreases` that cannot be
ranked fails verification, as in `mdtests/c_decreases_rejects_bad_loop_path.md`)
or be reported terminating by `function_termination_is_verified` in
`src/surface/tests/loop_tests.rs`, and each with the measure deliberately
non-decreasing must expect `fail: ... does not decrease`.

## Acceptance criteria

- Measures are arbitrary int32 expressions over program variables (with the
  measure's well-foundedness checked as `0 <= measure` under the guard), not
  a single decremented variable.
- Lexicographic tuples of such expressions are supported for nested loops
  and for recursion inside loops.
- The surface plan carries the expression and the kernel re-lowers and checks
  it, in keeping with the untrusted-plan design in `docs/internals/kernel.md`.
- The mdtests above pass; `scripts/check.sh` passes.

Note: the ranking rejects any measure whose address is taken
(`reject_address_escaped_measure` in `src/kernel/termination.rs`); a richer
measure language must keep that check for every variable a measure mentions.
