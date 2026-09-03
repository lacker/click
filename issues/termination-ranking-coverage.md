# Rank count-up loops, nested loops, recursion in loops, and compound measures

Found by the 2026-09-01 kernel audit at cb034b21.

The original loop ranking checker accepted only a single measure decremented
in place as `measure = measure - K` for positive constant `K`. That excluded
count-up loops and phase-style loops whose progress is naturally described by
more than one value. Recursive calls inside loops remain a separate unsupported
shape. Structural-resource termination also remains limited to direct,
simply-guarded recursion.

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
`mdtests/c_decreases_count_up.md`. Loop-local lexicographic tuples are now
represented as checked vectors of scalar expressions and are proved by a
strictly decreasing pivot after equal earlier components; the phase-loop
regressions are in `mdtests/c_decreases_lexicographic_loop.md` and
`mdtests/c_decreases_rejects_non_decreasing_lexicographic_loop.md`. A nested
loop with its own ranking is now summarized as a terminating opaque phase for
the enclosing loop; `mdtests/c_decreases_nested_loop.md` covers an outer first
component that decreases after the phase. Recursive calls inside loops are
still open.

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
- Lexicographic tuples of such expressions are supported for progress within
  one loop's back-edge paths. Separately ranked nested loops are supported as
  opaque terminating phases; aliases for enclosing ranking variables written
  by the phase are forgotten, so enclosing invariants must establish their
  post-phase nonnegativity. Recursive calls inside loops still require a
  separate effect-summary design.
- The surface plan carries the expression and the kernel re-lowers and checks
  it, in keeping with the untrusted-plan design in `docs/internals/kernel.md`.
- The mdtests above pass; `scripts/check.sh` passes.

Note: the ranking rejects any measure whose address is taken
(`reject_address_escaped_measure` in `src/kernel/termination.rs`); a richer
measure language must keep that check for every variable a measure mentions.
