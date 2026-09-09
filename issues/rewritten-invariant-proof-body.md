# Express the rewritten invariant proof body

## Violated invariant

A smart proof that finds a derivation must produce an independently checkable proof body.
This tooling failure blocks the explicit sorting proof and automatic invariant
body migration. It is not evidence that a new memory-equality rule is needed.

## Reproduction

Run `cargo nextest run --lib explicit_sorting_rewritten_invariant_reports_body_failure`.
The regression loads the unchanged C, contract, and invariants from
`mdtests/bubble_sort3_two_pass_sorted.md`. It expands the original verifying
proof, then adds explicit steps to the second loop's swap arm:

1. Prove entry `j == 0`, instantiate the two maximum bounds, and mark entry.
2. Execute the unchanged swap and increment.
3. Transport the two maximum bounds to their swapped destination cells.
4. Enumerate the fixed-range maximum invariant.
5. Prove current `j == 1`, transport the indexed strict branch comparison to
   `p[0] < p[1]`, and apply `int32_lt_implies_le`.
6. Prove `all_le_range(p, 0, j, p[j])` with
   `unfold(all_le_range); rewrite(j == 1); simp();`.

The last body fails with `have body is not surface-expressible`, with
`CertificateError { tactic_class: Smart(Simp), path: [Tactic(2)] }`.
The focused run returns in roughly four seconds, without overflow or timeout.
The failing proof is not expanded. Explicit-body execution invokes zero legacy
invariant discovery calls. The invariant is true: the swap orders cells 0 and
1, and the index after this singleton iteration is 1.

Replacing the last `simp` with `enumerate` reports missing exact instances.
Omitting the rewrite makes enumeration reject nonconstant bounds; `simp`
without that rewrite reports a derivation with no explicit simple proof for
the universal proposition. These are diagnostic alternatives, not fixes.

## Acceptance criteria

- Reduce the rewritten-goal/body conversion failure while retaining the
  original sorting regression, and repair its proof-object/source boundary.
- Replace the expected error with positive verification, expansion, and
  independent rewritten verification, without legacy invariant discovery.
- Do not change C, weaken invariants, increase budgets, or enable automatic
  migration as part of diagnosing this failure.
- Run `scripts/check.sh`; delete this issue and its index line when fixed.
