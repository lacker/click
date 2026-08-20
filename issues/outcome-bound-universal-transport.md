# Close bound universal outcomes with explicit specialization and transport

## Violated invariant

An outcome `simp` over a universal predicate should remain on its checked
`Proof` when the target binder determines one specialization and loop-exit
facts transport that specialization to the postcondition. The remaining direct
path can specialize only when the instantiated conclusion already equals the
focused goal. It falls back when, for example, the invariant concludes
`p[k] <= p[j]` and checked exit facts establish `j == 2`, making the target
`p[k] <= p[2]`.

The smart layer must select and retain an explicit sequence: introduce the
goal binder and guard, establish only the instantiated premise guards, apply
`InstantiateUsing`, apply `TransportUsing` when required, and close by
`Assumption`. It must not scan all universals, all path facts, or rerun the
legacy certificate planner.

## Current reproductions

The only passing fixtures in the 2026-08-19 census that still enter legacy
exit planning are:

- `mdtests/bubble_pass3_max_suffix.md`
- `mdtests/bubble_sort3_two_pass_sorted.md`

The expanded legacy certificate for the first fixture specializes the loop
invariant at the introduced `k`, names the goal guard and the two exit-order
facts, transports `p[k] <= p[j]` to `p[k] <= p[2]`, and closes by assumption.
That is the required explicit vocabulary; the legacy planner is not proof
authority to preserve.

## Intended regression

- A focused outcome proof introduces a universal binder, proves an
  instantiated guard from a bounded set of selected order facts, retains one
  `InstantiateUsing` and one `TransportUsing`, and independently replays.
- A multi-size curve grows unrelated universals and path facts while candidate
  selection visits only the unfold-owned universal bucket, target-guided
  arguments, and the selected guard/equality evidence.
- Both source fixtures assert absence of the compatibility and legacy spans.

## Acceptance criteria

- Both reproductions verify without either outcome fallback span.
- Every semantic transition is represented by a checked simple or structured
  step retained on the same `Proof`; no successful result comes from legacy
  planning or certificate reconstruction.
- No C or Click source is weakened or reshaped for the verifier.
- Expansion independently verifies and `scripts/check.sh` passes.

