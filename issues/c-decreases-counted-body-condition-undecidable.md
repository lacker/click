# C decreases cannot decide a counted resource body condition

`mdtests/c_decreases_resource_mutating_nullable.md` fails while applying the
recursive `list_destroy` contract. After unfolding the non-null list node,
Click reports that the counted population `allocated_list` body condition is
not decidable. The failure reproduces at commit `3e09380` and is independent
of restricted-simplification replay.

Quarantine this focused regression until contract application preserves or
reconstructs the condition needed to identify the recursive child population.
Do not reshape the recursive C or weaken its resource contract.

## Acceptance criteria

- The unchanged mdtest verifies within the normal tactic budget.
- Contract application decides the counted body condition from the certified
  branch and resource facts, without ambient fallback search.
- The mdtest leaves quarantine.
