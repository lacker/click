# Owned-string proof exceeds the example budget

The certificate-spelling and loadability failures in `owned-string` are fixed:
targeted verification passes for both `owned_string_push.contract` and
`owned_string_pop_preserves_first.contract`. The complete project still exceeds
the example harness's 10-minute per-project budget, so it remains quarantined
for performance only.

The last complete push profile before the correctness repair finished showed
the main known costs in `owned_string_push.contract`: about 96 s in the smart
`simp` at `owned_string.click:270`, 13 s in the smart `have` at line 256, and
8 s in the simple `fold` at line 268. The full gate now gets beyond the old
failure frontier, so re-profile the whole project and expand the slow smart
tactics before investigating any remaining slow simple replay.

Repro: `CLICK_EXAMPLE=owned-string cargo test --test examples example_projects
-- --nocapture`.

Done when: the unquarantined project passes inside the default 10-minute
example budget.
