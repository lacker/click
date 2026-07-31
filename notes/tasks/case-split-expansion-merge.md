# Faithful expansion of pure case-split certificates

Status: in progress
Claimed: claude/nervous-ptolemy-90e738 (worktree agent-a5e4815eaf1c6351a), 2026-07-31

Two quarantined mdtests (`sort3_sorted.md`, `bubble_sort3_loop_sorted.md`)
have smart simps over budget (2.2 s / 3.5 s) whose entire content is a
case split: the ACCEPTED certificate is an `if` tree with empty
branches, each leaf goal closing via the ordinary path-end check.
Empty `if` branches are now legal surface Click (owner decision
2026-07-31, pinned by lib test
`empty_proof_if_branches_contribute_only_their_case_split`), but the
expansion still does not re-verify: path 5 of expanded sort3 cannot
close `sorted(p, 3)` from its branch conditions.

Root cause: the merge of per-path certificates into ONE surface `if`
tree (`synthesize_surface_paths` / `append_surface_tactics_by_leaf`,
src/lang/click/proof.rs) is unfaithful for this shape. Certificate
replay pairs each execution path with its own branch trace; the
printed tree re-splits every execution path and the pairing is lost.

Dead end (do not re-attempt): `assumption();` as a leaf filler — fails
replay because leaves hold no open goal.

Direction: make the merge preserve the execution-path/branch-trace
pairing, or emit per-path scripts instead of one merged tree.

Repro:
```
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=sort3_sorted cargo test --test mdtests
cargo run --quiet --bin click-expand -- --time-limit 5m mdtests/sort3_sorted.md:50:9
```

Done when: both tests expand, pass within budget, and de-quarantine.
