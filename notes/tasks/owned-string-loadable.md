# owned-string: unfold cannot discharge loadable(data[len])

Status: in progress — agent running (launched 2026-07-31)
Claimed: worktree agent (coordinator session d42775d1)

Example `owned-string` (quarantined in tests/examples.rs) fails in
~2.6 s: in `owned_string_push`, the `terminated_at` smart-have's
unfold cannot discharge `loadable(data[len])`. A permission-plumbing
question, not load equality — independent of the containment-prover
critical path.

Dead end (recorded, do not re-attempt): feeding `replay.effect_facts`
into planning — stores are execution facts, not effect summaries.

Open question the agent may escalate: if the fix wants to extend the
"predicate that reads memory implies readability" ruling to a NEW
position (predicate bodies in have/unfold position), that is the
owner's call.

Repro:
```
./target/debug/click-verify examples/owned-string/owned_string.click
```

Done when: owned-string verifies and de-quarantines.
