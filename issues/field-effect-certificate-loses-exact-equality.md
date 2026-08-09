# Field-effect expansion loses an exact equality

`mdtests/field_derived_precise_effect_after_metadata_write.md` verifies its
smart execution search but the generated surface certificate does not replay.
The last emitted `step() using` asks for an int32 equality whose equivalent
kernel fact is present under a different representation, so exact-premise
checking rejects it. The failure reproduces at commit `3e09380` and is
independent of restricted-simplification replay.

This is an expansion/replay bug, not permission to retain a smart tactic,
weaken the post-write claim, or add redundant proof facts.

## Acceptance criteria

- The unchanged mdtest verifies and its generated certificate replays.
- Expansion records the exact field-effect equality representation required by
  `step() using`; simple replay does not search for an equivalent fact.
- The mdtest leaves quarantine.
