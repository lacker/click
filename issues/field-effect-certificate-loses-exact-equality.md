# Field-effect expansion loses an exact equality

`mdtests/field_derived_precise_effect_after_metadata_write.md` verifies its
smart execution search but the generated surface certificate does not replay.
The initially reported field-equality mismatch is only the first symptom. An
exact diagnostic reduces the final failure to the opaque call result:

```click
have ignored == at(statement(1).entry, (owner->len + 1)) by {
    assumption();
}
```

The contract postcondition is represented internally as
`defined(old_len + 1) -> result == old_len + 1`. Smart call planning proves the
signed-addition guard from the function's arithmetic preconditions and exposes
the consequent. Generated `step() using` replay retains only the guarded fact,
so the direct equality is not an exact assumption.

This exposes a broader provenance gap: smart planning records the higher-level
comparison facts used to derive an evaluator guard, but not a replayable
certificate for the guard itself. Merely changing snapshot spellings, accepting
an equivalent equality in `assumption`, or making `step() using` repeat ambient
arithmetic search would hide that gap.

The preferred fix is to make accepted precondition definedness explicit.
`requires owner->len + 1 < owner->cap` should give the function proof both
`defined(owner->len + 1)` and the comparison. Precise call provenance should
retain the exact consumed definedness fact, surface synthesis should spell it
as `defined(...)`, and guarded postconditions should be discharged only from
that certified fact. If that model is rejected, Click instead needs a named
simple arithmetic certificate for deriving definedness; it must not put the
derivation back into simple replay as a fallback.

This is an expansion/replay bug, not permission to retain a smart tactic,
weaken the post-write claim, discard a relevant call-result fact, or add
redundant proof facts to the mdtest.

After the `SimpleProof` boundary refactor, the failure is localized to the
final phase: smart search constructs a well-formed `SimpleProof`, but its
independent replay rejects the last `step() using` because the direct call
result equality is unavailable. This is not a `SimpleProof` construction or
surface-printing failure; the execution planner supplied an incomplete simple
proof.

## Acceptance criteria

- The unchanged mdtest verifies and its generated certificate replays.
- Function-entry arithmetic preconditions expose their checked definedness
  facts explicitly.
- Call provenance and `step() using` name the exact definedness fact consumed
  while applying the contract; simple replay performs no ambient arithmetic
  search.
- The direct call-result postcondition is published only after its guard has
  been certified, and its exact surface equality replays by `assumption`.
- The mdtest leaves quarantine.
