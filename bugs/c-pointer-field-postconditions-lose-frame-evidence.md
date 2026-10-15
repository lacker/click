# C pointer-field postconditions lose checked frame evidence

Priority: P1.

Soundness: incomplete. The verifier rejects unchanged supported C proofs. This
reproduction does not demonstrate acceptance of a false claim.

In the initial PR 646 bounded-object-model reproduction, the original
`examples/owned-vector/vector.click` rejects `vector_push` at its final
`assumption` steps: `owner->data == old(owner->data)` and
`owner->data[old(owner->len)] == value` remain unproved. The C body stores through
the backing pointer and then increments the descriptor's length. Its
`vector_storage` contract already separates the entire descriptor from the
backing range, and its precondition places the index inside that range.

A focused reproduction uses the unchanged `vector_push.c`, the original
`vector_storage` definition, and the original `vector_push` contract/proof;
other functions and resources are unnecessary. Inserting the diagnostic-only
claim `have owner->data == old(owner->data) by { assumption(); }` immediately
after the existing `fold(vector_storage(owner))` exposes the failure with
`--trace-proof vector_push`. The trace stops the eight-byte pointer-field read
at the four-byte backing-element store. Adding that same claim with `simp`
closes the pointer equality but still leaves the stored-element postcondition
unproved. Neither experiment changes the C or weakens its claims.

Private instrumentation found selected separation evidence whose write and
full read memberships both check, with no alias veto. That does not yet
identify why the failing comparison cannot use the evidence; do not replace
this investigation with an address-only origin rule. The original
`examples/owned-string/owned_string.click` also fails its stored-element
postcondition after the same kind of backing write.

Acceptance criteria:

- Verify the original vector and string projects with their C and claims
  unchanged, including the original frame and stored-value postconditions.
- Reduce the missing comparison into a regression that verifies, expands,
  verifies its rewritten proof, and rechecks a retained certificate.
- Reject controls removing the separation or allowing the write to overlap
  the descriptor, and reject a wrong stored-value claim.
- Preserve full pointer origins: numeric address equations must not establish
  native place validity or replace the pointer stored in a field.
- Keep existing proof and timing limits; profile only after the proof succeeds.

## Current progress after the scoped read-producer repair

PR #1023 fixes the intervening two-write execution gap. Explicit checked
equalities now prove the original `owned_string_set` and `vector_push`
contracts: the setter proves its stored element with `simp`, and vector push
proves its backing pointer unchanged and its stored element before folding.
The final `assumption` steps remain exact-fact lookup; no kernel rule changes.

The complete recovery projects are still rejected. String push reaches the
terminator equality `owner->data[owner->len] == 0`; its trace distinguishes the
pointer read used by the zero store from the later projected pointer read. A
direct `simp` attempt also rejects that equality despite the held
descriptor/backing separation. Vector proceeds past `vector_push` and fails a
later `allocated_vector_push` allocation-resource fold. Keep this report open
until its full-project acceptance criteria are met.
