# Preserve load identity in marked fact transport

After storing `obj->value = 11`, a marked proposition such as
`at(after_write, obj->value == 11)` lowers to the constant truth `11 == 11`.
That proves the fact at the mark, but erases the address and memory snapshot
needed to transport it across later opaque calls. Smart transport may find the
internal frame argument while its emitted surface certificate cannot replay.

This should be solved in fact lowering or transport certification. The example
must not add redundant C assignments or proof-only fields to keep the load
symbolic.

## Regression

Store a constant through an owned pointer, mark the frontier, call an opaque
function whose mutable footprint is disjoint from that pointer, and transport
the marked equality to the current frontier. Cover transport before function
exit and deferred post-execution transport.

## Acceptance criteria

- The checked source retains enough load/snapshot identity for framing.
- A smart transport emits explicit premises and replays.
- Post-execution transport emits the same replayable evidence rather than
  reporting that no surface-premise certificate exists.
- Mutation of the marked location makes the corresponding negative regression
  fail.
