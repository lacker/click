# Scoped composite close disagrees with allocation certification

## Violated invariant

Opening and closing a composite resource is a checked change of ghost resource
representation. Once the scope is closed, it must not change the subsequent C
memory transition or retain counted-population state that is absent from an
independent kernel execution of the same function. In particular, an opaque
call that replaces and retires an allocation must retire the same allocation in
proof replay and independent certification.

## Reproduction

In `examples/owned-vector/vector.click`, replace the persistent
`observe(allocated_vector(owner))` in the full-capacity branch of
`allocated_vector_push` with an `open(allocated_vector(owner)) { ... }` scope
around the three preparatory steps. Close the scope before the existing
multi-successor-aware call step:

```click
step() using {
    owner->cap <= 536870910;
}
```

With provisional ensure loadability lowered as explicit obligations, the call
step finishes promptly. The proof then fails in the successful `vector_grow`
branch with `execution replay ... contains a path not reproduced by kernel
certification`.

The replay path keeps both the consumed and returned allocations live and
retains counted populations for `allocation`, `vector_storage`, and
`allocated_vector`. Independent certification either retires the consumed
allocation or follows the distinct unchanged-allocation outcome; it produces no
path with both allocations live. The mismatch is therefore earlier than final
resource-representation certification and cannot be accepted as a harmless
fold/unfold difference.

## Intended regression

Build a small composite resource containing an allocation token and its owned
range. Open and close it before a verified call with failure and success
outcomes, where success returns a distinct allocation and retires the input.
Check the complete proof path against fresh independent certification. The
success paths must agree on the live/retired allocation sets and must not retain
population entries introduced only by the closed scope; the failure paths must
agree that the original allocation remains live.

## Acceptance criteria

- The reduced regression fails with the current replay/certification mismatch
  and passes without editing the C or weakening its contract.
- Closing the scope restores the exact pre-open counted-population state except
  for changes explicitly made inside the scope.
- Proof replay and independent certification produce matching live and retired
  allocation sets for every call outcome.
- The scoped `allocated_vector_push.contract` advances past path pairing under
  the ordinary 30-second limit.
- The focused regression and `scripts/check.sh` are green, and this issue is
  deleted when the fix lands.
