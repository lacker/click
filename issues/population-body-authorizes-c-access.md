# Let active resource populations authorize their bodies

The bounded-pool proof could open `pool_object(pool, object)` and write the
object, but independent whole-function kernel certification reported a missing
memory resource for the same store. Proof replay and kernel certification were
therefore using different representations of the same resource ownership.

An owned declared resource semantically owns its body whether its surface
representation is folded or temporarily opened. C execution must be
authorized by that body without requiring the C source to change and without
creating a second linear copy. Opening it in a proof should expose the existing
ownership, not mint duplicate memory.

## Regression

Have one opaque call consume `object(obj)` and produce `wrapper(obj)`, where
`wrapper` owns `object(obj)`. The caller immediately writes `obj->field` inside
`open(wrapper(obj))`, then passes the wrapper to another opaque call that
returns the raw object.

## Acceptance criteria

- Proof replay and independent kernel certification both accept the caller.
- The direct store is authorized by the wrapper body.
- `open` neither duplicates nor loses the body resource.
- Closing, consuming, and finalizing the wrapper each leave exactly one
  correct resource representation.
- A negative test still rejects access without the wrapper or raw object.
