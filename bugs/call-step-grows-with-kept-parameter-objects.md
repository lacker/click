# A call step grows with the caller's other owned parameter objects

A call `step` must cost work proportional to the call: its arguments, its
contract, and the memory it may write. A call that touches only two arrays
costs work that grows with every other object the caller owns, and faster
than linearly.

Reproduced on master `0d2b58555`:

```sh
python3 scripts/step-scaling-hunt.py many_objects objects_and_calls deep_chain --sizes 1,8,32,64
```

In `many_objects` the call `touch(flags, data, k)` beside N owned
`struct box*` parameters charges 4,098, 10,866 and 27,058 units at N = 8, 32
and 64; in `deep_chain` (N linked owned nodes) 5,317, 17,125 and 47,205. With
N objects and N calls (`objects_and_calls`) the whole proof is quadratic:
1,723,912 units at N = 64. Every parameter object sits in the shared
`ExternalArgument` block, so each is a candidate for the call's write set and
for what the caller keeps, and is examined at every call.

Diagnosis (master `b1523c784`): two thirds of the call's work is the same
walk as `field-store-step-grows-with-owned-parameter-objects.md`.
`with_call_memory_havoc` → `forget_cached_values` visits every cached cell
of the `ExternalArgument` block, and here each visit runs an order-fact
search (`proves_element_endpoint_order`, `condition_order_facts`), so the
call costs about 400 units per other object, against 16 for a store.
Fixing that walk likely fixes both.

Acceptance: a multi-size regression over `many_objects` and `deep_chain`
shows the call step's work and time constant in the number of owned objects
the call neither takes nor may write, up to logarithmic factors; the caller
still keeps each object's cached values across the call; no budget or
threshold is raised.
