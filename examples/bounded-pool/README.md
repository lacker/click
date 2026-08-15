# Bounded Pool

This project verifies a fixed-capacity checkout protocol. The C pool stores
only its capacity and current checkout count; object storage remains ordinary
caller-owned memory.

`pool_object(pool, object)` is the transferable permission and responsibility
for one checked-out object. Its body owns that object's memory.
`pool_slot(pool)` represents one unoccupied place in the bounded pool. Equal
resource units use Click's quantity model, while
`count(pool_object(pool, _))` sums all distinct checked-out objects belonging
to one pool.

`valid_pool(pool)` is a copyable predicate rather than a resource. It relates
the C counter to the current object population and states that capacity is the
sum of checked-out objects and available slots. Initialization produces
`capacity of pool_slot(pool)` algebraically. Checkout consumes one slot and
packages ordinary object memory into an object resource. Transfer returns a
slot to the source, consumes a destination slot, and moves the object resource
while updating both counters. Return consumes the object resource, gives its
memory back, and produces a slot.
Because declared resources may have multiple equal units, that final return
explicitly requires `count(pool_object(pool, object)) == 1`; only the last
unit may unwrap the population-wide body into raw object ownership.

The pipeline checks out two objects, mutates both through scoped `open` blocks,
and returns them in the opposite order before destroying the empty pool. The C
implementation contains only the runtime operations; all ownership adaptation
stays in the Click sidecar. A second focused pipeline checks out one object
from a source pool and transfers it to a distinct destination pool. It ends at
that API boundary so its postcondition exposes the moved resource directly:
the source population is empty and the destination population contains the
object. A zero-capacity pipeline initializes and destroys an empty pool,
checking that `0 of pool_slot(pool)` is the resource identity rather than a
hidden unit.
