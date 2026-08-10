# Bounded Pool

This project verifies a fixed-capacity checkout protocol. The C pool stores
only its capacity and current checkout count; object storage remains ordinary
caller-owned memory.

`pool_object(pool, object)` is the transferable permission and responsibility
for one checked-out object. Its body owns that object's memory. Equal resource
units use Click's ordinary quantity model, while
`count(pool_object(pool, _))` sums all distinct checked-out objects belonging
to one pool.

`valid_pool(pool)` is a copyable predicate rather than a resource. It relates
the C counter to the current resource population and enforces the capacity
bound. Checkout consumes ordinary object memory and packages it into the
resource; return consumes the resource and gives the object memory back.
Because declared resources may have multiple equal units, that final return
explicitly requires `count(pool_object(pool, object)) == 1`; only the last
unit may unwrap the population-wide body into raw object ownership.

The pipeline checks out two objects, mutates both through scoped `open` blocks,
and returns them in the opposite order before destroying the empty pool. The C
implementation contains only the runtime operations; all ownership adaptation
stays in the Click sidecar.
