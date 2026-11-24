# A helper cannot call checkout without transferring a slot

The bound requirement isolates the missing slot: counter increment safety is
available, but a control with zero slots cannot satisfy the callee's consumption.

```c filename=checkout_helper.c
struct pool { int32 checked_out; int32 capacity; };
struct object { int32 value; };
void pool_checkout(struct pool* pool, struct object* object) {
    pool->checked_out = pool->checked_out + 1;
}
void forward(struct pool* pool, struct object* object) {
    pool_checkout(pool, object);
}
```

```click
import click::integer;

authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns *object; }
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
verifying "checkout_helper.c";
void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    requires pool->checked_out < 2147483647;
    consumes pool_slot(pool);
    consumes *object;
    produces pool_object(pool, object);
} by {
    with(pool_control(pool)) {
        have 1 <= count(pool_slot(pool)) by close();
        have defined(pool->checked_out + 1);
        unfold(pool_slot(pool));
        step();
        fold(pool_object(pool, object));
        have pool->capacity == pool->checked_out + count(pool_slot(pool));
    }
}
void forward(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    requires pool->checked_out < 2147483647;
    requires count(pool_slot(pool)) == 0;
    consumes *object;
    produces pool_object(pool, object);
}
```

```expect
fail: population call transfer refused: fewer members of the population are held than the transition moves
```
