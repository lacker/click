# A drained pool proves its free-slot count by searching entry requirements

A pool control relates `capacity` to `checked_out` plus the free-slot count,
and `checked_out` to a second population count. A drained pool's spare-slot
query requires both fields zero. After unfolding, the unproved `have` must
search a chain through the entry requirements and the unfolded facts. Its
candidates present field loads at the function-entry state, and synthesis
must skip a load variable whose registered load is in another memory epoch
rather than pairing it with the current load.

```c filename=drained_pool_spare.c
struct pool { int32 checked_out; int32 capacity; };
int32 pool_spare(struct pool* pool) { return pool->capacity - pool->checked_out; }
```

```click
authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*) {}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool));
    fact pool->checked_out == count(pool_object(pool));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
verifying "drained_pool_spare.c";
int32 pool_spare(struct pool* pool) {
    owns pool_control(pool);
    requires pool->checked_out == 0;
    requires pool->capacity == 0;
    ensures result == count(pool_slot(pool));
} by {
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool));
    fold(pool_control(pool));
    open(pool_control(pool)) { step_until(function.exit); }
    solve();
}
```

```expect
pass
```
