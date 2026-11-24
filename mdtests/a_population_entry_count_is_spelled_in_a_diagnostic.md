# A population entry count is spelled in a diagnostic

A population's count at function entry is an opaque kernel symbol. A
diagnostic spells it as the count it is, `old(count(pool_slot(pool)))` or
`old(count(pool_object(pool, _)))`, rather than as an unnamed value. The
closing ledger fact below is off by one, so the proof fails and lists the
consumed-member bound on the entry slot count among its premises. The explicit
`known` failure exercises that diagnostic without searching for a proof
of the deliberately false ledger equality.

```c filename=a_population_entry_count_is_spelled_in_a_diagnostic.c
struct pool {
    int checked_out;
    int capacity;
};

struct object {
    int value;
};

void pool_checkout(struct pool *pool, struct object *object) {
    pool->checked_out = pool->checked_out + 1;
}
```

```click

verifying "a_population_entry_count_is_spelled_in_a_diagnostic.c";
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
void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    consumes pool_slot(pool);
    consumes *object;
    produces pool_object(pool, object);
    ensures pool->checked_out == old(pool->checked_out) + 1;
} by {
    with(pool_control(pool)) {
        have count(pool_slot(pool)) >= 1;
        have defined(count(pool_object(pool, _)) + 1);
        have defined(pool->checked_out + 1);
        unfold(pool_slot(pool));
        step();
        fold(pool_object(pool, object));
        have defined(old(pool->checked_out) + 1);
        have to_integer(pool->checked_out) == to_integer(count(pool_object(pool, _)));
        have to_integer(pool->capacity)
            == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool))) + 1 by close();
    }
}
```

```expect
fail: 1 <= old(count(pool_slot(pool)))
```
