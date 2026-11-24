# Pool control rejects duplicate authority

```c filename=pool_control.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void checkout(struct pool* pool, struct payload* p) {
    pool->checked_out = pool->checked_out + 1;
}
```

```click
import click::integer;

authorized resource slot(pool: struct pool*) {}
authorized resource item(pool: struct pool*, p: struct payload*) { owns *p; }
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
verifying "pool_control.c";
void checkout(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes *p;
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by {
    with(control(pool)) {
        have 1 <= count(slot(pool)) by close();
        unfold(slot(pool));
        step();
        fold(item(pool, p));
        have pool->capacity == pool->checked_out + count(slot(pool)) by close();
    }
}

```

```expect
fail: repeats a population authority
```
