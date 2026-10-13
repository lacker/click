# simp proves defined over a field read through a produced resource

After `init(pool, 1)`, `pool` is reached through the resource `control(pool)`
that `init` produced, so `defined(pool->capacity - 1)` lowers to the
subtraction's overflow condition together with the definedness of the read.
`simp` proves `defined(pool->capacity)` as a nested `have` and cites it,
beside the bound `pool->capacity == 1`, in the `int32_defined` rule, which
accepts the read's definedness as a cited premise.

```c filename=simp_defined_read_through_a_produced_resource.c
struct pool { int32 used; int32 capacity; };
void init(struct pool* pool, int32 capacity) { pool->capacity = capacity; }
void f(struct pool* pool) { init(pool, 1); }
```

```click
resource control(pool: struct pool*) {
    owns *pool;
}
verifying "simp_defined_read_through_a_produced_resource.c";
void init(struct pool* pool, int32 capacity) {
    consumes *pool;
    produces control(pool);
    ensures pool->capacity == capacity;
} by { step(); fold(control(pool)); execute(); }
void f(struct pool* pool) {
    consumes *pool;
    produces control(pool);
} by { step(); have defined(pool->capacity - 1) by simp; execute(); }
```

```expect
pass
```
