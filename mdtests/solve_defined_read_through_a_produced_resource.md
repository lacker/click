# solve proves defined over a field read through a produced resource

After `init(pool, 1)`, `pool` is reached through the resource `control(pool)`
that `init` produced, so `defined(pool->capacity - 1)` lowers to the
subtraction's overflow condition together with the definedness of the read.
The callee explicitly exports the typed validity of its written capacity cell.
`solve` retains `defined(pool->capacity)` separately from the arithmetic
bounds on the exact difference. Those ordinary facts establish the complete
definedness goal.

```c filename=solve_defined_read_through_a_produced_resource.c
struct pool { int32 used; int32 capacity; };
void init(struct pool* pool, int32 capacity) { pool->capacity = capacity; }
void f(struct pool* pool) { init(pool, 1); }
```

```click
resource control(pool: struct pool*) {
    owns *pool;
}
verifying "solve_defined_read_through_a_produced_resource.c";
void init(struct pool* pool, int32 capacity) {
    consumes *pool;
    produces control(pool);
    ensures pool->capacity == capacity;
    ensures defined(pool->capacity);
} by { step(); fold(control(pool)); }
void f(struct pool* pool) {
    consumes *pool;
    produces control(pool);
} by { step(); have defined(pool->capacity - 1) by close(); }
```

```expect
pass
```
