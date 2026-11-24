# An empty population counts no member

The count of an exact member is its own term; it never folds to `0` because
the facts prove its population empty. `population_member_count_zero` derives
`count(R(a, k)) == 0` from an available `count(R(a, _)) == 0`. The member's
entry count is spelled `old(count(R(a, k)))`, which lowers to that same
count, so the derived fact is cited in that spelling too.

```c filename=pool.c
struct pool { int checked_out; };
struct object { int value; };
void need_absent(struct pool* pool, struct object* object) {}
void caller(struct pool* pool, struct object* object) { need_absent(pool, object); }
```

```click
authorized resource item(pool: struct pool*, p: struct object*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(item(pool, _));
}
verifying "pool.c";
void need_absent(struct pool* pool, struct object* object) {
    owns control(pool);
    requires count(item(pool, object)) == 0;
}
void caller(struct pool* pool, struct object* object) {
    owns control(pool);
    requires count(item(pool, _)) == 0;
} by {
    with(control(pool)) {
        apply(population_member_count_zero(count(item(pool, object))));
        have old(count(item(pool, object))) == 0 by {
            close();
        }
    }
    step();
    step_until(function.exit);
}
```

```expect
pass
```
