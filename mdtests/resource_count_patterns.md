# Resource counts accept argument patterns

`_` aggregates every exact population in that argument position. Exact
arguments still select only populations whose identities are proved equal.

```c filename=resource_count_patterns.c
int32 inspect_counts(int32 pool, int32 first, int32 second, int32 other_pool) {
    return 0;
}
```

```click
abstract resource checked_out(pool: int32, object: int32);

verifying "resource_count_patterns.c";

int32 inspect_counts(int32 pool, int32 first, int32 second, int32 other_pool) {
    requires first != second;
    requires pool != other_pool;
    requires count(checked_out(pool, first)) == 2;
    requires count(checked_out(pool, second)) == 1;
    requires count(checked_out(other_pool, first)) == 1;
    requires count(checked_out(pool, _)) == 3;
    requires count(checked_out(_, first)) == 3;
    requires count(checked_out(_, _)) == 4;
    owns checked_out(pool, first);
    owns checked_out(pool, first);
    owns checked_out(pool, second);
    owns checked_out(other_pool, first);

    ensures count(checked_out(pool, first)) == 2;
    ensures count(checked_out(pool, _)) == 3;
    ensures count(checked_out(_, first)) == 3;
    ensures count(checked_out(_, _)) == 4;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
