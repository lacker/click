# a fully initialized aggregate return still verifies

The uninitialized-source check on aggregate copies must not reject returns
whose fields are all written. Both the return materialization and the
caller's assignment of the call result go through the centralized check, so
a fully written struct returns and reads back normally.

```c filename=aggregate_return_initialized_verifies.c
struct point {
    int32 x;
    int32 y;
};

struct point make_point() {
    struct point p;
    p.x = 3;
    p.y = 4;
    return p;
}

int32 read_point() {
    struct point q = make_point();
    return q.x + q.y;
}
```

```click
verifying "aggregate_return_initialized_verifies.c";

struct point make_point() {
    ensures result.x == 3;
    ensures result.y == 4;
} by {
    auto;
}

int32 read_point() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
