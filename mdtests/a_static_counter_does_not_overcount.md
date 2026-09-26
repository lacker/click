# a static counter read through a callee's `old` does not overcount

The negative companion of [`static_scalar_locals.md`](static_scalar_locals.md).
The callee's storage for `calls` is materialized when the call enters it, and
its `old(calls)` names that cell. That name is now the load variable of the
cell rather than a raw load of the storage, so the caller's `calls == 5` and
the callee's `old(calls)` are one term. Joining them must still count exactly:
two calls add four, and `result == 10` is refused.

```c filename=a_static_counter_does_not_overcount.c
int32 increment_twice() {
    static int32 calls = 5;
    calls = calls + 1;
    calls = calls + 1;
    return calls;
}

int32 call_twice() {
    int32 first;
    int32 second;
    first = increment_twice();
    second = increment_twice();
    return second;
}
```

```click
verifying "a_static_counter_does_not_overcount.c" as static_local;

int32 increment_twice() {
    owns &calls[0..1];
    requires calls < 1000;
    ensures result == old(calls) + 2 by auto;
    ensures calls == old(calls) + 2 by auto;
}

int32 call_twice() {
    owns &static_local::increment_twice::calls[0..1];
    requires static_local::increment_twice::calls == 5;
    ensures result == 10 by auto;
}
```

```expect
fail: unclosed goal
```
