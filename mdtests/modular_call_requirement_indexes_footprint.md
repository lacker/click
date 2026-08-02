# Modular effects may rely on callee requirements

An opaque call must prove the callee requirements and may then use those
requirements while evaluating later contract clauses. Here `1 <= n` rules out
underflow in the precise mutable base `p + (n - 1)`.

```c filename=requirement_indexed_clear_last.c
int32 clear_last(int32 p[], int32 n) {
    p[n - 1] = 0;
    return 0;
}
```

```c filename=requirement_indexed_call_clear_last.c
int32 call_clear_last(int32 p[], int32 n) {
    int32 result;
    result = clear_last(p, n);
    return result;
}
```

```click
verifying "requirement_indexed_clear_last.c";
verifying "requirement_indexed_call_clear_last.c";

int32 clear_last(int32 p[], int32 n) {
    requires 1 <= n;
    owns p[0..n];
    mutable (p + (n - 1))[0..1];
    ensures result == 0;
    ensures p[n - 1] == 0;
} by {
    have 0 <= n - 1 by simp;
    have n - 1 < n by simp;
    execute();
    frame();
    simp();
}

int32 call_clear_last(int32 p[], int32 n) {
    requires 1 <= n;
    owns p[0..n];
    mutable (p + (n - 1))[0..1];
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
