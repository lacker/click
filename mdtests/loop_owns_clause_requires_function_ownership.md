# A loop may not own a resource the function does not own

A loop's `owns` clause takes its resource out of the enclosing resource
context, exactly as a call takes a callee's requirement out of its caller's.
The function only views `q[0..1]`, so the loop cannot own it.

```c filename=loop_owns_clause_requires_function_ownership.c
void loop_owns_clause_requires_function_ownership(int32 p[], int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_owns_clause_requires_function_ownership.c";

void loop_owns_clause_requires_function_ownership(int32 p[], int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    requires loadable(q[0..1]);
    owns p[0..n];
    views q[0..1];
    requires separate(memory(p[0..n]), memory(q[0..1]));
} by {
    step();
    step();
    loop {
        owns p[0..n];
        owns q[0..1];
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
fail: loop declares a resource the enclosing function does not hold
```
