# memory reads in requires propositions

An indexed read in a `requires` proposition is evaluated against the
function-entry memory and may be justified by the function's view resource.

```c filename=requires_memory_read.c
int32 first(int32 a[], int32 n) {
    return a[0];
}
```

```c filename=requires_memory_read_caller.c
int32 caller(int32 a[], int32 n) {
    int32 result;
    result = first(a, n);
    return result;
}
```

```c filename=requires_memory_read_forall.c
int32 sorted_first(int32 a[], int32 n) {
    return a[0];
}
```

```click
verifying "requires_memory_read.c";
verifying "requires_memory_read_caller.c";
verifying "requires_memory_read_forall.c";

int32 first(int32 a[], int32 n) {
    requires 1 <= n;
    requires a[0] == 7;
    views a[0..n];
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 caller(int32 a[], int32 n) {
    requires 1 <= n;
    requires a[0] == 7;
    views a[0..n];
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 sorted_first(int32 a[], int32 n) {
    requires 1 <= n;
    requires forall (k: int32) {
        0 <= k and k < n - 1 implies a[k] <= a[k + 1]
    };
    requires a[0] == 7;
    views a[0..n];
    ensures result == 7 by {
        execute();
        simp();
    }
}
```

```expect
pass
```
