# memory reads in requires stay within the declared view

An indexed read in a `requires` proposition is rejected when the function's
entry resources do not cover the requested element.

```c filename=requires_memory_read_out_of_view.c
int32 first(int32 a[], int32 n) {
    return a[0];
}
```

```click
verifying "requires_memory_read_out_of_view.c";

int32 first(int32 a[], int32 n) {
    requires 1 <= n;
    requires a[1] == 7;
    views a[0..1];
    ensures result == 7 by {
        execute();
        simp();
    }
}
```

```expect
fail: missing pure fact: loadable
```
