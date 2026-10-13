# Checked arithmetic in both the premises and the goal

The symbolic child-size bound must be decomposed before deriving the bound on
an incremented size. Both the premise subtraction and the goal operations need
independent evidence that they do not overflow.

```c filename=bounds.c
int32 bounds(int32 left, int32 right) { return 0; }
```

```click
verifying "bounds.c";
int32 bounds(int32 left, int32 right) {
    requires 0 <= left;
    requires left <= 2147483646;
    requires 0 <= right;
    requires right <= 2147483646;
    requires left <= 2147483646 - right;
    ensures result == 0;
} by {
    have 1 + left <= 2147483647 - right by {
        arithmetic() using {
            0 <= left;
            left <= 2147483646;
            0 <= right;
            right <= 2147483646;
            left <= 2147483646 - right;
        }
    }
    execute(); simp();
}
```

```expect
pass
```
