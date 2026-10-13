# A wrapping premise cannot be decomposed as ordinary arithmetic

At `left = 0`, `right = 1`, the wrapped subtraction in the premise is
`INT_MAX`, so that premise holds while the proposed goal is false. The goal's
own operations are safe; the missing evidence belongs to the premise.

```c filename=bounds.c
int32 bounds(int32 left, int32 right) { return 0; }
```

```click
verifying "bounds.c";
int32 bounds(int32 left, int32 right) {
    requires 0 <= left;
    requires left <= 2147483646;
    requires 0 <= right;
    requires right <= 1;
    requires left <= -2147483648 - right;
    ensures result == 0;
} by {
    have 1 + left <= -2147483647 - right by {
        arithmetic() using {
            0 <= left;
            left <= 2147483646;
            0 <= right;
            right <= 1;
            left <= -2147483648 - right;
        }
    }
    execute(); simp();
}
```

```expect
fail: arithmetic
```
