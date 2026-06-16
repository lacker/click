# symbolic max rejects a false branch postcondition

This checks that all-path verification catches a postcondition that is true on
one branch but false on the other.

```c filename=max_bad.c
int32 max_bad(int32 a, int32 b) {
    if (a < b) {
        return b;
    } else {
        return a;
    }
}
```

```click
verifying "max_bad.c";

int32 max_bad(int32 a, int32 b) {
    ensures result == a by auto;
}
```

```expect
fail: failed for `max_bad.ensures_0` path
```

