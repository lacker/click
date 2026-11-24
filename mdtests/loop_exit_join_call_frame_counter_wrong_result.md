# Joined frame counters do not change the helper return value

An address-taken callee parameter uses a fresh automatic-storage frame. The
break path called the helper, while the guard-false exit did not. The join must
keep the largest frame counter rather than rejecting the otherwise compatible
states. A second call checks that subsequent automatic storage remains usable.

```c filename=call_then_break.c
static inline int32 identity(int32 x) { int32 *p = &x; return *p; }
int32 walk(int32 n) {
    int32 i = 0;
    while (i < n) { identity(i); break; }
    return identity(7);
}
```

```click
verifying "call_then_break.c";
int32 walk(int32 n) { requires n >= 0; ensures result == 8; } by {
    step(); step();
    loop {
        decreases n - i;
        invariant i == 0;
        initialize by close();
        maintain by { step(); step(); }
    }
}
```

```expect
fail: left side evaluated to 7, right side evaluated to 8
```
