# opaque calls expose weak postconditions

The callee writes the requested value, but its contract does not say that it
does. The caller therefore cannot use the hidden implementation write.

```c filename=weak_set.c
int32 weak_set(int32 p[], int32 value) {
    p[0] = value;
    return value;
}
```

```c filename=weak_set_caller.c
int32 weak_set_caller(int32 p[], int32 value) {
    int32 ignored;
    ignored = weak_set(p, value);
    return p[0];
}
```

```click
verifying "weak_set.c";
verifying "weak_set_caller.c";

int32 weak_set(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by auto;
    ensures result == value by auto;
}

int32 weak_set_caller(int32 p[], int32 value) {
    owns p[0..1] by auto;
    ensures result == value by auto;
}
```

```expect
fail: unclosed goal: result == value
```
