# A false static assertion cannot be bypassed by a trivial contract

```c filename=false_assert.c
int32 run() {
    _Static_assert(__builtin_types_compatible_p(long, long long), "incompatible ranks");
    return 0;
}
```

```click
verifying "false_assert.c";
int32 run() { ensures result == 0; } by { execute(); normalize(); }
```

```expect
fail: static assertion failed: incompatible ranks
```
