# incompatible conditional branch types fail explicitly

A conditional whose branches hold genuinely incompatible supported types is
refused at the parser boundary even when one branch contains a call. A call
in a branch does not weaken the type check into a silent int32 lowering.

```c filename=conditional_call_bad.c
int64 wide(void) { return 1L; }
int32* initiated(int32* seed) { return seed; }
int32 pick(int32 flag, int32* seed) {
    return flag ? wide() : seed;
}
```

```click
verifying "conditional_call_bad.c";

int32 pick(int32 flag, int32* seed) {
    requires flag != 0;
    ensures result == 0;
}
```

```expect
fail: conditional operator branches have incompatible types
```
