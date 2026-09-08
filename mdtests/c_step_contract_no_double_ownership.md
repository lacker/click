# Selecting one transition does not add another copy of ownership

```c filename=joint.c
int32 invoke(void (*callback)(int32), int32 x) { callback(x); return 0; }
```

```click
abstract resource Permit(x: int32);
contract void First(int32 x) { owns Permit(x); }
contract void Second(int32 x) { owns Permit(x); }
verifying "joint.c";
int32 invoke(void (*callback)(int32), int32 x) {
    requires First(callback);
    requires Second(callback);
    consumes Permit(x);
    produces Permit(x);
    produces Permit(x);
    ensures result == 0;
} by { step(First); execute(); simp(); }
```

```expect
fail: unverified claims: Ensure(1) = produces
```
