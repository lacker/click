# A selection does not leak to a second call in the same C statement

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) {
    return callback(callback(x));
}
```

```click
abstract resource Permit(x: int32);
contract int32 First(int32 x) { owns Permit(x); ensures result == x; }
contract int32 Second(int32 x) { owns Permit(x); ensures result == x; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires First(callback);
    requires Second(callback);
    owns Permit(x);
    ensures result == x;
} by { step(First); execute(); simp(); }
```

```expect
fail: ambiguous callback resource transition
```
