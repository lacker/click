# A selection cannot borrow membership from another pointer

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 (*other)(int32), int32 x) {
    return callback(x);
}
```

```click
contract int32 First(int32 x) { ensures result == x; }
contract int32 Second(int32 x) { ensures result == x; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 (*other)(int32), int32 x) {
    requires First(callback);
    requires Second(other);
    ensures result == x;
} by { step(Second); execute(); simp(); }
```

```expect
fail: is not established for this callback
```
