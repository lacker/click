# A const-returning contract cannot be used for a mutable-return callback

```click
contract const int *ReadOnly(int *p) { ensures result == p; }
contract int *Mutable(int *p) { ensures result == p; }
theorem bad(callback: int* (*)(int*)) executes callback(int* p) {
    requires ReadOnly(callback);
    ensures Mutable(callback) by { step(ReadOnly); close(); }
}
```

```expect
fail: expects const int32* (*)(int32*), got int32* (*)(int32*)
```
