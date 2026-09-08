# Multiple callback contracts: no applicable

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
contract int32 Positive(int32 value) { requires value > 0; ensures result == 1; }
contract int32 Negative(int32 value) { requires value < 0; ensures result == 2; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
 requires Positive(callback);
 requires Negative(callback);
 requires x == 0;
 ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: precondition
```

