# A different resource model cannot evaluate its postcondition in the input ledger

The alternative transition returns B, not A. Its conditional postcondition does
not promise result == 1 merely because the selected model keeps A.

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
abstract resource A(x: int32);
abstract resource B(x: int32);
contract int32 Keep(int32 x) {
    owns A(x);
    ensures result == 0;
}
contract int32 Alternative(int32 x) {
    consumes A(x);
    produces B(x);
    ensures count(A(x)) == 1 implies result == 1;
}
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires Keep(callback);
    requires Alternative(callback);
    owns A(x);
    ensures result == 1;
} by { step(Keep); execute(); simp(); }
```

```expect
fail: unclosed goal
```
