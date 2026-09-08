# An undecided precondition is not a reason to split execution

Identity suffices for the call. Positive contributes no guarantee unless its
precondition is established; applicability does not introduce an implicit case split.

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
contract int32 Positive(int32 value) { requires value > 0; ensures result == 1; }
contract int32 Identity(int32 value) { ensures result == value; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires Positive(callback);
    requires Identity(callback);
    ensures result == x;
} by { execute(); simp(); }
```

```expect
pass
```
