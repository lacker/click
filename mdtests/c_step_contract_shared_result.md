# Resource selection retains other applicable result guarantees

```c filename=joint.c
int32 invoke(int32 (*callback)(int32*, int32), int32* cell, int32 x) {
    return callback(cell, x);
}
```

```click
theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}
resource Cell(cell: int32*) { owns cell[0..1]; }
contract int32 Raw(int32* cell, int32 value) {
    owns cell[0..1];
    ensures result >= value;
}
contract int32 Buffered(int32* cell, int32 item) {
    owns Cell(cell);
    ensures result <= item;
}
verifying "joint.c";
int32 invoke(int32 (*callback)(int32*, int32), int32* cell, int32 x) {
    requires Raw(callback);
    requires Buffered(callback);
    owns Cell(cell);
    ensures result == x;
} by {
    step(Buffered);
    execute();
    have result <= x by { assumption(); }
    have x <= result by { simp(); }
    apply(int32_le_antisymmetric(result, x));
    simp();
}
```

```expect
pass
```
