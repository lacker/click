# Multiple callback contracts: bounds

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
theorem int32_le_antisymmetric(left: int32, right: int32) {
 requires left <= right;
 requires right <= left;
 ensures left == right;
}

contract int32 Lower(int32 value) { ensures result >= value; }
contract int32 Upper(int32 item) { ensures result <= item; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
 requires Lower(callback);
 requires Upper(callback);
 ensures result == x;
} by {
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
