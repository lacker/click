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

contract int32 ZLower(int32 value) { ensures result >= value; }
contract int32 AUpper(int32 item) { ensures result <= item; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
 requires AUpper(callback);
 requires ZLower(callback);
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
