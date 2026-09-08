# Multiple callback contracts: applicable

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }
```

```click
contract int32 APositive(int32 value) { requires value > 0; ensures result == 1; }
contract int32 ZIdentity(int32 value) { ensures result == value; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
 requires ZIdentity(callback);
 requires APositive(callback);
 requires x == 0;
 ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
