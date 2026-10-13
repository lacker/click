# Automatic call prerequisites prove the original true disjunctions

Correcting failure attribution must preserve the implicit auto behavior.

```c filename=pair.c
int32 first(int32 x, int32 y) { return x; }
int32 caller(int32 a, int32 b) { return first(a, b); }
```

```click
verifying "pair.c";
int32 first(int32 x, int32 y) {
 requires x > 0 or y > 0;
 requires y > 0 or x > 0;
 ensures 1 == 1 by auto;
}
int32 caller(int32 a, int32 b) {
 requires a > 0;
 ensures 1 == 1 by { have a > 0 or b > 0 by simp; step(); step(); simp(); }
}
```

```expect
pass
```
