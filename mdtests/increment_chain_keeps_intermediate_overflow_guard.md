# Combining increment values preserves every intermediate overflow check

The final mathematical value would equal `x`, but the second addition is
undefined for the required input. Value normalization cannot erase that guard.

```c filename=increment_overflow.c
int f(int x) { return ((x + 1) + 1) - 2; }
```

```click
verifying "increment_overflow.c";
int32 f(int32 x) {
    requires x == 2147483646;
    ensures result == x;
} by { execute(); simp(); }
```

```expect
fail: signed overflow
```
