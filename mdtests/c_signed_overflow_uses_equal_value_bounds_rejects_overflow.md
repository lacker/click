# Equality does not make an overflowing sum defined

```c filename=overflow.c
int32 f(int32 x, int32 y) { return y + 1; }
```

```click
verifying "overflow.c";
int32 f(int32 x, int32 y) {
    requires x == y;
    requires x == 2147483647;
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: signed overflow
```
