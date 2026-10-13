```c filename=scalar.c
int32 f(int32 x, int32 y) { return y + 1; }
```
```click
verifying "scalar.c";
int32 f(int32 x, int32 y) {
    requires x == y;
    requires 0 <= x;
    requires x <= 2147483646;
    ensures result == x + 1;
} by { execute(); simp(); }
```
```expect
pass
```
