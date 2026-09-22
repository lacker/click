# A borrowed call checks every part of separation's range validity

```c filename=borrowed.c
int32 a[1];
int32 b[1];
int32 read(int32 n) { return a[0]; }
int32 caller(int32 n) { return read(n); }
```

```click
verifying "borrowed.c";
int32 read(int32 n) {
    views a[0..1];
    requires separate(memory(a[0..n]), memory(b[0..1]));
    ensures result == a[0];
} by { execute(); simp(); }
int32 caller(int32 n) {
    views a[0..1];
    requires 0 <= n;
    ensures result == a[0];
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (read precondition)
```
