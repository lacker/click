# tentative scalar arrays still require one compatible linked object

Tentative declarations may coalesce only when their fixed-size array types
match. A different bound is a conflicting declaration, even when neither
translation unit supplies an initializer.

```c filename=left.c
int32 table[3];

int32 left() {
    return table[0];
}
```

```c filename=right.c
int32 table[2];

int32 right() {
    return table[0];
}
```

```click
verifying "left.c";
verifying "right.c";

int32 left() {
    ensures result == 0 by auto;
}

int32 right() {
    ensures result == 0 by auto;
}
```

```expect
fail: conflicting declarations for global array `table`
```
