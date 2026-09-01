# `==` binds more loosely than `<`, as in C

```c filename=c_equality_precedence.c
int32 mixed(int32 a, int32 b, int32 c) {
    return a == b < c;
}
```

```click
verifying "c_equality_precedence.c";

int32 mixed(int32 a, int32 b, int32 c) {
    requires a == 5;
    requires b == 5;
    requires c == 9;
    ensures result == 0 by auto;
}
```

```expect
pass
```
