# `a == b < c` is not `(a == b) < c`

```c filename=c_equality_precedence_rejects_left_grouping.c
int32 mixed(int32 a, int32 b, int32 c) {
    return a == b < c;
}
```

```click
verifying "c_equality_precedence_rejects_left_grouping.c";

int32 mixed(int32 a, int32 b, int32 c) {
    requires a == 5;
    requires b == 5;
    requires c == 9;
    ensures result == 1 by auto;
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
