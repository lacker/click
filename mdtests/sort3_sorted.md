# sort3 sorts three cells

This checks the fixed-size sorting target before introducing nested loops:
three compare-swap steps should leave `p[0..3]` nondecreasing.

```c filename=sort3.c
int32 sort3(int32 p[3]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        p[0] = p[0];
    }
    if (p[2] < p[1]) {
        tmp = p[1];
        p[1] = p[2];
        p[2] = tmp;
    } else {
        p[1] = p[1];
    }
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        p[0] = p[0];
    }
    return 0;
}
```

```click
verifying "sort3.c";

int32 sort3(int32 p[3]) {
    requires valid_range(p[0..3]);
    ensures sorted: p[0] <= p[1] and p[1] <= p[2] by auto;
}
```

```expect
pass
```
