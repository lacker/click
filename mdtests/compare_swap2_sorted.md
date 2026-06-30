# compare_swap2 sorts two cells

This checks the first fixed-size sorting target: a conditional swap on two
array cells should leave them in nondecreasing order.

```c filename=compare_swap2.c
int32 compare_swap2(int32 p[2]) {
    int32 tmp;
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
verifying "compare_swap2.c";

int32 compare_swap2(int32 p[2]) {
    requires valid_range(p[0..2]);
    requires write(p[0..2]);
    ensures sorted: p[0] <= p[1] by auto;
}
```

```expect
pass
```
