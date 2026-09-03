# C comma-separated `for` steps

The scalar updates in a `for` step execute from left to right, matching the
sequencing of the C comma operator.

```c filename=for_comma_step.c
int32 for_comma_step() {
    int32 i;
    int32 j;
    i = 0;
    j = 3;
    for (i = 0; i < 3; i++, j--) {
        j = j + 1;
    }
    return j;
}
```

```click
verifying "for_comma_step.c";

int32 for_comma_step() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
