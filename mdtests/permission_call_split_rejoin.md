# permission call splits and rejoins write access

This checks that a caller can pass one cell from a larger write range to a
helper, keep the remaining cell, and regain the full range when the helper
returns its subrange.

```c filename=write_first_cell.c
int32 write_first_cell(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=write_first_then_second_cell.c
int32 write_first_then_second_cell(int32 p[]) {
    int32 value;
    value = write_first_cell(p);
    p[1] = 2;
    return value;
}
```

```click
verifying "write_first_cell.c";
verifying "write_first_then_second_cell.c";

int32 write_first_cell(int32 p[]) {
    consumes p[0..1];

    ensures writes_first: p[0] == 1 by auto;
    produces p[0..1] by auto;
}

int32 write_first_then_second_cell(int32 p[]) {
    consumes p[0..2];

    ensures writes_both: p[0] == 1 and p[1] == 2 by auto;
    produces p[0..2] by auto;
}
```

```expect
pass
```
