# write resources split across helper calls

This checks that a caller can pass a subrange of a larger write resource to a
helper, keep the residue, and regain the larger resource when the helper
returns the subrange.

```c filename=write_first.c
int32 write_first(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=write_first_then_second.c
int32 write_first_then_second(int32 p[]) {
    int32 value;
    value = write_first(p);
    p[1] = 2;
    return value;
}
```

```click
verifying "write_first.c";
verifying "write_first_then_second.c";

int32 write_first(int32 p[]) {
    requires write(p[0..1]);

    ensures writes_first: p[0] == 1 by auto;
    ensures write(p[0..1]) by auto;
}

int32 write_first_then_second(int32 p[]) {
    requires write(p[0..2]);

    ensures writes_both: p[0] == 1 and p[1] == 2 by auto;
    ensures write(p[0..2]) by auto;
}
```

```expect
pass
```
