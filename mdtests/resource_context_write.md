# write resources

This checks the first resource-context slice. Owning `p[0..1]` is not a
classical predicate: it is carried in the verifier state and must be present for
external memory writes.

```c filename=write_next.c
int32 write_next(int32 p[], int32 x) {
    p[0] = x + 1;
    return p[0];
}
```

```c filename=write_twice.c
int32 write_twice(int32 p[]) {
    int32 value;
    value = write_next(p, 0);
    value = write_next(p, 1);
    return p[0];
}
```

```click
verifying "write_next.c";
verifying "write_twice.c";

int32 write_next(int32 p[], int32 x) {
    consumes p[0..1];
    requires x < 2147483647;

    ensures returns_written: result == p[0] by auto;
    ensures writes_next: p[0] == x + 1 by auto;
    produces p[0..1] by auto;
}

int32 write_twice(int32 p[]) {
    consumes p[0..1];

    ensures writes_two: p[0] == 2 by auto;
    produces p[0..1] by auto;
}
```

```expect
pass
```
