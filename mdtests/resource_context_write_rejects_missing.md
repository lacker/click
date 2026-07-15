# write resources reject uncovered stores

This checks that external stores require a covering write resource. The function
has permission for `p[1]`, but writes `p[0]`.

```c filename=write_first_without_resource.c
int32 write_first_without_resource(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```click
verifying "write_first_without_resource.c";

int32 write_first_without_resource(int32 p[]) {
    consumes p[1..2];

    ensures writes_first: p[0] == 1 by auto;
}
```

```expect
fail: missing resource fact `owns p[0..1]`
```
