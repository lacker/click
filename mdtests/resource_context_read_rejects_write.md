# read resources reject stores

This checks that a view does not grant write permission. External stores
require a covering owned-memory resource.

```c filename=write_with_read_only.c
int32 write_with_read_only(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```click
verifying "write_with_read_only.c";

int32 write_with_read_only(int32 p[]) {
    requires loadable(p[0..1]);
    views p[0..1];

}
```

```expect
fail: missing resource fact `owns p[0..1]`
```
