# read resources reject stores

This checks that `read(...)` does not grant write permission. External stores
require a covering `write(...)`.

```c filename=write_with_read_only.c
int32 write_with_read_only(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```click
verifying "write_with_read_only.c";

int32 write_with_read_only(int32 p[]) {
    requires valid_range(p[0..1]);
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

```expect
fail: missing resource `write(p[0..1])`
```
