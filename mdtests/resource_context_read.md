# read resources

This checks the first `read(...)` permission slice. `read(...)` permits
external loads and makes the covered memory valid, but it does not grant write
permission.

```c filename=read_first.c
int32 read_first(int32 p[]) {
    return p[0];
}
```

```click
verifying "read_first.c";

int32 read_first(int32 p[]) {
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

```expect
pass
```
