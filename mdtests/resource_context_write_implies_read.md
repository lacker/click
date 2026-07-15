# write resources imply read

This checks that owned memory permits external loads and can satisfy a viewed
requirement.

```c filename=read_with_write.c
int32 read_with_write(int32 p[]) {
    return p[0];
}
```

```click
verifying "read_with_write.c";

int32 read_with_write(int32 p[]) {
    requires loadable(p[0..1]);
    owns p[0..1];
}
```

```expect
pass
```
