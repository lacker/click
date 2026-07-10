# write resources imply read

This checks that `write(...)` permits external loads and can satisfy a
`read(...)` guarantee.

```c filename=read_with_write.c
int32 read_with_write(int32 p[]) {
    return p[0];
}
```

```click
verifying "read_with_write.c";

int32 read_with_write(int32 p[]) {
    requires loadable(p[0..1]);
    requires write(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

```expect
pass
```
