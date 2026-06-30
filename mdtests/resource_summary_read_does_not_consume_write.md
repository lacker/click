# read requirements do not consume write resources

This checks that a caller with `write(...)` can pass `read(...)` to a helper and
still write the same range after the call.

```c filename=peek_first.c
int32 peek_first(int32 p[]) {
    return p[0];
}
```

```c filename=peek_then_write.c
int32 peek_then_write(int32 p[]) {
    int32 value;
    value = peek_first(p);
    p[0] = 1;
    return p[0];
}
```

```click
verifying "peek_first.c";
verifying "peek_then_write.c";

int32 peek_first(int32 p[]) {
    requires valid_range(p[0..1]);
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}

int32 peek_then_write(int32 p[]) {
    requires valid_range(p[0..1]);
    requires write(p[0..1]);

    ensures write(p[0..1]) by auto;
}
```

```expect
pass
```
