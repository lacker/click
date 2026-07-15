# permission call consumes unreturned write access

This checks that write permission is linear across a call. The helper receives
`write(p[0..1])` but does not return it, so the caller cannot prove it still has
that write permission after the call.

```c filename=consume_first_write.c
int32 consume_first_write(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=needs_write_back.c
int32 needs_write_back(int32 p[]) {
    int32 value;
    value = consume_first_write(p);
    return value;
}
```

```click
verifying "consume_first_write.c";
verifying "needs_write_back.c";

int32 consume_first_write(int32 p[]) {
    consumes p[0..1];

    ensures returns_written: result == p[0] by auto;
}

int32 needs_write_back(int32 p[]) {
    consumes p[0..1];

    produces p[0..1] by auto;
}
```

```expect
fail: missing resource fact
```
