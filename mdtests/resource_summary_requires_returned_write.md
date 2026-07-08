# write resources follow function summaries

This checks that calls transfer resources through the callee's contract. The
helper is allowed to write `p[0]`, but it does not return that permission in an
`ensures write(...)` clause, so the caller cannot prove it still has the
permission after the call.

```c filename=consume_write.c
int32 consume_write(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=caller_needs_write_back.c
int32 caller_needs_write_back(int32 p[]) {
    int32 value;
    value = consume_write(p);
    return value;
}
```

```click
verifying "consume_write.c";
verifying "caller_needs_write_back.c";

int32 caller_needs_write_back(int32 p[]) {
    requires write(p[0..1]);

    ensures write(p[0..1]) by auto;
}

int32 consume_write(int32 p[]) {
    requires write(p[0..1]);

    ensures returns_written: result == p[0] by auto;
}
```

```expect
fail: missing resource fact
```
