# `unfold` rejects a resource without a body

The resource laws (`unfold`, `fold`, `observe`) read the named resource's body.
Composite resources may provide one. A bodyless declared resource has none, so
naming one must be reported before any law is applied.

```c filename=use_token.c
int32 use_token(int32 fd) {
    return 0;
}
```

```click
resource socket_open(fd: int32);

verifying "use_token.c";

int32 use_token(int32 fd) {
    consumes socket_open(fd);

    produces socket_open(fd) by {
        unfold(socket_open(fd));
        execute();
    }
}
```

```expect
fail: `unfold` expects resource `socket_open` to have a body
```
