# `observe` rejects an undeclared resource name

A tactic argument naming a resource that no `resource` declaration
introduces is a source error, reported against the name the proof used.

```c filename=use_token.c
int32 use_token(int32 fd) {
    return 0;
}
```

```click
verifying "use_token.c";

int32 use_token(int32 fd) {
    ensures zero: result == 0 by {
        observe(missing_resource(fd));
        execute();
        simp();
    }
}
```

```expect
fail: unknown resource `missing_resource`
```
