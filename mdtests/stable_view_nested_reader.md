# Nested readers retain the outer view dependency

An outer reader may call another reader on the same range. The inner call
uses a scoped read access supplied by the outer call, and the caller's owner
remains available after both calls return.

```c filename=stable_view_nested_reader.c
int32 stable_view_inner(int32 p[]) {
    return p[0];
}

int32 stable_view_outer(int32 p[]) {
    return stable_view_inner(p);
}

int32 stable_view_nested_caller(int32 p[]) {
    return stable_view_outer(p);
}
```

```click
verifying "stable_view_nested_reader.c";

int32 stable_view_inner(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}

int32 stable_view_outer(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}

int32 stable_view_nested_caller(int32 p[]) {
    owns p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
