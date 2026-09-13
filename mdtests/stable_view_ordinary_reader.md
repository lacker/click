# An ordinary reader uses a stable view for its call

The reader borrows one cell for the duration of the call. Its caller keeps
ownership and can use the same owned range after the read returns.

```c filename=stable_view_reader.c
int32 stable_view_reader(int32 p[]) {
    return p[0];
}

int32 stable_view_reader_caller(int32 p[]) {
    return stable_view_reader(p);
}
```

```click
verifying "stable_view_reader.c";

int32 stable_view_reader(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}

int32 stable_view_reader_caller(int32 p[]) {
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
