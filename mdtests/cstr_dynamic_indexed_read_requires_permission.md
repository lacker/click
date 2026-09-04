# Dynamic C-string reads require an explicit permission range

`cstr_readable` and `loadable` describe safe contents, but neither one grants
the resource-sensitive permission needed by an actual C array read.

```c filename=cstr_dynamic_indexed_read_requires_permission.c
int32 read_terminator_without_permission(uint8 bytes[]) {
    int32 length;
    length = strlen(bytes);
    return bytes[length];
}
```

```click
verifying "cstr_dynamic_indexed_read_requires_permission.c";

int32 read_terminator_without_permission(uint8 bytes[]) {
    requires cstr_readable(bytes);
    ensures result == '\0' by {
        unfold(cstr_readable);
        execute();
        simp();
    }
}
```

```expect
fail: missing resource fact `views bytes
```
