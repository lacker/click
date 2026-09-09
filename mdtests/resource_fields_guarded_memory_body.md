# Guarded named-instance memory bodies

The null case has no memory body. Both C return paths restore the same
exclusive instance and its unchanged fields.

```c filename=resource_fields_guarded_memory_body.c
int32 read_nullable(int32* p) {
    if (p == 0) return 0;
    return *p;
}
```

```click
verifying "resource_fields_guarded_memory_body.c";

resource cell(p: int32*) {
    field value: int32;
    if p != 0 {
        owns p[0..1];
        fact p[0] == value;
    }
}

int32 read_nullable(int32* p) {
    owns c: cell(p);
    ensures p == 0 or result == c.value;
    ensures c.value == old(c.value);
} by {
    if p == 0 {
        unfold(c);
        execute();
        fold(c);
        simp();
    } else {
        unfold(c);
        execute();
        fold(c);
        simp();
    }
}
```

```expect
pass
```
