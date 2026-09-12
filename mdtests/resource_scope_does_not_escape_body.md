# A scoped open does not leak its body authority

The body exposed by `open` is available only inside the block. After close,
the folded resource does not authorize a direct memory mutation.

```c filename=resource_scope_does_not_escape_body.c
struct object { int32 field; };

int32 resource_scope_does_not_escape_body(struct object* obj) {
    obj->field = 1;
    obj->field = 2;
    return obj->field;
}
```

```click
resource wrapper(obj: struct object*) {
    owns obj->field;
}

verifying "resource_scope_does_not_escape_body.c";

int32 resource_scope_does_not_escape_body(struct object* obj) {
    owns wrapper(obj);
} by {
    open(wrapper(obj)) {
        step();
    }
    step();
}
```

```expect
fail: missing resource fact
```
