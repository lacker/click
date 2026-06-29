# jsonc-mini struct field unsupported

This records the first real-library-shaped pilot blocker. The frozen fixture in
`examples/real/jsonc-mini/json_object_ref_count.c` needs struct declarations,
pointer-to-struct parameters, and `->` field loads. C0 rejects that syntax today.

```c filename=json_object_ref_count.c
struct json_object {
    int32 ref_count;
};

int32 json_object_get_ref_count(struct json_object* obj) {
    return obj->ref_count;
}
```

```click
verifying "json_object_ref_count.c";
```

```expect
fail: expected type `int32` or `uint8`, got Ident("struct")
```
