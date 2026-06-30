# json-c refcount getter

This is the first library-shaped pilot proof. The fixture in
`examples/jsonc-refcount/json_object_ref_count.c` uses a tiny json-c-shaped
object with a reference-count field. The current struct slice supports a
single `int32` field and lowers `obj->ref_count` to a field load.

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

int32 json_object_get_ref_count(struct json_object* obj) {
    requires valid_field(obj->ref_count);
    requires read(obj[0..1]);
    ensures returns_ref_count: result == obj->ref_count by auto;
    immutable by frame;
}
```

```expect
pass
```
