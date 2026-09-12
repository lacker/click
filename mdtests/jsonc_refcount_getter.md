# json-c refcount getter

This is a synthetic library-shaped regression proof. The fixture in
`examples/jsonc-refcount/json_object_ref_count.c` uses a tiny json-c-shaped
object with a single `int32` reference-count field. The expression
`obj->ref_count` lowers to a field load.

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
    views obj->ref_count;
    ensures returns_ref_count: result == obj->ref_count by auto;
}
```

```expect
pass
```
