# json-c refcount increment

This pilot keeps the json-c-shaped reference-count slice on the non-ownership
side of the design boundary. It proves a field increment under an ordinary
signed-overflow precondition.

```c filename=json_object_inc_ref_count.c
struct json_object {
    int32 ref_count;
};

int32 json_object_inc_ref_count(struct json_object* obj) {
    obj->ref_count = obj->ref_count + 1;
    return obj->ref_count;
}
```

```click
verifying "json_object_inc_ref_count.c";

int32 json_object_inc_ref_count(struct json_object* obj) {
    consumes obj->ref_count;
    requires obj->ref_count < 2147483647;
    ensures returns_incremented: result == old(obj->ref_count) + 1 by auto;
    ensures stores_incremented: obj->ref_count == old(obj->ref_count) + 1 by auto;
    produces obj->ref_count by auto;
}
```

```expect
pass
```
