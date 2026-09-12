# json-c refcount setter

This regression checks a single field write in a synthetic json-c-shaped
struct. The object has one `int32` field, and the contract uses a field-sized
write resource.

```c filename=json_object_set_ref_count.c
struct json_object {
    int32 ref_count;
};

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    obj->ref_count = count;
    return obj->ref_count;
}
```

```click
verifying "json_object_set_ref_count.c";

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    consumes obj->ref_count;
    ensures returns_count: result == count by auto;
    ensures stores_count: obj->ref_count == count by auto;
    produces obj->ref_count by auto;
}
```

```expect
pass
```
