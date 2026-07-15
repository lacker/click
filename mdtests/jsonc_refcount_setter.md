# json-c refcount setter

This pilot extends the json-c-shaped struct slice from field reads to a single
field write. The C0 lowering still treats the struct as one `int32` field at
the start of the object, and the contract uses a field-sized write resource.

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
