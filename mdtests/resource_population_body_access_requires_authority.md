# C access still requires the resource population or its raw body

Opening a wrapper is not optional proof ceremony: without either the wrapper
or its raw object body, a direct store remains unauthorized.

```c filename=resource_population_body_access_requires_authority.c
struct object {
    int32 field;
};

void unauthorized_write(struct object* obj) {
    obj->field = 7;
}
```

```click
resource wrapper(obj: struct object*) {
    owns object(obj);
}

verifying "resource_population_body_access_requires_authority.c";

void unauthorized_write(struct object* obj) {
    mutable obj->field;
} by {
    execute();
}
```

```expect
fail: missing resource
```
