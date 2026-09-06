# const aggregate writes are rejected

The source boundary must reject mutation of a const-qualified aggregate field.

```c filename=const_aggregate.c
struct state {
    int32 value;
};

const struct state shared = {1};

int32 bad() {
    shared.value = 2;
    return shared.value;
}
```

```click
verifying "const_aggregate.c";
```

```expect
fail:const-qualified
```
