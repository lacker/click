# a write outside the named static field's footprint is rejected

The negative half of `static_struct_field_footprint.md`: a footprint naming
`shared.second` does not authorize a write to `shared.first`, which lives at a
different ABI offset in the same object.

```c filename=static_struct_field_footprint_rejected.c
struct pair {
    int32 first;
    int32 second;
};

struct pair shared;

int32 static_struct_field_footprint_rejected() {
    shared.first = 9;
    return 0;
}
```

```click
verifying "static_struct_field_footprint_rejected.c";

int32 static_struct_field_footprint_rejected() {
    mutable &shared.second;
    ensures result == 0;
}
```

```expect
fail: outside the mutable footprint
```
