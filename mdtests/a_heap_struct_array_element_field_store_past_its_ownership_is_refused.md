# A heap struct array element's field store past its ownership is refused

`owns p[0..3]` holds three eight-byte elements, but the loop writes
`p[3].y` on its last iteration. The element bound does not place that field
inside the owned range, so the store is refused.

```c filename=heap_struct_array_element_field_store_past_ownership.c
struct point { int32 x; int32 y; };
int32 fill_too_many_heap_fields(struct point* p) {
    int32 i;
    i = 0;
    while (i < 4) {
        p[i].y = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "heap_struct_array_element_field_store_past_ownership.c";

int32 fill_too_many_heap_fields(struct point* p) {
    owns p[0..3];
    ensures result == 0;
} by {
    step(); step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
fail: missing resource fact `owns p[i].y`
```
