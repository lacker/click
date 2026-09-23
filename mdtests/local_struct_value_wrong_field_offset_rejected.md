# A sidecar cannot prove a second field from the first field's bytes

The C function returns 11. This false intermediate claim previously passed
because Click lowered `pair.second` to a load at the struct base.

```c filename=local_struct_value_wrong_field_offset_rejected.c
struct pair { int first; int second; };

int probe(void) {
    struct pair pair = {7, 11};
    return pair.second;
}
```

```click
verifying "local_struct_value_wrong_field_offset_rejected.c";

int probe() {
    ensures result == 11;
} by {
    step();
    step();
    step();
    have pair.second == 7 by { normalize(); }
    execute();
    simp();
}
```

```expect
fail: goal did not normalize to true
```
