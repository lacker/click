# A sidecar reads the second field of an automatic struct value

Automatic struct values carry their layout into Click expressions. The
second field must read its own initialized slot, rather than the first
field at offset zero.

```c filename=local_struct_value_field_offset.c
struct pair { int first; int second; };

int probe(void) {
    struct pair pair = {7, 11};
    return pair.second;
}
```

```click
verifying "local_struct_value_field_offset.c";

int probe() {
    ensures result == 11;
} by {
    step();
    step();
    step();
    have pair.second == 11 by { normalize(); }
    execute();
    simp();
}
```

```expect
pass
```
