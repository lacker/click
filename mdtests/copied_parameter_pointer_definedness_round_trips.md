# Indexed definedness returned through a by-value parameter

The caller uses the pointer field of the callee’s copy to name the initialized
byte. `close()` checks that the two paths use the same read.

```c filename=copied_parameter_pointer_definedness_round_trips.c
struct Buffer { unsigned char* data; unsigned long size; };
void fill(struct Buffer b, unsigned long k) { b.data[k] = 9; }
void caller(unsigned char* data, unsigned long k) {
    struct Buffer b = {data, 2};
    fill(b, k);
}
```

```click
verifying "copied_parameter_pointer_definedness_round_trips.c";
void fill(struct Buffer b, uint64 k) {
    requires k < 2u64;
    owns uninitialized(b.data[0u64..2u64]);
    ensures defined(load<uint8>(old(b.data) + k));
}
void caller(uint8* data, uint64 k) {
    requires k < 2u64;
    owns uninitialized(data[0u64..2u64]);
} by {
    step_until(call(0).entry);
    step();
    have defined(load<uint8>(call(0).parameter(b).data + k)) by { close(); }
    step_until(function.exit);
}
```

```expect
pass
```
