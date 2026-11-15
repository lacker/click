# a stored element of a long global array is not its entry value

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. The element a store
writes is compared with its entry state and differs from it: `old(buf[1])`
names the run's slot, and the final state holds the stored `7` there.

```c filename=a_stored_global_array_element_is_not_its_entry_value.c
int32 buf[1000];

void write_one() {
    buf[1] = 7;
}
```

```click
verifying "a_stored_global_array_element_is_not_its_entry_value.c";

void write_one() {
    owns buf[1..2];
    ensures buf[1] == old(buf[1]);
}
```

```expect
fail: buf[1] == old(buf[1])
```
