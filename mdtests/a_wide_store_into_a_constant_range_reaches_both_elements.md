# a wide store into a seeded constant range reaches both elements it covers

An eight-byte store at `&a[1]` covers elements 1 and 2 of the run seeded for
`owns a[0..1000000]`. Both leave the run; element 3, past the store's last
byte, keeps its entry value. So `result == old(a[2])` is refused while the
same claim about `a[3]` holds.

```c filename=a_wide_store_into_a_constant_range_reaches_both_elements.c
#include <stdint.h>

int32_t third_element_kept(int32_t* a) {
    int64_t* w;
    w = (int64_t*)(void*) &a[1];
    *w = 0;
    return a[3];
}

int32_t second_element_written(int32_t* a) {
    int64_t* w;
    w = (int64_t*)(void*) &a[1];
    *w = 0;
    return a[2];
}
```

```click
verifying "a_wide_store_into_a_constant_range_reaches_both_elements.c";

int32_t third_element_kept(int32_t* a) {
    owns a[0..1000000];
    ensures result == old(a[3]);
} by {
    execute();
    simp();
}

int32_t second_element_written(int32_t* a) {
    owns a[0..1000000];
    ensures result == old(a[2]);
} by {
    execute();
    simp();
}
```

```expect
fail: result == old(a[2])
```
