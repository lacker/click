# memcmp accepts two const byte pointers

```c filename=memcmp_const_unsigned_char_arguments.c
#include <string.h>
int compare4(const unsigned char *a, const unsigned char *b) {
    return memcmp(a, b, 4);
}
```

```click
verifying "memcmp_const_unsigned_char_arguments.c";
int32 compare4(const uint8* a, const uint8* b) {
    requires viewable(a[0..4]);
    requires viewable(b[0..4]);
    ensures result == 0 implies bytes_equal(a, 0u64, b, 0u64, 4u64);
} by {
    have forall (k: uint64) {
        k < 4u64 implies defined(a[k]) and defined(b[k])
    } by simp;
    execute();
    simp();
}
```

```expect
pass
```
