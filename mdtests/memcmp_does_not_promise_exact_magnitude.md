# memcmp specifies a sign rather than an exact negative value

```c filename=compare.c
#include <string.h>
int ordered(void) {
    unsigned char left[1] = { 1 };
    unsigned char right[1] = { 2 };
    return memcmp(left, right, 1);
}
```

```click
import click::bytes;
verifying "compare.c";
int32 ordered() { ensures result == -1; } by {
    step_until(statement(2).call(memcmp, 0).entry);
    let { result: cmp } = step(memcmp);
    have bytes::equal_range(left, right, 0u64, 0u64) by {
        unfold(bytes::equal_range(left, right, 0u64, 0u64));
        intro();
        intro();
        close();
    }
    apply(bytes::comparison_negative_after_prefix(left, right, 1u64, 0u64, cmp));
}
```

```expect
fail: unclosed goal
```
