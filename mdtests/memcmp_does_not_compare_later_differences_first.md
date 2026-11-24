# A later smaller byte cannot reverse the first difference

```c filename=compare.c
#include <string.h>
int ordered(void) {
    unsigned char left[2] = { 2, 0 };
    unsigned char right[2] = { 1, 255 };
    return memcmp(left, right, 2) < 0;
}
```

```click
import click::bytes;
verifying "compare.c";
int32 ordered() { ensures result == 1; } by {
    step_until(statement(2).call(memcmp, 0).entry);
    let { result: cmp } = step(memcmp);
    have bytes::equal_range(left, right, 0u64, 0u64) by {
        unfold(bytes::equal_range(left, right, 0u64, 0u64));
        intro();
        intro();
        close();
    }
    apply(bytes::comparison_positive_after_prefix(left, right, 2u64, 0u64, cmp));
}
```

```expect
fail: unclosed goal
```
