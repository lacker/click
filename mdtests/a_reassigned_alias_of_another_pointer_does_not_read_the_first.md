# a pointer reassigned away from a viewed pointer does not read its cell

The negative companion of
[`a_reassigned_alias_of_a_viewed_pointer_reads_its_cell.md`](a_reassigned_alias_of_a_viewed_pointer_reads_its_cell.md).
The first call makes `q` equal to `p`, the second makes it equal to `r`, and
nothing relates `r` to `p`. Offering every recorded equality to the rewrite
chain must not let the stale `q == p` speak for the value `q` holds now, so
`result == p[0]` is refused.

```c filename=view.h
const int *view(int *p);
```

```c filename=view.c
#include "view.h"
const int *view(int *p) { return p; }
```

```c filename=caller.c
#include "view.h"
int read_after_moving(int *p, int *r, int n) {
    const int *q = view(p);
    q = view(r);
    return q[0];
}
```

```click
verifying "view.c";
verifying "caller.c";

const int *view(int *p) { ensures result == p; } by { execute(); simp(); }

int read_after_moving(int *p, int *r, int n) {
    views p[0..n];
    views r[0..n];
    requires 0 < n;
    ensures result == p[0];
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
