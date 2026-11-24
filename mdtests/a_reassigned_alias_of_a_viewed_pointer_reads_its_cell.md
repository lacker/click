# a pointer reassigned to an alias of a viewed pointer reads that pointer's cell

`q` is set twice to a call result the callee promises is `p`. Each call records
its own equality, so the outcome knows `q == p` at two points, once about the
value `q` held after the first call and once about the value it holds now. The
read of `q[0]` is a load through the newer value.

The proof applies a checked alias-read theorem while `q` names the value
from the second call. The theorem names both pointers and the viewable cell,
and its proof rewrites the alias to `p`. This establishes a fact the return
can reuse with `close()`.

The range is variable-length on purpose: nothing seeds a cell for `p[0]`, so
the proof has to go through the loads' addresses. The sibling below, whose
second call returns a different pointer, is still refused.

```c filename=view.h
const int *view(int *p);
```

```c filename=view.c
#include "view.h"
const int *view(int *p) { return p; }
```

```c filename=caller.c
#include "view.h"
int read_twice(int *p, int n) {
    const int *q = view(p);
    q = view(p);
    return q[0];
}
```

```click
verifying "view.c";
verifying "caller.c";

theorem aliased_cell_read(p: int32*, q: const int32*) {
    requires p == q;
    requires viewable(p[0..1]);
    ensures q[0] == p[0] by {
        rewrite(q, p);
        close();
    }
}

const int *view(int *p) { ensures result == p; }

int read_twice(int *p, int n) {
    views p[0..n];
    requires 0 < n;
    ensures result == p[0] by {
        step_until(statement(2).entry);
        have q[0] == p[0] by {
            apply(aliased_cell_read(p, q));
        }
        step_until(function.exit);
        close();
    }
}
```

```expect
pass
```
