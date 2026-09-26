# a pointer reassigned to an alias of a viewed pointer reads that pointer's cell

`q` is set twice to a call result the callee promises is `p`. Each call records
its own equality, so the outcome knows `q == p` at two points, once about the
value `q` held after the first call and once about the value it holds now. The
read of `q[0]` is a load through the newer value.

`simp` closes such a goal by rewriting with the recorded equalities. It used to
commit to the first one that applied, and rewriting `p` into the *older* value
of `q` leaves a goal no rewrite by the newer equality makes reflexive. Every
remaining equality is now offered the chance to close the goal before one that
merely applies is taken.

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

const int *view(int *p) { ensures result == p; } by { execute(); simp(); }

int read_twice(int *p, int n) {
    views p[0..n];
    requires 0 < n;
    ensures result == p[0];
} by {
    execute();
    simp();
}
```

```expect
pass
```
