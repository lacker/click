# A `_Bool` parameter holds zero or one

A C `_Bool` object holds only `0` or `1`, and returning one from an `int`
function converts it to that same integer. Both facts are usable without a
case split: the entry value of a `bool` parameter carries its range
`flag == 0 or flag == 1`, so `simp()` proves the range disjunction of the
converted result as well as its equality with the parameter. A caller that
passes a `bool`, or an integer converted to `bool` at the call, uses the
callee's contract as written.

```c filename=bool_parameter.c
#include <stdbool.h>

int present(bool flag) { return flag; }
int in_range(bool flag) { return flag; }
int in_range_reversed(_Bool flag) { return flag; }
int auto_equal(bool flag) { return flag; }
int auto_range(bool flag) { return flag; }
int forwards(bool b) { return present(b); }
int converts(void) { return present(5); }
int forwards_range(bool b) { return in_range(b); }
```

```click
verifying "bool_parameter.c";

int32 present(bool flag) {
    ensures result == flag;
} by {
    execute();
    simp();
}

int32 in_range(bool flag) {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}

int32 in_range_reversed(bool flag) {
    ensures result == 1 or result == 0;
} by {
    execute();
    simp();
}

int32 auto_equal(bool flag) {
    ensures result == flag by auto;
}

int32 auto_range(bool flag) {
    ensures result == 0 or result == 1 by auto;
}

int32 forwards(bool b) {
    ensures result == b;
} by {
    execute();
    simp();
}

int32 converts() {
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 forwards_range(bool b) {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
