# A scoped open restores the named resource on both return paths

On each return path the scope restores the instance and proves its body fact
from the value written by that path.

```c filename=open_named.c
int32 set_and_read(int32* p, int32 x, int32 y) {
    if (x > 0) { *p = x; return x; }
    else { *p = y; return y; }
}
```

```click
verifying "open_named.c";

resource positive_cell(p: int32*) {
    field tag: int32;
    owns *p;
    fact *p > 0 or *p < -1;
}

int32 set_and_read(int32* p, int32 x, int32 y) {
    requires y > 0;
    owns c: positive_cell(p);
    ensures c.tag == old(c.tag);
    ensures result > 0;
} by {
    with(c) {
        branch {
            true => { step_until(function.exit); }
            false => { step_until(function.exit); }
        }
    }
    close();
}
```

```expect
pass
```
