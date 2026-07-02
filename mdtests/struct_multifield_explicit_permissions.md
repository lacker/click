# multi-field struct fields

This checks the first ordinary multi-field struct slice. C0 can lower field
loads and stores at nonzero offsets, while the Click contract still gives the
object footprint as an explicit memory range.

```c filename=write_second.c
struct pair {
    int32 first;
    int32 second;
};

int32 write_second(struct pair* p) {
    p->first = 1;
    p->second = 2;
    return p->second;
}
```

```click
verifying "write_second.c";

int32 write_second(struct pair* p) {
    requires valid_range(p[0..2]);
    requires write(p[0..2]);

    ensures result == 2 by auto;
    ensures write(p[0..2]) by auto;
}
```

```expect
pass
```
