# struct field resources imply loadability

This checks the intended field-resource shape. A field `read(...)` or
`write(...)` resource is enough to make that field loadable for symbolic
execution, so the contract does not need separate `loadable(...)` clauses.

```c filename=set_second.c
struct pair {
    int32 first;
    int32 second;
};

int32 set_second(struct pair* p, int32 x) {
    p->second = x;
    return p->first;
}
```

```click
verifying "set_second.c";

int32 set_second(struct pair* p, int32 x) {
    requires read(p->first);
    requires write(p->second);

    ensures result == old(p->first) by auto;
    ensures p->second == x by auto;
    ensures read(p->first) by auto;
    ensures write(p->second) by auto;
}
```

```expect
pass
```
