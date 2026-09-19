# a global store still frames reads of objects proven distinct from it

The stricter frame filter of `global_may_alias_an_array_argument.md` only
withdraws the cases where the two block identities are merely spelled
differently. Two file-scope arrays are two declared objects, and a
function-scope `static` array is a third, so reads of them survive a store to
`g` with no separation clause.

```c filename=a_global_store_frames_distinct_objects.c
int32 g[4];
int32 h[4];

int32 read_other_global() {
    g[0] = 1;
    return h[0];
}

int32 read_static_local() {
    static int32 calls[2];
    g[0] = 1;
    return calls[0];
}
```

```click
verifying "a_global_store_frames_distinct_objects.c";

int32 read_other_global() {
    requires h[0] == 5;
    owns g[0..1];
    ensures result == 5;
} by { execute(); simp(); }

int32 read_static_local() {
    requires calls[0] == 5;
    owns g[0..1];
    owns calls[0..2];
    ensures result == 5;
} by { execute(); simp(); }
```

```expect
pass
```
