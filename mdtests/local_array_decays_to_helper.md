# local array decays when passed to a helper

This checks that a local array name decays to an `int32*` rvalue when passed to
a known helper function.

```c filename=read_first.c
int32 read_first(int32* p) {
    return p[0];
}
```

```c filename=local_array_decays_to_helper.c
int32 local_array_decays_to_helper() {
    int32 a[2];
    int32 result;
    a[0] = 11;
    result = read_first(a);
    return result;
}
```

```click
verifying "read_first.c";
verifying "local_array_decays_to_helper.c";

int32 local_array_decays_to_helper() {
    ensures returns_first: result == 11 by auto;
}
```

```expect
pass
```
