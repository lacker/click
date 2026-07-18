# stepped modular swap then get

This checks that separate `execute_step()` calls assign distinct opaque call
identities and preserve an explicitly established `old(...)` fact across a
later immutable modular call.

```c filename=swap_pair.c
int32 swap_pair(int32 data[]) {
    int32 temporary;
    temporary = data[0];
    data[0] = data[1];
    data[1] = temporary;
    return data[0];
}
```

```c filename=get_first.c
int32 get_first(int32 data[]) {
    return data[0];
}
```

```c filename=swap_get.c
int32 swap_get(int32 data[]) {
    int32 ignored;
    ignored = swap_pair(data);
    ignored = get_first(data);
    return ignored;
}
```

```click
verifying "swap_pair.c";
verifying "get_first.c";
verifying "swap_get.c";

int32 swap_pair(int32 data[]) {
    owns data[0..2];
    mutable data[0..2];
    ensures result == old(data[1]);
    ensures data[0] == old(data[1]);
    ensures data[1] == old(data[0]);
} by {
    execute_rest();
    frame();
    simp();
}

int32 get_first(int32 data[]) {
    views data[0..1];
    immutable;
    ensures result == data[0];
} by {
    execute_rest();
    frame();
    simp();
}

int32 swap_get(int32 data[]) {
    owns data[0..2];
    mutable data[0..2];
    ensures result == old(data[1]);
} by {
    execute_step();
    execute_step();
    have data[0] == old(data[1]) by {
        simp();
    }
    execute_step();
    execute_step();
    frame();
    simp();
}
```

```expect
pass
```
