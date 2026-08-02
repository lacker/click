# batched modular swap then get

This checks that opaque call identities remain distinct when one
`execute()` expansion contains multiple modular calls.

```c filename=batch_swap_pair.c
int32 swap_pair(int32 data[]) {
    int32 temporary;
    temporary = data[0];
    data[0] = data[1];
    data[1] = temporary;
    return data[0];
}
```

```c filename=batch_get_first.c
int32 get_first(int32 data[]) {
    return data[0];
}
```

```c filename=batch_swap_get.c
int32 swap_get(int32 data[]) {
    int32 ignored;
    ignored = swap_pair(data);
    ignored = get_first(data);
    return ignored;
}
```

```click
verifying "batch_swap_pair.c";
verifying "batch_get_first.c";
verifying "batch_swap_get.c";

int32 swap_pair(int32 data[]) {
    owns data[0..2];
    mutable data[0..2];
    ensures result == old(data[1]);
    ensures data[0] == old(data[1]);
    ensures data[1] == old(data[0]);
} by {
    execute();
    frame();
    simp();
}

int32 get_first(int32 data[]) {
    views data[0..1];
    immutable;
    ensures result == data[0];
} by {
    execute();
    frame();
    simp();
}

int32 swap_get(int32 data[]) {
    owns data[0..2];
    mutable data[0..2];
    ensures result == old(data[1]);
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
