# Loop invariants can describe global and static writes

The loop invariant explicitly relates each static-storage object to the loop
counter. Both true postconditions verify after loop havoc forgets the entry
values at the abstract loop head.

```c filename=loop_global_and_static_havoc.c
int32 global_counter = 0;

int32 loop_global_havoc(int32 n) {
    int32 i = 0;
    global_counter = 0;
    while (i < n) {
        global_counter = global_counter + 1;
        i = i + 1;
    }
    return global_counter;
}

int32 loop_static_havoc(int32 n) {
    static int32 static_counter = 0;
    int32 i = 0;
    static_counter = 0;
    while (i < n) {
        static_counter = static_counter + 1;
        i = i + 1;
    }
    return static_counter;
}
```

```click
verifying "loop_global_and_static_havoc.c";

int32 loop_global_havoc(int32 n) {
    requires n >= 0 and n <= 100;
    owns &global_counter[0..1];
    ensures result == n;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
        invariant global_counter == i;
    }
    step();
    simp();
}

int32 loop_static_havoc(int32 n) {
    requires n >= 0 and n <= 100;
    owns &static_counter[0..1];
    ensures result == n;
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
        invariant static_counter == i;
    }
    step();
    simp();
}
```

```expect
pass
```
