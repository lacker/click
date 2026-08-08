# `execute` expansion preserves certified post-call facts

A verified call may establish the exact current-memory fact required by a
later call. Whole-function `execute()` must carry that certified postcondition
through its generated `step() using` certificate, even when the same surface
expression described an older snapshot earlier in the function.

```c filename=set_one.c
struct cell {
    int32 value;
};

void set_one(struct cell* cell) {
    cell->value = 1;
}
```

```c filename=set_two.c
struct cell {
    int32 value;
};

void set_two(struct cell* cell) {
    cell->value = 2;
}
```

```c filename=restore_one.c
struct cell {
    int32 value;
};

void restore_one(struct cell* cell) {
    cell->value = cell->value - 1;
}
```

```c filename=require_one.c
struct cell {
    int32 value;
};

void require_one(struct cell* cell) {
}
```

```c filename=post_call_chain.c
struct cell {
    int32 value;
};

int32 post_call_chain(struct cell* cell) {
    set_one(cell);
    set_two(cell);
    restore_one(cell);
    require_one(cell);
    return 0;
}
```

```click
verifying "set_one.c";
verifying "set_two.c";
verifying "restore_one.c";
verifying "require_one.c";
verifying "post_call_chain.c";

void set_one(struct cell* cell) {
    owns object(cell);
    mutable cell->value;
    ensures cell->value == 1;
} by {
    execute();
    frame();
    simp();
}

void set_two(struct cell* cell) {
    requires cell->value == 1;
    owns object(cell);
    mutable cell->value;
    ensures cell->value == 2;
} by {
    execute();
    frame();
    simp();
}

void restore_one(struct cell* cell) {
    requires cell->value == 2;
    owns object(cell);
    mutable cell->value;
    ensures cell->value == 1;
} by {
    execute();
    frame();
    simp();
}

void require_one(struct cell* cell) {
    requires cell->value == 1;
    views object(cell);
} by {
    execute();
    simp();
}

int32 post_call_chain(struct cell* cell) {
    owns object(cell);
    mutable cell->value;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
