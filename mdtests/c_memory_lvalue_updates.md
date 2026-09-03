# C memory-lvalue compound updates

This checks that compound assignment and prefix/postfix increment syntax works
for indexed memory and typed struct fields, while retaining C's checked
read-modify-write behavior.

```c filename=update_index.c
int32 update_index(int32 values[]) {
    values[0] += 1;
    return values[0];
}
```

```c filename=increment_field.c
struct counter {
    int32 count;
};

int32 increment_field(struct counter* counter) {
    ++counter->count;
    return counter->count;
}
```

```c filename=decrement_field.c
struct counter {
    int32 count;
};

int32 decrement_field(struct counter* counter) {
    counter->count--;
    return counter->count;
}
```

```click
verifying "update_index.c";
verifying "increment_field.c";
verifying "decrement_field.c";

int32 update_index(int32 values[]) {
    consumes values[0..1];
    requires values[0] < 2147483647;
    ensures result == old(values[0]) + 1 by auto;
    ensures values[0] == old(values[0]) + 1 by auto;
    produces values[0..1] by auto;
}

int32 increment_field(struct counter* counter) {
    consumes counter->count;
    requires counter->count < 2147483647;
    ensures result == old(counter->count) + 1 by auto;
    ensures counter->count == old(counter->count) + 1 by auto;
    produces counter->count by auto;
}

int32 decrement_field(struct counter* counter) {
    consumes counter->count;
    requires counter->count > -2147483648;
    ensures result == old(counter->count) - 1 by auto;
    ensures counter->count == old(counter->count) - 1 by auto;
    produces counter->count by auto;
}
```

```expect
pass
```
