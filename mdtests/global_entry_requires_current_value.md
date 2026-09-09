# an explicit global precondition can state the current value

An ordinary function cannot assume a static-storage initializer, but a
precondition may constrain the current value at entry.

```c filename=global_entry_requires_current_value.c
int32 counter = 3;

int32 read_counter() {
    return counter;
}
```

```click
verifying "global_entry_requires_current_value.c";

int32 read_counter() {
    requires counter == 3;
    ensures result == 3;
}
```

```expect
pass
```
