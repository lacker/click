# ordinary function entry does not reset globals to their initializer

Static-storage objects are initialized once before program startup. Entering a
later function must not recreate that initializer, or a caller can prove a
false result after another function has changed the object.

```c filename=global_entry_initializer_rejected.c
int32 counter = 3;

int32 increment_counter() {
    counter = counter + 1;
    return counter;
}

int32 read_counter() {
    return counter;
}

int32 run() {
    int32 ignored;
    ignored = increment_counter();
    return read_counter();
}
```

```click
verifying "global_entry_initializer_rejected.c";

int32 increment_counter() {
    requires counter < 1000;
    owns &counter[0..1];
    ensures result == old(counter) + 1;
    ensures counter == old(counter) + 1;
}

int32 read_counter() {
    ensures stale_initializer: result == 3;
}

int32 run() {
    owns &counter[0..1];
    ensures stale_initializer: result == 3;
}
```

```expect
fail: stale_initializer
```
