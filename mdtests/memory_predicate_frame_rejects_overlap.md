# Predicate framing rejects an overlapping write

Automatic predicate frame transport must not preserve a predicate when the
executed statement writes the memory cell on which that predicate depends.

```c filename=overwrite_terminator.c
int32 overwrite_terminator(int32 data[], int32 length, int32 value) {
    data[length] = value;
    return 0;
}
```

```click
verifying "overwrite_terminator.c";

predicate terminated(int32 data[], int32 length) {
    data[length] == 0
}

int32 overwrite_terminator(int32 data[], int32 length, int32 value) {
    requires 0 <= length;
    requires length < 2147483647;
    requires value != 0;
    requires terminated(data, length);
    consumes data[0..length + 1];
    mutable data[length..length + 1];

    produces data[0..length + 1];
    ensures terminated(data, length);
} by {
    execute_step();
    have terminated(data, length) by simp;
    execute_step();
    frame();
    simp();
}
```

```expect
fail: missing pure fact: Predicate
```
