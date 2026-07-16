# Explicitly framing a memory-dependent predicate

This checks that an execution proof can preserve a memory-dependent predicate
without automatic predicate frame transport. The proof unfolds the old
predicate, executes one store before the terminator, proves the terminator cell
is unchanged in the current memory state, and then re-establishes the predicate.
The second function checks that statement execution performs the same
deterministic transport automatically.

```c filename=set_before_terminator.c
int32 set_before_terminator(
    int32 data[],
    int32 length,
    int32 index,
    int32 value
) {
    data[index] = value;
    return data[length];
}
```

```c filename=set_before_terminator_auto.c
int32 set_before_terminator_auto(
    int32 data[],
    int32 length,
    int32 index,
    int32 value
) {
    data[index] = value;
    return data[length];
}
```

```click
verifying "set_before_terminator.c";
verifying "set_before_terminator_auto.c";

predicate terminated(int32 data[], int32 length) {
    data[length] == 0
}

int32 set_before_terminator(
    int32 data[],
    int32 length,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < length;
    requires length < 2147483647;
    requires terminated(data, length);
    consumes data[0..length + 1];
    mutable data[index..index + 1];

    produces data[0..length + 1];
    ensures terminated(data, length);
    ensures result == 0;
} by {
    unfold(terminated);
    execute_step();
    have data[length] == 0 by simp;
    have terminated(data, length) by {
        unfold(terminated);
        simp();
    }
    execute_step();
    frame();
    simp();
}

int32 set_before_terminator_auto(
    int32 data[],
    int32 length,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < length;
    requires length < 2147483647;
    requires terminated(data, length);
    consumes data[0..length + 1];
    mutable data[index..index + 1];

    produces data[0..length + 1];
    ensures terminated(data, length);
    ensures result == 0;
} by {
    execute_step();
    have terminated(data, length) by simp;
    execute_step();
    unfold(terminated);
    frame();
    simp();
}
```

```expect
pass
```
