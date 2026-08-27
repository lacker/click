# Symbolic-index store keeps a cell a recorded order separates

A store through a symbolic index keeps every cell whose index a strict order
in the proof context separates from the written one. The bare `step();`
carries nothing; the kernel's store edge freezes the transition's context and
a later load crosses it by that recorded order alone, so the fact about the
untouched cell is still available afterwards without any `using` list or
transport.

```c filename=set_then_read_end.c
int32 set_then_read_end(int32* data, int32 index, int32 len, int32 cap) {
    int32 value;
    data[index] = 1;
    value = data[len];
    return value;
}
```

```click
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource zero_terminated(data: int32*, len: int32, cap: int32) {
    owns data[0..cap];
    fact 0 <= len;
    fact len < cap;
    fact terminated_at(data, len);
}

verifying "set_then_read_end.c";

int32 set_then_read_end(int32* data, int32 index, int32 len, int32 cap) {
    requires 0 <= index;
    requires index < len;
    owns zero_terminated(data, len, cap);
    mutable data[index..index + 1];
    ensures result == 0;
} by {
    unfold(zero_terminated(data, len, cap));
    unfold(terminated_at);
    have index < cap by {
        apply(int32_lt_transitive(index, len, cap)) using {
            index < len;
            len < cap;
        }
        assumption();
    }
    step();
    step();
    have terminated_at(data, len) by {
        unfold(terminated_at);
        assumption();
    }
    step();
    fold(zero_terminated(data, len, cap));
    step();
    frame();
    simp();
}
```

```expect
pass
```
