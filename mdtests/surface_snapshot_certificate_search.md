# Surface certificate search follows relevant snapshots

Surface reconstruction should find a quantified fact at its recorded snapshot
even after many other program points have accumulated. It must index the
memory nested under the quantifier instead of constructing `old(...)` and
`at(...)` combinations over every recorded point.

```c filename=peek_first.c
int32 peek_first(int32 data[]) {
    return data[0];
}
```

```c filename=peek_many.c
int32 peek_many(int32 data[]) {
    int32 value;
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    value = peek_first(data);
    return value;
}
```

```click
verifying "peek_first.c";
verifying "peek_many.c";

int32 peek_first(int32 data[]) {
    views data[0..1];
    immutable;
    ensures result == data[0];
    ensures forall (k: int32) {
        0 <= k and k < 1 implies data[k] == old(data[k])
    };
} by {
    execute();
    frame();
    simp();
}

int32 peek_many(int32 data[]) {
    views data[0..1];
    immutable;
    ensures forall (k: int32) {
        0 <= k and k < 1 implies data[k] == old(data[k])
    };
} by {
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    step() using { loadable(data[0..1]); }
    execute();
    frame();
    simp();
}
```

```expect
pass
```
