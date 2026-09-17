# Sequence guarantees participate in callback refinement

```c filename=sequence_callback.c
void swap_pair(int32* cells) {
    int32 temporary = cells[0];
    cells[0] = cells[1];
    cells[1] = temporary;
}
void invoke(void (*callback)(int32*), int32* cells) {
    callback(cells);
}
void caller(int32* cells) {
    invoke(&swap_pair, cells);
}
```

```click
verifying "sequence_callback.c";

contract void PairPermutation(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[0], cells[1]])
         or [cells[0], cells[1]] == old([cells[1], cells[0]]);
}

void swap_pair(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[1], cells[0]]);
} by {
    execute();
    simp();
}

theorem swap_is_permutation() {
    ensures PairPermutation(&swap_pair) by {
        unfold(PairPermutation);
        simp();
    }
}

void invoke(void (*callback)(int32*), int32* cells) {
    requires PairPermutation(callback);
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[0], cells[1]])
         or [cells[0], cells[1]] == old([cells[1], cells[0]]);
} by {
    execute();
    simp();
}

void caller(int32* cells) {
    owns cells[0..2];
    ensures [cells[0], cells[1]] == old([cells[0], cells[1]])
         or [cells[0], cells[1]] == old([cells[1], cells[0]]);
} by {
    apply(swap_is_permutation());
    execute();
    simp();
}
```

```expect
pass
```
