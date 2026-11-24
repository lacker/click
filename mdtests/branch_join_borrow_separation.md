# A branch join separates changed cells from active views at entry

```c filename=branch_join_borrow_separation.c
int run(int *out, const int *input, int choice) {
    if (choice) {
        *out = 10;
    } else {
        *out = 11;
    }
    return *input;
}
```

```click
verifying "branch_join_borrow_separation.c";
int32 run(int32 *out, const int32 *input, int32 choice) {
    owns out[0..2];
    views input[0..1];
    ensures result == old(input[0]);
} by {
    have separate(memory((out as (uint8 *))[0..4]), memory(input[0..1])) by { close(); }
    branch ensuring {
        fact 1 == 1;
    } {
        true => { step(); }
        false => { step(); }
    }
    step();
}
```

```expect
pass
```
