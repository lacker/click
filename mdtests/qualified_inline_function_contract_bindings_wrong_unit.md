# Qualified inline calls bind the selected contract's resource outputs

```c filename=first.c
static inline void helper(int *p) { *p = 1; }
void run(int *p) { helper(p); }
```

```c filename=second.c
static inline void helper(int *p) { *p = 2; }
void other(int *p) { helper(p); }
```

```click
verifying "first.c" as first;
verifying "second.c" as second;
resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
void first::helper(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.value == 1;
} by {
    unfold(before); step_until(function.exit);
    let after = fold(cell(p), { value: 1 }); close();
}
void second::helper(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.value == 2;
} by {
    unfold(before); step_until(function.exit);
    let after = fold(cell(p), { value: 2 }); close();
}
void run(int32* p) {
    consumes input: cell(p);
    produces output: cell(p);
    ensures output.value == 1;
} by {
    let { after: output } = step(second::helper, { before: input });
}
void other(int32* p) {
    consumes input: cell(p);
    produces output: cell(p);
    ensures output.value == 2;
} by {
    let { after: output } = step(second::helper, { before: input });
}
```

```expect
fail: requires a call to `second::helper` at the current frontier
```
