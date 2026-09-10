# Outcome proof cases use current memory, not an entry fact with the same spelling

```c filename=set_seven.c
void set_seven(int32* cell) { cell[0] = 7; }
```

```click
resource input_cell(cell: int32*) {
    owns cell[0..1];
    fact cell[0] == 8;
}
verifying "set_seven.c";
void set_seven(int32* cell) {
    consumes input_cell(cell);
    ensures cell[0] == 7;
} by {
    unfold(input_cell(cell));
    execute();
    have cell[0] == 7 by {
        if cell[0] == 8 {
            normalize();
        } else {
            normalize();
        }
    }
    assumption();
}
```

```expect
pass
```
