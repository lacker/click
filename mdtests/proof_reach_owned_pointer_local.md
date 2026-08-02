# reach abstracts an owned selected pointer

Both branches select an owned input pointer. The `reach` interface exports
ownership of the selected cell, allowing the shared suffix to mutate it without
retaining either branch's concrete symbolic state.

```c filename=advance_owned_selected_pointer.c
int32 advance_owned_selected_pointer(
    int32* left,
    int32* right,
    int32 choose_left,
    int32 value
) {
    int32* selected;
    if (choose_left != 0) {
        selected = left;
    } else {
        selected = right;
    }
    selected[0] = value;
    return selected[0];
}
```

```click
verifying "advance_owned_selected_pointer.c";

int32 advance_owned_selected_pointer(
    int32* left,
    int32* right,
    int32 choose_left,
    int32 value
) {
    consumes left[0..1];
    consumes right[0..1];

    ensures result == value by {
        step();
        reach(statement(1).exit)
        ensuring {
            fact selected == left or selected == right;
            owns selected[0..1];
        }
        by {
            if choose_left != 0 {
                step();
                step();
            } else {
                step();
                step();
            }
        }
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
