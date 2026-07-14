# advance abstracts a selected pointer

Both branches select a valid input pointer, and the shared suffix reads through
that selection. The `advance` interface hides which branch supplied the pointer
and exports only the viewed range needed by the continuation.

```c filename=advance_selected_pointer.c
int32 advance_selected_pointer(int32* left, int32* right, int32 choose_left) {
    int32* selected;
    if (choose_left != 0) {
        selected = left;
    } else {
        selected = right;
    }
    return selected[0];
}
```

```click
verifying "advance_selected_pointer.c";

int32 advance_selected_pointer(int32* left, int32* right, int32 choose_left) {
    requires read(left[0..1]);
    requires read(right[0..1]);

    ensures result == result by {
        execute_step();
        advance(statement(1).exit)
        ensuring {
            fact selected == left or selected == right;
            views selected[0..1];
        }
        by {
            if choose_left != 0 {
                execute_then_step();
                execute_step();
            } else {
                execute_else_step();
                execute_step();
            }
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
