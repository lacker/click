# branch preserves a selected pointer

Both branches select a valid input pointer, and the shared suffix reads through
that selection at the common frontier.

The selected pointer has no local name once the function has returned.
Certificate generation recovers a point-qualified spelling from the retained
program-point state so the final `simp` can replay without a hand-written
bridge.

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
    views left[0..1];
    views right[0..1];

    ensures result == left[0] or result == right[0] by {
        step();
        branch {
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
