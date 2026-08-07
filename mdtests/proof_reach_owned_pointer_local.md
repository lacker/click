# branch preserves an owned selected pointer

Both branches select an owned input pointer, allowing the shared suffix to
mutate it at the common frontier.

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
        branch {
            ensuring {
                owns selected[0..1];
            }
            then {
                step();
            }
            else {
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
