# a current-state premise may not discharge an entry-array requirement

The converse of `apply_theorem_to_an_entry_array.md`. The body clears `box[0]`,
so the theorem's requirement holds of the current array and fails of the entry
array. An application written at `old(box)` asks for the entry array, so the
current-state fact `box[0] < 1` is not its premise and the conclusion the
theorem would yield is about the entry cell, which is `7`.

The application used to drop the `old`, accept the current-state premise, and
state its conclusion about the current cell. That instantiation is a true
instance of the theorem — the parameter was uniformly bound to the current
memory, on both sides of the implication — so no false statement followed from
it, but the claim below is false and must not verify by any route.

```c filename=apply_theorem_to_an_entry_array_refuses_a_current_premise.c
int32 clear_head(int32 box[2]) {
    box[0] = box[1];
    return 0;
}
```

```click
verifying "apply_theorem_to_an_entry_array_refuses_a_current_premise.c";

theorem head_small_doubles(a: int32[]) {
    requires to_integer(0 - 1) < to_integer(a[0]);
    requires a[0] < 1;

    ensures to_integer(a[0] + a[0]) < 2 by {
        close();
    }
}

int32 clear_head(int32 box[2]) {
    requires box[0] == 7;
    requires box[1] == 0;
    owns box[0..2];
    ensures false_old_head_doubled: to_integer(old(box[0]) + old(box[0])) < 2 by {
        step_until(function.exit);
        have to_integer(0 - 1) < to_integer(box[0]) by {
            close();
        }
        have box[0] < 1 by {
            close();
        }
        apply(head_small_doubles(old(box)));
        close();
    }
}
```

```expect
fail: has an unproved obligation: `old(box)[0] < 1`
```
