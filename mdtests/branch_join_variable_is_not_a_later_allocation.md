# A branch join's abstracted local is not a later heap allocation

A branch interface abstracts every local the arms disagree on into a fresh
symbolic value, and a `malloc` invents a fresh allocation identity. Both come
from the execution's one identity counter, so nothing relates `picked` to
`fresh` and `have fresh == picked` has no proof.

The join used to count from the base of the execution's identity range with an
allocator of its own, and the surface carried the arms' counter across the join
unchanged. The very next allocation that does not first consult a reserved set
-- a heap identity, a re-bound loop binder's model fields, an aggregate
field -- was then handed an identity a live abstracted local was still using:
`picked` and the fresh allocation became the *same* symbolic block, and a
freshly allocated object aliased a pointer the caller passed in.

```c filename=branch_join_variable_is_not_a_later_allocation.c
int32* pick_then_allocate(int32* left, int32* right, int32 flag) {
    int32* picked;
    int32* fresh;
    if (flag >= 0) {
        picked = left;
    } else {
        picked = right;
    }
    fresh = malloc(4);
    return fresh;
}
```

```click
verifying "branch_join_variable_is_not_a_later_allocation.c";

int32* pick_then_allocate(int32* left, int32* right, int32 flag) {
    ensures 0 == 0;
} by {
    step();
    step();
    branch {
        ensuring {
            fact flag == flag;
        }
        then {
            step();
        }
        else {
            step();
        }
    }
    step();
    have fresh == picked by { simp(); }
    step();
    simp();
}
```

```expect
fail: `have` failed for `fresh == picked`
```
