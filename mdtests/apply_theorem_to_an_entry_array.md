# a theorem argument that names the entry array is read there

A theorem parameter is bound to the array reference its argument denotes, and
an array reference is a memory together with a pointer. `old(box)` therefore
binds the parameter to the entry memory, so the theorem's own indexing of that
parameter reads the cell as the entry held it.

The body writes `box[0]`, so the entry cell and the current cell hold different
values. The application used to drop the `old` and check `a[0] == 3` against
the current memory, where the cell is `5`: a true instance was refused.

```c filename=apply_theorem_to_an_entry_array.c
int32 write_box(int32 box[1]) {
    box[0] = 5;
    return 0;
}
```

```click
verifying "apply_theorem_to_an_entry_array.c";

theorem head_is_three_is_small(a: int32[]) {
    requires a[0] == 3;

    ensures a[0] < 4 by {
        simp();
    }
}

int32 write_box(int32 box[1]) {
    requires box[0] == 3;
    consumes box[0..1];
    produces box[0..1];
    ensures old_head_small: old(box[0]) < 4 by {
        execute();
        apply(head_is_three_is_small(old(box))) using {
            old(box[0]) == 3;
        }
        assumption();
    }
}
```

```expect
pass
```
