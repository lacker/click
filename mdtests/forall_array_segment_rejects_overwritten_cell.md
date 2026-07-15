# forall array segment rejects an overwritten cell

This checks that quantified segment preservation does not become vacuous:
`auto` should reject a `forall` postcondition when the segment includes a cell
that the function overwrites.

```c filename=forall_array_segment_rejects_overwritten_cell.c
int32 forall_array_segment_rejects_overwritten_cell(int32 p[]) {
    p[0] = 5;
    return 0;
}
```

```click
verifying "forall_array_segment_rejects_overwritten_cell.c";

int32 forall_array_segment_rejects_overwritten_cell(int32 p[]) {
    requires loadable(p, 4);
    consumes p[0..1];
    ensures segment_unchanged: forall (int32 k) {
        0 <= k and k < 1 implies p[k] == old(p[k])
    } by auto;
}
```

```expect
fail: missing pure fact
```
