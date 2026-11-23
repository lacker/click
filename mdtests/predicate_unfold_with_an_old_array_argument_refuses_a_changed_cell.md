# A predicate unfold with an `old` array argument refuses a changed cell

`overwrite_first` writes `p[0]`, so `same0(p, old(p))`, which unfolds to
`p[0] == old(p[0])`, does not follow, and `known` finds no fact for it.
Unfolding used to read `old(p)` in the current memory, which made the body
`p[0] == p[0]` and let `known` close it. Its companion,
`predicate_unfold_reads_an_old_array_argument_at_entry.md`, proves the
claim for a write to another cell.

```c filename=old_array_argument.c
int32 overwrite_first(int32 p[3]) { p[0] = 7; return 0; }
```

```click
verifying "old_array_argument.c";

predicate same0(a: int32[], b: int32[]) { a[0] == b[0] }

int32 overwrite_first(int32 p[3]) {
    consumes p[0..3];
    ensures kept: same0(p, old(p)) by {
        step();
        step();
        unfold(same0(p, old(p)));
        known();
    }
}
```

```expect
fail: `known()` could not close the current goal
```
