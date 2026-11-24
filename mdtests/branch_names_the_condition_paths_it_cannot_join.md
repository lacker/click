# branch names the condition paths it cannot join

A C `branch` has one arm per truth value. `x > 0 && y > 0` is false along two
checked paths, and one arm cannot stand for both, so `branch` refuses at the
`if` and lists each path with the facts that select it, instead of entering
one of them and failing at the join with "checked C branch split does not
exhaust its recorded condition paths". A proof `if` on `x > 0` first leaves one
path per arm in each case, and the implicit tail makes that split itself; see
`a_condition_reaching_one_value_along_two_paths_splits_into_them.md`.

```c filename=branch_names_the_condition_paths_it_cannot_join.c
int32 both_positive(int32 x, int32 y) {
    int32 r;
    if (x > 0 && y > 0) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}
```

```click
verifying "branch_names_the_condition_paths_it_cannot_join.c";

int32 both_positive(int32 x, int32 y) {
    ensures result == 2 or x > 0;
} by {
    step();
    branch { true => { step(); } false => { step(); } }
    step();
    close();
}
```

```expect
fail: its condition `((x > 0) && (y > 0))` is false along 2 checked paths, and `branch` has one arm per truth value
```
