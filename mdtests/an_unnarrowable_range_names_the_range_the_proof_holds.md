# an unnarrowable range names the range the proof holds

A refused range narrowing has to say what it was looking at. `views a[0..n]`
states a range, but a `views` clause becomes a resource rather than a recorded
`loadable` proposition, so the walk over stated propositions finds nothing and
used to report `no stated viewable range over the same base is available here
to narrow` — telling the reader to state a range their contract opens with.
The refusal names the range the proof actually holds over that base instead.

```c filename=unnarrowable_range_names_held_range.c
void walk(int32 *a, int32 *b, int32 n) {
    b[0] = 1;
}
```

```click
verifying "unnarrowable_range_names_held_range.c";

void walk(int32 *a, int32 *b, int32 n) {
    views a[0..n];
    owns b[0..n];
    requires 1 <= n;
    requires n <= 1073741823;
} by {
    have viewable(a[0..n + 1]) by { simp(); }
    execute();
    simp();
}
```

```expect
fail: `viewable(a[0..(n + 1)])` was not proved: the range this proof holds over that base is `a[0..n]`, so narrowing has to reach `viewable(a[0..(n + 1)])` from it, and it did not
```
