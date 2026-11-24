# A false `transport using` between execution steps is refused

The entry value of `a[m]` is not known to be 5, so no listed premise carries
`at(entry, a[m]) == at(entry, a[m])` to `at(entry, a[m]) == 5`. Written between
execution steps, the `transport using` is refused. The companion
`a_false_transport_using_after_execution_is_refused.md` writes the same tactic at
function exit and expects the same refusal.

```c filename=a_false_transport_using_between_execution_steps_is_refused.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_false_transport_using_between_execution_steps_is_refused.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    step();
    have at(entry, a[m]) == at(entry, a[m]) by close();
    have at(entry, a[m]) == 5 by { close(); }
}
```

```expect
fail: `solve` failed
```
