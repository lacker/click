# known closes an evaluated goal

Binding `value` to the assigned constant `1` makes `have value == 1` the goal
`true`. The computational leaf of `close()` closes it directly.

```c filename=known_closes_an_evaluated_goal.c
int f(int x) { int r; r = 1; return r; }
```

```click
verifying "known_closes_an_evaluated_goal.c";

int32 f(int32 x) {
    ensures result == 1;
} by {
    step();
    let { result: value } = step();
    have value == 1 by close();
}
```

```expect
pass
```
