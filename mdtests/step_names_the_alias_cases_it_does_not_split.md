# step names the alias cases it does not split

`step()` executes one statement into one checked successor. The load
`r = g[0]` after `g[u] = 7` has two, told apart only by whether `u == 0`, and a
simple step never splits the proof. The refusal names the statement, the
condition each case assumes, and the proof `if` that gives each case its own
frontier; `a_load_that_may_read_an_earlier_store_splits_into_its_cases.md`
proves the same function that way.

```c filename=step_names_the_alias_cases_it_does_not_split.c
int32 g[4];

int32 stepped(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}
```

```click
verifying "step_names_the_alias_cases_it_does_not_split.c";

int32 stepped(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8 or result == old(g[0]) + 1;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    close();
}
```

```expect
fail: a simple step never splits the proof. Split the proof on the case condition first, then step each case:
  if 0 == u {
```
