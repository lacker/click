# A bound after a call ignores the call's equality for the same value

Soundness: not soundness. Click refuses a true, one-step claim and names the
wrong cause. Nothing false is accepted.

`simp` (the closer of a bare `have P;`) must prove an order fact about a
value when the context already holds that value's equality to a constant. After a call
whose postcondition fixes a global's new value, the context holds exactly
that equality, yet `have g > -1000;` is refused. Its diagnostic also blames
the pre-call fact as possibly stale ("may have changed since the available
fact was stated") instead of the missing step, which misleads.

Reproduced on master `77548f53`:

```c
int g;
int bumpg(void) { g = g + 1; return 0; }
int h(void) { int a = bumpg(); return a; }
```

```click
verifying "s.c";
int bumpg() {
    requires g < 1000;
    owns g;
    ensures result == 0 by auto;
    ensures g == old(g) + 1 by auto;
}
int h() {
    requires g == 10;
    owns g;
    ensures result == 0;
} by {
    step();
    step();
    have g > -1000;
    execute();
    simp();
}
```

`have g > -1000;` fails with "could not establish `g > -1000`". The trace
after `step(bumpg(...))` shows `int32 =(load A=read<Bits32>(snapshot#1,
pointer=value#1), 11) is true`, and the goal reads the same `load A`. Adding
`have g == 11;` first makes the bound pass. The same happens for a struct
field (`counters[0].value` updated by the callee). Found while
un-quarantining `examples/multifile-registry`, whose `registry_run` proof
carries the extra `have counters[0].value == 11;` for this reason.

Acceptance:

- `have g > -1000;` directly after the call verifies in the reproduction,
  and the `have counters[0].value == 11;` step in
  `examples/multifile-registry/registry.click` can be removed.
- A bound the call's facts do not imply is still refused, and its diagnostic
  names the missing fact rather than a stale pre-call one.
