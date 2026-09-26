# undecided statement successors spell their condition

`step()` needs exactly one successor, and the unsigned comparison `x < 4`
splits this statement in two. The refusal lists the condition that tells the
successors apart, but it used to name only its kind,

```text
undecided condition:
  successor 1: signed less-than is true
  successor 2: signed less-than is false
```

which is the kernel's signed encoding of an unsigned comparison and does not
say which comparison. It now spells the condition itself.

```c filename=undecided_statement_successors_spell_their_condition.c
uint32 pick(uint32 x) {
    uint32 z;
    z = x < 4 ? x : 5;
    return z;
}
```

```click
verifying "undecided_statement_successors_spell_their_condition.c";

uint32 pick(uint32 x) {
    ensures result <= 5;
} by {
    step();
    step();
    step();
    simp();
}
```

```expect
fail: undecided condition:
  successor 1: `x < 4 (unsigned)`
  successor 2: `x < 4 (unsigned) is false`
```
