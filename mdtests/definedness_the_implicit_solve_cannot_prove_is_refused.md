# definedness the implicit solve cannot prove is refused

`requires s == 1 or s == 40` admits a shift by 40, so the requirement
`s >= 0 and s < 32` does not hold and the step is refused at it.

```c filename=definedness_the_implicit_solve_cannot_prove_is_refused.c
unsigned shifted(unsigned x, int s) { return x << s; }
```

```click
verifying "definedness_the_implicit_solve_cannot_prove_is_refused.c";

uint32 shifted(uint32 x, int32 s) {
    requires s == 1 or s == 40;
    ensures result == result;
} by {
    step();
    close();
}
```

```expect
fail: invalid shift
```
